import SubVerso.Examples
import Lean.Data.NameMap
import Lean.DocString.Syntax
import VersoManual
import Verso.Code.HighlightedToTex

open Lean (NameMap MessageSeverity)
open Lean.Doc.Syntax

namespace TPiL

open Verso Doc Elab Genre.Manual ArgParse Code Highlighted WebAssets Output Html Log Code External
open SubVerso.Highlighting
open SubVerso.Examples.Messages
open Lean
open Std

export Verso.Code.External (lit)

private def projectDir : System.FilePath := "../examples/"

def alphabet := "abcdefghijklmnopqrstuvwxyz0123456789"

def hashString (n : UInt64) : String := Id.run do
  let mut n : Nat := n.toNat
  let mut out : String := "Example" -- always start with a letter
  while n > 0 do
    out := out.push ({ byteIdx := n % 36 : String.Pos.Raw} |>.get! alphabet )
    n := n / 36
  return out

section
open System
open SubVerso.Module

variable [Monad m] [MonadError m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [MonadFinally m]
variable [MonadTrace m] [AddMessageContext m] [MonadOptions m] [MonadAlwaysExcept ε m]

/--
The SubVerso revision recorded in the example project's Lake manifest.

That revision writes the extracted JSON, and the copy of SubVerso that Verso brings in here
reads it back, so the serialization the two agree on is part of what an extraction depends on.
-/
def exampleSubversoRev : m String := do
  let manifestPath := projectDir / "lake-manifest.json"
  unless ← manifestPath.pathExists do
    throwError m!"File {manifestPath} doesn't exist, couldn't determine the SubVerso revision"
  let .ok json := Json.parse (← IO.FS.readFile manifestPath)
    | throwError m!"Expected JSON in {manifestPath}"
  let .ok packages := json.getObjValAs? (Array Json) "packages"
    | throwError m!"Expected a 'packages' array in {manifestPath}"
  for pkg in packages do
    match pkg.getObjValAs? String "name" with
    | .ok "subverso" =>
      match pkg.getObjValAs? String "rev" with
      | .ok rev => return rev
      | .error e => throwError m!"No revision for SubVerso in {manifestPath}: {e}"
    | _ => pure ()
  throwError m!"No SubVerso entry in {manifestPath}"

/--
Extracts the highlighted contents of an example.

When `expectErrors` is set, building the example is allowed to fail: the errors it reports are
described in the document, and checked against the extracted messages there. Extraction itself
must still succeed.
-/
def extractFile (contents : String) (suppressNamespaces : Option String)
    (expectErrors : Bool := false) : m (Array ModuleItem) := do
  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throwError m!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let toolchainfile := projectDir / "lean-toolchain"
  let toolchain ← do
      if !(← toolchainfile.pathExists) then
        throwError m!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trimAscii.copy

  -- Extractions are cached under a name derived from this hash, so it covers the tools that
  -- produce them as well as the code itself. A new toolchain or SubVerso yields a new name.
  let codeHash := hash (contents, toolchain, ← exampleSubversoRev)
  let modBase := hashString codeHash
  let filename := modBase ++ ".lean"
  let mod := "Examples." ++ modBase
  let jsonFile := s!"{modBase}.json"

  let jsonPath := (projectDir / "Examples" / jsonFile)
  let jsonExists : Bool ←
    if (← jsonPath.pathExists) then (IO.FS.readFile jsonPath) <&> (!·.isEmpty)
    else pure false

  unless jsonExists do
    IO.FS.writeFile (projectDir / "Examples" / filename) contents

    -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
    -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
    -- libraries.
    let lakeVars :=
      #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
        "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
        "LEAN", "ELAN", "ELAN_HOME", "LEAN_GITHASH",
        "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]


    let toolchainFile ← IO.FS.Handle.mk toolchainfile .read
    toolchainFile.lock (exclusive := true)
    try
      let cmd := "elan"

      let runCmd' (args : Array String) : m Unit := do
          let res ← IO.Process.output {
            cmd, args, cwd := projectDir
            -- Unset Lake's environment variables
            env := lakeVars.map (·, none)
          }
          if res.exitCode != 0 then reportFail projectDir cmd args res

      -- An example that reports errors builds unsuccessfully by design. Its messages are
      -- checked against the document after extraction.
      let runCmdAllowingErrors (args : Array String) : m Unit := do
          let res ← IO.Process.output {
            cmd, args, cwd := projectDir
            env := lakeVars.map (·, none)
          }
          if res.exitCode != 0 && !expectErrors then reportFail projectDir cmd args res

      let runCmd (trace : MessageData) (args : Array String) : m Unit :=
        withTraceNode `Elab.Verso.Code.External.loadModule (fun _ => pure trace) (runCmd' args)

      runCmd m!"loadModuleContent': building subverso" #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"]

      withTraceNode `Elab.Verso.Code.External.loadModule
        (fun _ => pure m!"loadModuleContent': building example project's module") do
        runCmdAllowingErrors #["run", "--install", toolchain, "lake", "build", "+" ++ mod]

      let suppressArgs :=
        if let some nss := suppressNamespaces then
          nss |>.splitToList (· == ' ') |>.filter (!String.isEmpty ·) |>.map (#["--suppress-namespace", ·]) |>.toArray |>.flatten
        else #[]

      withTraceNode `Elab.Verso.Code.External.loadModule (fun _ => pure m!"loadModuleContent': extracting '{mod}'") do
          let args :=
            #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod"] ++
            suppressArgs ++
            #[mod, "Examples/" ++ jsonFile]
          runCmd' args
    finally
      toolchainFile.unlock

  let jsonString ← IO.FS.readFile (projectDir / "Examples" / jsonFile)

  let .ok json := Json.parse jsonString
    | if jsonString.isEmpty then
        throwError s!"Expected JSON in {projectDir / "Examples" / jsonFile}, got empty output"
      else
        throwError s!"Expected JSON in {projectDir / "Examples" / jsonFile}, got {jsonString}"
  match Module.fromJson? json with
  | .error err =>
    throwError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
  | .ok m => pure m.items

where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : m α := do
    throwError ("Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr)

end

open Std.Iterators in
private def hasAtLeastM [Monad m] [Iterator α m β] [Productive α m] (it : IterM (α := α) m β) : Nat → m Bool
  | 0 => pure true
  | n + 1 => do
    match (← it.step).inflate with
    | .done .. => pure false
    | .skip it' .. => hasAtLeastM it' (n + 1)
    | .yield it' .. => hasAtLeastM it' n
termination_by n => (n, it.finitelyManySkips)

open Std.Iterators in
private def hasAtLeast [Iterator α Id β] [Productive α Id] (it : Iter (α := α) β) (n : Nat) : Bool :=
  hasAtLeastM it.toIterM n

def splitExample (code : Highlighted) : Option Highlighted × Highlighted := Id.run do
  let lines := code.lines
  let mut out := .empty
  for h : i in [0:lines.size] do
    let line := lines[i]
    if isSplit line then
      return (some out, lines.extract (i+1) lines.size |>.foldl (init := .empty) (· ++ ·))
    out := out ++ line
  return (none, out)
where
  isSplit (line : Highlighted) : Bool :=
    let trimmed := line.toString.trimAscii
    hasAtLeast trimmed.positions 4 && trimmed.all (· == '-')

partial def hlIsWs (hl : Highlighted) : Bool :=
  match hl with
  | .text s | .unparsed s => s.all Char.isWhitespace
  | .seq xs => xs.all hlIsWs
  | .span _ x | .tactics _ _ _ x => hlIsWs x
  | .point .. => true
  | .token .. => false


section

open SubVerso.Module

private inductive LineType where
  | whitespace
  | split
  | other

private def lineType (line : Highlighted) : LineType :=
  let trimmed := line.toString.trimAscii
  if trimmed.isEmpty then .whitespace
  else if hasAtLeast trimmed.positions 4 && trimmed.all (· == '-') then .split
  else .other


def detachPrefix (code : Array ModuleItem) : Option (Array ModuleItem) × Array ModuleItem := Id.run do
  let mut out : Array ModuleItem := #[]
  for h : i in [0:code.size] do
    let lines := code[i].code.lines
    -- Check for pre-split
    for h : j in [0:lines.size] do
      match lineType lines[j] with
      | .whitespace => continue
      | .other => break -- not a pre-split
      | .split =>
        let leadingWs := lines.extract 0 j
        let pre := out.modify (out.size - 1) (fun c => {c with code := c.code ++ .seq leadingWs})
        return (pre, #[{code[i] with code := .seq <| lines.extract (j+1)}] ++ code.extract (i + 1) code.size)
    -- Check for post-split
    for h : j in [0:lines.size] do
      let j' := lines.size - (j + 1)
      have : j' < lines.size := by
        have : j < lines.size := by get_elem_tactic
        omega
      match lineType lines[j'] with
      | .whitespace => continue
      | .other => break -- not a post-split
      | .split =>
        let trailingWs := lines.extract (j' + 1) lines.size
        let thisItem := { code[i] with code := lines.extract 0 j' |>.foldl (init := .empty) (· ++ ·) }
        let nextItem? := code[i + 1]? |>.map (fun c => {c with code := Highlighted.seq trailingWs ++ c.code})
        return (out.push thisItem, nextItem?.toArray ++ code.extract (i + 2) code.size)
    -- No split here
    out := out.push code[i]
  -- No split anywhere
  return (none, out)

def detachSuffix (code : Array ModuleItem) : Array ModuleItem × Option (Array ModuleItem) := Id.run do
  let mut out : Array ModuleItem := #[]
  for h : k in [0:code.size] do
    let i := code.size - (k + 1)
    have : i < code.size := by
      have : k < code.size := by get_elem_tactic
      omega
    let lines := code[i].code.lines
    -- Check for post-split
    for h : j in [0:lines.size] do
      let j' := lines.size - (j + 1)
      have : j' < lines.size := by
        have : j < lines.size := by get_elem_tactic
        omega
      match lineType lines[j'] with
      | .whitespace => continue
      | .other => break -- not a post-split
      | .split =>
        let trailingWs := lines.extract (j' + 1) lines.size
        let thisItem := { code[i] with code := lines.extract 0 j' |>.foldl (init := .empty) (· ++ ·) }
        let nextItem? := if i > 0 then some {code[i - 1] with code := Highlighted.seq trailingWs ++ code[i-1].code} else none
        return (nextItem?.toArray ++ code.extract (i + 2) code.size, out.push thisItem |>.reverse)
    -- Check for pre-split
    for h : j in [0:lines.size] do
      match lineType lines[j] with
      | .whitespace => continue
      | .other => break -- not a pre-split
      | .split =>
        let leadingWs := lines.extract 0 j
        return (code.extract 0 i |>.modify (i-1) (fun c => {c with code := c.code ++ .seq leadingWs}), some (out.push {code[i] with code := .seq (lines.extract (j+1))} |>.reverse))
    -- No split here
    out := out.push code[i]
  -- No split anywhere
  return (out.reverse, none)

def splitExample' (code : Array ModuleItem) : Option (Array ModuleItem) × Array ModuleItem × Option (Array ModuleItem) :=
  let (pre, code) := detachPrefix code
  let (code, suffix) := detachSuffix code
  (pre, code, suffix)

end

def copyButtonCss : String :=
r#"

.tpil-code-container {
    position: relative;
    margin: 20px 0;
}

.copy-btn,
.toggle-btn {
    position: absolute;
    top: 0px;
    background: inherit;
    color: black;
    border: none;
    border-radius: 4px;
    cursor: pointer;
    font-size: 12px;
    display: flex;
    align-items: center;
    opacity: 0.7;
    transition: opacity 0.2s;
    padding: 8px;
}

.copy-btn:hover,
.toggle-btn:hover {
    opacity: 1;
    background: #555;
}

.copy-btn {
    right: 10px;
    gap: 5px;
}

.toggle-btn {
    right: 45px; /* Position to the left of copy button */
}

.copy-btn.copied {
    background: #28a745;
}

.copy-icon,
.toggle-icon {
    width: 14px;
    height: 14px;
}

.hidden {
  display: grid;
  grid-template-rows: 1fr;
  transition: grid-template-rows 0.3s ease-out, opacity 0.2s ease-out, margin 0.3s ease-out;
  opacity: 0.8;
}

.tpil-hide-prefix .hidden {
  grid-template-rows: 0fr;
  opacity: 0;
  margin: 0;
}

.hidden > .hl.lean {
  overflow: hidden;
  margin-bottom: 0;
}
"#

def copyButtonJs : String :=
r#"
function addToggleButtonToElement(elementId, className = 'tpil-hide-prefix') {
    const element = document.getElementById(elementId);
    if (!element) {
        console.error(`Element with ID '${elementId}' not found`);
        return false;
    }

    // Create container wrapper if it doesn't exist
    let container = element.parentElement;
    if (!container.classList.contains('code-container')) {
        container = document.createElement('div');
        container.className = 'code-container';
        container.classList.toggle(className);

        // Insert container before element
        element.parentNode.insertBefore(container, element);

        // Move element into container
        container.appendChild(element);
    }

    // Remove existing toggle button if present
    const existingBtn = container.querySelector('.toggle-btn');
    if (existingBtn) {
        existingBtn.remove();
    }

    // Create toggle button
    const toggleBtn = document.createElement('button');
    toggleBtn.className = 'toggle-btn';
    toggleBtn.title = 'Show hidden lines';
    toggleBtn.innerHTML = `
        <svg class="toggle-icon" viewBox="0 0 24 24" fill="currentColor">
            <path d="M12 4.5C7 4.5 2.73 7.61 1 12c1.73 4.39 6 7.5 11 7.5s9.27-3.11 11-7.5c-1.73-4.39-6-7.5-11-7.5zM12 17c-2.76 0-5-2.24-5-5s2.24-5 5-5 5 2.24 5 5-2.24 5-5 5zm0-8c-1.66 0-3 1.34-3 3s1.34 3 3 3 3-1.34 3-3-1.34-3-3-3z"/>
        </svg>
    `;

    // Add click event listener
    toggleBtn.addEventListener('click', () => {
        container.classList.toggle(className);

        // Update icon based on state
        const isHidden = container.classList.contains(className);
        toggleBtn.innerHTML = !isHidden ? `
            <svg class="toggle-icon" viewBox="0 0 24 24" fill="currentColor">
                <path d="M12 7c2.76 0 5 2.24 5 5 0 .65-.13 1.26-.36 1.83l2.92 2.92c1.51-1.26 2.7-2.89 3.43-4.75-1.73-4.39-6-7.5-11-7.5-1.4 0-2.74.25-3.98.7l2.16 2.16C10.74 7.13 11.35 7 12 7zM2 4.27l2.28 2.28.46.46C3.08 8.3 1.78 10.02 1 12c1.73 4.39 6 7.5 11 7.5 1.55 0 3.03-.3 4.38-.84l.42.42L19.73 22 21 20.73 3.27 3 2 4.27zM7.53 9.8l1.55 1.55c-.05.21-.08.43-.08.65 0 1.66 1.34 3 3 3 .22 0 .44-.03.65-.08l1.55 1.55c-.67.33-1.41.53-2.2.53-2.76 0-5-2.24-5-5 0-.79.2-1.53.53-2.2zm4.31-.78l3.15 3.15.02-.16c0-1.66-1.34-3-3-3l-.17.01z"/>
            </svg>
        ` : `
            <svg class="toggle-icon" viewBox="0 0 24 24" fill="currentColor">
                <path d="M12 4.5C7 4.5 2.73 7.61 1 12c1.73 4.39 6 7.5 11 7.5s9.27-3.11 11-7.5c-1.73-4.39-6-7.5-11-7.5zM12 17c-2.76 0-5-2.24-5-5s2.24-5 5-5 5 2.24 5 5-2.24 5-5 5zm0-8c-1.66 0-3 1.34-3 3s1.34 3 3 3 3-1.34 3-3-1.34-3-3-3z"/>
            </svg>
        `;
        toggleBtn.title = isHidden ? 'Show hidden lines' : 'Hide lines';
    });

    // Position toggle button to the left of copy button if it exists
    const copyBtn = container.querySelector('.copy-btn');
    if (copyBtn) {
        container.insertBefore(toggleBtn, copyBtn);
    } else {
        container.appendChild(toggleBtn);
    }

    return true;
}

function addCopyButtonToElement(elementId, codeText) {
    const element = document.getElementById(elementId);
    if (!element) {
        console.error(`Element with ID '${elementId}' not found`);
        return false;
    }

    // Create container wrapper if it doesn't exist
    let container = element.parentElement;
    if (!container.classList.contains('code-container')) {
        container = document.createElement('div');
        container.className = 'tpil-code-container';

        // Insert container before element
        element.parentNode.insertBefore(container, element);

        // Move element into container
        container.appendChild(element);
    }

    // Remove existing copy button if present
    const existingBtn = container.querySelector('.copy-btn');
    if (existingBtn) {
        existingBtn.remove();
    }

    // Create copy button
    const copyBtn = document.createElement('button');
    copyBtn.className = 'copy-btn';
    copyBtn.title = 'Copy to clipboard';
    copyBtn.innerHTML = `
        <svg class="copy-icon" viewBox="0 0 24 24" fill="currentColor">
            <path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/>
        </svg>
    `;

    // Add click event listener
    copyBtn.addEventListener('click', async () => {
        try {
            // Copy the provided code text to clipboard
            await navigator.clipboard.writeText(codeText);

            // Show success feedback
            const originalText = copyBtn.innerHTML;
            copyBtn.innerHTML = `
                <svg class="copy-icon" viewBox="0 0 24 24" fill="currentColor">
                    <path d="M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41z"/>
                </svg>
                Copied!
            `;
            copyBtn.classList.add('copied');

            // Reset after 2 seconds
            setTimeout(() => {
                copyBtn.innerHTML = originalText;
                copyBtn.classList.remove('copied');
            }, 2000);

        } catch (err) {
            // Fallback for older browsers
            fallbackCopyTextToClipboard(codeText);

            // Show feedback
            copyBtn.textContent = 'Copied!';
            setTimeout(() => {
                copyBtn.innerHTML = `
                    <svg class="copy-icon" viewBox="0 0 24 24" fill="currentColor">
                        <path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/>
                    </svg>
                `;
            }, 2000);
        }
    });

    // Add button to container
    container.appendChild(copyBtn);
    return true;
}

// Fallback function for older browsers
function fallbackCopyTextToClipboard(text) {
    const textArea = document.createElement('textarea');
    textArea.value = text;
    textArea.style.position = 'fixed';
    textArea.style.left = '-999999px';
    textArea.style.top = '-999999px';
    document.body.appendChild(textArea);
    textArea.focus();
    textArea.select();

    try {
        document.execCommand('copy');
    } catch (err) {
        console.error('Fallback: Oops, unable to copy', err);
    }

    document.body.removeChild(textArea);
}

// Expose API function globally
window.addCopyButtonToElement = addCopyButtonToElement;
window.addToggleButtonToElement = addToggleButtonToElement;
"#

def examplesCss := r#"
.example {
  margin-left: 0.75em;
}
.example .hl.lean.block {
  margin: 0;
}
.example .information pre {
  margin: 0 0 0.25em 0;
}
"#

def tpilBlock (block : BlockDescr) : BlockDescr :=
  { block with
    extraJsFiles :=
      block.extraJsFiles
        |>.insert { filename := "copybutton.js", contents := copyButtonJs, sourceMap? := none }
    extraCssFiles :=
      block.extraCssFiles
        |>.insert { filename := "copybutton.css", contents := copyButtonCss }
        |>.insert { filename := "examples.css", contents := examplesCss }

    }

def tpilInline (inline : InlineDescr) : InlineDescr :=
  { inline with
    extraJsFiles :=
      inline.extraJsFiles
        |>.insert {filename := "copybutton.js", contents := copyButtonJs, sourceMap? := none}
    extraCssFiles :=
      inline.extraCssFiles
        |>.insert { filename := "copybutton.css", contents := copyButtonCss }
        |>.insert { filename := "examples.css", contents := examplesCss }
    }

structure ExampleItem where
  code : Highlighted
  output : Option Highlighted.Message
  trailing : String
deriving ToJson, FromJson, Repr, Quote

def verbatimBlock (cmd : Highlighted) : TeX :=
  let contents := cmd.trimOneTrailingNl.trimOneLeadingNl.toVerbatimTeX
  .seq #[.raw s!"\\begin\{LeanVerbatim}[vspace=0pt]\n", contents, .raw "\n\\end{LeanVerbatim}\n"]

block_extension Block.lean
    (allowToggle : Bool)
    (pre : Option Highlighted)
    (code : Array ExampleItem)
    (post : Option Highlighted)
    (goalVisibility : HighlightHtmlM.VisibleProofStates := .none)
    via withHighlighting, tpilBlock where
  data :=
    let defined : Array (Name × String) := code.flatMap (definedNames ·.code)
    .arr #[.bool allowToggle, toJson pre, toJson code, toJson post, toJson goalVisibility, toJson defined]
  traverse id data _ := do
    let .arr #[_allowToggle, _pre, _code, _post, _visibility, definesJson] := data
      | Verso.reportError s!"Expected array for Lean block, got {data.compress}"; return none
    match FromJson.fromJson? definesJson with
    | .error err =>
      Verso.reportError <| "Failed to deserialize code config during traversal:" ++ err
      return none
    | .ok (defines : Array (Name × String)) =>
      for (d, s) in defines do
        if d.isAnonymous then continue
        let d := d.toString
        let path ← (·.path) <$> read
        let _ ← externalTag id path d
        let context := (← read).headers.map (·.titleString)
        modify (·.saveDomainObject exampleDomain d id)
        if let some link := (← get).externalTags[id]? then
          modify (·.modifyDomainObjectData exampleDomain d fun v =>
            let v := if let .obj _ := v then v else .obj {}
            v.setObjVal! link.link (json%{"context": $context, "display": $s}))
    pure none
  toTeX :=
    open Verso.Output.TeX in
    open Verso.Doc.TeX in
    some <| fun _ _ _ data _ => do
      let .arr #[.bool _allowToggle, hlPreJson, hlJson, hlPostJson, goalVisibilityJson, _defs] := data
        | Verso.reportError "Expected five-element JSON for Lean code"
          pure .empty
      let pre ←
        match FromJson.fromJson? (α := Option Highlighted) hlPreJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code intro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let code ←
        match FromJson.fromJson? (α := Array ExampleItem) hlJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let _post ←
        match FromJson.fromJson? (α := Option Highlighted) hlPostJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code outro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let _visibility ←
        match FromJson.fromJson? (α := HighlightHtmlM.VisibleProofStates) goalVisibilityJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code outro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let codeIndent := code.foldl (init := pre.map (·.indentation)) (fun i? y => i?.map (min · y.1.indentation)) |>.getD 0
      let mut codeTeX : TeX := .empty

      for ⟨cmd, out?, ws⟩ in code do
        let cmd := cmd.deIndent codeIndent
        codeTeX := codeTeX ++ verbatimBlock cmd
        if let some msg := out? then
          codeTeX := codeTeX ++ (← msg.toTeX)
        unless ws.isEmpty do
          codeTeX := codeTeX ++ (← (Highlighted.text ws).toTeX)

      pure codeTeX

  extraJsFiles := .ofList [{ filename := "copybutton.js", contents := copyButtonJs, sourceMap? := none }]
  extraCssFiles := .ofList [
    { filename := "copybutton.css", contents := copyButtonCss },
    { filename := "examples.css", contents := examplesCss }
  ]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.bool allowToggle, hlPreJson, hlJson, hlPostJson, goalVisibilityJson, _defs] := data
        | Verso.reportError "Expected five-element JSON for Lean code"
          pure .empty
      let pre ←
        match FromJson.fromJson? (α := Option Highlighted) hlPreJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code intro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let code ←
        match FromJson.fromJson? (α := Array ExampleItem) hlJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let post ←
        match FromJson.fromJson? (α := Option Highlighted) hlPostJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code outro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let visibility ←
        match FromJson.fromJson? (α := HighlightHtmlM.VisibleProofStates) goalVisibilityJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code outro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl

      let codeIndent := code.foldl (init := pre.map (·.indentation)) (fun i? y => i?.map (min · y.1.indentation)) |>.getD 0

      let mut codeHtml : Html := .empty
      let mut codeString := ""

      if allowToggle then
        if let some p := pre then
          let p := p.deIndent codeIndent
          let inner ←
            withDefinitionsAsTargets false <|
            withVisibleProofStates visibility <|
            p.trimOneLeadingNl |>.blockHtml "examples" (trim := false) (g := Verso.Genre.Manual)
          codeHtml := codeHtml ++ {{ <div class="hidden">{{ inner }}</div> }}
          codeString := codeString ++ p.toString

      for ⟨cmd, out?, ws⟩ in code do
        let cmd := cmd.deIndent codeIndent
        let moreCode ←
          withDefinitionsAsTargets true <|
          withVisibleProofStates visibility <|
          cmd.trimOneLeadingNl |>.blockHtml "examples" (trim := false) (g := Verso.Genre.Manual)
        codeHtml := codeHtml ++ moreCode
        codeString := codeString ++ cmd.toString
        if let some msg := out? then
          let msgHtml ← msg.toHtml (g := Verso.Genre.Manual) []
          codeHtml := codeHtml ++ {{<pre class=s!"hl lean lean-output {msg.severity.class}">{{msgHtml}}</pre>}}
        unless ws.isEmpty do
          codeHtml := codeHtml ++ (← (Highlighted.text ws).blockHtml "examples" (trim := false) (g := Verso.Genre.Manual))

      if allowToggle then
        if let some p := post then
          let p := p.deIndent codeIndent
          let inner ←
            withDefinitionsAsTargets false <|
            withVisibleProofStates visibility <|
            p.trimOneLeadingNl |>.blockHtml "examples" (trim := false) (g := Verso.Genre.Manual)
          codeHtml := codeHtml ++ {{ <div class="hidden">{{ inner }}</div> }}
          codeString := codeString ++ p.toString

      let i ← uniqueId (g := Verso.Genre.Manual)
      let toCopy := (pre.map (·.toString)).getD "" ++ codeString
      let mut script := s!"addCopyButtonToElement({i.quote}, {toCopy.quote});"
      if allowToggle && (pre.isSome || post.isSome) then
        script := script ++ s!"\naddToggleButtonToElement({i.quote});"

      return {{
        <div class="example" id={{i}}>{{codeHtml}}</div>
        <script>
        {{Html.text false script}}
        </script>
      }}

block_extension Block.leanAnchor (code : Highlighted) (completeCode : String)
    via withHighlighting, tpilBlock where
  data := .arr #[toJson code, toJson completeCode]
  traverse _ _ _ := pure none
  toTeX :=
    open Verso.Output.TeX in
    open Verso.Doc.TeX in
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, completeCodeJson] := data
        | Verso.reportError "Expected two-element JSON for Lean code"
          pure .empty
      let code ←
        match FromJson.fromJson? (α := Highlighted) hlJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code block while rendering TeX: " ++ err
          return .empty
        | .ok hl => pure hl
      let _completeCode ←
        match FromJson.fromJson? (α := String) completeCodeJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code string while rendering TeX: " ++ err
          return .empty
        | .ok hl => pure hl

      let code := code.deIndent code.indentation
      pure (verbatimBlock code)

  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, completeCodeJson] := data
        | Verso.reportError "Expected two-element JSON for Lean code"
          pure .empty
      let code ←
        match FromJson.fromJson? (α := Highlighted) hlJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let completeCode ←
        match FromJson.fromJson? (α := String) completeCodeJson with
        | .error err =>
          Verso.reportError <| "Couldn't deserialize Lean code string while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl

      let code := code.deIndent code.indentation

      let codeHtml : Html := (← code.blockHtml "examples" (trim := false) (g := Verso.Genre.Manual))

      let i ← uniqueId (g := Verso.Genre.Manual)
      let mut script := s!"addCopyButtonToElement({i.quote}, {completeCode.quote});"

      return {{
        <div class="example" id={{i}}>{{codeHtml}}</div>
        <script>
        {{Html.text false script}}
        </script>
      }}

def proofStateStyle := r#"
.hl.lean.proof-state-view {
  white-space: collapse;
  margin-left: 0.75em;
}
.hl.lean.proof-state-view .hypothesis {
  display: table !important;
  border-spacing: 0 0.2rem;
  border-collapse: separate;
}
.hl.lean.proof-state-view .tactic-state {
  display: block;
  left: 0;
  padding: 0;
  border: none;
}

.hl.lean.proof-state-view .tactic-state:has(.goal + .goal) {
  display: flex;
  flex-wrap: wrap;
  gap: 2rem;
  justify-content: space-evenly;
  width: 100%;
}
.hl.lean.proof-state-view .tactic-state .goal {
  margin: 0 !important;
  align-self: flex-start;
  width: fit-content;
}
"#

block_extension Block.goals (goals : Array (Highlighted.Goal Highlighted))
    via withHighlighting, tpilBlock where
  data := toJson goals
  traverse _ _ _ := pure none
  toTeX :=
    open Verso.Output.TeX in
    open Verso.Doc.TeX in
    some <| fun _ _ _ data _ => do
      let goals ←
        match fromJson? (α := Array (Highlighted.Goal Highlighted)) data with
        | .ok v => pure v
        | .error e =>
          Verso.reportError <| "Failed to deserialize proof state: " ++ e
          return .empty
      -- TODO: lay these out side-by-side
      pure <| .seq (← goals.mapM (·.toTeX))
  extraCssFiles := .ofList [{ filename := "proof-state.css", contents := proofStateStyle }]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let goals ←
        match fromJson? (α := Array (Highlighted.Goal Highlighted)) data with
        | .ok v => pure v
        | .error e =>
          Verso.reportError <| "Failed to deserialize proof state: " ++ e
          return .empty
      pure {{
        <div class="hl lean proof-state-view" data-lean-context="examples">
          <span class="tactic-state">
            {{← if goals.isEmpty then
                pure {{"All goals completed! 🐙"}}
              else
                withCollapsedSubgoals (g := Verso.Genre.Manual) .never <|
                  .seq <$> (goals.mapIdxM (fun i x => x.toHtml (·.toHtml) i))}}
          </span>
        </div>
      }}

inline_extension Inline.goal (goal : Highlighted.Goal Highlighted)
    via withHighlighting, tpilInline where
  data := toJson goal
  traverse _ _ _ := pure none
  toTeX :=
    open Verso.Doc.TeX in
    open Verso.Output.TeX in
    some <| fun _ _ data _ => do
      let goal ←
        match fromJson? (α := Highlighted.Goal Highlighted) data with
        | .ok v => pure v
        | .error e =>
          Verso.reportError <| "Failed to deserialize proof goal: " ++ e
          return .empty
      verbatimInline (goal.name.getD "<anonymous>")

  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let goal ←
        match fromJson? (α := Highlighted.Goal Highlighted) data with
        | .ok v => pure v
        | .error e =>
          Verso.reportError <| "Failed to deserialize proof goal: " ++ e
          return .empty
      pure {{
        <code class="proof-goal-ref hl lean">
          <span class="tactic">
            {{goal.name |>.getD "<anonymous>"}}
            <span class="tactic-state">
              {{← goal.toHtml (g := Verso.Genre.Manual) (·.toHtml) 0}}
            </span>
          </span>
        </code>
      }}

def kbdCSS := r#"
code.unicode-abbrev {
  background-color: #eee;
  border-radius: 3px;
  border: 1px solid #ccc;
  white-space: nowrap;
}

kbd {
  white-space: nowrap;
}

kbd > code {
  background-color: #eee;
  border-radius: 3px;
  border: 1px solid #b4b4b4;
  box-shadow:
    0 1px 1px rgba(0, 0, 0, 0.2),
    0 2px 0 0 rgba(255, 255, 255, 0.7) inset;
  color: #333;
  display: inline-block;
  font-size: 0.85em;
  font-weight: 700;
  line-height: 1;
  padding: 2px 4px;
  white-space: nowrap;
  vertical-align: middle;
}
"#

inline_extension Inline.kbd (items : Array String) where
  data := toJson items
  traverse _ _ _ := pure none
  toTeX :=
    open Verso.Output.TeX in
    open Verso.Doc.TeX in
    let verb (s : String) : TeX := .seq #[.raw "\\verb|", .raw s, raw "|"] -- Fails if s contains "|"
    let verbs (ss : List String) : TeX := List.intersperse (TeX.text " ") (ss.map verb)
    some <| fun _ _ data _ => do
      let items ←
        match fromJson? (α := Array String) data with
        | .ok v => pure v
        | .error e =>
          Verso.reportError <| "Failed to deserialize keyboard shortcut: " ++ e
          return .empty
      if let #[item] := items then
        if item.startsWith "\\" then
          pure (verb item)
        else
          let items : List String := item.toList.map fun c => s!"{c}"
          pure (verbs items)
      else
        pure (verbs items.toList)

  extraCss := [kbdCSS]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let items ←
        match fromJson? (α := Array String) data with
        | .ok v => pure v
        | .error e =>
          Verso.reportError <| "Failed to deserialize keyboard shortcut: " ++ e
          return .empty
      if let #[item] := items then
        if item.startsWith "\\" then
          pure {{<code class="unicode-abbrev">{{item}}</code>}}
        else
          let items : Array Html := item.toList.toArray.map fun c =>  {{<code>{{s!"{c}"}}</code>}}
          pure {{<kbd>{{items}}</kbd>}}
      else
        let items : Array Html := items.map (fun (s : String) => {{<code>s!"{s}"</code>}})
        pure {{<kbd>{{items}}</kbd>}}

private def oneCodeStr [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m StrLit := do
  let #[code] := inlines
    | (if inlines.size == 0 then (throwError ·) else (throwErrorAt (mkNullNode inlines) ·)) "Expected one code element"
  let `(inline|code($code)) := code
    | throwErrorAt code "Expected a code element"
  return code

private def codeStrs [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m (Array StrLit) := do
  let mut out := #[]
  for i in inlines do
    match i with
    | `(inline|code($code)) =>
      out := out.push code
    | `(inline|$s:str) =>
      unless s.getString.all (·.isWhitespace) do
        throwErrorAt s "Expected a code literal"
    | other => throwErrorAt other "Expected a code literal"
  return out


structure Kept (α : Type u) where
  values : Array α
  next : Nat
  in_bounds : next < values.size
deriving Repr

instance [Inhabited α] : Inhabited (Kept α) where
  default := ⟨#[default], 0, by simp⟩

def Kept.add (kept : Kept α) (val : α) : Kept α where
  values := kept.values.set kept.next val (h := kept.in_bounds)
  next := if kept.next = 0 then kept.values.size - 1 else kept.next - 1
  in_bounds := by
    have := kept.in_bounds
    rw [Array.size_set]
    split <;> omega

instance [Monad m] : ForM m (Kept α) α where
  forM kept f := do
    for h : i in [kept.next:kept.values.size] do
      f kept.values[i]
    for h : i in [0:kept.next] do
      have := kept.in_bounds
      have : i < kept.next := by get_elem_tactic
      f kept.values[i]

instance [Monad m] : ForIn m (Kept α) α := ⟨ForM.forIn⟩

initialize recentHighlightsExt : EnvExtension (Kept Highlighted) ←
  registerEnvExtension (pure ⟨.replicate 12 .empty, 0, by simp⟩)

/--
A mapping from anchor names to the corresponding code. Each code element is paired with it's
de-anchored context for copy-paste purposes.
-/
initialize savedAnchorExt : EnvExtension (HashMap String (Highlighted × String)) ←
  registerEnvExtension (pure {})


def allProofInfo (hl : Highlighted) : Array Highlighted :=
  go #[] hl
where
  go (acc : Array Highlighted) : Highlighted → Array Highlighted
    | .seq xs =>
      xs.foldl (init := acc) go
    | .span _ x => go acc x
    | .tactics gs _ _ x => gs.foldl (init := (go acc x)) (fromGoal · ·)
    | .point .. | .text .. | .token .. | .unparsed .. => acc
  fromGoal (acc : Array Highlighted) (g : Highlighted.Goal Highlighted) :=
    g.hypotheses.foldl (init := acc.push g.conclusion) fun acc ⟨xs, hl, _⟩ =>
      let names : Highlighted := xs.foldl (init := .empty) fun hl tok =>
        if hl.isEmpty then .token tok
        else hl ++ .text " " ++ .token tok
      acc.push (names ++ .text " " ++ .token ⟨.unknown, ":"⟩ ++ .text " " ++ hl)


def saveBackref (hl : Highlighted) : DocElabM Unit := do
  -- Construct a document with all the proof states in it, so references can target them but they
  -- don't eat up individual slots in the history ring
  let hl := allProofInfo hl |>.foldl (init := hl) (· ++ .text "\n" ++ ·)

  modifyEnv (recentHighlightsExt.modifyState · (·.add hl))

structure ProofState where
  goals : Array (Highlighted.Goal Highlighted)
  start : Nat
  stop : Nat
  «syntax» : Highlighted
deriving Repr

initialize proofStatesExt : EnvExtension (HashMap String ProofState) ←
  registerEnvExtension (pure {})

/-- Extracts all messages from the given code. -/
def allInfo (hl : Highlighted) : Array (Highlighted.Message × Option Highlighted) :=
  match hl with
  | .seq xs => xs.flatMap allInfo
  | .point k str => #[(⟨k, str⟩, none)]
  | .tactics _ _ _ x => allInfo x
  | .span infos x => (infos.map fun (k, str) => (⟨k, str⟩, some x)) ++ allInfo x
  | .text .. | .token .. | .unparsed .. => #[]

/--
Splits the trailing text off some code.

Comments are read as text only when `comments` is set. Everywhere else they are part of the code
and are shown as they were written.
-/
def trailingText (hl : Highlighted) (comments := false) : Highlighted × String :=
  match hl with
  | .seq xs => Id.run do
    let mut txt := ""
    for h : i in [0:xs.size] do
      let i' := xs.size - (i + 1)
      have : i < xs.size := by get_elem_tactic
      have : i' < xs.size := by grind
      let (hl', txt') := trailingText xs[i'] comments
      txt := txt' ++ txt
      if hl'.isEmpty then continue
      else return (.seq (xs.extract 0 i' |>.push hl'), txt)
    return (.empty, txt)
  | .token ⟨kind, content⟩ =>
    if comments && kind.isComment then (.empty, content) else (hl, "")
  | .point .. => (hl, "")
  | .tactics i s e hl' =>
    let (hl', txt) := trailingText hl' comments
    (.tactics i s e hl', txt)
  | .span i hl' =>
    let (hl', txt) := trailingText hl' comments
    (.span i hl', txt)
  | .text txt | .unparsed txt => (.empty, txt)

/--
Splits the marker that introduces a message off a comment's text, along with the severity it
names, if any.

A comment below a command describes the message it produces only when marked this way, which
tells it apart from a comment that remarks on the code.
-/
def messageComment? (s : String) : Option (Option String × String) :=
  let s := s.trimAsciiStart
  if !s.startsWith "message" then none
  else
    let rest := s.drop "message".length
    if rest.startsWith ":" then
      some (none, (rest.drop 1).trimAsciiStart.copy)
    else if rest.startsWith "(" then
      match (rest.drop 1).split ')' |>.toList with
      | [sev, after] =>
        if !after.startsWith ":" then none
        else
          let named : Option String :=
            match sev.trimAscii.copy with
            | "info" => some "info"
            | "error" => some "error"
            | "warning" => some "warning"
            | _ => none
          named.map fun k => (some k, (after.drop 1).trimAsciiStart.copy)
      | _ => none
    else none

/-- A comment that describes the message a command produces. -/
structure ExpectedMessage where
  /-- The severity the comment names, if it names one. -/
  severity : Option String
  /-- The message text. -/
  text : String
  /-- The whitespace that followed the comment. -/
  trailing : String

/--
Extracts the text of a comment, which may span several lines.

Each line contributes its content after the delimiter and the single space that conventionally
follows it. Any further indentation is part of the text, because messages indent their details.
-/
private def commentContents (s : String) : Option ExpectedMessage :=
  let ws := s.takeEndWhile (·.isWhitespace)
  let lines : List String.Slice := (s.dropEnd ws.positions.length).split '\n' |>.toList
    |>.filter (fun l => !l.trimAscii.isEmpty)
  if lines.isEmpty then none
  else if lines.all (·.trimAsciiStart.startsWith "--") then
    let raw : List String := lines.map fun l =>
      let l := l.trimAsciiStart.dropWhile (· == '-')
      (if l.startsWith " " then l.drop 1 else l).copy
    -- The marker introduces the text rather than being part of it.
    -- Only a marked comment describes a message; any other is a remark on the code.
    (raw.head?.bind messageComment?).map fun m =>
      { severity := m.1, text := "\n".intercalate (m.2 :: raw.tail), trailing := ws.copy }
  else none

/--
The comment that describes a message.

A message of one line is written on the command's own line; a longer one is written on the lines
below it, at the command's indentation.
-/
def expectedComment (indent severity : String) (msg : String) : String :=
  let marker := "-- message(" ++ severity ++ "): "
  let lines := msg.split '\n' |>.toList |>.map (·.copy)
  match lines with
  | [] => ""
  | [one] => " " ++ marker ++ one
  | first :: rest =>
    let head := indent ++ marker ++ first
    let tail := rest.map fun l =>
      if l.trimAscii.isEmpty then indent ++ "--" else indent ++ "-- " ++ l
    "\n" ++ "\n".intercalate (head :: tail)

/-- The name of a message's severity. -/
def messageSeverityName (msg : Highlighted.Message) : String :=
  match msg.severity with
  | .info => "info"
  | .error => "error"
  | .warning => "warning"

/-- The indentation of the last line of some code. -/
def lastLineIndent (s : String) : String :=
  match s.split '\n' |>.toList |>.getLast? with
  | none => ""
  | some l => (l.takeWhile (· == ' ')).copy

/--
Extracts a trailing comment from code, if present.

Returns the code along with the comment and its trailing whitespace.
-/
def trailingComment (hl : Highlighted) : Highlighted × Option ExpectedMessage :=
  let x := trailingText hl (comments := true)
  match commentContents x.2 with
  | some txt' => (x.1, some txt')
  | none => (hl, none)


section

inductive ShowProofStates where
  | none
  | named (which : Array String)
  | all

structure LeanConfig where
  checkOutput : Bool
  suppressNamespaces : Option String
  allowVisible : Bool
  showProofStates : ShowProofStates
  «show» : Bool
  /--
  Whether the example is expected to report errors. Each error is described by a trailing
  comment on the command that reports it, and is shown along with the code.
  -/
  expectErrors : Bool

variable [Monad m] [MonadError m ] [MonadLiftT CoreM m]

instance : FromArgVal ShowProofStates m where
  fromArgVal := {
    description := "`all`, `none`, or a string literal",
    signature := .String ∪ .Ident
    get := fun
      | .name x =>
        match x.getId with
        | `all => pure .all
        | `none => pure .none
        | _ => do
          let h ← MessageData.hint m!"Use 'all', 'none', or a string" #["all", "none", "NAME1 NAME2 ...".quote] (ref? := x)
          throwErrorAt x m!"Expected 'all' or 'none' or a string literal\n{h}"
      | .str s => pure <| .named <| (s.getString.splitOn " ").toArray
      | .num n => do
        let h ← MessageData.hint m!"Use 'all', 'none', or a string" #["all", "none", "NAME1 NAME2 ...".quote] (ref? := n)
        throwErrorAt n m!"Expected 'all' or 'none' or a string literal\n{h}"
  }

instance : FromArgs LeanConfig m where
  fromArgs :=
    LeanConfig.mk <$>
      .namedD `check .bool true <*>
      .named `suppressNamespaces .string true <*>
      .namedD `allowVisible .bool true <*>
      .namedD' `showProofStates .none <*>
      .namedD' `show .true <*>
      .flag `error false

structure SavedLeanConfig where
  name : Option Ident
  suppressNamespaces : Option String

instance : FromArgs SavedLeanConfig m where
  fromArgs :=
    SavedLeanConfig.mk <$>
      (some <$> .positional `name .ident <|> pure none) <*>
      .named `suppressNamespaces .string true

end

def isNewline (hl : Highlighted) : Bool :=
  match hl with
  | .text str | .unparsed str => str == "\n"
  | .token .. => false
  | .seq xs => Id.run do
    for h : i in [0:xs.size] do
      if xs[i].isEmpty then continue
      else if isNewline xs[i] then return xs.extract (i+1) |>.all (·.isEmpty)
      else return false
    return false
  | .tactics _ _ _ x | .span _ x => isNewline x
  | .point .. => false



/-- The column at which the comment on a line begins, if it has one. -/
def commentColumn (hl : Highlighted) : Option Nat := (go 0 hl).2
where
  go (col : Nat) : Highlighted → Nat × Option Nat
    | .token ⟨k, content⟩ =>
      (col + content.length, if k.isComment then some col else none)
    | .text s | .unparsed s => (col + s.length, none)
    | .seq xs =>
      xs.foldl (init := (col, none)) fun (c, found) x =>
        let (c', f) := go c x
        (c', found.orElse (fun _ => f))
    | .span _ x | .tactics _ _ _ x => go col x
    | .point .. => (col, none)

/-- Whether a line is a comment that introduces a message. -/
def isMessageCommentLine (hl : Highlighted) : Bool :=
  let s := hl.toString.trimAsciiStart
  s.startsWith "--" && (messageComment? (s.dropWhile (· == '-')).copy).isSome

/-- Whether a line consists of a comment, along with any surrounding whitespace. -/
def isCommentLine (hl : Highlighted) : Bool :=
  hasComment hl && !hasCode hl
where
  hasComment : Highlighted → Bool
    | .token ⟨k, _⟩ => k.isComment
    | .seq xs => xs.any hasComment
    | .span _ x | .tactics _ _ _ x => hasComment x
    | _ => false
  hasCode : Highlighted → Bool
    | .token ⟨k, _⟩ => !k.isComment
    | .unparsed s => !s.all Char.isWhitespace
    | .seq xs => xs.any hasCode
    | .span _ x | .tactics _ _ _ x => hasCode x
    | _ => false

open SubVerso.Module in
/--
Leading anchor comments are always incorrect. They probably result from Lean placing them with the
_next_ command, so we should move them back up before processing them.

Line comments form one comment when they share a column, and a comment that describes a command
follows it directly: on the command's own line, on the lines below it, or both. Those move back as
well. A comment at some other column, or one held off by a blank line, is a separate comment that
belongs to the command below it.
-/
def fixupAnchorComments (items : Array ModuleItem) : Array ModuleItem := Id.run do
  let mut out := #[]
  let mut prev? : Option ModuleItem := none

  for i in items do
    let mut i := i
    if prev?.isSome then
      let mut lines := i.code.lines
      -- The column of the comment these lines belong to. A comment on the command's own line
      -- fixes it; otherwise the first of these lines does.
      let mut anchorCol? : Option Nat := prev?.bind fun p =>
        p.code.lines.filter (fun l => !l.toString.trimAscii.isEmpty) |>.back?.bind commentColumn
      let mut sawTerminator := false
      let mut sawBlank := false
      while h : lines.size > 0 do
        let mut take := false
        if isNewline lines[0] then
          -- The first one ends the previous command's own line; a second is a blank line, which
          -- separates a comment from the command above it.
          if sawTerminator then sawBlank := true
          sawTerminator := true
          take := true
        else if proofState? lines[0].toString |>.isOk then
          take := true
        else if !sawBlank && isCommentLine lines[0] then
          if let some col := commentColumn lines[0] then
            match anchorCol? with
            | some anchor => if anchor == col then take := true
            | none =>
              -- With no comment on the command's own line, only a marked one describes it.
              if isMessageCommentLine lines[0] then
                anchorCol? := some col
                take := true
        if take then
          prev? := prev?.map (fun i => {i with code := i.code ++ lines[0]})
          lines := lines.drop 1
        else break
      i := {i with code := .seq lines}
      if let some prev := prev? then
        out := out.push prev
    prev? := some i
  if let some prev := prev? then
    out := out.push prev

  return out

/--
Reports a comment that doesn't describe the message its command produced.

The corrected block is offered when the command occurs just once, so that replacing it is
unambiguous. Any existing comment is dropped, which moves it to the place that suits the message.
-/
def logCommentMismatch (block : StrLit) (itemText strippedText severity msg : String)
    (what : MessageData) : DocElabM Unit := do
  -- Replacing the command is unambiguous only when it occurs once.
  let parts := block.getString.split itemText |>.toList
  if parts.length == 2 then
    -- The comment describes the command, so it goes directly below it rather than past the blank
    -- lines that follow, which would attach it to whatever comes next.
    let ws := strippedText.takeEndWhile (·.isWhitespace)
    let body := (strippedText.dropEnd ws.positions.length).copy
    -- A comment runs to the end of its line, so what follows has to start on a new one.
    let sep := if ws.startsWith "\n" then "" else "\n"
    let fixed := body ++ expectedComment (lastLineIndent body) severity msg ++ sep ++ ws.copy
    let corrected := parts[0]!.copy ++ fixed ++ parts[1]!.copy
    let hint ← MessageData.hint "Describe the message that this command produces:"
      #[{suggestion := .string corrected}] (ref? := some block)
    logErrorAt block (what ++ hint)
  else logErrorAt block what

/--
Reports a comment that names a severity other than the one its command produced.

A comment that names no severity describes a message of any kind.
-/
def checkSeverity (block : StrLit) (itemText strippedText : String)
    (expected : ExpectedMessage) (msg : Highlighted.Message) : DocElabM Unit := do
  let actual := messageSeverityName msg
  if let some declared := expected.severity then
    unless declared == actual do
      logCommentMismatch block itemText strippedText actual msg.toString
        m!"This message is {actual}, but the comment describes {declared}."

private def showGoals (goals : Array (Highlighted.Goal Highlighted)) : MessageData := Id.run do
  if goals.isEmpty then return m!"No goals"
  let mut out := m!""
  for g in goals do
    if let some n := g.name then
      out := out ++ m!"case {n}\n"
    for ⟨xs, h, _⟩ in g.hypotheses do
      let xs := " ".intercalate (xs.toList.map (fun ⟨_, x⟩ => x))
      out := out ++ m!"{xs} : {h.toString}\n"
    out := out ++ m!"  {g.goalPrefix} {g.conclusion.toString}\n\n"
  pure out

@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, code => do
    let {checkOutput, suppressNamespaces, allowVisible, showProofStates, «show», expectErrors} ←
      parseThe LeanConfig args
    let mut showProofStates := showProofStates
    let codeBlock := code
    let codeStr := code.getString
    let contents ← extractFile codeStr suppressNamespaces expectErrors
    let contents := contents.filter (!·.code.isEmpty)
    let (pre, mid, post) := splitExample' contents
    let mid := fixupAnchorComments mid
    let pre : Option Highlighted := pre.map fun p => p.foldl (init := .empty) fun acc c => acc ++ c.code
    let mut toShow : Array ExampleItem := #[]
    let mut sawError := false
    let mut visibility : HighlightHtmlM.VisibleProofStates :=
      match showProofStates with
      | .none => .none
      | .all => .all
      | .named _ => .states #[]
    for item in mid do
      let code ←
        match item.code.anchored (textAnchors := false) with
        | .ok a =>
          for (k, v) in a.proofStates.toArray do
            if let .tactics goals start stop hl := v then
              logSilentInfo m!"Proof state {k} on `{v.toString}`:\n{showGoals goals}"
              modifyEnv (proofStatesExt.modifyState · (·.insert k ⟨goals, start, stop, hl⟩))
              if let (.states ss, .named xs) := (visibility, showProofStates) then
                if k ∈ xs then
                  visibility := .states (ss.push (start, stop))
                  showProofStates := .named (xs.filter (· ≠ k))
            else throwError "Unexpected syntax for proof state '{k}':{indentD <| repr v}"
          pure a.code
        | .error e =>
          throwError "Error while extracting proof states:{indentD e}"
      let item := {item with code}
      -- An error is attached to the code that provoked it rather than to a command keyword, so
      -- it is found separately from the output of commands like `#check`.
      let error? : Option Highlighted.Message := allInfo item.code |>.firstM fun (msg, _) =>
        if msg.severity matches .error then some msg else none
      if let some msg := error? then
        sawError := true
        let txt := msg.toString
        unless expectErrors do
          throwError "Unexpected error in example:{indentD txt}\n\
            Mark the code block with '+error' if the error is intended."
        let (code, comment?) := trailingComment item.code
        let some expected := comment?
          | logCommentMismatch codeBlock item.code.toString item.code.toString (messageSeverityName msg) txt
              m!"Undescribed error in example:{indentD txt}"
            toShow := toShow.push ⟨item.code, some msg, ""⟩
            continue
        checkSeverity codeBlock item.code.toString code.toString expected msg
        if checkOutput && !eqMessages expected.text txt then
          logCommentMismatch codeBlock item.code.toString code.toString (messageSeverityName msg) txt
            m!"Mismatch! Expected{indentD expected.text}\nbut got{indentD txt}"
        toShow := toShow.push ⟨code, some msg, dropOneNl expected.trailing⟩
      else
        match item.kind with
        | ``Lean.Parser.Command.check | ``Lean.Parser.Command.eval | ``Lean.reduceCmd | ``Lean.Parser.Command.check_failure
        | ``Lean.Parser.Command.print | ``Lean.Parser.Command.printAxioms | ``Lean.Parser.Command.printEqns
        | ``Lean.guardMsgsCmd =>
          let info? : Option Highlighted.Message := allInfo item.code |>.firstM fun (msg, hl?) =>
            if hl? matches some (.token ⟨.keyword .., _⟩) then some msg else none
          if let some msg := info? then
            if let (code, some expected) := trailingComment item.code then
              let txt := msg.toString
              checkSeverity codeBlock item.code.toString code.toString expected msg
              if checkOutput && !eqMessages expected.text txt then
                logCommentMismatch codeBlock item.code.toString code.toString (messageSeverityName msg) txt
                  m!"Mismatch! Expected{indentD expected.text}\nbut got{indentD txt}"
              toShow := toShow.push ⟨code, some msg, dropOneNl expected.trailing⟩
            else
              let (code', ws) := trailingText item.code
              toShow := toShow.push ⟨code', some msg, dropOneNl ws⟩
          else toShow := toShow.push ⟨item.code, none, ""⟩
        | _ => toShow := toShow.push ⟨item.code, none, ""⟩
    if expectErrors && !sawError then
      throwError "No error in example marked '+error'.\n\
        Remove the flag, so that an error here is reported."
    let post : Option Highlighted := post.map fun p => p.foldl (init := .empty) fun acc c => acc ++ c.code
    let visible := .seq <| toShow.map (·.1)
    saveBackref visible
    for (msg, _)  in allInfo visible do
      logSilentInfo msg.toString
    if let .named xs := showProofStates then
      unless xs.isEmpty do
        logWarning m!"Unused proof state names: {m!", ".joinSep (xs.map (m!"'{·}'")).toList}"
    if «show» then
      return #[← ``(Block.other (Block.lean $(quote allowVisible) $(quote pre) $(quote toShow) $(quote post) $(quote visibility)) #[])]
    else
      return #[]
where
  -- A comment that spans several lines lines up with the message; one that is written on a
  -- single line is compared as if the message were too.
  eqMessages (s1 s2 : String) :=
    SubVerso.Examples.Messages.messagesMatch s1 s2 ||
    SubVerso.Examples.Messages.messagesMatch (s1.replace "\n" " ") (s2.replace "\n" " ")
  dropOneNl (s : String) : String :=
    if s.back == '\n' then (s.dropEnd 1).copy else s


@[code_block_expander save]
def save : CodeBlockExpander
  | args, code => do
    let {name, suppressNamespaces} ← parseThe SavedLeanConfig args
    let codeStr := code.getString
    let contents ← extractFile codeStr suppressNamespaces
    let contents : Highlighted := .seq <| contents.map (·.code)
    match contents.anchored with
    | .error e => throwError s!"Error extracting anchors: {e}"
    | .ok {anchors, proofStates, code} =>
      let codeStr := code.toString
      for (k, v) in anchors.toArray do
        logSilentInfo m!"Anchor {k}:\n{v.toString}"
        modifyEnv (savedAnchorExt.modifyState · (·.insert k (v, codeStr)))
      for (k, v) in proofStates.toArray do
        if let .tactics goals start stop hl := v then
          logSilentInfo m!"Proof state {k} on `{v.toString}`:\n{showGoals goals}"
          modifyEnv (proofStatesExt.modifyState · (·.insert k ⟨goals, start, stop, hl⟩))
      if let some x := name then
        modifyEnv (savedAnchorExt.modifyState · (·.insert x.getId.toString (code, codeStr)))
    pure #[]

@[code_block_expander savedAnchor]
def savedAnchor : CodeBlockExpander
  | args, code => do
    let name ← ArgParse.run (.positional `name .ident) args
    let env ← getEnv
    let some (hl, complete) := (savedAnchorExt.getState env)[name.getId.toString]?
      | throwErrorAt name m!"Not found: '{name.getId}'"
    discard <| ExpectString.expectString "code" code hl.toString
    saveBackref hl
    return #[← ``(Block.other (Block.leanAnchor $(quote hl) $(quote complete)) #[])]

section

structure ProofStateConfig where
  name : StrLit

structure GoalConfig where
  name : StrLit

variable [Monad m] [MonadError m ] [MonadLiftT CoreM m]

private def strOrName : ValDesc m StrLit where
  description := "identifier or string literal"
  signature := .Ident ∪ .String
  get
    | .name x => pure <| Syntax.mkStrLit x.getId.toString (info := x.raw.getHeadInfo)
    | .str s => pure s
    | .num n => throwErrorAt n "Expected identifier or string literal"

instance : FromArgs ProofStateConfig m where
  fromArgs := ProofStateConfig.mk <$> .positional `name strOrName

instance : FromArgs GoalConfig m where
  fromArgs := GoalConfig.mk <$> .positional `name strOrName

end

@[code_block_expander proofState]
def proofState : CodeBlockExpander
  | args, code => do
    let {name} ← parseThe ProofStateConfig args
    let some {goals, ..} := (proofStatesExt.getState (← getEnv))[name.getString]?
      | let allStates := (proofStatesExt.getState (← getEnv)).keys
        let h ←
          if allStates.isEmpty then
            pure <| MessageData.hint' "Name a proof state with a suitable PROOF_STATE: comment"
          else
            MessageData.hint "Use a proof state name:" (allStates.toArray.map ({suggestion := .string ·})) (ref? := some name)
        logErrorAt name m!"Not found: {name.getString}\n{h}"
        return #[← ``(sorry)]
    let mut goalView := ""
    for g in goals do
      goalView := goalView ++ g.toString ++ "\n\n"
    goalView := goalView.trimAsciiEnd.copy ++ "\n"
    _ ← ExpectString.expectString "proof" code goalView
    return #[← ``(Block.other (Block.goals $(quote goals)) #[])]

@[role_expander goal]
def goal : RoleExpander
  | args, inls => do
    let {name} ← parseThe GoalConfig args
    let caseTag ← oneCodeStr inls
    let some {goals, ..} := (proofStatesExt.getState (← getEnv))[name.getString]?
      | logErrorAt name m!"Not found: {name.getString}"
        return #[← ``(sorry)]
    let goal? := goals.find? fun
      | {name := some x, ..} => caseTag.getString == x
      | _ => false
    let some goal := goal?
      | let validTags := goals.filterMap (·.name)
        let h ←
          if validTags.isEmpty then
            pure <| MessageData.hint' m!""
          else
            MessageData.hint m!"Use a case label:" (validTags.map ({suggestion := .string ·})) (ref? := some caseTag)
        logErrorAt caseTag m!"Not found: {caseTag.getString}\n{h}"
        return #[← ``(sorry)]
    return #[← ``(Inline.other (Inline.goal $(quote goal)) #[])]

structure Helper where
  highlight (term : String) (type? : Option String) : IO Highlighted
  command (cmd : String) : IO Highlighted
  signature (code : String) : IO Highlighted
  name (code : String) : IO Highlighted

open System in
open SubVerso.Helper in
def Helper.fromModule (setup : String) : IO Helper := do
  let codeHash := hash setup
  let modBase := "Interact" ++ hashString codeHash
  let filename := modBase ++ ".lean"
  let mod := "Examples." ++ modBase

  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let toolchainfile := projectDir / "lean-toolchain"
  let toolchain ← do
      if !(← toolchainfile.pathExists) then
        throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trimAscii.copy

  IO.FS.writeFile (projectDir / "Examples" / filename) setup

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

  let cmd := "elan"

  let toolchainFile ← IO.FS.Handle.mk toolchainfile .read
  toolchainFile.lock (exclusive := true)
  try
    let args := #["run", "--install", toolchain, "lake", "build", "subverso-helper"]
    let res ← IO.Process.output {
      cmd, args, cwd := projectDir
      -- Unset Lake's environment variables
      env := lakeVars.map (·, none)
    }
    if res.exitCode != 0 then reportFail projectDir cmd args res
  finally
    toolchainFile.unlock

  let setupFile ← IO.FS.Handle.mk (projectDir / "Examples" / filename) .read
  setupFile.lock (exclusive := true)
  try
    let args := #["run", "--install", toolchain, "lake", "env", "subverso-helper", mod]
    let (hlTm, hlCmd, hlSig, hlName) ← do
      let (procIn, proc) ← do
        let proc ← IO.Process.spawn {
          cmd, args, cwd := projectDir
          -- Unset Lake's environment variables
          env := lakeVars.map (·, none)
          stdin := .piped
          stdout := .piped
          stderr := .inherit
        }
        proc.takeStdin
      let mutex ← Std.Mutex.new (IO.FS.Stream.ofHandle procIn, IO.FS.Stream.ofHandle proc.stdout)
      let hlTm := fun (tm : String) (ty? : Option String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.term tm ty?)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      let hlCmd := fun (cmd : String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.command cmd)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      let hlSig := fun (cmd : String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.signature cmd)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      let hlName := fun (cmd : String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.name cmd)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      pure (hlTm, hlCmd, hlSig, hlName)

    return Helper.mk hlTm hlCmd hlSig hlName
  finally
    setupFile.unlock
where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"

  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : IO α := do
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr

initialize helperExt : EnvExtension (Option Helper) ←
  registerEnvExtension (pure none)

initialize defaultHelperExt : EnvExtension (Option Helper) ←
  registerEnvExtension (pure none)

@[directive_expander setup]
def setup : DirectiveExpander
  | args, contents => do
    ArgParse.done.run args
    if h : contents.size < 1 then
      throwError "Expected a setup code block"
    else
      let first := contents[0]
      let contents := contents.extract 1 contents.size
      let `(block|``` | $setupCode ```) := first
        | throwErrorAt first "Expected undecorated code block"
      if helperExt.getState (← getEnv) |>.isSome then
        throwError "Already highlighting Lean"
      let helper ← Helper.fromModule setupCode.getString
      modifyEnv fun env => helperExt.setState env (some helper)
      try
        contents.mapM elabBlock
      finally
        modifyEnv fun env => helperExt.setState env none


def prioritizedElab [Monad m] (prioritize : α → m Bool) (act : α  → m β) (xs : Array α) : m (Array β) := do
  let mut out := #[]
  let mut later := #[]
  for h:i in [0:xs.size] do
    let x := xs[i]
    if ← prioritize x then
      out := out.push (i, (← act x))
    else later := later.push (i, x)
  for (i, x) in later do
    out := out.push (i, (← act x))
  out := out.qsort (fun (i, _) (j, _) => i < j)
  return out.map (·.2)

open Lean Elab in
def isLeanBlock : TSyntax `block → CoreM Bool
  | `(block|```$nameStx:ident $_args*|$_contents:str```) => do
    let name ← realizeGlobalConstNoOverloadWithInfo nameStx
    return name == ``TPiL.lean || name == `TPiL.signature || name == `TPiL.savedAnchor
  | _ => pure false


/--
Elaborates Lean blocks first, maintaining the order of blocks. This makes their code available for `leanRef`.
-/
@[directive_expander leanFirst]
def leanFirst : DirectiveExpander
  | args, contents => do
    ArgParse.done.run args

    -- Elaborate Lean blocks first, so inlines in prior blocks can refer to them
    prioritizedElab (isLeanBlock ·) elabBlock contents


@[code_block_expander setup]
def setupCode : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let helper ← Helper.fromModule code.getString
    modifyEnv fun env => defaultHelperExt.setState env (some helper)
    return #[]

@[directive_expander comment]
def comment : DirectiveExpander
  | _, _ => pure #[]

@[directive_expander TODO]
def TODO : DirectiveExpander
  | _, _ => pure #[]

@[role_expander TODO]
def TODOinline : RoleExpander
  | _, _ => pure #[]

@[role_expander kw]
def kw : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO kw xref
    return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote kw.getString)])]

@[role_expander attr]
def attr : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO attr xref
    return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote kw.getString)])]


@[role_expander tactic]
def tactic : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO kw xref
    return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote kw.getString)])]

@[role_expander kbd]
def kbd : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kbd ← codeStrs inls
    return #[← ``(Inline.other (Inline.kbd $(quote <| kbd.map (·.getString))) #[])]

@[role_expander option]
def option : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    return #[← ``(Inline.code $(quote kw.getString))]


def currentHelper : DocElabM Helper := do
  if let some h := helperExt.getState (← getEnv) then pure h
  else if let some h := defaultHelperExt.getState (← getEnv) then pure h
  else
    let helper ← Helper.fromModule s!"-- EMPTY for {← getMainModule}\n"
    modifyEnv fun env => defaultHelperExt.setState env (some helper)
    pure helper

def multiVar? (str : String) : Option (Array String × String) := do
  let mut out := #[]
  let mut str := str.trimAscii
  repeat
    let pref1 := str.takeWhile alpha
    let length1 := pref1.positions.length
    if length1 < 1 then failure
    str := str.drop length1
    let pref2 := str.takeWhile (fun c => alpha c || c.isDigit)
    let length2 := pref2.positions.length
    str := str.drop length2
    let pref := pref1.copy ++ pref2.copy
    let c := str.startPos.get?
    if pref.length > 0 && (c.isEqSome ' ' || c.isEqSome ':') then
      out := out.push pref
      str := str.dropWhile (· == ' ')
    else failure

    if str.startPos.get? |>.isEqSome ':' then
      str := str.drop 1
      str := str.dropWhile (· == ' ')
      if str.isEmpty then failure
      return (out, str.copy)
  failure
where
  alpha c := c.isAlpha || c ∈ ['α', 'β', 'γ']

def highlightInline (code : String) (type? : Option String := none) : DocElabM Highlighted := do
  let helper ← currentHelper
  try
    if type?.isSome then throwError "failed"
    let some (vars, type) := multiVar? code
      | throwError "failed"
    let mut out : Highlighted := .empty
    for v in vars do
      out := out ++ (← helper.highlight v (some type)) ++ .text " "
    out := out ++ .text ": "
    out := out ++ (← helper.highlight type none)
    pure out
  catch e1 =>
    try
      let codeStr := "(\n" ++ code ++ "\n)"
      let hl ← helper.highlight codeStr type?
      pure (hl.lines.extract 1 (hl.lines.size - 1) |> Highlighted.seq)
    catch e2 =>
      throwError "Failed to highlight code. Errors:{indentD e1.toMessageData}\nand:{indentD e2.toMessageData}"

def highlightCommand (code : String) : DocElabM Highlighted := do
  let helper ← currentHelper
  helper.command code

def highlightSignature (code : String) : DocElabM Highlighted := do
  let helper ← currentHelper
  helper.signature code

def highlightName (code : String) : DocElabM Highlighted := do
  let helper ← currentHelper
  helper.name code

@[role_expander lean]
def leanInline : RoleExpander
  | args, inls => do
    let type? ← ArgParse.run (.named `type .string true) args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    try
      let hl ← highlightInline codeStr type?

      saveBackref hl

      return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e

@[role_expander name]
def name : RoleExpander
  | args, inls => do
    let show? ← ArgParse.run (.named `show .string true) args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    try
      let hl ← highlightName codeStr
      let hl :=
        if let some s := show? then
          if let .token ⟨k, _⟩ := hl then
            .token ⟨k, s⟩
          else hl
        else hl

      saveBackref hl
      match hl with
      | .token ⟨k, _⟩ =>
        match k with
        | .const _ sig doc? _ _ =>
          Hover.addCustomHover code <|
            s!"```\n{sig}\n```\n" ++
            (doc?.map ("\n\n***\n\n" ++ ·) |>.getD "")
        | .var _ sig _ =>
          Hover.addCustomHover code <|
            s!"```\n{sig}\n```\n"
        | _ => pure ()
      | _ => pure ()

      return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e


@[role_expander leanCommand]
def leanCommand : RoleExpander
  | args, inls => do
    let type? ← ArgParse.done.run args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    try
      let hl ← highlightCommand codeStr

      saveBackref hl
      for (msg, _) in allInfo hl do
        let k := match msg.severity with | .info => "info" | .error => "error" | .warning => "warning"
        logSilentInfo m!"{k}: {msg.toString}"

      return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e


@[code_block_expander leanCommand]
def leanCommandBlock : CodeBlockExpander
  | args, code => do
    let type? ← ArgParse.done.run args
    let codeStr := code.getString

    try
      let hl ← highlightCommand codeStr

      saveBackref hl
      for (msg, _) in allInfo hl do
        let k := match msg.severity with | .info => "info" | .error => "error" | .warning => "warning"
        logSilentInfo m!"{k}: {msg.toString}"

      return #[← ``(Block.other (Block.lean false none #[ExampleItem.mk $(quote hl) none ""] none) #[])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e


@[code_block_expander signature]
def signature : CodeBlockExpander
  | args, code => do
    let type? ← ArgParse.done.run args
    let codeStr := code.getString

    try
      let hl ← highlightSignature codeStr

      saveBackref hl
      for (msg, _) in allInfo hl do
        let k := match msg.severity with | .info => "info" | .error => "error" | .warning => "warning"
        logSilentInfo m!"{k}: {msg.toString}"

      return #[← ``(Block.other (Block.lean false none #[ExampleItem.mk $(quote hl) none ""] none) #[])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e


@[role_expander leanRef]
def leanRef : RoleExpander
  | args, inls => do
    let in? ← ArgParse.run (.named `in .string true) args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    for prev in recentHighlightsExt.getState (← getEnv) do
      if let some «in» := in? then
        if let some hl := prev.matchingExpr? «in» then
          if let some hl := hl.matchingExpr? codeStr then
            return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
          else break
      else if let some hl := prev.matchingExpr? codeStr then
        return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]

    throwError "Not found: '{codeStr}'"

@[role_expander empty]
def empty : RoleExpander
  | args, _inls => do
    ArgParse.done.run args
    return #[]

private def keywords := [
  "#print", "#eval", "#print axioms", "#reduce", "#check",
  "noncomputable", "protected", "partial",
  "import", "export", "local",
  "def", "example", "instance", "macro_rules", "axiom", "if", "then", "else", "show", "have", "calc",
  "universe", "section", "end", "variable", "open", "set_option",
  "let", "fun"
]

private def tactics := [
  "if", "then", "else", "show", "have", "calc", "simp", "rw",
  "let", "fun", "<;>"
]


private def leanLits := [
  "→", "->", ";", "×", ".", "_", "⟨", "⟩"
]


open MessageData (hint) in
/--
Internal detail of suggestion mechanism.
-/
@[inline_expander Lean.Doc.Syntax.code]
private def suggest : InlineExpander
  |  `(inline| code( $str )) => do
    let str' := str.getString

    -- unless verso.examples.suggest.get (← getOptions) do
    --   -- Delegate to the next handler
    --   Elab.throwUnsupportedSyntax
    if str' ∈ keywords then
      let h ← hint m!"Add the `kw` role:" #["{kw}`" ++ str' ++ "`"]
      logWarning <| m!"Code element could be a keyword." ++ h
    else if str'.startsWith "\\" then
      let h ← hint m!"Add the `kbd` role:" #["{kbd}`" ++ str' ++ "`"]
      logWarning <| m!"Code element could be a Unicode abbreviation." ++ h
    else if (← getOptionDecls).any (fun x _ => x.toString == str'.trimAscii) then
      let h ← hint m!"Add the `option` role:" #["{option}`" ++ str' ++ "`"]
      logWarning <| m!"Code element could be a compiler option." ++ h
    else
      let mut suggs : Array Meta.Hint.Suggestion := #[]
      let mut exns := #[]
      try
        let _ ← highlightInline str'
        suggs := suggs.push <| "{lean}`" ++ str' ++ "`"
      catch e =>
        exns := exns.push e
      if str' ∈ tactics then
        suggs := suggs.push <| "{tactic}`" ++ str' ++ "`"

      for prev in recentHighlightsExt.getState (← getEnv) do
        if let some _ := prev.matchingExpr? str' then
          suggs := suggs.push <| "{leanRef}`" ++ str' ++ "`"
          break
      if str' ∈ leanLits then
        suggs := suggs.push <| "{lit}`" ++ str' ++ "`"

      for (name, {goals := gs, ..}) in proofStatesExt.getState (← getEnv) do
        let name := if name.any (·.isWhitespace) then name.quote else name
        if gs.any (·.name |>.isEqSome str') then
          suggs := suggs.push <| "{goal " ++ name ++ "}`" ++ str' ++ "`"

      if suggs.isEmpty then
        let h ← hint m!"Add the `lit` role to indicate that it denotes literal characters:" #["{lit}`" ++ str' ++ "`"]
        logWarning <| m!"Code element is missing a role, and can't be Lean code:{m!"\nand\n".joinSep (exns.map (indentD ·.toMessageData) |>.toList)}" ++ h
      else
        let h ← hint m!"Add a `lean` role:" suggs
        logWarning <| m!"Code element could be highlighted." ++ h


    return (← ``(Inline.code $(quote str.getString)))
  | _ => Elab.throwUnsupportedSyntax
