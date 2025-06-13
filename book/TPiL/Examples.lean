import SubVerso.Examples
import Lean.Data.NameMap
import VersoManual

open Lean (NameMap MessageSeverity)

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
    out := out.push (alphabet.get! ⟨n % 36⟩)
    n := n / 36
  return out

section
open System
open SubVerso.Module

variable [Monad m] [MonadError m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [MonadFinally m]
variable [MonadTrace m] [AddMessageContext m] [MonadOptions m] [MonadAlwaysExcept ε m]

def extractFile (contents : String) (suppressNamespaces : Option String) : m (Array ModuleItem) := do
  let codeHash := hash contents
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

    -- Validate that the path is really a Lean project
    let lakefile := projectDir / "lakefile.lean"
    let lakefile' := projectDir / "lakefile.toml"
    if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
      throwError m!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
    let toolchainfile := projectDir / "lean-toolchain"
    let toolchain ← do
        if !(← toolchainfile.pathExists) then
          throwError m!"File {toolchainfile} doesn't exist, couldn't load project"
        pure (← IO.FS.readFile toolchainfile).trim

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

      let runCmd (trace : MessageData) (args : Array String) : m Unit :=
        withTraceNode `Elab.Verso.Code.External.loadModule (fun _ => pure trace) (runCmd' args)

      runCmd m!"loadModuleContent': building subverso" #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"]

      runCmd m!"loadModuleContent': building example project's module" #["run", "--install", toolchain, "lake", "build", "+" ++ mod]

      let suppressArgs :=
        if let some nss := suppressNamespaces then
          nss |>.split (· == ' ') |>.filter (!String.isEmpty ·) |>.map (#["--suppress-namespace", ·]) |>.toArray |>.flatten
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

  let .ok (.arr json) := Json.parse jsonString
    | if jsonString.isEmpty then
        throwError s!"Expected JSON array in {projectDir / "Examples" / jsonFile}, got empty output"
      else
        throwError s!"Expected JSON array in {projectDir / "Examples" / jsonFile}, got {jsonString}"
  match json.mapM fromJson? with
  | .error err =>
    throwError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
  | .ok val => pure val

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
    let trimmed := line.toString.trim
    trimmed.length ≥ 4 && trimmed.all (· == '-')

partial def hlIsWs (hl : Highlighted) : Bool :=
  match hl with
  | .text s => s.all (·.isWhitespace)
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
  let trimmed := line.toString.trim
  if trimmed.isEmpty then .whitespace
  else if trimmed.length ≥ 4 && trimmed.all (· == '-') then .split
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
  for h : i in [0:code.size] do
    let i := code.size - (i + 1)
    have : i < code.size := by
      rename_i i' _ _
      have : i' < code.size := by get_elem_tactic
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

def trimOneLeadingNl : Highlighted → Highlighted
  | .text s => .text <| if "\n".isPrefixOf s then s.drop 1 else s
  | .seq xs =>
    let i? := xs.findIdx? (!·.isEmpty)
    match h : i? with
    | some i =>
      have : i < xs.size := (Array.findIdx?_eq_some_iff_findIdx_eq.mp h).left
      xs.extract (i+1) |>.foldl (init := trimOneLeadingNl xs[i]) (· ++ ·)
    | none => .empty
  | hl@(.point ..) | hl@(.token ..) => hl
  | .tactics i s e hl => .tactics i s e (trimOneLeadingNl hl)
  | .span i hl => .span i (trimOneLeadingNl hl)

structure ExampleItem where
  code : Highlighted
  output : Option (Highlighted.Span.Kind × String)
  trailing : String
deriving ToJson, FromJson, Repr, Quote

block_extension Block.lean
    (allowToggle : Bool)
    (pre : Option Highlighted)
    (code : Array ExampleItem)
    (post : Option Highlighted)
    (goalVisibility : HighlightHtmlM.VisibleProofStates := .none) where
  data := .arr #[.bool allowToggle, toJson pre, toJson code, toJson post, toJson goalVisibility]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy), ("copybutton.js", copyButtonJs)]
  extraCssFiles := [("tippy-border.css", tippy.border.css), ("copybutton.css", copyButtonCss), ("examples.css", examplesCss)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.bool allowToggle, hlPreJson, hlJson, hlPostJson, goalVisibilityJson] := data
        | HtmlT.logError "Expected five-element JSON for Lean code"
          pure .empty
      let pre ←
        match FromJson.fromJson? (α := Option Highlighted) hlPreJson with
        | .error err =>
          HtmlT.logError <| "Couldn't deserialize Lean code intro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let code ←
        match FromJson.fromJson? (α := Array ExampleItem) hlJson with
        | .error err =>
          HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let post ←
        match FromJson.fromJson? (α := Option Highlighted) hlPostJson with
        | .error err =>
          HtmlT.logError <| "Couldn't deserialize Lean code outro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let visibility ←
        match FromJson.fromJson? (α := HighlightHtmlM.VisibleProofStates) goalVisibilityJson with
        | .error err =>
          HtmlT.logError <| "Couldn't deserialize Lean code outro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl

      let codeIndent := code.foldl (init := pre.map (·.indentation)) (fun i? y => i?.map (min · y.1.indentation)) |>.getD 0

      let mut codeHtml : Html := .empty
      let mut codeString := ""

      if allowToggle then
        if let some p := pre then
          let p := p.deIndent codeIndent
          let inner ← withVisibleProofStates visibility <|  trimOneLeadingNl p |>.blockHtml "examples" (trim := false)
          codeHtml := codeHtml ++ {{ <div class="hidden">{{ inner }}</div> }}
          codeString := codeString ++ p.toString

      let outClass
        | .info => "information"
        | .warning => "warning"
        | .error => "error"

      for ⟨cmd, out?, ws⟩ in code do
        let cmd := cmd.deIndent codeIndent

        codeHtml := codeHtml ++ (← withVisibleProofStates visibility <| trimOneLeadingNl cmd |>.blockHtml "examples" (trim := false))
        codeString := codeString ++ cmd.toString
        if let some (k, out) := out? then
          codeHtml := codeHtml ++ {{ <div class={{outClass k}}><pre>{{out}}</pre></div> }}
        unless ws.isEmpty do
          codeHtml := codeHtml ++ (← (Highlighted.text ws).blockHtml "examples" (trim := false))

      if allowToggle then
        if let some p := post then
          let p := p.deIndent codeIndent
          let inner ← withVisibleProofStates visibility <|  trimOneLeadingNl p |>.blockHtml "examples" (trim := false)
          codeHtml := codeHtml ++ {{ <div class="hidden">{{ inner }}</div> }}
          codeString := codeString ++ p.toString

      let i ← uniqueId
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

def proofStateStyle := r#"
.hl.lean.proof-state-view {
  white-space: collapse;
}
.hl.lean.proof-state-view .tactic-state {
  display: block;
  left: 0;
  padding: 0;
  border: none;
}

.hl.lean.proof-state-view .tactic-state:has(.goal + .goal) {
  display: flex;
  justify-content: space-evenly;
  width: 100%;
}
.hl.lean.proof-state-view .tactic-state .goal {
  margin: 0 !important;
  align-self: flex-start;
}
"#

block_extension Block.goals (goals : Array (Highlighted.Goal Highlighted)) where
  data := toJson goals
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css), ("proof-state.css", proofStateStyle)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let goals ←
        match fromJson? (α := Array (Highlighted.Goal Highlighted)) data with
        | .ok v => pure v
        | .error e =>
          HtmlT.logError <| "Failed to deserialize proof state: " ++ e
          return .empty
      pure {{
        <div class="hl lean proof-state-view" data-lean-context="examples">
          <span class="tactic-state">
            {{← if goals.isEmpty then
                pure {{"All goals completed! 🐙"}}
              else
                withCollapsedSubgoals .never <|
                  .seq <$> goals.mapIndexedM (fun ⟨i, _⟩ x => x.toHtml (·.toHtml) i)}}
          </span>
        </div>
      }}

inline_extension Inline.goal (goal : Highlighted.Goal Highlighted) where
  data := toJson goal
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let goal ←
        match fromJson? (α := Highlighted.Goal Highlighted) data with
        | .ok v => pure v
        | .error e =>
          HtmlT.logError <| "Failed to deserialize proof goal: " ++ e
          return .empty
      pure {{
        <code class="proof-goal-ref hl lean">
          <span class="tactic">
            {{goal.name.map (·.toString) |>.getD "<anonymous>"}}
            <span class="tactic-state">
              {{← goal.toHtml (·.toHtml) 0}}
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
}
"#

inline_extension Inline.kbd (items : Array String) where
  data := toJson items
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [kbdCSS]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let items ←
        match fromJson? (α := Array String) data with
        | .ok v => pure v
        | .error e =>
          HtmlT.logError <| "Failed to deserialize keyboard shortcut: " ++ e
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

instance [Inhabited α] : Inhabited (Kept α) where
  default := ⟨#[default], 0, by simp⟩

def Kept.add (kept : Kept α) (val : α) : Kept α where
  values := kept.values.set kept.next val (h := kept.in_bounds)
  next := if kept.next = 0 then kept.values.size - 1 else kept.next - 1
  in_bounds := by
    have := kept.in_bounds
    rw [Array.size_set]
    split <;> omega

instance : ForM m (Kept α) α where
  forM kept f := do
    for h : i in [kept.next:kept.values.size] do
      f kept.values[i]
    for h : i in [0:kept.next] do
      have := kept.in_bounds
      have : i < kept.next := by get_elem_tactic
      f kept.values[i]

instance : ForIn m (Kept α) α := ⟨ForM.forIn⟩

initialize recentHighlightsExt : EnvExtension (Kept Highlighted) ←
  registerEnvExtension (pure ⟨.replicate 12 .empty, 0, by simp⟩)


def allProofInfo (hl : Highlighted) : Array Highlighted :=
  go #[] hl
where
  go (acc : Array Highlighted) : Highlighted → Array Highlighted
    | .seq xs =>
      xs.foldl (init := acc) go
    | .span _ x => go acc x
    | .tactics gs _ _ x => gs.foldl (init := (go acc x)) (fromGoal · ·)
    | .point .. | .text .. | .token .. => acc
  fromGoal (acc : Array Highlighted) (g : Highlighted.Goal Highlighted) :=
    g.hypotheses.foldl (init := acc.push g.conclusion) fun acc (x, k, hl) =>
      acc.push (Highlighted.token ⟨k, x.toString⟩ ++ .text " " ++ .token ⟨.unknown, ":"⟩ ++ .text " " ++ hl)


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
def allInfo (hl : Highlighted) : Array (Highlighted.Span.Kind × String × Option Highlighted) :=
  match hl with
  | .seq xs => xs.flatMap allInfo
  | .point k str => #[(k, str, none)]
  | .tactics _ _ _ x => allInfo x
  | .span infos x => (infos.map fun (k, str) => (k, str, some x)) ++ allInfo x
  | .text .. | .token .. => #[]

def trailingText (hl : Highlighted) : Highlighted × String :=
  match hl with
  | .seq xs => Id.run do
    let mut txt := ""
    for h : i in [0:xs.size] do
      let i' := xs.size - (i + 1)
      have : i < xs.size := by get_elem_tactic
      have : i' < xs.size := by omega
      let (hl', txt') := trailingText xs[i']
      txt := txt' ++ txt
      if hl'.isEmpty then continue
      else return (.seq (xs.extract 0 i' |>.push hl'), txt)
    return (.empty, txt)
  | .point .. | .token .. => (hl, "")
  | .tactics i s e hl' =>
    let (hl', txt) := trailingText hl'
    (.tactics i s e hl', txt)
  | .span i hl' =>
    let (hl', txt) := trailingText hl'
    (.span i hl', txt)
  | .text txt => (.empty, txt)

/--
Extracts a trailing comment from code, if present.

Returns the code along with the comment and its trailing whitespace.
-/
def trailingComment (hl : Highlighted) : Highlighted × Option (String × String) :=
  let (hl', txt) := trailingText hl
  if let some txt' := commentContents txt then
    (hl', some txt')
  else (hl, none)
where
  commentContents s :=
    let s := s.trimLeft
    if "--".isPrefixOf s then
      let s := s.dropWhile (· == '-') |>.trimLeft
      let ws := s.takeRightWhile (·.isWhitespace)
      some (s.dropRight ws.length, ws)
    else
      none

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

variable [Monad m] [MonadError m ] [MonadLiftT CoreM m]

instance : FromArgVal ShowProofStates m where
  fromArgVal := {
    description := "`all`, `none`, or a string literal",
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
      .namedD' `show .true

end

def isNewline (hl : Highlighted) : Bool :=
  match hl with
  | .text str => str == "\n"
  | .token .. => false
  | .seq xs => Id.run do
    for h : i in [0:xs.size] do
      if xs[i].isEmpty then continue
      else if isNewline xs[i] then return xs.extract (i+1) |>.all (·.isEmpty)
      else return false
    return false
  | .tactics _ _ _ x | .span _ x => isNewline x
  | .point .. => false



open SubVerso.Module in
/--
Leading anchor comments are always incorrect. They probably result from Lean placing them with the
_next_ command, so we should move them back up before processing them.
-/
def fixupAnchorComments (items : Array ModuleItem) : Array ModuleItem := Id.run do
  let mut out := #[]
  let mut prev? : Option ModuleItem := none

  for i in items do
    let mut i := i
    if prev?.isSome then
      let mut lines := i.code.lines
      while h : lines.size > 0 do
        if isNewline lines[0] || (proofState? lines[0].toString |>.isOk) then
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

private def showGoals (goals : Array (Highlighted.Goal Highlighted)) : MessageData := Id.run do
  if goals.isEmpty then return m!"No goals"
  let mut out := m!""
  for g in goals do
    if let some n := g.name then
      out := out ++ m!"case {n.toString}\n"
    for (x, _, h) in g.hypotheses do
      out := out ++ m!"  {x.toString} : {h.toString}\n"
    out := out ++ m!"  {g.goalPrefix} {g.conclusion.toString}\n\n"
  pure out

@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, code => do
    let {checkOutput, suppressNamespaces, allowVisible, showProofStates, «show»} ← parseThe LeanConfig args
    let mut showProofStates := showProofStates
    let codeStr := code.getString
    let contents ← extractFile codeStr suppressNamespaces
    let contents := contents.filter (!·.code.isEmpty)
    let (pre, mid, post) := splitExample' contents
    let mid := fixupAnchorComments mid
    let pre : Option Highlighted := pre.map fun p => p.foldl (init := .empty) fun acc c => acc ++ c.code
    let mut toShow : Array ExampleItem := #[]
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
      match item.kind with
      | ``Lean.Parser.Command.check | ``Lean.Parser.Command.eval | ``Lean.reduceCmd
      | ``Lean.Parser.Command.print | ``Lean.Parser.Command.printAxioms | ``Lean.Parser.Command.printEqns
      | ``Lean.guardMsgsCmd =>
        let info? : Option (_ × String) := allInfo item.code |>.firstM fun (sev, str, hl?) =>
          if hl? matches some (.token ⟨.keyword .., _⟩) then some (sev, str) else none
        if let some (sev, txt) := info? then
          if let (code, some (comment, ws)) := trailingComment item.code then
            if checkOutput && !eqMessages comment txt then
              throwError "Mismatch! Expected {comment} but got {txt}"
            toShow := toShow.push ⟨code, some (sev, txt), dropOneNl ws⟩
          else
            let (code', ws) := trailingText item.code
            toShow := toShow.push ⟨code', some (sev, txt), dropOneNl ws⟩
        else toShow := toShow.push ⟨item.code, none, ""⟩
        | _ => toShow := toShow.push ⟨item.code, none, ""⟩
    let post : Option Highlighted := post.map fun p => p.foldl (init := .empty) fun acc c => acc ++ c.code
    let visible := .seq <| toShow.map (·.1)
    saveBackref visible
    for (_, msg, _)  in allInfo visible do
      logSilentInfo msg
    if let .named xs := showProofStates then
      unless xs.isEmpty do
        logWarning m!"Unused proof state names: {m!", ".joinSep (xs.map (m!"'{·}'")).toList}"
    if «show» then
      return #[← ``(Block.other (Block.lean $(quote allowVisible) $(quote pre) $(quote toShow) $(quote post) $(quote visibility)) #[])]
    else
      return #[]
where
  eqMessages (s1 s2 : String) := SubVerso.Examples.Messages.messagesMatch (s1.replace "\n" " ") (s2.replace "\n" " ")
  dropOneNl (s : String) : String :=
    if s.back == '\n' then s.dropRight 1 else s

section

structure ProofStateConfig where
  name : StrLit

structure GoalConfig where
  name : StrLit

variable [Monad m] [MonadError m ] [MonadLiftT CoreM m]

private def strOrName : ValDesc m StrLit where
  description := "identifier or string literal"
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
    goalView := goalView.trimRight ++ "\n"
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
      | {name := some x, ..} => caseTag.getString == x.toString
      | _ => false
    let some goal := goal?
      | let validTags := goals.filterMap (Name.toString <$> ·.name)
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
      pure (← IO.FS.readFile toolchainfile).trim

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
    return name == ``TPiL.lean
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
    return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote kw.getString)])]

@[role_expander attr]
def attr : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO attr xref
    return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote kw.getString)])]


@[role_expander tactic]
def tactic : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO kw xref
    return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote kw.getString)])]

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
  let mut str := str.trim
  repeat
    let pref1 := str.takeWhile alpha
    if pref1.length < 1 then failure
    str := str.drop pref1.length
    let pref2 := str.takeWhile (fun c => alpha c || c.isDigit)
    str := str.drop pref2.length
    let pref := pref1 ++ pref2
    let c := str.get? ⟨0⟩
    if pref.length > 0 && (c.isEqSome ' ' || c.isEqSome ':') then
      out := out.push pref
      str := str.dropWhile (· == ' ')
    else failure

    if str.get? ⟨0⟩ |>.isEqSome ':' then
      str := str.drop 1
      str := str.dropWhile (· == ' ')
      if str.isEmpty then failure
      return (out, str)
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

      return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote hl.toString)])]
    catch
      | .error ref e =>
        logErrorAt ref e
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
        | .const _ sig doc? _ =>
          Hover.addCustomHover code <|
            s!"```\n{sig}\n```\n" ++
            (doc?.map ("\n\n***\n\n" ++ ·) |>.getD "")
        | .var _ sig =>
          Hover.addCustomHover code <|
            s!"```\n{sig}\n```\n"
        | _ => pure ()
      | _ => pure ()

      return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote hl.toString)])]
    catch
      | .error ref e =>
        logErrorAt ref e
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
      for (k, msg, _) in allInfo hl do
        let k := match k with | .info => "info" | .error => "error" | .warning => "warning"
        logSilentInfo m!"{k}: {msg}"

      return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote hl.toString)])]
    catch
      | .error ref e =>
        logErrorAt ref e
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
      for (k, msg, _) in allInfo hl do
        let k := match k with | .info => "info" | .error => "error" | .warning => "warning"
        logSilentInfo m!"{k}: {msg}"

      return #[← ``(Block.other (Block.lean false none #[ExampleItem.mk $(quote hl) none ""] none) #[])]
    catch
      | .error ref e =>
        logErrorAt ref e
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
      for (k, msg, _) in allInfo hl do
        let k := match k with | .info => "info" | .error => "error" | .warning => "warning"
        logSilentInfo m!"{k}: {msg}"

      return #[← ``(Block.other (Block.lean false none #[ExampleItem.mk $(quote hl) none ""] none) #[])]
    catch
      | .error ref e =>
        logErrorAt ref e
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
            return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote hl.toString)])]
          else break
      else if let some hl := prev.matchingExpr? codeStr then
        return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote hl.toString)])]

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
@[inline_expander Verso.Syntax.code]
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
    else if (← getOptionDecls).any (fun x _ => x.toString == str'.trim) then
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
        if gs.any (Name.toString <$> ·.name |>.isEqSome str') then
          suggs := suggs.push <| "{goal " ++ name ++ "}`" ++ str' ++ "`"

      if suggs.isEmpty then
        let h ← hint m!"Add the `lit` role to indicate that it denotes literal characters:" #["{lit}`" ++ str' ++ "`"]
        logWarning <| m!"Code element is missing a role, and can't be Lean code:{m!"\nand\n".joinSep (exns.map (indentD ·.toMessageData) |>.toList)}" ++ h
      else
        let h ← hint m!"Add a `lean` role:" suggs
        logWarning <| m!"Code element could be highlighted." ++ h


    return (← ``(Inline.code $(quote str.getString)))
  | _ => Elab.throwUnsupportedSyntax
