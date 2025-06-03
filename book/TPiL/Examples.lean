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

  unless (← jsonPath.pathExists) do
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
    | throwError s!"Expected JSON array"
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
  margin: 0;
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

block_extension Block.lean
    (allowToggle : Bool)
    (pre : Option Highlighted)
    (code : Array (Highlighted × Option (Highlighted.Span.Kind × String)))
    (post : Option Highlighted) where
  data := .arr #[.bool allowToggle, toJson pre, toJson code, toJson post]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy), ("copybutton.js", copyButtonJs)]
  extraCssFiles := [("tippy-border.css", tippy.border.css), ("copybutton.css", copyButtonCss), ("examples.css", examplesCss)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.bool allowToggle, hlPreJson, hlJson, hlPostJson] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      let pre ←
        match FromJson.fromJson? (α := Option Highlighted) hlPreJson with
        | .error err =>
          HtmlT.logError <| "Couldn't deserialize Lean code intro block while rendering HTML: " ++ err
          return .empty
        | .ok hl => pure hl
      let code ←
        match FromJson.fromJson? (α := Array (Highlighted × Option (Highlighted.Span.Kind × String))) hlJson with
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

      let codeIndent := code.foldl (init := pre.map (·.indentation)) (fun i? y => i?.map (min · y.1.indentation)) |>.getD 0

      let mut codeHtml : Html := .empty
      let mut codeString := ""

      if allowToggle then
        if let some p := pre then
          let p := p.deIndent codeIndent
          codeHtml := codeHtml ++ {{ <div class="hidden">{{← trimOneLeadingNl p|>.blockHtml "examples" (trim := false) }}</div> }}
          codeString := codeString ++ p.toString

      let outClass
        | .info => "information"
        | .warning => "warning"
        | .error => "error"

      for (cmd, out?) in code do
        let cmd := cmd.deIndent codeIndent

        codeHtml := codeHtml ++ (← trimOneLeadingNl cmd |>.blockHtml "examples" (trim := false))
        codeString := codeString ++ cmd.toString
        if let some (k, out) := out? then
          codeHtml := codeHtml ++ {{ <div class={{outClass k}}><pre>{{out}}</pre></div> }}

      if allowToggle then
        if let some p := post then
          let p := p.deIndent codeIndent
          codeHtml := codeHtml ++ {{ <div class="hidden">{{← trimOneLeadingNl p|>.blockHtml "examples" (trim := false) }}</div> }}
          codeString := codeString ++ p.toString

      let i ← uniqueId
      let toCopy := (pre.map (·.toString)).getD "" ++ codeString
      let mut script := s!"addCopyButtonToElement({i.quote}, {toCopy.quote});"
      if allowToggle && (pre.isSome || post.isSome) then
        script := script ++ s!"\naddToggleButtonToElement({i.quote});"

      return {{
        <div class="example" id={{i}}>{{codeHtml}}</div>
        <script>
        {{script}}
        </script>
      }}


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

def saveBackref (hl : Highlighted) : DocElabM Unit := do
  modifyEnv (recentHighlightsExt.modifyState · (·.add hl))

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

/-- Extracts a trailing comment from code, if present -/
def trailingComment (hl : Highlighted) : Highlighted × Option String :=
  let (hl', txt) := trailingText hl
  if let some txt' := commentContents txt then
    (hl', some txt')
  else (hl, none)
where
  commentContents s :=
    let s := s.trim
    if "--".isPrefixOf s then some (s.dropWhile (· == '-') |>.trimLeft) else none

section

structure LeanConfig where
  checkOutput : Bool
  suppressNamespaces : Option String
  allowVisible : Bool

variable [Monad m] [MonadError m ] [MonadLiftT CoreM m]

instance : FromArgs LeanConfig m where
  fromArgs := LeanConfig.mk <$> .namedD `check .bool true <*> .named `suppressNamespaces .string true <*> .namedD `allowVisible .bool true
end

@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, code => do
    let {checkOutput, suppressNamespaces, allowVisible} ← parseThe LeanConfig args
    let codeStr := code.getString
    let contents ← extractFile codeStr suppressNamespaces
    let contents := contents.filter (!·.code.isEmpty)
    let (pre, mid, post) := splitExample' contents
    let pre : Option Highlighted := pre.map fun p => p.foldl (init := .empty) fun acc c => acc ++ c.code
    let mid : Array (Highlighted × Option (Highlighted.Span.Kind × String)) ← mid.mapM fun item => do
      match item.kind with
      | ``Lean.Parser.Command.check | ``Lean.Parser.Command.eval | ``Lean.reduceCmd
      | ``Lean.Parser.Command.print | ``Lean.Parser.Command.printAxioms | ``Lean.Parser.Command.printEqns =>
        let info? := allInfo item.code |>.firstM fun (sev, str, hl?) =>
          if hl? matches some (.token ⟨.keyword .., _⟩) then some (sev, str) else none
        if checkOutput then
          if let (code, some comment) := trailingComment item.code then
            if let some (_, txt) := info? then
              if !eqMessages comment txt then throwError "Mismatch! Expected {comment} but got {txt}"
            else logError "Expected {comment} but no info was found."
            pure (code, info?)
          else
            pure (item.code, info?)
        else pure (item.code, info?)
      | _ => pure (item.code, none)
    let post : Option Highlighted := post.map fun p => p.foldl (init := .empty) fun acc c => acc ++ c.code
    saveBackref (.seq <| mid.map (·.1))
    return #[← ``(Block.other (Block.lean $(quote allowVisible) $(quote pre) $(quote mid) $(quote post)) #[])]
where
  eqMessages (s1 s2 : String) := SubVerso.Examples.Messages.messagesMatch (s1.replace "\n" " ") (s2.replace "\n" " ")

structure Helper where
  highlight (term : String) (type? : Option String) : IO Highlighted

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
    let hl ← do
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
      pure <| fun tm ty? => do
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

    return Helper.mk hl
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


private def oneCodeStr [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m StrLit := do
  let #[code] := inlines
    | (if inlines.size == 0 then (throwError ·) else (throwErrorAt (mkNullNode inlines) ·)) "Expected one code element"
  let `(inline|code($code)) := code
    | throwErrorAt code "Expected a code element"
  return code

@[role_expander kw]
def kw : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO kw xref
    return #[← ``(Inline.other (Inline.lean $(quote hl)) #[Inline.code $(quote kw.getString)])]

@[role_expander kbd]
def kbd : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    return #[← ``(Inline.code $(quote kw.getString))]

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
    let pref1 := str.takeWhile (·.isAlpha)
    if pref1.length < 1 then failure
    str := str.drop pref1.length
    let pref2 := str.takeWhile (fun c => c.isAlpha || c.isDigit)
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
  "#print", "#eval", "#print axioms",
  "noncomputable",
  "def", "example", "#reduce", "#check", "macro_rules", "axiom", "if", "then", "else", "show", "have", "calc", "simp", "rw",
  "universe", "section", "end", "variable", "open", "set_option",
  "let", "fun"
]

private def leanLits := [
  "→", "->", ";", "×", ".", "_", "⟨", "⟩"
]


open MessageData (hint) in
/--
Internal detail of anchor suggestion mechanism.
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
      for prev in recentHighlightsExt.getState (← getEnv) do
        if let some _ := prev.matchingExpr? str' then
          suggs := suggs.push <| "{leanRef}`" ++ str' ++ "`"
          break
      if str' ∈ leanLits then
        suggs := suggs.push <| "{lit}`" ++ str' ++ "`"

      if suggs.isEmpty then
        let h ← hint m!"Add the `lit` role to indicate that it denotes literal characters:" #["{lit}`" ++ str' ++ "`"]
        logWarning <| m!"Code element is missing a role, and can't be Lean code:{m!"\nand\n".joinSep (exns.map (indentD ·.toMessageData) |>.toList)}" ++ h
      else
        let h ← hint m!"Add a `lean` role:" suggs
        logWarning <| m!"Code element could be highlighted." ++ h


    return (← ``(Inline.code $(quote str.getString)))
  | _ => Elab.throwUnsupportedSyntax
