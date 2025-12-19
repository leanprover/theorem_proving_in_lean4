import VersoManual
import TPiL

open Verso.Genre Manual
open Verso Code External

open Verso.Output.Html in
def plausible := {{
    <script defer="defer" data-domain="lean-lang.org" src="https://plausible.io/js/script.outbound-links.js"></script>
  }}

def config : Config where
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 1
  extraFiles := [("static", "static")]
  extraCss := Std.HashSet.ofList [
    "/static/theme.css",
    "/static/fonts/source-serif/source-serif-text.css",
    "/static/fonts/source-code-pro/source-code-pro.css",
    "/static/fonts/source-sans/source-sans-3.css",
    "/static/fonts/noto-sans-mono/noto-sans-mono.css"
  ]
  extraHead := #[plausible]
  logo := some "/static/lean_logo.svg"
  sourceLink := some "https://github.com/leanprover/theorem_proving_in_lean4"
  issueLink := some "https://github.com/leanprover/theorem_proving_in_lean4/issues"
  linkTargets := fun st => st.localTargets ++ st.remoteTargets

def main := manualMain (%doc TPiL) (config := config)
