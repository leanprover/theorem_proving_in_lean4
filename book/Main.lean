import VersoManual
import TPiL

open Verso.Genre Manual
open Verso Code External

open Verso.Output.Html in
def plausible := {{
    <script async src="https://plausible.io/js/pa-RTua_4FfKHhfAvAc3liZd.js"></script>
    <script>{{Verso.Output.Html.text false r#"
      window.plausible=window.plausible||function(){(plausible.q=plausible.q||[]).push(arguments)},plausible.init=plausible.init||function(i){plausible.o=i||{}};
      plausible.init()
    "#}}</script>
  }}

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
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

def main := manualMain (%doc TPiL) (config := config)
