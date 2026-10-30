import VersoManual
import TPiL

open Verso.Genre Manual
open Verso Code External

open Verso.Output.Html in
def plausible := {{
    <script defer="defer" data-domain="lean-lang.org" src="https://plausible.io/js/script.outbound-links.js"></script>
  }}

open Verso.Output.Html in
def staticCss := {{
    <link rel="stylesheet" href="static/theme.css" />
    <link rel="stylesheet" href="static/fonts/source-serif/source-serif-text.css" />
    <link rel="stylesheet" href="static/fonts/source-code-pro/source-code-pro.css" />
    <link rel="stylesheet" href="static/fonts/source-sans/source-sans-3.css" />
    <link rel="stylesheet" href="static/fonts/noto-sans-mono/noto-sans-mono.css" />
  }}

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  extraFiles := [("static", "static")]
  extraHead := #[plausible, staticCss]
  logo := some "/static/lean_logo.svg"
  sourceLink := some "https://github.com/leanprover/theorem_proving_in_lean4"
  issueLink := some "https://github.com/leanprover/theorem_proving_in_lean4/issues"

def main := manualMain (%doc TPiL) (config := config)
