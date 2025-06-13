-- This module serves as the root of the `Examples` library.
-- Import modules here that should be built as part of the library.
import Examples.Basic
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String

-- This reference is ambiguous, so `#check` shows all possibilities:
#check add
