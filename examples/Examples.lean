-- This module serves as the root of the `Examples` library.
-- Import modules here that should be built as part of the library.
import Examples.Basic

inductive Blah (α : Type u) : Type (max u v) where
  | mk : Blah α

def x : Prop := True
