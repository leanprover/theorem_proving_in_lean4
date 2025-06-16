-- This module serves as the root of the `Examples` library.
-- Import modules here that should be built as part of the library.
import Examples.Basic

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp | inr hq =>
    simp [*]
