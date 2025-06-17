-- This module serves as the root of the `Examples` library.
-- Import modules here that should be built as part of the library.
import Examples.Basic


example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    -- ⊢ g x x + x
    arg 1
    -- ⊢ g x x
    rw [h₁]
    -- 2 goals: ⊢ 1, ⊢ x ≠ 0
    . skip
    . tactic =>
      exact h₂
