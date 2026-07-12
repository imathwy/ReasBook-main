import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.15.1: the textbook implication
`I * J ≤ 𝔭 → I ≤ 𝔭 ∨ J ≤ 𝔭` for a prime ideal `𝔭` is the forward direction of the
canonical theorem `Ideal.IsPrime.mul_le`, which states the equivalent condition
`I * J ≤ 𝔭 ↔ I ≤ 𝔭 ∨ J ≤ 𝔭`. -/
recall Ideal.IsPrime.mul_le
