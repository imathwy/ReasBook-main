import Mathlib
import BauschkeLean.Chap13.Proposition_13_23

-- Declarations for this item will be appended below by the statement pipeline.


universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: unfold `conjugate`, rewrite `conjugate f (-u)` as the supremum of
-- `x ↦ ⟪x, -u⟫ - f x`, replace `x` by `-x`, and use the evenness of `f`.
/-- Proposition 13.21: the conjugate of an even extended-real-valued function on a real
inner-product space is even. -/
theorem conjugate_even (f : H → EReal) (hf : Function.Even f) :
    Function.Even f∗ := by
  have hreverse : fᵛ = f := by
    ext x
    simpa [Function.Even] using hf x
  have hconj : (f∗)ᵛ = f∗ := by
    calc
      (f∗)ᵛ = (fᵛ)∗ := by
        simpa using (conjugate_precompose_neg f).symm
      _ = f∗ := by rw [hreverse]
  rw [Function.Even]
  intro u
  simpa using congrFun hconj u

end Conjugation

end ERealFunction
