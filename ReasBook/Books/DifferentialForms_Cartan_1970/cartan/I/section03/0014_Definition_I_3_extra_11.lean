import DifferentialForms_Cartan_1970.cartan.I.section03.«frozen_0008_Definition_I_3_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

open Set

namespace Complex

/-- Definition I.3-extra-11: a branch of `t^α` on `D` is a single-valued function obtained from
some branch `L` of `log t` on `D` by the formula `z ↦ exp (α * L z)`. -/
def IsPowerBranchOn (α : ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ L : ℂ → ℂ, IsLogBranchOn L D ∧ EqOn f (fun z ↦ Complex.exp (α * L z)) D

/-- A chosen logarithm branch on `D` induces the corresponding branch of `t^α`. -/
-- Proof sketch: take the given logarithm branch `L` as the witness in
-- `IsPowerBranchOn`; the required equality on `D` is exactly reflexivity.
theorem IsLogBranchOn.isPowerBranchOn {α : ℂ} {D : Set ℂ} {L : ℂ → ℂ}
    (hL : IsLogBranchOn L D) : IsPowerBranchOn α D (fun z ↦ Complex.exp (α * L z)) :=
  ⟨L, hL, fun _ _ ↦ rfl⟩

end Complex
