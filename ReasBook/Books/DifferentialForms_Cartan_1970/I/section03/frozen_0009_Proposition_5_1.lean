import DifferentialForms_Cartan_1970.I.section03.«frozen_0008_Definition_I_3_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

namespace Complex

-- Proof sketch: if `g` is another branch, then `(f - g) / (2π i)` is a continuous
-- integer-valued function on the connected set `D`, hence is constant with some value
-- `k : ℤ`; conversely, adding `2π i k` preserves continuity and the defining exponential
-- identity because `Complex.exp` is `2π i`-periodic on integer shifts.
/-- Proposition 5.1: once `f` is a branch of the logarithm on a connected open set `D`, a
function `g` is another branch on `D` exactly when it differs from `f` on `D` by a constant
integer multiple of `2π i`. -/
theorem IsLogBranchOn.other_iff_eqOn_add_two_pi_I_mul_int
    {f g : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) :
    IsLogBranchOn g D ↔
      ∃ k : ℤ,
        Set.EqOn g (fun z ↦ f z + k * (2 * Real.pi * Complex.I)) D := sorry

end Complex
