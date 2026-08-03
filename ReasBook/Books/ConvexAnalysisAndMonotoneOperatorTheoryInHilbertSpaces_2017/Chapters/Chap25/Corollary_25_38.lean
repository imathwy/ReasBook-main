import BauschkeLean.Chap25.Proposition_25_37

open scoped ContinuousLinearMap InnerProductSpace

universe u

variable {𝓗 : Type u}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
variable [FiniteDimensional ℝ 𝓗]
variable (C D : Submodule ℝ 𝓗)

local notation "P_C" => C.starProjection
local notation "P_D" => D.starProjection

-- Domain sampling:
-- * `source-facing`: Corollary 25.38 is the finite-dimensional Anderson--Duffin formula for the
--   projector onto `C ∩ D`.
-- * `core/canonical`: Proposition 25.37 already owns the Moore-Penrose projector identity on the
--   `ClosedSubmodule` surface.
-- * `bridge/view`: this file specializes that owner theorem from closed submodules to arbitrary
--   submodules in finite dimension, while reusing the textbook surface notation `P_C`, `P_D`.

/-- Corollary 25.38 (Anderson--Duffin): in a finite-dimensional real Hilbert space, the orthogonal
projection onto `C ∩ D` is `2 P_C (P_C + P_D)⁺ P_D`. -/
theorem anderson_duffin_inf_starProjection_eq
    :
    let Cc : ClosedSubmodule ℝ 𝓗 := ⟨C, Submodule.closed_of_finiteDimensional C⟩
    let Dc : ClosedSubmodule ℝ 𝓗 := ⟨D, Submodule.closed_of_finiteDimensional D⟩
    (C ⊓ D).starProjection =
      (2 : ℝ) •
        ((P_C).comp
          (((P_C + P_D)⁺[
            (isClosed_range_starProjection_add_starProjection_of_isClosed_sup
              Cc Dc
              (Submodule.closed_of_finiteDimensional (C ⊔ D)))]).comp P_D)) := by
  let Cc : ClosedSubmodule ℝ 𝓗 := ⟨C, Submodule.closed_of_finiteDimensional C⟩
  let Dc : ClosedSubmodule ℝ 𝓗 := ⟨D, Submodule.closed_of_finiteDimensional D⟩
  simpa using
    (inf_starProjection_eq_double_comp_moorePenroseInverseOperator_comp_of_isClosed_sup
      Cc Dc
      (Submodule.closed_of_finiteDimensional (C ⊔ D)))
