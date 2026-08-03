import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Banach

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProduct InnerProductSpace

universe u v w

namespace ContinuousLinearMap

section Hilbert

variable {𝕜 : Type w} [RCLike 𝕜]
variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-
Source/core/bridge triage:
- `source-facing`: Example 21.3 asserts invertibility of the Hilbert-space Gram perturbations
  `Id + L† ∘L L` and `Id + L ∘L L†`.
- `core/canonical`: the bounded-operator owner is `IsUnit`, with
  `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` as the canonical Hilbert-space
  invertibility criterion.
- `bridge/view`: `ContinuousLinearMap.isUnit_iff_bijective` translates this owner back to the
  textbook wording “bijective with continuous inverse”.

Primitive data: the bounded linear map `L`.
Derived API: the `Id + L ∘L L†` clause is the `Id + A† ∘L A` owner applied to `A := L†`. -/

/-- Example 21.3 (1): for a bounded linear map `L : H →L[𝕜] K` between Hilbert spaces, the
operator `Id + L† ∘L L` on `H` is bijective with continuous inverse, formalized as
`IsUnit (1 + L† ∘L L : H →L[𝕜] H)`. -/
theorem one_add_adjoint_comp_isUnit (L : H →L[𝕜] K) :
    IsUnit (1 + (L† ∘L L) : H →L[𝕜] H) := by
  let T : H →L[𝕜] H := 1 + (L† ∘L L)
  let c : NNReal := 1
  have hc : 0 < c := by
    simp [c]
  refine isUnit_of_forall_le_norm_inner_map T hc ?_
  intro x
  calc
    ‖x‖ ^ 2 * c = ‖x‖ ^ 2 := by
      simp [c]
    _ ≤ RCLike.re ⟪T x, x⟫ := by
      have hLx_nonneg : 0 ≤ ‖L x‖ ^ 2 := sq_nonneg ‖L x‖
      have hxT : ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫ := by
        calc
        ‖x‖ ^ 2 = RCLike.re ⟪x, x⟫ := by
          exact (inner_self_eq_norm_sq x).symm
        _ ≤ RCLike.re ⟪x, x⟫ + ‖L x‖ ^ 2 := by
          linarith
        _ = RCLike.re ⟪x, x⟫ + RCLike.re ⟪(L† ∘L L) x, x⟫ := by
          rw [L.apply_norm_sq_eq_inner_adjoint_left]
        _ = RCLike.re ⟪T x, x⟫ := by
          simp [T, inner_add_left]
      exact hxT
    _ ≤ ‖⟪T x, x⟫‖ := by
      exact RCLike.re_le_norm _

/-- Example 21.3 (2): for a bounded linear map `L : H →L[𝕜] K` between Hilbert spaces, the
operator `Id + L ∘L L†` on `K` is bijective with continuous inverse, formalized as
`IsUnit (1 + L ∘L L† : K →L[𝕜] K)`. -/
theorem one_add_comp_adjoint_isUnit (L : H →L[𝕜] K) :
    IsUnit (1 + (L ∘L L†) : K →L[𝕜] K) := by
  simpa using (one_add_adjoint_comp_isUnit (L†))

end Hilbert

end ContinuousLinearMap
