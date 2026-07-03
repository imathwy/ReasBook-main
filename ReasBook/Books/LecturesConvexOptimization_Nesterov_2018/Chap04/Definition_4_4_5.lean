import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}

/-
Definition 4.4.5 lies in the normed-space operator / minimal-singular-value domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.opNorm` with `ratio_le_opNorm`, the canonical mathlib owner for quotient
  norms of continuous linear maps;
- `FiniteDimensional.proper`, the compactness bridge that turns the unit sphere into a compact set
  in finite-dimensional normed spaces;
- `LinearMap.singularValues`, the stronger finite-dimensional inner-product bridge for identifying
  `σ_min(A)` with the last singular value when that extra structure is available;
- `LinearMap.singularValues_nonneg`, the canonical nonnegativity API on that stronger bridge side.

Best owner abstraction:
- source-facing: the textbook least singular value `σ_min(A)` of a continuous linear operator `A`;
- core/canonical: the infimum of the ratio `‖A x‖ / ‖x‖` over nonzero vectors;
- bridge/view: the finite-dimensional unit-sphere formula and, under stronger inner-product
  hypotheses, the identification with the last singular value.

Primitive data:
- a continuous linear operator `A : E₁ →L[𝕜] E₂`.

Derived API:
- the source-facing notation `σ_min(A)`;
- the nonnegativity theorem;
- the defining infimum formula over nonzero vectors;
- the finite-dimensional unit-sphere bridge;
- the stronger singular-value identification under inner-product hypotheses.
-/
namespace ContinuousLinearMap

section Owner

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Definition 4.4.5: the least singular value of `A` is the infimum of the quotients
`‖A x‖ / ‖x‖` over nonzero vectors `x`. -/
def minimalSingularValue (A : E₁ →L[𝕜] E₂) : ℝ :=
  sInf (Set.range fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖)

end Owner

end ContinuousLinearMap

namespace MinimalSingularValue

/- Source-facing Lean notation for the textbook least singular value `σ_min(A)`. -/
scoped notation:max "σ_min(" A ")" => ContinuousLinearMap.minimalSingularValue A

end MinimalSingularValue

open scoped MinimalSingularValue

namespace ContinuousLinearEquiv

section Bridge

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Coercion bridge: the least singular value of a continuous linear equivalence, viewed through
the canonical coercion to a continuous linear map. -/
abbrev minimalSingularValue (A : E₁ ≃L[𝕜] E₂) : ℝ :=
  ContinuousLinearMap.minimalSingularValue (A : E₁ →L[𝕜] E₂)

/- Source-facing Lean notation for the textbook least singular value of a continuous linear
equivalence. -/
scoped notation:max "σ_min(" A ")" => ContinuousLinearEquiv.minimalSingularValue A

end Bridge

section NormBridge

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/- Thin operator-norm bridge: a continuous linear equivalence carries the operator norm of its
underlying continuous linear map. -/
instance : Norm (E₁ ≃L[𝕜] E₂) where
  norm A := ‖(A : E₁ →L[𝕜] E₂)‖

@[simp] theorem norm_toContinuousLinearMap (A : E₁ ≃L[𝕜] E₂) :
    ‖A.toContinuousLinearMap‖ = ‖A‖ :=
  rfl

end NormBridge

end ContinuousLinearEquiv

section Owner

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Source-facing bridge: `σ_min(A)` equals the infimum of `‖A x‖ / ‖x‖` over nonzero vectors. -/
theorem minimalSingularValue_def (A : E₁ →L[𝕜] E₂) :
    σ_min(A) =
      sInf (Set.range fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖) := by
  rfl

/-- The least singular value is nonnegative. -/
theorem minimalSingularValue_nonneg (A : E₁ →L[𝕜] E₂) :
    0 ≤ σ_min(A) := by
  rw [minimalSingularValue_def]
  refine Real.sInf_nonneg ?_
  rintro _ ⟨x, rfl⟩
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- If the domain is subsingleton, then the least singular value is zero. -/
theorem minimalSingularValue_eq_zero [Subsingleton E₁] (A : E₁ →L[𝕜] E₂) :
    σ_min(A) = 0 := by
  rw [minimalSingularValue_def]
  have hrange :
      Set.range (fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact x.2 <| Subsingleton.elim _ _
  simp [hrange, Real.sInf_empty]

end Owner

section SingularValuesBridge

variable [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]

/-- Stronger bridge: over finite-dimensional inner-product spaces, `σ_min(A)` is the last singular
value of `A.toLinearMap`. -/
theorem minimalSingularValue_eq_singularValues_last (A : E₁ →L[𝕜] E₂) :
    σ_min(A) = A.toLinearMap.singularValues (Module.finrank 𝕜 E₁ - 1) := by
  sorry

end SingularValuesBridge

section FiniteDimensional

variable [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Over finite-dimensional normed spaces, `σ_min(A)` is the infimum of `‖A x‖` over the unit
sphere. -/
theorem minimalSingularValue_eq_sInf_norm_image_unitSphere
    (A : E₁ →L[𝕜] E₂) :
    σ_min(A) =
      sInf (Set.range fun x : Metric.sphere (0 : E₁) 1 ↦ ‖A x.1‖) := by
  sorry

end FiniteDimensional
