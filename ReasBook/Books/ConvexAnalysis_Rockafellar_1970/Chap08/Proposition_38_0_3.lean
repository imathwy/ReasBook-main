import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_9
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_15
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Proposition_36_4_3

noncomputable section

open LinearMap
open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.0.3 identifies the inverse and inverse-adjoint of the convex
  indicator bifunction attached to a nonsingular linear transformation.
- `core/canonical`: the existing owners are `graphIndicator`, `graphConcaveIndicator`,
  inverse notation `F _*`, and `concaveAdjoint`; the linear-algebra owner for the adjoint map
  is `LinearMap.adjoint`.
- `bridge/view`: the source phrase "nonsingular linear transformation" is rendered by the
  canonical Lean owner `LinearEquiv`, and the source expression `(A⁻¹)^* = (A^*)⁻¹` is recorded
  on the indicator side through the map `adjoint (A.symm : F →ₗ[ℝ] E)`.

Domain-style sampling used here:
- inverse notation `F _*` from `Chap07.Definition_36_4_1`;
- `graphIndicator`, `graphConcaveIndicator`, and the pointwise pairing equation for those owners
  from `Chap07.Lemma33_0_30`;
- `concaveAdjoint` from the Chapter 6 concave-bifunction-adjoint owner layer;
- `LinearMap.adjoint` as the canonical inner-product-space adjoint.

Primitive data vs derived API:
- primitive input data: an invertible linear map `A`;
- primitive owner expressions: `graphIndicator ℝ A`, `(graphIndicator ℝ A) _*`, and the
  concave-adjoint owner applied to that inverse;
- derived API: the identification of the inverse with the concave indicator of `A.symm`, and the
  identification of the concave adjoint of that inverse with the convex indicator of
  `adjoint (A.symm : F →ₗ[ℝ] E)`.

Layer target:
- `source-facing` for the two indicator-bifunction equalities;
- `bridge/view` only in the passage from the source's Euclidean adjoint notation to
  `LinearMap.adjoint`.
-/

section InverseClause

variable {𝕜 : Type*} {E : Type u} {F : Type v}
variable [Ring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: unfold the inverse notation `F _*`, `graphIndicator`, and
-- `graphConcaveIndicator`. The singleton condition `x = A u` is equivalent to `u = A.symm x`
-- because `A` is a `LinearEquiv`, so both sides reduce to the same pointwise indicator formula.
/-- Proposition 38.0.3 (1): the inverse of the convex indicator bifunction of a nonsingular linear
transformation `A` is the concave indicator bifunction of `A⁻¹`. -/
theorem inverse_graphIndicator_eq_graphConcaveIndicator_symm
    (A : E ≃ₗ[𝕜] F) :
    (graphIndicator 𝕜 A) _* = graphConcaveIndicator 𝕜 A.symm := by
  funext x u
  have hA : x = A u ↔ u = A.symm x := by
    simpa [eq_comm] using
      (A.toEquiv.apply_eq_iff_eq_symm_apply : A u = x ↔ u = A.symm x)
  by_cases h : x = A u
  · have hu : u = A.symm x := hA.mp h
    have hxmem : x ∈ ({A u} : Set F) := by
      simpa [Set.mem_singleton_iff] using h
    have humem : u ∈ ({A.symm x} : Set E) := by
      simpa [Set.mem_singleton_iff] using hu
    rw [inverse_apply]
    simp [graphIndicator, graphConcaveIndicator, hxmem, humem]
  · have hu : u ≠ A.symm x := by
      intro hu
      exact h (hA.mpr hu)
    have hxnot : x ∉ ({A u} : Set F) := by
      simpa [Set.mem_singleton_iff] using h
    have hunot : u ∉ ({A.symm x} : Set E) := by
      simpa [Set.mem_singleton_iff] using hu
    rw [inverse_apply]
    simp [graphIndicator, graphConcaveIndicator, hxnot, hunot]

end InverseClause

section AdjointClause

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

local instance : Neg (WithBotTop ℝ) := WithBotTop.instNeg
local instance : InvolutiveNeg (WithBotTop ℝ) := WithBotTop.instInvolutiveNeg

-- Proof sketch: first rewrite `inverse (graphIndicator ℝ A)` using the preceding inverse-indicator
-- identification, then rewrite the adjoint branch via the hypothesis `hAdj`. In the inner-product
-- self-dual setting this yields the convex indicator bifunction of `(A⁻¹)^*`, which is the
-- canonical Lean rendering of the source map `(A^*)⁻¹`.
/-- Proposition 38.0.3 (2), conditional bridge form: assuming the adjoint-side singleton-graph
identification `hAdj`, the concave adjoint of the inverse indicator bifunction is the convex
indicator bifunction of `(A⁻¹)^*`, equivalently of `(A^*)⁻¹`. -/
theorem concaveAdjoint_inverse_graphIndicator_eq_graphIndicator_adjoint_symm
    (A : E ≃ₗ[ℝ] F)
    (hAdj :
      Bifunction.adjoint (XStar := F) (UStar := E) (graphIndicator ℝ A) =
        graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) :
    concaveAdjoint E F ((graphIndicator ℝ A) _*) =
      graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) := by
  let Aadj : E ≃ₗ[ℝ] F :=
    { toLinearMap := LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)
      invFun := LinearMap.adjoint (A : E →ₗ[ℝ] F)
      left_inv := by
        intro x
        have hcomp :
            (LinearMap.adjoint (A : E →ₗ[ℝ] F)) ∘ₗ
              LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) = LinearMap.id := by
          simpa using
            (LinearMap.adjoint_comp (A.symm : F →ₗ[ℝ] E) (A : E →ₗ[ℝ] F)).symm
        simpa using congrArg (fun T : E →ₗ[ℝ] E ↦ T x) hcomp
      right_inv := by
        intro y
        have hcomp :
            (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) ∘ₗ
              LinearMap.adjoint (A : E →ₗ[ℝ] F) = LinearMap.id := by
          simpa using
            (LinearMap.adjoint_comp (A : E →ₗ[ℝ] F) (A.symm : F →ₗ[ℝ] E)).symm
        simpa using congrArg (fun T : F →ₗ[ℝ] F ↦ T y) hcomp }
  have hAadj :
      (graphIndicator ℝ Aadj) _* = graphConcaveIndicator ℝ Aadj.symm :=
    inverse_graphIndicator_eq_graphConcaveIndicator_symm Aadj
  have hInv :
      (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* =
        graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) := by
    have hInv' :
        graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) =
          (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* := by
      have hInv'' :
          (graphIndicator ℝ Aadj) _* _* =
            (graphConcaveIndicator ℝ Aadj.symm) _* :=
        congrArg (fun H => H _*) hAadj
      have hInv''' : (graphIndicator ℝ Aadj) _* _* = graphIndicator ℝ Aadj :=
        inverse_inverse (graphIndicator ℝ Aadj)
      calc
        graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) = graphIndicator ℝ Aadj := by
          simp [Aadj]
        _ = (graphIndicator ℝ Aadj) _* _* := by
          exact hInv'''.symm
        _ = (graphConcaveIndicator ℝ Aadj.symm) _* := hInv''
        _ = (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* := by
          simp [Aadj]
    exact hInv'.symm
  have hComm :
      concaveAdjoint E F ((graphIndicator ℝ A) _*) =
        ((adjoint (XStar := F) (UStar := E) (graphIndicator ℝ A)) _*) :=
    concaveAdjoint_inverse_eq_inverse_adjoint (graphIndicator ℝ A)
  calc
    concaveAdjoint E F ((graphIndicator ℝ A) _*) =
        ((adjoint (XStar := F) (UStar := E) (graphIndicator ℝ A)) _*) := hComm
    _ = (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* := by rw [hAdj]
    _ = graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) := hInv

end AdjointClause

end Bifunction
