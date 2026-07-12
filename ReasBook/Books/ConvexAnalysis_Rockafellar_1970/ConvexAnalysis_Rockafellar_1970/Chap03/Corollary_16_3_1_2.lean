import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsOrderedAddMonoid 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [ClosedIciTopology 𝕜]
variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]
variable [HasPairingSwap E E 𝕜] [HasPairingSwap F F 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.1.2 identifies the support function of the inverse image
  `A⁻¹ (closure D)` with the closure of the dual-side image `A* δ*(· | closure D)`.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`, the
  lower-semicontinuous closure `lowerSemicontinuousHull`, the function image operator
  `Function.linearImage`, the set closure `closure`, and an explicit dual map `Astar`.
- `bridge/view`: Rockafellar's `δ*(· | D)` is rendered by `supportFunction D`, and the source's
  `cl (A* δ*(· | closure D))` is rendered by
  `lowerSemicontinuousHull (Astar ◁ supportFunction D)`, using closure-invariance of support.

Domain-style sampling used here:
- `supportFunction` and the pairing-symmetric indicator/support bridge from Text 13.1.4;
- `indicatorFunction_isConvex_iff` from `Chap01.Remark_4_8_1`;
- `lowerSemicontinuousHull_indicator_eq_indicator_closure` from Text 7.0.14;
- `convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex`
  from Theorem 16.3.2;
- `intrinsicClosure_eq_closure` for the intrinsic-closure pairing bridge.

Primitive data vs derived API:
- primitive inputs: a primal map `A : E → F`, a dual map `Astar : F → E`, a pairing
  compatibility identity, a set `D ⊆ F`, and the convexity hypothesis on `D`;
- derived API: the support-function identity itself, stated directly at the pairing owner layer.

Layer target: `source-facing`, expressed through the canonical project owners.

Ambient note: the upstream owner theorem `Theorem_16_3_2` already has a pairing-layer primary
statement with an explicit dual map. This file keeps that pairing-level owner surface.

Topology note: this first section keeps ambient `closure` as primary because the available pairing
assumptions here are only topological-module assumptions; replacing `closure` by
`intrinsicClosure 𝕜` requires stronger normed/metric hypotheses to use
`intrinsicClosure_eq_closure`. A scalar-generic intrinsic-closure bridge is added below at the
same pairing owner layer.
-/

-- Theorem 16.3.2 is applied to `indicatorFunction D`.
-- Convexity of that indicator comes from `indicatorFunction_isConvex_iff`.
-- Text 13.1.5 identifies `cl(δ(· | D))` with `δ(· | closure D)`, and the
-- pairing-symmetric indicator/support bridges rewrite both conjugate terms.
/-- Corollary 16.3.1.2 at the pairing owner layer: for primal/dual maps `A` and `Astar` with
`⟪Astar y, x⟫ = ⟪y, A x⟫`, and a convex set `D ⊆ F`, the support function of
`A ⁻¹' closure D` equals the lower-semicontinuous closure of the `Astar`-image of the support
function of `D`. -/
theorem supportFunction_preimage_closure_eq_lowerSemicontinuousHull_linearImage_of_pairing
    (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (D : Set F) (hD : Convex 𝕜 D) :
    (δᵛ(· | A ⁻¹' closure D) : E → WithBotTop 𝕜) =
      cl(Astar ◁ (δᵛ(· | D) : F → WithBotTop 𝕜)) := by
  have hcore :
      ((cl((δ[𝕜](· | D))) ∘ A)⋆ : E → WithBotTop 𝕜) =
        cl(Astar ◁ (((δ[𝕜](· | D))⋆ : F → WithBotTop 𝕜))) := by
    exact
      convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex
        (A := A) (Astar := Astar) (hAstar := hAstar) (g := (δ[𝕜](· | D)))
        ((indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) D).2 hD)
  have hleft :
      ((cl((δ[𝕜](· | D))) ∘ A)⋆ : E → WithBotTop 𝕜) =
        (δᵛ[WithBotTop 𝕜](· | A ⁻¹' closure D) : E → WithBotTop 𝕜) := by
    have hcl_ind :
        (cl((δ[𝕜](· | D))) : F → WithBotTop 𝕜) =
          (δ[𝕜](· | closure D) : F → WithBotTop 𝕜) := by
      simpa using
        (lowerSemicontinuousHull_indicator_eq_indicator_closure
          (X := F) (𝕜 := 𝕜) D)
    have hcl_comp :
        (cl((δ[𝕜](· | D))) ∘ A) = (δ[𝕜](· | A ⁻¹' closure D)) := by
      funext x
      exact congrFun hcl_ind (A x)
    calc
      ((cl((δ[𝕜](· | D))) ∘ A)⋆ : E → WithBotTop 𝕜) =
          ((δ[𝕜](· | A ⁻¹' closure D))⋆ : E → WithBotTop 𝕜) := by
            exact
              congrArg (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜)) hcl_comp
      _ = (δᵛ[WithBotTop 𝕜](· | A ⁻¹' closure D) : E → WithBotTop 𝕜) := by
            simpa using
              (convexConjugate_indicatorFunction_eq_supportFunction
                (E := E) (EStar := E) (α := 𝕜) (C := A ⁻¹' closure D))
  have hright :
      cl(Astar ◁ (((δ[𝕜](· | D))⋆ : F → WithBotTop 𝕜))) =
        cl(Astar ◁ (δᵛ[WithBotTop 𝕜](· | D))) := by
    simpa using
      congrArg (fun f : F → WithBotTop 𝕜 ↦ cl(Astar ◁ f))
        (convexConjugate_indicatorFunction_eq_supportFunction
          (E := F) (EStar := F) (α := 𝕜) (C := D))
  exact hleft.symm.trans (hcore.trans hright)

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [ClosedIciTopology 𝕜]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]
variable [HasPairingSwap E E 𝕜] [HasPairingSwap F F 𝕜]

/-- Intrinsic-closure bridge of Corollary 16.3.1.2 at the pairing owner layer: under the
finite-dimensional normed hypotheses needed for `intrinsicClosure_eq_closure`, the same support
formula can be read with `intrinsicClosure 𝕜 D` on the preimage side. -/
theorem supportFunction_preimage_intrinsicClosure_eq_lowerSemicontinuousHull_linearImage_of_pairing
    (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (D : Set F) (hD : Convex 𝕜 D) :
    (δᵛ(· | A ⁻¹' intrinsicClosure 𝕜 D) : E → WithBotTop 𝕜) =
      cl(Astar ◁ (δᵛ(· | D) : F → WithBotTop 𝕜)) := by
  calc
    (δᵛ(· | A ⁻¹' intrinsicClosure 𝕜 D) : E → WithBotTop 𝕜) =
        (δᵛ(· | A ⁻¹' closure D) : E → WithBotTop 𝕜) := by
          simp
    _ = cl(Astar ◁ (δᵛ(· | D) : F → WithBotTop 𝕜)) := by
      simpa using
        (supportFunction_preimage_closure_eq_lowerSemicontinuousHull_linearImage_of_pairing
          A Astar hAstar D hD)

end
