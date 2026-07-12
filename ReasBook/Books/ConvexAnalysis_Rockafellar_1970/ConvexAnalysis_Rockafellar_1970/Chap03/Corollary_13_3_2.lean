import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_3

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.2 characterizes when `dom f*` is an affine set for a closed
  proper convex function `f`.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.IsClosedProperConvex`, the Chapter 13 support-function owner
  `supportFunction`, the support-asymmetry criterion on `dom(f⋆)`, the effective-domain
  support/recession bridge from `Theorem_13_3`, and the recession-function owner
  `Function.recessionFunction` written in this chapter as `f0⁺`.
- `bridge/view`: the textbook phrase `dom f*` is rendered by the chapter owner notation
  `dom(f⋆)`, while the phrase "is an affine set" is rendered by the affine-span fixed-point
  owner equation `(affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆)`.

Domain-style sampling used here:
- `supportFunction` from Chapter 1's owner declarations;
- the support-asymmetry affine criterion for a convex set, specialized in this file to `dom(f⋆)`;
- `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from `Theorem_13_3`.
- `Function.IsClosedProperConvex` from `Text_12_3_6`.

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot 𝕜`;
- primitive owner-side data: the convex-set support-asymmetry owner criterion;
- derived owner-side data: convexity of `dom(f⋆)`, supplied canonically by
  `Function.isConvex_convexConjugate`;
- derived API: the source-facing closed-proper-convex specialization obtained by rewriting
  `δᵛ(· | dom(f⋆))` as `f0⁺` via `Theorem_13_3`.

Layer target: this item stays `source-facing`, with a pairing-level support-function theorem as
the primitive public owner surface and the `f0⁺` statement as a bridge specialization.
-/

/-- Canonical support-asymmetry affine criterion on a convex set. -/
theorem affineSpan_eq_self_iff_supportFunction_eq_top_of_support_asymmetry
    {C : Set E} (hC : Convex 𝕜 C) :
    (affineSpan 𝕜 C : Set E) = C ↔
      ∀ y : E,
        -δᵛ[WithTopBot 𝕜](-y | C) ≠
            δᵛ[WithTopBot 𝕜](y | C) →
          δᵛ[WithTopBot 𝕜](y | C) = ⊤ := by
  sorry

/-- Primitive owner form for Corollary 13.3.2: `dom(f⋆)` is affine exactly when every
support-asymmetric direction has support value `+∞`. -/
theorem effectiveDomain_convexConjugate_affine_iff_supportFunction_eq_top_of_support_asymmetry
    (f : E → WithTopBot 𝕜) :
    (affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆) ↔
      ∀ y : E,
        -δᵛ[WithTopBot 𝕜](-y | dom(f⋆)) ≠
            δᵛ[WithTopBot 𝕜](y | dom(f⋆)) →
          δᵛ[WithTopBot 𝕜](y | dom(f⋆)) = ⊤ := by
  have hdom_convex : Convex 𝕜 dom(f⋆) := by
    simpa using ((Function.isConvex_convexConjugate f).convex_dom)
  simpa using
    (affineSpan_eq_self_iff_supportFunction_eq_top_of_support_asymmetry
      (C := dom(f⋆)) hdom_convex)

section Bridge

variable [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

-- Proof sketch: apply the primitive support-function theorem above and rewrite the
-- support-function owner to `f0⁺` via the supplied bridge.
/-- Bridge form for Corollary 13.3.2: if the support function of `dom(f⋆)`
agrees with the recession function `f0⁺`, then `dom(f⋆)` is affine exactly when every
support-asymmetric primal direction already has recession value `+∞`. -/
private theorem
    effectiveDomain_convexConjugate_affine_iff_recessionFunction_eq_top_of_asymmetry_of_bridge
    (f : E → WithTopBot 𝕜)
    (hsupport :
      (δᵛ[WithTopBot 𝕜](· | dom(f⋆)) : E → WithTopBot 𝕜) = (f₀⁺ : E → WithTopBot 𝕜)) :
    (affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆) ↔
      ∀ y : E, -(f₀⁺ (-y)) ≠ f₀⁺ y → f₀⁺ y = ⊤ := by
  constructor
  · intro haff y hy
    have hy_support :
        -δᵛ[WithTopBot 𝕜](-y | dom(f⋆)) ≠
            δᵛ[WithTopBot 𝕜](y | dom(f⋆)) := by
      simpa [hsupport] using hy
    have htop_support :
        δᵛ[WithTopBot 𝕜](y | dom(f⋆)) = (⊤ : WithTopBot 𝕜) :=
      (effectiveDomain_convexConjugate_affine_iff_supportFunction_eq_top_of_support_asymmetry
        (f := f)).1 haff y hy_support
    simpa [hsupport] using htop_support
  · intro hrec
    refine
      (effectiveDomain_convexConjugate_affine_iff_supportFunction_eq_top_of_support_asymmetry
        (f := f)).2 ?_
    intro y hy_support
    have hy_rec : -(f₀⁺ (-y)) ≠ f₀⁺ y := by
      simpa [hsupport] using hy_support
    have htop_rec : f₀⁺ y = (⊤ : WithTopBot 𝕜) := hrec y hy_rec
    simpa [hsupport] using htop_rec

-- Proof sketch: by Theorem 13.3, `f0⁺` is the support function of `dom(f⋆)`. Apply the bridge
-- theorem above and rewrite the support-function owner to `f0⁺`.
/-- Corollary 13.3.2: for a closed proper convex function `f`, the effective domain of `f*` is an
affine set exactly when every direction where the recession function `f0⁺` fails the support
symmetry relation `-f0⁺(-y) = f0⁺ y` already has recession value `+∞`. -/
theorem effectiveDomain_convexConjugate_affine_iff_recessionFunction_eq_top_of_support_asymmetry
    (f : E → WithTopBot 𝕜) (hf : IsClosedProperConvex[𝕜] f) :
    (affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆) ↔
      ∀ y : E, -(f₀⁺ (-y)) ≠ f₀⁺ y → f₀⁺ y = ⊤ := by
  have hsupport :
      (δᵛ[WithTopBot 𝕜](· | dom(f⋆)) : E → WithTopBot 𝕜) = (f₀⁺ : E → WithTopBot 𝕜) := by
    simpa using
      supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction
        (f := f) hf
  exact
    effectiveDomain_convexConjugate_affine_iff_recessionFunction_eq_top_of_asymmetry_of_bridge
      (f := f) hsupport

end Bridge

end
