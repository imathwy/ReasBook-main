import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_15

noncomputable section

open Function
open scoped Rockafellar

universe u v u' v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.30.1 says that inconsistency of the dual program is equivalent to
  some primal slice `F u` being unbounded below, while inconsistency of the primal program is
  equivalent to some adjoint slice `F* x⋆` being unbounded above.
- `core/canonical`: the chapter owners already present are `IsConsistent`, `adjoint`,
  `perturbationFunction`, and `upperPerturbationFunction`.
- `bridge/view`: the textbook phrases “has no lower bound” and “has no upper bound” are rendered
  canonically by the extended-order slice values `perturbationFunction F u = ⊥` and
  `supᵇ(F⋆) x⋆ = ⊤`.

Domain-style sampling used here:
- `IsConsistent` from Definition 6.29.1;
- `adjoint` from Definition 6.30.14;
- `upperPerturbationFunction` from Definition 6.30.11;
- the two conjugacy identities from Theorem 6.30.15.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜` on pairing spaces
  `(U, UStar)` and `(X, XStar)`;
- canonical owners: primal consistency `IsConsistent F` and dual consistency
  `IsConsistent (adjoint F)`;
- derived source-facing conclusions: existence of a primal slice with infimum `⊥`, and existence
  of an adjoint slice with supremum `⊤`.

Layer target: `bridge/view`, stated directly on the canonical Chapter 6 owners without introducing
any separate package for primal or dual programs.
-/

section

variable {𝕜 : Type*}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

-- Proof sketch: dual inconsistency means the zero slice `objective (adjoint F)` is
-- everywhere `⊤`. Apply the first conjugacy identity from Theorem 6.30.15,
-- `concaveConjugate (- perturbationFunction F) = objective (adjoint F)`, and use the
-- defining infimum formula for the concave conjugate to identify this with existence of some
-- parameter `u` where `perturbationFunction F u = ⊥`.
/-- Corollary 6.30.1 (1): the dual program associated with `F` is inconsistent exactly when some
primal slice `F u` has no lower bound, rendered canonically by
`perturbationFunction F u = ⊥`. -/
theorem not_isConsistent_adjointFunction_iff_exists_perturbationFunction_eq_bot
    :
    ¬ IsConsistent ((F⋆) : XStar → UStar → WithBotTop 𝕜) ↔
      ∃ u : U, perturbationFunction F u = ⊥ := sorry

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [Neg UStar] [AddCommMonoid UStar] [Module 𝕜 UStar]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

-- Proof sketch: primal inconsistency means the zero slice `objective F` is everywhere `⊤`.
-- For a closed proper convex bifunction, Theorem 6.30.15 identifies `objective F` with the
-- Fenchel conjugate of `- supᵇ(F⋆)`. A Fenchel conjugate is
-- identically `⊤` exactly when the underlying function takes the value `⊥` somewhere, i.e. when
-- `supᵇ(F⋆)` takes the value `⊤` at some dual point.
/-- Corollary 6.30.1 (2): the primal program associated with a closed proper convex bifunction
`F` is inconsistent exactly when some adjoint slice `F* x⋆` has no upper bound, rendered
canonically by `supᵇ(F⋆) x⋆ = ⊤`. -/
theorem not_isConsistent_iff_exists_upperPerturbationFunction_adjoint_eq_top
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    ¬ IsConsistent F ↔
      ∃ xStar : XStar, supᵇ(((F⋆) : XStar → UStar → WithBotTop 𝕜)) xStar = ⊤ := sorry

end

end Bifunction
