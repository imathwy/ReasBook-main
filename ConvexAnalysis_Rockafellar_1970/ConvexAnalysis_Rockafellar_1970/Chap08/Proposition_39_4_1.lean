import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_39_3

noncomputable section

open scoped Rockafellar SetRel

universe u v w z

namespace SetRel

section PrimalDualExtrema

variable {U : Type u} {X : Type v}

section Primal

variable {𝕜 : Type*} {XStar : Type w}
variable [ConditionallyCompleteLattice 𝕜] [HasPairing XStar X 𝕜]

-- Proof sketch: unfold `supremumProcessPairing` as the support function of the fiber
-- `A.image ({u} : Set U)`, then apply `supportFunction_def`.
/-- For fixed `u` and `xStar`, the supremum-oriented process pairing `⟨Au, xStar⟩` is the
supremum of the linear functional `x ↦ ⟪xStar, x⟫ₚ` over the fiber
`A.image ({u} : Set U)`. -/
theorem supremumProcessPairing_eq_iSup_pairing_over_fiber
    (A : SetRel U X) (u : U) (xStar : XStar) :
    supremumProcessPairing 𝕜 XStar A u xStar =
      ⨆ x : A.image ({u} : Set U), (⟪xStar, (x : X)⟫ₚ : WithBotTop 𝕜) := sorry

end Primal

section Dual

variable {𝕜 : Type*} {XStar : Type w} {UStar : Type z}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

-- Proof sketch: unfold `supremumAdjointProcessPairing` to the Chapter 34 upper representative of
-- the same fiber-indicator kernel, then rewrite the resulting adjoint-side pairing as the infimum
-- of `uStar ↦ ⟪u, uStar⟫ₚ` over the adjoint fiber
-- `((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar))`.
/-- The dual Chapter 39 pairing `⟨u, A⋆ xStar⟩` is the infimum of the linear functional
`uStar ↦ ⟪u, uStar⟫ₚ` over the adjoint fiber
`((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar))`.
-/
theorem supremumAdjointProcessPairing_eq_iInf_pairing_over_adjointFiber
    (A : SetRel U X) (u : U) (xStar : XStar) :
    supremumAdjointProcessPairing 𝕜 XStar UStar A u xStar =
      ⨅ uStar : (A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar),
        (⟪u, (uStar : UStar)⟫ₚ : WithBotTop 𝕜) := sorry

end Dual

section PrimalDualRelation

variable {𝕜 : Type*} {XStar : Type w} {UStar : Type z}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Neg UStar] [HasPairing U UStar 𝕜]
variable [HasPairing X XStar 𝕜] [HasPairing XStar X 𝕜]

-- Proof sketch: rewrite the primal and dual sides using the two preceding fiber formulas, then
-- substitute the assumed equality
-- `supremumProcessPairing 𝕜 XStar A u xStar =
--   supremumAdjointProcessPairing 𝕜 XStar UStar A u xStar`.
/-- Equality of the primal and dual Chapter 39 pairings is exactly the corresponding primal-dual
extremum relation between the supremum over the primal fiber and the infimum over the adjoint
fiber. -/
theorem primal_dual_extremum_relation_of_pairing_eq
    (A : SetRel U X) (u : U) (xStar : XStar)
    (hEq : supremumProcessPairing 𝕜 XStar A u xStar =
      supremumAdjointProcessPairing 𝕜 XStar UStar A u xStar) :
    (⨆ x : A.image ({u} : Set U), (⟪xStar, (x : X)⟫ₚ : WithBotTop 𝕜)) =
      ⨅ uStar : (A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar),
        (⟪u, (uStar : UStar)⟫ₚ : WithBotTop 𝕜) := sorry

end PrimalDualRelation

section Polyhedral

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable {UStar : Type z} [AddCommMonoid UStar] [Module 𝕜 UStar]
variable {XStar : Type w}
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
variable {Y : Type _} [HasPairing (U × X) Y 𝕜]

-- Proof sketch: view the primal fiber and the adjoint fiber as coordinate slices of the
-- polyhedral graphs of `A` and `A∗[XStar, UStar; 𝕜]`. Slicing a polyhedral graph by a singleton
-- coordinate constraint yields a polyhedral feasible set, so the displayed primal and dual
-- extremum problems have polyhedral feasible regions.
/-- If `A` is polyhedral, then both the primal fiber `A.image ({u} : Set U)` and the dual adjoint
fiber `((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar))` are polyhedral. Hence the two displayed
extremum problems are linear-function-over-polyhedron problems. -/
theorem primal_and_dual_fibers_are_polyhedral_of_isPolyhedralProcess
    (A : SetRel U X) (hA : A.IsPolyhedralProcess 𝕜 Y) (u : U) (xStar : XStar) :
    (A.image ({u} : Set U)).IsPolyhedral 𝕜 ∧
      ((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar)).IsPolyhedral 𝕜 := sorry

end Polyhedral

end PrimalDualExtrema

end SetRel
