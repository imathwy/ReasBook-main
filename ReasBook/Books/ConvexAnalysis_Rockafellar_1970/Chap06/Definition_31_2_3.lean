import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_31_2_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar
open Bifunction

universe u v u' v' w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 31.2.3 computes the two conjugate branches attached to the Chapter 31
  LP Fenchel presentation from Definition 31.2.2, and then identifies the resulting dual LP value
  as the supremum over the canonical feasible region.
- `core/canonical`: the owner declarations already present upstream are the conjugation owners
  `(·)⋆` and `(·)∗`, the Chapter 31 branch owners `linearProgramFenchelPrimal` and
  `linearProgramFenchelConcave`, and the Section 30 feasible-set owner
  `linearProgramFeasibleSet`.
- `bridge/view`: the value clause remains the source-facing dual LP formula, but it is expressed on
  those existing owners rather than through longer re-expanded spellings.

Mandatory domain-style sampling used here:
- `convexConjugate` / `(·)⋆` from `Chap03.Defn_12_2`;
- `concaveConjugate` / `(·)∗` from `Chap06.Definition_6_30_4`;
- `linearProgramFenchelPrimal` / `linearProgramFenchelConcave` from `Definition_31_2_2`;
- `linearProgramFeasibleSet` from `Chap06.Definition_6_30_18`, sampled through the canonical LP
  owner stack already reused in `Definition_31_2_2`.

Best owner abstraction:
- branch data stays on `linearProgramFenchelPrimal` / `linearProgramFenchelConcave`;
- feasibility stays on `linearProgramFeasibleSet`;
- no extra local wrapper around the dual objective is introduced here.

Primitive data vs derived API:
- primitive source data: `aStar`, `a`, and the dual-side linear map `Astar`;
- primitive owner-side bridge data: the canonical linear functional
  `HasLinearPairing.pairingLinear.flip aStar` induced by the pairing-side coefficient `aStar`;
- primitive owners reused directly: the branch functions from Definition 31.2.2 and the feasible
  region from Section 30;
- derived API: the conjugate identities and the dual-value equality.

Layer target: `source-facing`, with the theorem surfaces shortened to the existing owner notation.
-/

section PrimalConjugate

variable {𝕜 : Type w} {X : Type u} {XStar : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup XStar] [PartialOrder XStar] [Module 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜]

local notation "pairingObj[" aStar "]" =>
  (LinearMap.flip (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 XStar) aStar)

-- Proof sketch: write the primal branch with the canonical pairing-induced functional
-- `HasLinearPairing.pairingLinear.flip aStar`, then apply the chapter translation rule for
-- `convexConjugate_add_inner` to the orthant indicator. The remaining conjugate is the canonical
-- cone-indicator owner theorem for the nonnegative orthant, and `xStar - aStar ∈ Set.Iic 0` is
-- exactly the order condition `xStar ≤ aStar`.
/-- Definition 31.2.3 (1): for the Chapter 31 primal LP function
`f(x) = ⟪a⋆, x⟫ₚ + δ[𝕜](x | x ≥ 0)`, the Fenchel conjugate is the indicator of the lower set
`{x⋆ | x⋆ ≤ a⋆}`. -/
theorem convexConjugate_linearProgramFenchelPrimal_eq_indicator_Iic
    (aStar : XStar) :
    ((linearProgramFenchelPrimal
        pairingObj[aStar])⋆ :
      XStar → WithBotTop 𝕜) =
      (δ[𝕜](· | Set.Iic aStar) : XStar → WithBotTop 𝕜) := sorry

end PrimalConjugate

section DualConjugate

variable {𝕜 : Type w} {U : Type u} {UStar : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup U] [PartialOrder U] [IsOrderedAddMonoid U] [Module 𝕜 U]
variable [AddCommGroup UStar] [PartialOrder UStar] [IsOrderedAddMonoid UStar] [Module 𝕜 UStar]
variable [HasPairing U UStar 𝕜]

-- Proof sketch: rewrite `Set.Ici a` as the translate of the canonical nonnegative orthant
-- `Set.Ici 0`, identify the corresponding indicator as a translation of the orthant indicator, and
-- apply the chapter translation rule for convex conjugates together with the sign bridge
-- `concaveConjugate_eq_neg_convexConjugate_neg`. The orthant conjugate is clause (1) specialized
-- to `aStar = 0`, and negating the resulting indicator moves `Set.Iic 0` to `Set.Ici 0`.
/-- Definition 31.2.3 (2): for the Chapter 31 concave LP function
`g(u) = -δ[𝕜](u | u ≥ a)`, the concave conjugate is
`u⋆ ↦ ⟪a, u⋆⟫ - δ[𝕜](u⋆ | u⋆ ≥ 0)`. -/
theorem concaveConjugate_linearProgramFenchelConcave_eq_pairing_sub_indicator_Ici_zero
    (a : U) :
    ((linearProgramFenchelConcave a)∗ : UStar → WithBotTop 𝕜) =
      fun uStar ↦ ((⟪a, uStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - δ[𝕜](uStar | Set.Ici (0 : UStar)) := sorry

end DualConjugate

section DualOptimalValue

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup U] [PartialOrder U] [IsOrderedAddMonoid U] [Module 𝕜 U]
variable [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup UStar] [PartialOrder UStar] [IsOrderedAddMonoid UStar] [Module 𝕜 UStar]
variable [PosSMulMono 𝕜 UStar]
variable [AddCommGroup XStar] [PartialOrder XStar] [Module 𝕜 XStar]
variable [HasPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

local notation "pairingObj[" aStar "]" =>
  (LinearMap.flip (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 XStar) aStar)

-- Proof sketch: substitute the two conjugate formulas from the first two clauses into the Chapter
-- 31 dual objective `u⋆ ↦ g∗ u⋆ - f⋆ (A⋆ u⋆)`. The indicator terms combine into the single
-- feasibility condition `u⋆ ∈ linearProgramFeasibleSet (0 : XStar) (-Astar) aStar`, and on that
-- feasible set the objective reduces to the pairing value `⟪a, u⋆⟫`.
/-- Definition 31.2.3 (3): the optimal value of the dual linear program is the supremum of the
pairing `⟪a, u⋆⟫` over the canonical dual feasible set
`linearProgramFeasibleSet (0 : XStar) (-Astar) aStar`, i.e. over `u⋆ ≥ 0` with
`Astar u⋆ ≤ aStar`. -/
theorem iSup_linearProgramFenchelDualObjective_eq_iSup_pairing_dualFeasible
    (aStar : XStar) (a : U) (Astar : UStar →ₗ[𝕜] XStar) :
    (⨆ uStar : UStar,
      ((linearProgramFenchelConcave a)∗) uStar -
        ((linearProgramFenchelPrimal
          pairingObj[aStar])⋆)
          (Astar uStar)) =
      ⨆ uStar : linearProgramFeasibleSet (0 : XStar) (-Astar) aStar,
        ((⟪a, (uStar : UStar)⟫ₚ : 𝕜) : WithBotTop 𝕜) := sorry

end DualOptimalValue
