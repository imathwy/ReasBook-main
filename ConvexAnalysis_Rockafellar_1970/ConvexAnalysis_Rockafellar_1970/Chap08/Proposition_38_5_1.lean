import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_24
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_5

noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v w

variable {U : Type u} {X : Type v} {Y : Type w}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, this item is Rockafellar's Corollary 38.5.1 on
  the product `GF` of closed proper convex bifunctions, asserting closedness of `GF`, pointwise
  attainment of the defining infimum, and the adjoint-side closure identity.
- `core/canonical`: the owner declarations in the chapter are the product owner `Bifunction.comp`
  used as `comp G F`,
  `Bifunction.adjoint`, `Bifunction.inverse`,
  `Bifunction.dom`, `Bifunction.IsProper`, `Bifunction.IsClosedConvex`, and the bifunction-closure
  owner `Bifunction.closure`.
- `bridge/view`: the source right-hand side `cl(F^* G^*)` is rendered by the closure owner
  applied to `comp (adjoint F) (adjoint G)`.

Primary mathematical domain:
- composition of convex bifunctions and adjoint-side closure formulas.

Domain-style sampling used here:
- `Bifunction.comp` and `Bifunction.comp_apply_eq_iInf` from `Theorem_38_5`;
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`;
- `Bifunction.closure` from `Chap06.Definition_6_29_24`;
- `Bifunction.inverse` from `Chap07.Definition_36_4_1`;
- `Bifunction.IsClosedConvex`, `Bifunction.dom`, and `Bifunction.IsProper` from
  `Chap07.Defn_34_2` and `Chap08.Theorem_38_1`.

Primitive data vs derived API:
- primitive source data: closed proper convex bifunctions `F : U → X → EReal` and
  `G : X → Y → EReal`;
- primitive owner layer: the source-facing product `comp G F`;
- derived API: closedness of `comp G F`, pointwise attainment of its defining infimum, and the
  adjoint-side closure identity.

Layer target: `source-facing`, stated directly on the Chapter 38 product owner and existing
adjoint/inverse/domain owners rather than through a parallel “closed composition” package.
-/

variable (F : U → X → EReal) (G : X → Y → EReal)

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation "F⋆" => (adjoint X U F : X → U → EReal)
local notation "G⋆" => (adjoint Y X G : Y → X → EReal)
local notation "(GF)⋆" => (adjoint Y U (comp G F) : Y → U → EReal)

-- Proof sketch: this is the closed-case companion to Theorem 38.5. The common-relative-interior
-- hypothesis is already expressed through the chapter owners `dom`, `adjoint`, and
-- `inverse`, so the closedness conclusion should stay on the product owner `comp G F`.
/-- Corollary 38.5.1, closedness clause: if `F` and `G` are closed proper convex bifunctions and
`ri (dom F^*)` meets `ri (dom (G^*)_*)`, rendered here by `ri(dom (adjoint F))` and
`ri(dom (inverse (adjoint G)))`, then the product `comp G F` is closed convex. -/
theorem isClosedConvex_comp_of_common_riDom_adjoint_inverse
    (hF : IsClosedConvex F) (hF_proper : IsProper F)
    (hG : IsClosedConvex G) (hG_proper : IsProper G)
    (hri :
      (ri(dom (F⋆)) ∩ ri(dom ((G⋆) _*))).Nonempty)
    : IsClosedConvex (comp G F) := by
  sorry

-- Proof sketch: the same regularity hypothesis yields attainment of the source infimum
-- `inf_x (F u x + G x y)` for every `(u, y)`. The theorem keeps that source-facing equality
-- surface instead of packaging attainment as auxiliary data.
/-- Corollary 38.5.1, attainment clause: under the same hypotheses, the infimum in the definition
of `comp G F` is attained at every pair `(u, y)`. -/
theorem exists_eq_comp_of_common_riDom_adjoint_inverse
    (hF : IsClosedConvex F) (hF_proper : IsProper F)
    (hG : IsClosedConvex G) (hG_proper : IsProper G)
    (hri :
      (ri(dom (F⋆)) ∩ ri(dom ((G⋆) _*))).Nonempty)
    (u : U) (y : Y) :
    ∃ x : X, comp G F u y = F u x + G x y := by
  sorry

-- Proof sketch: the adjoint of the product is identified with the closure of the product of the
-- adjoints. The right-hand side is stated directly with the source-facing closure owner.
/-- Corollary 38.5.1, adjoint clause:
`(GF)^* = cl(F^* G^*)`, rendered by `adjoint`, `comp`, and `closure`. -/
theorem
    adjointFunction_comp_eq_closure_comp_adjointFunction_of_common_riDom_adjoint_inverse
    (hF : IsClosedConvex F) (hF_proper : IsProper F)
    (hG : IsClosedConvex G) (hG_proper : IsProper G)
    (hri :
      (ri(dom (F⋆)) ∩ ri(dom ((G⋆) _*))).Nonempty)
    :
    (GF)⋆ = cl (comp F⋆ G⋆) := by
  sorry

end

end Bifunction
