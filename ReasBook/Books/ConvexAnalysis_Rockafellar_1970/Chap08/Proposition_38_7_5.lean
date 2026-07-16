import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_7_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_5

noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]
variable {F : U → X → EReal} {G : X → Y → EReal}

local notation "F⋆" => (adjoint X U F : X → U → EReal)
local notation "G⋆" => (adjoint Y X G : Y → X → EReal)

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 38.7.5 studies the Chapter 38 product `GF` of co-finite
  closed-convex bifunctions, asserting that this product is again co-finite and that the adjoint
  commutes with it as `(GF)^* = F^* G^*`.
- `core/canonical`: the stable owner layer is already present upstream as `Bifunction.comp`,
  `Bifunction.adjoint`, the Chapter 38.5 product-adjoint theorem
  `adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom`, and the co-finiteness owner
  `Bifunction.IsCofinite`.
- `bridge/view`: this item contributes only the bridge from the Chapter 38.7 closed-convex
  co-finite owner hypotheses to the common-`riDom` qualification and properness data needed by
  Theorem 38.5, together with the co-finiteness preservation statement for `comp`.

Primary mathematical domain:
- convex bifunction duality for Chapter 38 products in the finite-dimensional real paired setting.

Domain-style sampling used here:
- `Bifunction.comp` and
  `Bifunction.adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom` from `Theorem_38_5`;
- `Bifunction.IsCofinite` and
  `Bifunction.isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ`,
  `Bifunction.uncurry_isProper_of_isClosedConvex_of_isCofinite` from `Proposition_38_7_2`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive inputs: bifunctions `F : U → X → EReal` and `G : X → Y → EReal`;
- primitive owner hypotheses: `IsClosedConvex F`, `IsCofinite X U F`,
  `IsClosedConvex G`, `IsCofinite Y X G`;
- derived API: the common-relative-interior bridge for Theorem 38.5, the induced Chapter 38
  properness data, the adjoint identity, and co-finiteness of `comp G F`.

Layer target: `bridge/view`.
-/

-- Proof sketch: Proposition 38.7.2 upgrades co-finiteness, under the closed-convex owner, to
-- full source domain `dom G = Set.univ` and full adjoint-side source domain `dom (-F⋆) = Set.univ`.
-- For `EReal`-valued slices these are the same effective domains as `dom G` and `dom F⋆`, so the
-- relative interiors are both all of the ambient spaces. This is exactly the qualification needed
-- by Theorem 38.5.
/-- Bridge/view lemma: closed-convex co-finite bifunctions satisfy the common-relative-interior
qualification `riDom(F⋆) ∩ riDom(G) ≠ ∅` required by the Chapter 38 product-adjoint theorem. -/
theorem common_riDom_adjoint_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hG : IsClosedConvex G) (hG_cofinite : IsCofinite Y X G) :
    (riDom(F⋆) ∩ riDom(G)).Nonempty := sorry

-- Proof sketch: combine the bridge theorem
-- `common_riDom_adjoint_of_isClosedConvex_of_isCofinite` with the Chapter 38.5 adjoint formula
-- for the product `comp G F`, and derive the Chapter 38 properness owner from the full-domain
-- consequences of Proposition 38.7.2.
/-- Proposition 38.7.5: if `F` and `G` are closed-convex co-finite bifunctions, then the adjoint
of their product is the reversed product of the adjoints, i.e.
`adjoint Y U (comp G F) = comp F⋆ G⋆`. -/
theorem adjointFunction_comp_eq_comp_adjoint_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hG : IsClosedConvex G) (hG_cofinite : IsCofinite Y X G) :
    adjoint Y U (comp G F) = comp F⋆ G⋆ := sorry

-- Proof sketch: express co-finiteness of `comp G F` through the Chapter 33 pointwise pairing
-- equation, then use the product adjoint identity above together with the co-finiteness
-- equations for `F` and `G` to rewrite the required pairings into a composed finite duality
-- expression.
/-- The product of closed-convex co-finite bifunctions is again co-finite. Convexity of
`comp G F` itself is already provided upstream by `uncurry_comp_isConvex`. -/
theorem isCofinite_comp_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hG : IsClosedConvex G) (hG_cofinite : IsCofinite Y X G) :
    IsCofinite Y U (comp G F) := sorry

end

end Bifunction
