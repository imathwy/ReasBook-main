import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8
import ConvexAnalysis_Rockafellar_1970.Chap08.Corollary_38_7_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_7_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_5_5
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]
variable {F : U → X → EReal} {G : X → Y → EReal}

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation "F⋆" => adjoint X U F
local notation "G⋆" => adjoint Y X G

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.7.2 identifies the three source terms
  `⟨GFu, y⋆⟩`, `⟨Fu, G⋆ y⋆⟩`, and `⟨u, F⋆ G⋆ y⋆⟩` under the regularity hypothesis
  `ri(dom F⋆) ∩ ri(dom G) ≠ ∅` and the slice qualification `u ∈ ri(dom (comp G F))`.
- `core/canonical`: the owner layer already present in the chapter is `Bifunction.comp`,
  `Bifunction.adjoint`, `Bifunction.dom`, and the Chapter 33 convex-pairing notation
  `⟪·, ·⟫ᶠ`.
- `bridge/view`: the two atomic equalities in the source chain are stated directly here on the
  existing owner layer, while the proof route still reuses Corollary 38.7.1's image/adjoint
  pairing bridge and Theorem 38.5's product-adjoint identity.

Primary mathematical domain:
- composition of proper convex bifunctions and slice-wise Fenchel pairings.

Domain-style sampling used here:
- `Bifunction.comp` and the adjoint identity theorems from `Theorem_38_5`;
- the Chapter 33 source-facing convex-pairing notation `⟪f, y⟫ᶠ` from
  `Definition33_0_8`;
- Corollary 38.7.1 in `Definition_38_7_1`, which already owns the slice-wise bridge between
  a bifunction image conjugate and the Chapter 38 inner-product owner.

Primitive data vs derived API:
- primitive inputs: proper convex bifunctions `F` and `G`, a primal point `u`, and a dual point
  `yStar`;
- primitive owner hypotheses: convexity and properness of `F` and `G`, the common-relative-
  interior hypothesis on `dom F⋆` and `dom G`, and the slice qualification
  `u ∈ ri(dom (comp G F))`;
- derived API: the two source-facing atomic equalities
  `⟨GFu, y⋆⟩ = innerProduct(Fu, G⋆ y⋆)` and
  `innerProduct(Fu, G⋆ y⋆) = ⟨u, F⋆ G⋆ y⋆⟩`, together with the transitive outer equality as a
  companion consequence.

Layer target: `source-facing`, using the existing Chapter 38 owners directly rather than
introducing a separate “composition pairing data” wrapper.
-/

-- Proof sketch: the source middle equality `⟨GFu, y^*⟩ = ⟨Fu, G^* y^*⟩` is the Chapter 38.7.1
-- image/adjoint bridge specialized to the slice pair `(F u, G)`, where the middle term is the
-- Chapter 38 owner `Function.innerProduct (F u) (G⋆ yStar)`. The second equality then reads that
-- same owner through Theorem 38.5's identity `(GF)^* = F^* G^*`.
variable
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri : (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)

include hF_convex hF_proper hG_convex hG_proper hri

/-- Corollary 38.7.2, first source edge: under the common-relative-interior hypothesis and
`u ∈ ri (dom (GF))`, the pairing `⟨GFu, y^*⟩` agrees with the Chapter 38 inner-product owner
`Function.innerProduct (F u) (G^* y^*)`. -/
theorem convexPairing_comp_slice_eq_innerProduct_adjointFunction_slice_of_mem_riDom_comp
    (u : U) (hu : u ∈ ri(dom (comp G F))) (yStar : Y) :
    ⟪comp G F u, yStar⟫ᶠ = Function.innerProduct (F u) (G⋆ yStar) := by
  sorry

/-- Corollary 38.7.2, second source edge: the Chapter 38 middle term
`Function.innerProduct (F u) (G^* y^*)` is the pairing `⟨u, F^* G^* y^*⟩`. -/
theorem innerProduct_adjointFunction_slice_eq_convexPairing_comp_adjoint_slice_of_mem_riDom_comp
    (u : U) (hu : u ∈ ri(dom (comp G F))) (yStar : Y) :
    Function.innerProduct (F u) (G⋆ yStar) = ⟪u, comp F⋆ G⋆ yStar⟫ᶠ := by
  sorry

/-- Corollary 38.7.2, transitive companion: the first and third source pairings coincide. -/
theorem convexPairing_comp_slice_eq_convexPairing_comp_adjoint_slice_of_mem_riDom_comp
    (u : U) (hu : u ∈ ri(dom (comp G F))) (yStar : Y) :
    ⟪comp G F u, yStar⟫ᶠ =
      ⟪u, comp F⋆ G⋆ yStar⟫ᶠ := by
  exact
    (convexPairing_comp_slice_eq_innerProduct_adjointFunction_slice_of_mem_riDom_comp
      hF_convex hF_proper hG_convex hG_proper hri u hu yStar).trans
      (innerProduct_adjointFunction_slice_eq_convexPairing_comp_adjoint_slice_of_mem_riDom_comp
        hF_convex hF_proper hG_convex hG_proper hri u hu yStar)

end

end Bifunction
