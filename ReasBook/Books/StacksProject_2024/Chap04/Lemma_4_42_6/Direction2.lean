import Mathlib
import StacksProject_2024.Chap04.Lemma_4_42_6.Direction2AbsFamily
import StacksProject_2024.Chap04.Lemma_4_42_6.Direction2Left
import StacksProject_2024.Chap04.Lemma_4_42_6.Direction2Right

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open Bicategory

variable {C : Type (max u v)} [Category.{v} C]

-- These wrappers only *delegate* to the transport lemmas; matching their bundled
-- two-fibre-product goals would otherwise unfold the (transparent) explicit-pullback tower and
-- overflow whnf.  `twoFibreProduct` stays transparent globally (so `Pasting2` can project through
-- it); sealing it here keeps the delegation matching syntactic.
attribute [local irreducible] FibredInGroupoidsOver.twoFibreProduct

/-! ### Lemma 4.42.6, direction (2) ⟹ (1) -/

/-- Fixed-test absolute form of Lemma 4.42.6, direction `(2) -> (1)`. -/
private opaque diagonal_twoFibreProduct_isRepresentable_of_all_slice_morphisms_representable_aux
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G)
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    absoluteTfpRep H
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) := by
  let T := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  haveI hT : Bicategory.IsFinal T := diagonal_target_square_isFinal X
  let PDg := diagonalSourceSquare X
  let uDg : PDg ⟶ T := diagonal_source_terminal_map X T
  let L := H ≫ T.p
  let R := H ≫ T.q
  have hprodLR : (FibredInGroupoidsOver.twoFibreProduct R L).IsRepresentable :=
    diagonal_component_product_isRepresentable X hAll L R
  let PP := productSliceSourceSquare X L R
  let uH : PP ⟶ T := diagonal_product_terminal_map X L R T
  have hcanonDiag :
      (FibredInGroupoidsOver.twoFibreProduct
        (FibredInGroupoidsOver.overMap
            (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom)
        uDg.hom).IsRepresentable :=
    diagonal_canonical_basechange_isRepresentable X L R uDg uH hprodLR
  let eL : (FibredInGroupoidsOver.overMap
        (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
      (productSliceSourceSquare X L R).p) ≅ L :=
    diagonal_left_base_iso X L R
  let eR : (FibredInGroupoidsOver.overMap
        (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
      (productSliceSourceSquare X L R).q) ≅ R :=
    diagonal_right_base_iso X L R
  let leftK :=
    diagonal_canonical_left_projection_cell X H L R uH eL
  let rightK :=
    diagonal_canonical_right_projection_cell X H L R uH eR
  have hLocal : (FibredInGroupoidsOver.twoFibreProduct H uDg.hom).IsRepresentable :=
    diagonal_final_left_transport_with_alpha X H L R uDg uH
      (actualTwoFibreProductMapsComparisonIsoOfTwoCells X
        (FibredInGroupoidsOver.overMap
          (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom)
        H leftK rightK)
      hcanonDiag
  exact absoluteTfpRep_of_isRepresentable H
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)
    (diagonal_transport_right_to_formal X H uDg hLocal)

/-- Absolute family form of Lemma 4.42.6, direction `(2) -> (1)`. -/
private opaque diagonal_absoluteFamily_of_all_slice_morphisms_representable
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G) :
    absoluteTfpFamily
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) := by
  refine absoluteTfpFamily_of_forall
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) ?_
  intro W H
  exact diagonal_twoFibreProduct_isRepresentable_of_all_slice_morphisms_representable_aux X hAll H

/-- Lemma 4.42.6, direction (2) ⟹ (1): if every slice morphism `G : C/U ⟶ X` is representable,
then the diagonal `Δ : X ⟶ X ×_C X` is representable. -/
opaque representable_diagonal_of_all_slice_morphisms_representable
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G) :
    FibredInGroupoidsMor.IsRepresentable
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) :=
  absoluteTfpFamily_to_isRepresentable
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)
    (diagonal_absoluteFamily_of_all_slice_morphisms_representable X hAll)

end CategoryTheory
