import Mathlib
import stacks_project.Chap04.Lemma_4_42_6.Direction2AbsFamily
import stacks_project.Chap04.Lemma_4_42_6.Direction2Left
import stacks_project.Chap04.Lemma_4_42_6.Direction2Right

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open Bicategory

variable {C : Type (max u v)} [Category.{v} C]

/-- Fixed-test absolute form of Lemma 4.42.6, direction `(2) -> (1)`. -/
opaque diagonal_twoFibreProduct_isRepresentable_of_all_slice_morphisms_representable_aux
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
  let T : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection :=
    FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  haveI hT : Bicategory.IsFinal T := diagonal_target_square_isFinal X
  let PDg := diagonalSourceSquare X
  haveI : Limits.HasTerminal (PDg ⟶ T) := Bicategory.IsFinal.hasTerminal (x := T) PDg
  let uDg : PDg ⟶ T := ⊤_ (PDg ⟶ T)
  let L := H ≫ T.p
  let R := H ≫ T.q
  have hprodLR : (FibredInGroupoidsOver.twoFibreProduct R L).IsRepresentable :=
    diagonal_component_product_isRepresentable X hAll L R
  let PP := productSliceSourceSquare X L R
  haveI : Limits.HasTerminal (PP ⟶ T) := Bicategory.IsFinal.hasTerminal (x := T) PP
  let uH : PP ⟶ T := ⊤_ (PP ⟶ T)
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

end CategoryTheory
