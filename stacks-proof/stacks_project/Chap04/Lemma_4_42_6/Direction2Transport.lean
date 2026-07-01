import Mathlib
import stacks_project.Chap04.Lemma_4_42_6.Direction2Aux

universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open Functor IsHomLift IsStronglyCartesian Bicategory
open CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

variable {C : Type (max u v)} [Category.{v} C]

noncomputable opaque diagonalTarget_as_raw
    (X : FibredInGroupoidsOver C)
    {A : FibredInGroupoidsOver C}
    (H : A ⟶ FibredInGroupoidsMor.twoFibreProductDiagonalTarget X.baseProjection) :
    A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection := by
  unfold FibredInGroupoidsMor.twoFibreProductDiagonalTarget at H
  exact H

noncomputable opaque diagonalTarget_from_raw
    (X : FibredInGroupoidsOver C)
    {A : FibredInGroupoidsOver C}
    (H : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    A ⟶ FibredInGroupoidsMor.twoFibreProductDiagonalTarget X.baseProjection := by
  unfold FibredInGroupoidsMor.twoFibreProductDiagonalTarget
  exact H

@[irreducible] noncomputable def canonicalSelfProduct (X : FibredInGroupoidsOver C) :
    FibredInGroupoidsOver C :=
  FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection

opaque canonicalSelfProduct_to_raw
    (X : FibredInGroupoidsOver C) :
    canonicalSelfProduct X =
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection := by
  unfold canonicalSelfProduct
  rfl

noncomputable opaque canonicalSelfProduct_to_raw_hom
    (X : FibredInGroupoidsOver C) :
    canonicalSelfProduct X ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection := by
  rw [canonicalSelfProduct_to_raw X]
  exact 𝟙 _

noncomputable opaque canonicalSelfProduct_raw_to_hom
    (X : FibredInGroupoidsOver C) :
    FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection ⟶
      canonicalSelfProduct X := by
  rw [canonicalSelfProduct_to_raw X]
  exact 𝟙 _

noncomputable opaque canonicalSelfProduct_as_raw
    (X : FibredInGroupoidsOver C)
    {A : FibredInGroupoidsOver C}
    (H : A ⟶ canonicalSelfProduct X) :
    A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection :=
  H ≫ canonicalSelfProduct_to_raw_hom X

noncomputable opaque canonicalSelfProduct_from_raw
    (X : FibredInGroupoidsOver C)
    {A : FibredInGroupoidsOver C}
    (H : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    A ⟶ canonicalSelfProduct X :=
  H ≫ canonicalSelfProduct_raw_to_hom X

noncomputable opaque canonical_left_component
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶ canonicalSelfProduct X) :
    ofFunctor (Over.forget W) ⟶ X := by
  exact canonicalSelfProduct_as_raw X H ≫
    FibredInGroupoidsOver.twoFibreProductLeftProjection X.baseProjection X.baseProjection

noncomputable opaque canonical_right_component
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶ canonicalSelfProduct X) :
    ofFunctor (Over.forget W) ⟶ X := by
  exact canonicalSelfProduct_as_raw X H ≫
    FibredInGroupoidsOver.twoFibreProductRightProjection X.baseProjection X.baseProjection

noncomputable opaque squareHom_as_raw
    (X : FibredInGroupoidsOver C)
    {P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    (u : P ⟶ FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    P.obj ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection := by
  exact u.hom

@[irreducible] noncomputable def tfpRep {A B T : FibredInGroupoidsOver C} (F : A ⟶ T) (G : B ⟶ T) :
    Prop :=
  (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable

@[irreducible] noncomputable def absTfpRep {A B T : FibredInGroupoidsOver C}
    (F : A ⟶ T) (G : B ⟶ T) : Prop :=
  (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable

opaque absTfpRep_of_isRepresentable
    {A B T : FibredInGroupoidsOver C}
    (F : A ⟶ T) (G : B ⟶ T) :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable → absTfpRep F G := by
  intro hRep
  unfold absTfpRep
  exact hRep

opaque absTfpRep_to_isRepresentable
    {A B T : FibredInGroupoidsOver C}
    (F : A ⟶ T) (G : B ⟶ T) :
    absTfpRep F G → (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable := by
  intro hRep
  unfold absTfpRep at hRep
  exact hRep

/-- Package ordinary two-fibre-product representability as the irreducible `tfpRep` predicate. -/
opaque tfpRep_of_isRepresentable
    {A B T : FibredInGroupoidsOver C}
    (F : A ⟶ T) (G : B ⟶ T) :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable → tfpRep F G := by
  intro hRep
  unfold tfpRep
  exact hRep

/-- Unpack the lightweight `tfpRep` predicate. -/
opaque tfpRep_to_isRepresentable
    {A B T : FibredInGroupoidsOver C}
    (F : A ⟶ T) (G : B ⟶ T) :
    tfpRep F G → (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable := by
  intro hRep
  unfold tfpRep at hRep
  exact hRep

/-- Terminal map from any square over the canonical diagonal target to the canonical target square.
Keeping the source square named avoids repeated unfolding of product-slice squares. -/
noncomputable opaque canonical_target_terminal_map
    (X : FibredInGroupoidsOver C)
    (P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection) :
    P ⟶ FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection := by
  let T := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  haveI : Bicategory.IsFinal T := diagonal_target_square_isFinal X
  haveI : Limits.HasTerminal (P ⟶ T) :=
    Bicategory.IsFinal.hasTerminal (x := T) P
  exact ⊤_ (P ⟶ T)

/-- Pass from absolute representability over `C` back to the slice base-change form. -/
opaque sliceTwoFibreProduct_isRepresentable_of_absolute
    [Limits.HasPullbacks C]
    {X Y : FibredInGroupoidsOver C}
    (F : X ⟶ Y) {W : C}
    (H : ofFunctor (Over.forget W) ⟶ Y) :
    (FibredInGroupoidsOver.twoFibreProduct H F).IsRepresentable →
    (FibredInGroupoidsMor.sliceTwoFibreProduct F H).IsRepresentable := by
  intro hRep
  apply (isRepresentable_iff_absolutize_isRepresentable _).mpr
  exact absolutize_sliceTwoFibreProduct_isRepresentable_of_twoFibreProduct F H hRep

/-- Slice representability from the lightweight absolute `tfpRep` predicate. -/
opaque sliceTwoFibreProduct_isRepresentable_of_tfpRep
    [Limits.HasPullbacks C]
    {X Y : FibredInGroupoidsOver C}
    (F : X ⟶ Y) {W : C}
    (H : ofFunctor (Over.forget W) ⟶ Y) :
    tfpRep H F → (FibredInGroupoidsMor.sliceTwoFibreProduct F H).IsRepresentable := by
  intro hRep
  exact sliceTwoFibreProduct_isRepresentable_of_absolute F H
    (tfpRep_to_isRepresentable H F hRep)

/-- Lightweight name for slice representability. -/
@[irreducible] noncomputable def sliceRep
    {X Y : FibredInGroupoidsOver C}
    (F : X ⟶ Y) {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) : Prop :=
  (FibredInGroupoidsMor.sliceTwoFibreProduct F H).IsRepresentable

/-- Unpack `sliceRep`. -/
opaque sliceRep_to_isRepresentable
    {X Y : FibredInGroupoidsOver C}
    (F : X ⟶ Y) {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) :
    sliceRep F H → (FibredInGroupoidsMor.sliceTwoFibreProduct F H).IsRepresentable := by
  intro hRep
  unfold sliceRep at hRep
  exact hRep

/-- Build `sliceRep` from `tfpRep`. -/
opaque sliceRep_of_tfpRep
    [Limits.HasPullbacks C]
    {X Y : FibredInGroupoidsOver C}
    (F : X ⟶ Y) {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) :
    tfpRep H F → sliceRep F H := by
  intro hRep
  unfold sliceRep
  exact sliceTwoFibreProduct_isRepresentable_of_tfpRep F H hRep

/-- Left projection component of a raw map into the canonical self product. -/
noncomputable opaque raw_diagonal_left_component
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    ofFunctor (Over.forget W) ⟶ X := by
  exact H ≫
    FibredInGroupoidsOver.twoFibreProductLeftProjection X.baseProjection X.baseProjection

/-- Right projection component of a raw map into the canonical self product. -/
noncomputable opaque raw_diagonal_right_component
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    ofFunctor (Over.forget W) ⟶ X := by
  exact H ≫
    FibredInGroupoidsOver.twoFibreProductRightProjection X.baseProjection X.baseProjection

/-- The square over `X -> C <- X` induced by a map into another such square. -/
noncomputable def targetMapSquare
    (X : FibredInGroupoidsOver C)
    (T : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    {A : FibredInGroupoidsOver C} (H : A ⟶ T.obj) :
    BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection where
  obj := A
  p := H ≫ T.p
  q := H ≫ T.q
  ψ := (α_ H T.p X.baseProjection) ≪≫
    whiskerLeftIso H T.ψ ≪≫ (α_ H T.q X.baseProjection).symm

/-- If two maps into a final square have the same two projections up to `2`-cells, then the apex
maps are isomorphic. -/
noncomputable opaque apexIso_of_projection_cells_final
    (X : FibredInGroupoidsOver C)
    (T : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    [Bicategory.IsFinal T]
    {A : FibredInGroupoidsOver C}
    (M H : A ⟶ T.obj)
    (left : M ≫ T.p ⟶ H ≫ T.p)
    (right : M ≫ T.q ⟶ H ≫ T.q) : M ≅ H := by
  let P := targetMapSquare X T H
  let uH : P ⟶ T :=
    { hom := H
      left := (λ_ (H ≫ T.p)).hom
      right := (λ_ (H ≫ T.q)).hom
      comm := by exact twoCell_to_identity_unique _ _ }
  let uM : P ⟶ T :=
    { hom := M
      left := left
      right := right
      comm := by exact twoCell_to_identity_unique _ _ }
  haveI : Bicategory.IsLocallyGroupoid (FibredInGroupoidsOver C) :=
    fibredInGroupoidsOver_isLocallyGroupoid (C := C)
  haveI : Bicategory.IsLocallyGroupoid
      (BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection) :=
    BicategoricalTwoCommutativeSquare.instIsLocallyGroupoid
  exact apexIsoOfSquareHomIso (isoOfFinal uM uH)

/-- Transport `tfpRep` across an owner-level isomorphism of the left leg. -/
opaque tfpRep_transport_left_iso
    {A B T : FibredInGroupoidsOver C}
    {M H : A ⟶ T} {G : B ⟶ T}
    (α : M ≅ H) :
    tfpRep M G → tfpRep H G := by
  intro hRep
  unfold tfpRep at hRep ⊢
  exact twoFibreProduct_representable_transport_iso α (Iso.refl G) hRep

/-- Named version of left-leg `tfpRep` transport, keeping all morphisms explicit. -/
opaque tfpRep_transport_left_iso_named
    {A B T : FibredInGroupoidsOver C}
    (M H : A ⟶ T) (G : B ⟶ T)
    (α : M ≅ H) :
    tfpRep M G → tfpRep H G := by
  exact tfpRep_transport_left_iso α

/-- Transport `tfpRep` across an isomorphism of the right leg after postcomposing the common target
with an equivalence. -/
opaque tfpRep_transport_right_postcompose_iso
    {A B T : FibredInGroupoidsOver C} {E : Type*} [Category E]
    {F : A ⟶ T} {G G' : B ⟶ T}
    (eT : T.S ≌ E)
    (β : FibredInGroupoidsMor.G G ⋙ eT.functor ≅
      FibredInGroupoidsMor.G G' ⋙ eT.functor) :
    tfpRep F G → tfpRep F G' := by
  intro hRep
  unfold tfpRep at hRep ⊢
  exact twoFibreProduct_representable_transport_postcompose_functor_iso eT (Iso.refl _) β hRep

/-- Transport raw representability across an isomorphism of the right leg after postcomposing the
common target with an equivalence. -/
opaque twoFibreProduct_transport_right_postcompose_iso_named
    {A B T : FibredInGroupoidsOver C} {E : Type*} [Category E]
    (H : A ⟶ T) (G G' : B ⟶ T)
    (eT : T.S ≌ E)
    (β : FibredInGroupoidsMor.G G ⋙ eT.functor ≅
      FibredInGroupoidsMor.G G' ⋙ eT.functor) :
    (FibredInGroupoidsOver.twoFibreProduct H G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct H G').IsRepresentable := by
  intro hRep
  exact twoFibreProduct_representable_transport_postcompose_functor_iso
    eT (Iso.refl _) β hRep

opaque diagonal_final_absTfpRep_of_params
    (X : FibredInGroupoidsOver C)
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsMor.twoFibreProductDiagonalTarget X.baseProjection)
    (Dg : X ⟶ FibredInGroupoidsMor.twoFibreProductDiagonalTarget X.baseProjection)
    (Hraw : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (Dgraw uDgraw : X ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (M : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (α : M ≅ Hraw)
    (β : FibredInGroupoidsMor.G uDgraw ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G Dgraw ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor)
    (hcanonDiag : (FibredInGroupoidsOver.twoFibreProduct M uDgraw).IsRepresentable) :
    @absTfpRep C _ (ofFunctor (Over.forget W)) X
      (FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) Hraw Dgraw := by
  have hM := tfpRep_of_isRepresentable M uDgraw hcanonDiag
  have hHtfp := tfpRep_transport_left_iso_named M Hraw uDgraw α hM
  have hH := tfpRep_to_isRepresentable Hraw uDgraw hHtfp
  have hraw : (FibredInGroupoidsOver.twoFibreProduct Hraw Dgraw).IsRepresentable :=
    twoFibreProduct_transport_right_postcompose_iso_named Hraw uDgraw Dgraw
      (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection) β hH
  unfold absTfpRep
  exact hraw

opaque tfpRep_transport_left_postcompose_alpha
    (X : FibredInGroupoidsOver C)
    {W : C}
    (M H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (G : X ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (α : FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G H ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor) :
    tfpRep M G → tfpRep H G := by
  intro hRep
  exact tfpRep_of_isRepresentable H G <|
    twoFibreProduct_representable_transport_postcompose_left
      (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection) α
      (tfpRep_to_isRepresentable M G hRep)

/-- Final left-leg representability transport in the diagonal argument, with the postcomposed
comparison supplied explicitly. -/
opaque diagonal_final_transport_with_alpha
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uH : productSliceSourceSquare X L R ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (α :
      FibredInGroupoidsMor.G
            (FibredInGroupoidsOver.overMap
                (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom) ⋙
          (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
        FibredInGroupoidsMor.G H ⋙
          (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor)
    (hcanonDiag :
      (FibredInGroupoidsOver.twoFibreProduct
        (FibredInGroupoidsOver.overMap
            (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom)
        uDg.hom).IsRepresentable) :
    (FibredInGroupoidsOver.twoFibreProduct H uDg.hom).IsRepresentable :=
  twoFibreProduct_representable_transport_postcompose_left
    (A := ofFunctor (Over.forget W)) (B := X)
    (T := FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (F := FibredInGroupoidsOver.overMap
      (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom)
    (F' := H) (G := uDg.hom)
    (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection) α hcanonDiag

/-- Transport the right leg from a local terminal diagonal map to the canonical diagonal morphism. -/
opaque diagonal_transport_right_to_formal
    (X : FibredInGroupoidsOver C)
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct H uDg.hom).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct H
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)).IsRepresentable := by
  intro hH
  let β : FibredInGroupoidsMor.G uDg.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G
          (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor :=
    diagonalSourceSquareComparisonIso X uDg ≪≫ (diagonalMorComparisonIso X).symm
  exact twoFibreProduct_transport_right_postcompose_iso_named H uDg.hom
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)
    (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection) β hH

/-- The Remark-4.35.8 comparison followed by the first categorical-pullback projection is the
underlying functor of the canonical left projection. -/
noncomputable opaque selfProductComparison_leftProjectionIso
    (X : FibredInGroupoidsOver C) :
    (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ⋙
        π₁ (FibredInGroupoidsMor.G X.baseProjection)
          (FibredInGroupoidsMor.G X.baseProjection) ≅
      FibredInGroupoidsMor.G
        (FibredInGroupoidsOver.twoFibreProductLeftProjection
          X.baseProjection X.baseProjection) := by
  rw [twoFibreProductEquivCatPullback]
  unfold FibredInGroupoidsOver.twoFibreProductLeftProjection
  unfold FibredInGroupoidsOver.twoFibreProduct
  unfold FibredInGroupoidsMor.G FibredInGroupoidsMor.toBasedFunctor
  unfold FibredCategoryMor.toBasedFunctor FibredCategoryOver.twoFibreProductLeftProjection
  exact Iso.refl _

/-- The Remark-4.35.8 comparison followed by the second categorical-pullback projection is the
underlying functor of the canonical right projection. -/
noncomputable opaque selfProductComparison_rightProjectionIso
    (X : FibredInGroupoidsOver C) :
    (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ⋙
        π₂ (FibredInGroupoidsMor.G X.baseProjection)
          (FibredInGroupoidsMor.G X.baseProjection) ≅
      FibredInGroupoidsMor.G
        (FibredInGroupoidsOver.twoFibreProductRightProjection
          X.baseProjection X.baseProjection) := by
  rw [twoFibreProductEquivCatPullback]
  unfold FibredInGroupoidsOver.twoFibreProductRightProjection
  unfold FibredInGroupoidsOver.twoFibreProduct
  unfold FibredInGroupoidsMor.G FibredInGroupoidsMor.toBasedFunctor
  unfold FibredCategoryMor.toBasedFunctor FibredCategoryOver.twoFibreProductRightProjection
  exact Iso.refl _

/-- Postcomposed first-projection form of `selfProductComparison_leftProjectionIso`. -/
noncomputable opaque selfProductComparison_postcompose_leftProjectionIso
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (M : A ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    (FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor) ⋙
        π₁ (FibredInGroupoidsMor.G X.baseProjection)
          (FibredInGroupoidsMor.G X.baseProjection) ≅
      FibredInGroupoidsMor.G
        (M ≫ FibredInGroupoidsOver.twoFibreProductLeftProjection
          X.baseProjection X.baseProjection) := by
  rw [twoFibreProductEquivCatPullback]
  unfold FibredInGroupoidsOver.twoFibreProductLeftProjection
  unfold FibredInGroupoidsOver.twoFibreProduct
  unfold FibredInGroupoidsMor.G FibredInGroupoidsMor.toBasedFunctor
  unfold FibredCategoryMor.toBasedFunctor FibredCategoryOver.twoFibreProductLeftProjection
  exact Iso.refl _

/-- Postcomposed second-projection form of `selfProductComparison_rightProjectionIso`. -/
noncomputable opaque selfProductComparison_postcompose_rightProjectionIso
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (M : A ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    (FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor) ⋙
        π₂ (FibredInGroupoidsMor.G X.baseProjection)
          (FibredInGroupoidsMor.G X.baseProjection) ≅
      FibredInGroupoidsMor.G
        (M ≫ FibredInGroupoidsOver.twoFibreProductRightProjection
          X.baseProjection X.baseProjection) := by
  rw [twoFibreProductEquivCatPullback]
  unfold FibredInGroupoidsOver.twoFibreProductRightProjection
  unfold FibredInGroupoidsOver.twoFibreProduct
  unfold FibredInGroupoidsMor.G FibredInGroupoidsMor.toBasedFunctor
  unfold FibredCategoryMor.toBasedFunctor FibredCategoryOver.twoFibreProductRightProjection
  exact Iso.refl _

end CategoryTheory
