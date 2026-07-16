import StacksProject_2024.stacks_project.Chap04.Lemma_4_31_6

open CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

noncomputable section

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

variable (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D)

/- Domain-style sampling for Lemma 4.31.8:
- primary domain: categorical `2`-fibre products of functors;
- canonical owner abstractions already used in this chapter/project:
  `CategoricalPullback`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `two_fibre_product_map`,
  `Functor.IsEquivalence`.

Source/core/bridge triage:
- `source-facing`: the reassociation isomorphism between the iterated `2`-fibre product models
  `((A ×_B C) ×_D E)` and `A ×_B (C ×_D E)`;
- `core/canonical`: `CategoricalPullback`, its universal-property functor
  `toFunctorToCategoricalPullback`, and the equivalence owner predicate
  `Functor.IsEquivalence`;
- `bridge/view`: this file packages the two source-facing reassociation squares into the induced
  equivalence of pullback categories. -/

local notation "LeftAssoc" =>
  ((π₂ F G) ⋙ H) ⊡ I

local notation "RightAssoc" =>
  F ⊡ ((π₁ H I) ⋙ G)

private abbrev leftAssocSndRightIso (I : E ⥤ D) :
    (𝟭 E) ⋙ I ≅ I ⋙ 𝟭 D :=
  Functor.leftUnitor I ≪≫ (Functor.rightUnitor I).symm

private abbrev leftAssocSndLeftIso (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) :
    (((π₂ F G) ⋙ H) ⋙ 𝟭 D) ≅ (π₂ F G) ⋙ H :=
  Functor.rightUnitor ((π₂ F G) ⋙ H)

private abbrev leftAssocSnd : LeftAssoc ⥤ H ⊡ I :=
  two_fibre_product_map (leftAssocSndRightIso I) (leftAssocSndLeftIso F G H)

@[simp] private theorem leftAssocSnd_obj_fst (X : LeftAssoc) :
    ((leftAssocSnd F G H I).obj X).fst = X.fst.snd :=
  rfl

@[simp] private theorem leftAssocSnd_obj_snd (X : LeftAssoc) :
    ((leftAssocSnd F G H I).obj X).snd = X.snd :=
  rfl

@[simp] private theorem leftAssocSnd_obj_iso_hom (X : LeftAssoc) :
    ((leftAssocSnd F G H I).obj X).iso.hom = X.iso.hom := by
  simpa [leftAssocSndRightIso, leftAssocSndLeftIso] using
    (two_fibre_product_map_obj_iso_hom
      (leftAssocSndRightIso I)
      (leftAssocSndLeftIso F G H)
      X)

@[simp] private theorem leftAssocSnd_map_fst {X Y : LeftAssoc} (f : X ⟶ Y) :
    ((leftAssocSnd F G H I).map f).fst = f.fst.snd :=
  rfl

@[simp] private theorem leftAssocSnd_map_snd {X Y : LeftAssoc} (f : X ⟶ Y) :
    ((leftAssocSnd F G H I).map f).snd = f.snd :=
  rfl

private abbrev rightAssocFstRightIso (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D) :
    (π₁ H I) ⋙ G ≅ ((π₁ H I) ⋙ G) ⋙ 𝟭 B :=
  (Functor.rightUnitor ((π₁ H I) ⋙ G)).symm

private abbrev rightAssocFstLeftIso (F : A ⥤ B) :
    F ⋙ 𝟭 B ≅ (𝟭 A) ⋙ F :=
  Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm

private abbrev rightAssocFst : RightAssoc ⥤ F ⊡ G :=
  two_fibre_product_map (rightAssocFstRightIso G H I) (rightAssocFstLeftIso F)

@[simp] private theorem rightAssocFst_obj_fst (X : RightAssoc) :
    ((rightAssocFst F G H I).obj X).fst = X.fst :=
  rfl

@[simp] private theorem rightAssocFst_obj_snd (X : RightAssoc) :
    ((rightAssocFst F G H I).obj X).snd = X.snd.fst :=
  rfl

@[simp] private theorem rightAssocFst_obj_iso_hom (X : RightAssoc) :
    ((rightAssocFst F G H I).obj X).iso.hom = X.iso.hom := by
  simpa [rightAssocFstRightIso, rightAssocFstLeftIso] using
    (two_fibre_product_map_obj_iso_hom
      (rightAssocFstRightIso G H I)
      (rightAssocFstLeftIso F)
      X)

@[simp] private theorem rightAssocFst_map_fst {X Y : RightAssoc} (f : X ⟶ Y) :
    ((rightAssocFst F G H I).map f).fst = f.fst :=
  rfl

@[simp] private theorem rightAssocFst_map_snd {X Y : RightAssoc} (f : X ⟶ Y) :
    ((rightAssocFst F G H I).map f).snd = f.snd.fst :=
  rfl

private def assocSquare : CatCommSqOver F ((π₁ H I) ⋙ G) LeftAssoc where
  fst := π₁ (((π₂ F G) ⋙ H)) I ⋙ π₁ F G
  snd := leftAssocSnd F G H I
  iso := NatIso.ofComponents
    (fun X ↦ by simpa using X.fst.iso)
    (fun {_ _} f ↦ by
      simpa [leftAssocSnd, two_fibre_product_map, leftAssocSndRightIso, leftAssocSndLeftIso] using
        f.fst.w)

private def assocInvSquare :
    CatCommSqOver (((π₂ F G) ⋙ H)) I RightAssoc where
  fst := rightAssocFst F G H I
  snd := π₂ F ((π₁ H I) ⋙ G) ⋙ π₂ H I
  iso := NatIso.ofComponents
    (fun X ↦ by simpa using X.snd.iso)
    (fun {_ _} f ↦ by
      simpa [rightAssocFst, two_fibre_product_map, rightAssocFstRightIso, rightAssocFstLeftIso]
        using f.snd.w)

private abbrev assocHom : LeftAssoc ⥤ RightAssoc :=
  (toFunctorToCategoricalPullback F ((π₁ H I) ⋙ G) LeftAssoc).obj
    (assocSquare F G H I)

private abbrev assocInv : RightAssoc ⥤ LeftAssoc :=
  (toFunctorToCategoricalPullback (((π₂ F G) ⋙ H)) I RightAssoc).obj
    (assocInvSquare F G H I)

@[simp] private theorem assocHom_obj_fst (X : LeftAssoc) :
    ((assocHom F G H I).obj X).fst = X.fst.fst :=
  rfl

@[simp] private theorem assocHom_obj_snd (X : LeftAssoc) :
    ((assocHom F G H I).obj X).snd = (leftAssocSnd F G H I).obj X :=
  rfl

@[simp] private theorem assocHom_obj_iso (X : LeftAssoc) :
    ((assocHom F G H I).obj X).iso = X.fst.iso := by
  ext
  simp [assocHom, assocSquare]

@[simp] private theorem assocInv_obj_fst (X : RightAssoc) :
    ((assocInv F G H I).obj X).fst = (rightAssocFst F G H I).obj X :=
  rfl

@[simp] private theorem assocInv_obj_snd (X : RightAssoc) :
    ((assocInv F G H I).obj X).snd = X.snd.snd :=
  rfl

@[simp] private theorem assocInv_obj_iso (X : RightAssoc) :
    ((assocInv F G H I).obj X).iso = X.snd.iso := by
  ext
  simp [assocInv, assocInvSquare]

private def assocUnitIso :
    𝟭 LeftAssoc ≅ assocHom F G H I ⋙ assocInv F G H I := by
  sorry

private def assocCounitIso :
    assocInv F G H I ⋙ assocHom F G H I ≅ 𝟭 RightAssoc := by
  sorry

private instance assocHom_isEquivalence :
    (assocHom F G H I).IsEquivalence :=
  Functor.IsEquivalence.mk'
    (assocInv F G H I)
    (assocUnitIso F G H I)
    (assocCounitIso F G H I)

/-- Lemma 4.31.8: the iterated `2`-fibre product categories
`(A ×_B C) ×_D E` and `A ×_B (C ×_D E)` are canonically equivalent. -/
def two_fibre_product_assoc :
    LeftAssoc ≌ RightAssoc :=
  (assocHom F G H I).asEquivalence

/-- The forward functor of `two_fibre_product_assoc` preserves the outer-left component. -/
-- Proof sketch: unfold `two_fibre_product_assoc` through `Functor.asEquivalence`; its forward
-- functor is the reassociation comparison functor `assocHom`, whose first projection is
-- definitionally `X.fst.fst`.
theorem two_fibre_product_assoc_functor_obj_fst
    (X : LeftAssoc) :
    ((two_fibre_product_assoc F G H I).functor.obj X).fst = X.fst.fst := sorry

/-- The inverse functor of `two_fibre_product_assoc` preserves the outer-right component. -/
-- Proof sketch: unfold `two_fibre_product_assoc` through `Functor.asEquivalence`; its inverse
-- functor is the comparison functor `assocInv`, whose second projection is definitionally
-- `X.snd.snd`.
theorem two_fibre_product_assoc_inverse_obj_snd
    (X : RightAssoc) :
    ((two_fibre_product_assoc F G H I).inverse.obj X).snd = X.snd.snd := sorry

end

end CategoryTheory
