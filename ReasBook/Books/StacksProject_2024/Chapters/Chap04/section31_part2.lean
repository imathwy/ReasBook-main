import Mathlib
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_31_7 (from Chap04) -/
open CategoryTheory.Limits
open CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

variable {H : X ⥤ Z} {I : Y ⥤ Z} {L : X ⥤ A} {K : Y ⥤ B}
variable {M : Z ⥤ C} {F : A ⥤ C} {G : B ⥤ C}
variable (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)

/- Domain-style sampling for Lemma 4.31.7:
- primary domain: categorical pullbacks of functors and the induced functor on pullback categories;
- sampled owner API:
  `CategoricalPullback.Hom`,
  `CategoricalPullback.hom_ext`,
  `Limits.CatCospanTransform`,
  `two_fibre_product_map`,
  `Functor.FullyFaithful.ofFullyFaithful`;
- best owner abstraction: the source-facing functor `two_fibre_product_map α β`, whose canonical
  derived API is expressed by the owner predicates `Functor.Faithful`, `Functor.Full`,
  `Functor.FullyFaithful`, and `Functor.IsEquivalence`;
- primitive-vs-derived split: the primitive source-facing data are the comparison isomorphisms
  `α` and `β` together with the functors `K`, `L`, and `M`; the public hypotheses should live in
  the owner predicates `Functor.Full`, `Functor.Faithful`, and `Functor.IsEquivalence`, while the
  non-`Prop` witness `Functor.FullyFaithful` is derived API recovered canonically by
  `Functor.FullyFaithful.ofFullyFaithful` when needed.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma about `two_fibre_product_map α β`;
- `core/canonical`: `Functor.Faithful`, `Functor.Full`, `Functor.FullyFaithful`, and
  `Functor.IsEquivalence` applied to `two_fibre_product_map α β`;
- `bridge/view`: this file specializes those owner predicates to the functor of Lemma 4.31.6. -/

-- Proof sketch: on morphisms, `two_fibre_product_map α β` is induced by the map between the
-- defining pullback hom-sets coming from `L.map` and `K.map`; if `K` and `L` are faithful, this
-- induced map is injective.
/-- Lemma 4.31.7 (1): under the assumptions of `Lemma 4.31.6`, if `K` and `L` are faithful, then
the induced functor `X ×[Z] Y ⥤ A ×[C] B` is faithful. -/
theorem two_fibre_product_map_faithful
    [K.Faithful] [L.Faithful] :
    (two_fibre_product_map α β).Faithful where
  map_injective {P Q} f g h := by
    apply hom_ext
    · exact L.map_injective (congrArg Hom.fst h)
    · exact K.map_injective (congrArg Hom.snd h)

private theorem two_fibre_product_map_preimage_w
    [K.Full] [L.Full] {P Q : H ⊡ I}
    (f : (two_fibre_product_map α β).obj P ⟶ (two_fibre_product_map α β).obj Q) :
    M.map (H.map (L.preimage f.fst)) ≫ M.map Q.iso.hom =
      M.map P.iso.hom ≫ M.map (I.map (K.preimage f.snd)) := by
  let lhs := M.map (H.map (L.preimage f.fst)) ≫ M.map Q.iso.hom
  let rhs := M.map P.iso.hom ≫ M.map (I.map (K.preimage f.snd))
  -- Move the target compatibility relation back across the comparison isomorphisms.
  have hβ :=
    (β.inv.naturality_assoc (L.preimage f.fst) (M.map Q.iso.hom ≫ α.inv.app Q.snd)).symm
  simp only [Functor.comp_map, L.map_preimage] at hβ
  have hα := α.inv.naturality_assoc (K.preimage f.snd) (𝟙 _)
  simp only [Functor.comp_map, K.map_preimage, Category.comp_id] at hα
  have hα' := congrArg (fun k ↦ β.inv.app P.fst ≫ M.map P.iso.hom ≫ k) hα
  have h₁ :
      β.inv.app P.fst ≫ lhs ≫ α.inv.app Q.snd =
        F.map f.fst ≫ β.inv.app Q.fst ≫ M.map Q.iso.hom ≫ α.inv.app Q.snd := by
    simpa [lhs, Category.assoc] using hβ
  have h₂ :
      F.map f.fst ≫ β.inv.app Q.fst ≫ M.map Q.iso.hom ≫ α.inv.app Q.snd =
        β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd ≫ G.map f.snd := by
    simpa [two_fibre_product_map_obj_iso_hom, Category.assoc] using f.w
  have h₃ :
      β.inv.app P.fst ≫ rhs ≫ α.inv.app Q.snd =
        β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd ≫ G.map f.snd := by
    simpa [rhs, Category.assoc] using hα'
  have h' : β.inv.app P.fst ≫ lhs ≫ α.inv.app Q.snd = β.inv.app P.fst ≫ rhs ≫ α.inv.app Q.snd :=
    h₁.trans (h₂.trans h₃.symm)
  have h'' : β.inv.app P.fst ≫ lhs = β.inv.app P.fst ≫ rhs := by
    exact
      (Iso.cancel_iso_hom_right _ _ (α.symm.app Q.snd)).1
        (by simpa [Category.assoc] using h')
  exact
    (Iso.cancel_iso_hom_left (β.symm.app P.fst) _ _).1
      (by simpa [lhs, rhs, Category.assoc] using h'')

private theorem two_fibre_product_map_full
    [K.Full] [L.Full] [M.Faithful] :
    (two_fibre_product_map α β).Full := by
  refine ⟨?_⟩
  intro P Q f
  have hw :
      H.map (L.preimage f.fst) ≫ Q.iso.hom =
        P.iso.hom ≫ I.map (K.preimage f.snd) := by
    apply M.map_injective
    simpa using two_fibre_product_map_preimage_w α β f
  refine ⟨⟨L.preimage f.fst, K.preimage f.snd, hw⟩, ?_⟩
  ext <;> simp [two_fibre_product_map]

attribute [local instance] two_fibre_product_map_faithful two_fibre_product_map_full

-- Proof sketch: the map on morphisms is the pullback of the hom-set maps induced by `L` and `K`;
-- full faithfulness of `K` and `L` gives surjectivity on the outer hom-sets, and faithfulness of
-- `M` ensures the chosen lifts satisfy the required compatibility over the middle hom-set.
/-- Lemma 4.31.7 (2): if `K` and `L` are full and faithful, and `M` is faithful, then the induced
functor `X ×[Z] Y ⥤ A ×[C] B` is fully faithful. -/
noncomputable abbrev two_fibre_product_map_fullyFaithful
    [K.Full] [K.Faithful] [L.Full] [L.Faithful] [M.Faithful] :
    (two_fibre_product_map α β).FullyFaithful :=
  .ofFullyFaithful (two_fibre_product_map α β)

-- Proof sketch: apply the canonical `map_bijective` field of the bundled fully faithful witness
-- for `two_fibre_product_map α β`.
/-- The fully faithful `2`-fibre product map induces bijections on all hom-sets. -/
theorem two_fibre_product_map_fullyFaithful_map_bijective
    [K.Full] [K.Faithful] [L.Full] [L.Faithful] [M.Faithful] (P Q : H ⊡ I) :
    Function.Bijective
      ((two_fibre_product_map α β).map :
        (P ⟶ Q) → ((two_fibre_product_map α β).obj P ⟶ (two_fibre_product_map α β).obj Q)) := by
  -- The bundled fully faithful witness already records bijectivity on every hom-set.
  simpa using (two_fibre_product_map_fullyFaithful α β).map_bijective P Q

private noncomputable def two_fibre_product_map_preimage
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] (P : F ⊡ G) :
    H ⊡ I where
  fst := L.objPreimage P.fst
  snd := K.objPreimage P.snd
  iso :=
    M.preimageIso <|
      β.app (L.objPreimage P.fst) ≪≫
        F.mapIso (L.objObjPreimageIso P.fst) ≪≫
        P.iso ≪≫
        G.mapIso (K.objObjPreimageIso P.snd).symm ≪≫
        α.app (K.objPreimage P.snd)

private theorem two_fibre_product_map_preimage_hom
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] (P : F ⊡ G) :
    F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom =
      ((two_fibre_product_map α β).obj (two_fibre_product_map_preimage α β P)).iso.hom ≫
        G.map (K.objObjPreimageIso P.snd).hom := by
  -- Expand the chosen `M`-preimage iso so the inserted comparison isomorphisms become visible.
  suffices hmain :
      F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom =
        β.inv.app (L.objPreimage P.fst) ≫
          β.hom.app (L.objPreimage P.fst) ≫
            F.map (L.objObjPreimageIso P.fst).hom ≫
              P.iso.hom ≫
                G.map (K.objObjPreimageIso P.snd).inv ≫
                  α.hom.app (K.objPreimage P.snd) ≫
                    α.inv.app (K.objPreimage P.snd) ≫
                      G.map (K.objObjPreimageIso P.snd).hom by
    simpa [two_fibre_product_map_preimage, two_fibre_product_map_obj_iso_hom, Category.assoc] using
      hmain
  let e := K.objObjPreimageIso P.snd
  let tail :=
    F.map (L.objObjPreimageIso P.fst).hom ≫
      P.iso.hom ≫ G.map e.inv ≫
        α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom
  have rhs_eq_tail :
      β.inv.app (L.objPreimage P.fst) ≫
          β.hom.app (L.objPreimage P.fst) ≫
            F.map (L.objObjPreimageIso P.fst).hom ≫
              P.iso.hom ≫
                G.map e.inv ≫
                  α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        tail := by
    simpa [tail, Category.assoc] using β.inv_hom_id_app_assoc (L.objPreimage P.fst) tail
  have hα₀ :
      α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        G.map e.hom := by
    simpa [Category.assoc] using α.hom_inv_id_app_assoc (K.objPreimage P.snd) (G.map e.hom)
  have hα₁ :
      G.map e.inv ≫ α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        G.map e.inv ≫ G.map e.hom := by
    simpa [Category.assoc] using congrArg (fun k ↦ G.map e.inv ≫ k) hα₀
  have tail_step :
      F.map (L.objObjPreimageIso P.fst).hom ≫
          P.iso.hom ≫ G.map e.inv ≫ α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom ≫ G.map e.inv ≫ G.map e.hom := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom ≫ k) hα₁
  have tail_eq : tail = F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom := by
    dsimp [tail]
    exact tail_step.trans (by rw [← G.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id])
  exact tail_eq.symm.trans rhs_eq_tail.symm

private theorem two_fibre_product_map_essSurj
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] :
    (two_fibre_product_map α β).EssSurj := by
  refine ⟨?_⟩
  intro P
  refine ⟨two_fibre_product_map_preimage α β P, ⟨?_⟩⟩
  refine CategoricalPullback.mkIso (L.objObjPreimageIso P.fst) (K.objObjPreimageIso P.snd) ?_
  simpa using two_fibre_product_map_preimage_hom α β P

-- Proof sketch: choose quasi-inverses to `K` and `L` from the equivalence hypotheses; the fully
-- faithfulness of `M` lets one lift the comparison isomorphism in `A ×[C] B` to one in `X ×[Z] Y`,
-- yielding essential surjectivity, while the previous parts provide the faithful and fully
-- faithful input needed to upgrade the functor to an equivalence.
/-- Lemma 4.31.7 (3): under the assumptions of `Lemma 4.31.6`, if `K` and `L` are equivalences and
`M` is full and faithful, then the induced functor `X ×[Z] Y ⥤ A ×[C] B` is an equivalence. -/
theorem two_fibre_product_map_isEquivalence
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] :
    (two_fibre_product_map α β).IsEquivalence := by
  let _ : (two_fibre_product_map α β).Faithful := two_fibre_product_map_faithful α β
  let _ : (two_fibre_product_map α β).Full := two_fibre_product_map_full α β
  let _ : (two_fibre_product_map α β).EssSurj := two_fibre_product_map_essSurj α β
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

end CategoryTheory

/-! ### Lemma_4_31_8 (from Chap04) -/
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
  -- The unit isomorphism is the identity on the three underlying components `A`, `C`, and `E`.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · -- First identify the inner pullback `(A ×_B C)` component objectwise.
    refine CategoricalPullback.mkIso ?_ (.refl _) ?_
    · refine CategoricalPullback.mkIso (.refl _) (.refl _) ?_
      -- The reassociation does not change the structural map on the inner pullback.
      have hfst₁ :
          ((assocHom F G H I ⋙ assocInv F G H I).obj X).fst.iso.hom =
            ((assocHom F G H I).obj X).iso.hom := by
        simpa [assocInv, assocInvSquare] using
          (rightAssocFst_obj_iso_hom (F := F) (G := G) (H := H) (I := I)
            ((assocHom F G H I).obj X))
      have hfst₂ :
          ((assocHom F G H I).obj X).iso.hom = X.fst.iso.hom := by
        simpa using congrArg Iso.hom (assocHom_obj_iso (F := F) (G := G) (H := H) (I := I) X)
      have hmain :
          ((assocHom F G H I ⋙ assocInv F G H I).obj X).fst.iso.hom = X.fst.iso.hom :=
        hfst₁.trans hfst₂
      rw [hmain]
      change F.map (𝟙 X.fst.fst) ≫ X.fst.iso.hom = X.fst.iso.hom ≫ G.map (𝟙 X.fst.snd)
      rw [Functor.map_id, Functor.map_id, Category.comp_id, Category.id_comp]
    · -- Then identify the outer pullback structural map on the `E` side.
      simpa [assocHom, assocInv, assocSquare, assocInvSquare] using
        (leftAssocSnd_obj_iso_hom (F := F) (G := G) (H := H) (I := I) X)
  · -- Naturality is componentwise because every displayed component is an identity isomorphism.
    intro X Y f
    apply CategoricalPullback.hom_ext
    · apply CategoricalPullback.hom_ext
      · simp [assocHom, assocInv, assocSquare, assocInvSquare, rightAssocFst, leftAssocSnd]
      · simp [assocHom, assocInv, assocSquare, assocInvSquare, rightAssocFst, leftAssocSnd]
    · simp [assocHom, assocInv, assocSquare, assocInvSquare, rightAssocFst, leftAssocSnd]

private def assocCounitIso :
    assocInv F G H I ⋙ assocHom F G H I ≅ 𝟭 RightAssoc := by
  -- The counit isomorphism is the same reassociation in the opposite direction.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · -- First identify the inner pullback `(C ×_D E)` component objectwise.
    refine CategoricalPullback.mkIso (.refl _) ?_ ?_
    · refine CategoricalPullback.mkIso (.refl _) (.refl _) ?_
      -- This is the symmetric form of the existing computation for `leftAssocSnd`.
      simpa [Iso.refl_hom, assocInv, assocHom, assocSquare, assocInvSquare] using
        (leftAssocSnd_obj_iso_hom (F := F) (G := G) (H := H) (I := I)
          ((assocInv F G H I).obj X)).symm
    · -- Then compare the outer structural map back to the original one on `A ×_B (C ×_D E)`.
      simpa [assocInv, assocHom, assocSquare, assocInvSquare] using
        (rightAssocFst_obj_iso_hom (F := F) (G := G) (H := H) (I := I) X).symm
  · -- Naturality is again componentwise because the reassociation leaves each entry unchanged.
    intro X Y f
    apply CategoricalPullback.hom_ext
    · simp [assocHom, assocInv, assocSquare, assocInvSquare, rightAssocFst, leftAssocSnd]
    · apply CategoricalPullback.hom_ext
      · simp [assocHom, assocInv, assocSquare, assocInvSquare, rightAssocFst, leftAssocSnd]
      · simp [assocHom, assocInv, assocSquare, assocInvSquare, rightAssocFst, leftAssocSnd]

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
  Equivalence.mk
    (assocHom F G H I)
    (assocInv F G H I)
    (assocUnitIso F G H I)
    (assocCounitIso F G H I)

/-- The forward functor of `two_fibre_product_assoc` preserves the outer-left component. -/
-- Proof sketch: unfold `two_fibre_product_assoc` through `Functor.asEquivalence`; its forward
-- functor is the reassociation comparison functor `assocHom`, whose first projection is
-- definitionally `X.fst.fst`.
theorem two_fibre_product_assoc_functor_obj_fst
    (X : LeftAssoc) :
    ((two_fibre_product_assoc F G H I).functor.obj X).fst = X.fst.fst := by
  -- The packaged equivalence uses `assocHom` as its forward functor.
  simpa [two_fibre_product_assoc] using assocHom_obj_fst (F := F) (G := G) (H := H) (I := I) X

/-- The inverse functor of `two_fibre_product_assoc` preserves the outer-right component. -/
-- Proof sketch: unfold `two_fibre_product_assoc` through `Functor.asEquivalence`; its inverse
-- functor is the comparison functor `assocInv`, whose second projection is definitionally
-- `X.snd.snd`.
theorem two_fibre_product_assoc_inverse_obj_snd
    (X : RightAssoc) :
    ((two_fibre_product_assoc F G H I).inverse.obj X).snd = X.snd.snd := by
  -- The packaged equivalence uses `assocInv` as its inverse functor.
  simpa [two_fibre_product_assoc] using
    (assocInv_obj_snd (F := F) (G := G) (H := H) (I := I) X)

end

end CategoryTheory

/-! ### Lemma_4_31_9 (from Chap04) -/
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]
variable {F : Type u₆} [Category.{v₆} F]

/-
Domain-style sampling for Lemma 4.31.9:
- primary domain: categorical pullbacks of functors and induced functors between pullback
  categories;
- sampled owner API:
  `CategoricalPullback`,
  `CatCommSq`,
  `CategoricalPullback.catCommSq`,
  `two_fibre_product_map`,
  `Functor.leftUnitor`;
- core/canonical owner abstraction: the chapter owner `two_fibre_product_map` from Lemma `4.31.6`
  is the induced functor on categorical pullbacks; this file only needs its source-facing
  specialization to the projection from an iterated pullback; the only extra derived datum is the
  nontrivial left comparison isomorphism, while the right comparison is the canonical unitor;
- primitive-vs-derived split: the primitive data are the pullback square `catCommSq AB CB` and the
  strict commutativity hypothesis `hcomm : CB ⋙ BF = CD ⋙ DF`; the projection functor `pr_{02}` is
  derived API.

Source/core/bridge triage:
- `source-facing`: the canonical projection
  `two_fibre_product_pr02 : (A ×[B] C) ×[D] E ⥤ A ×[F] E`;
- `core/canonical`: `CategoricalPullback`, `CategoricalPullback.catCommSq`, and the chapter owner
  `two_fibre_product_map`;
- `bridge/view`: the two comparison isomorphisms needed to specialize
  `two_fibre_product_map` to the cospan `A ⥤ B ⥤ F`, `C ⥤ B`, `C ⥤ D ⥤ F`, `E ⥤ D`. -/

section

variable (AB : A ⥤ B) (CB : C ⥤ B) (CD : C ⥤ D) (ED : E ⥤ D) (BF : B ⥤ F) (DF : D ⥤ F)
variable (hcomm : CB ⋙ BF = CD ⋙ DF)

local notation "LeftAssoc" => ((π₂ AB CB) ⋙ CD) ⊡ ED
local notation "OuterPullback" => (AB ⋙ BF) ⊡ (ED ⋙ DF)

/-- The comparison isomorphism sending the iterated pullback cospan
`π₂ AB CB ⋙ CD ⋙ DF` to the outer cospan `π₁ AB CB ⋙ AB ⋙ BF`. -/
private abbrev pr02BaseIso :
    π₂ AB CB ⋙ CD ⋙ DF ≅ π₁ AB CB ⋙ AB ⋙ BF :=
  Functor.associator (π₂ AB CB) CD DF ≪≫
    Functor.isoWhiskerLeft (π₂ AB CB) (eqToIso hcomm.symm) ≪≫
    (Functor.associator (π₂ AB CB) CB BF).symm ≪≫
    Functor.isoWhiskerRight (catCommSq AB CB).iso.symm BF ≪≫
    Functor.associator (π₁ AB CB) AB BF

/-- Lemma 4.31.9: a strictly commutative diagram
`A ⥤ B ⥤ F`, `C ⥤ B`, `C ⥤ D ⥤ F`, and `E ⥤ D` induces the canonical projection functor
`pr_{02} : (A ×[B] C) ×[D] E ⥤ A ×[F] E`. -/
abbrev two_fibre_product_pr02 :
    LeftAssoc ⥤ OuterPullback :=
  two_fibre_product_map (Functor.leftUnitor (ED ⋙ DF)) (pr02BaseIso AB CB CD BF DF hcomm)

/-- The projection functor `pr_{02}` is the pullback comparison functor specialized using the
canonical left unitor on `ED ⋙ DF` and the comparison isomorphism `pr02BaseIso`. -/
theorem two_fibre_product_pr02_def :
    two_fibre_product_pr02 AB CB CD ED BF DF hcomm =
      two_fibre_product_map (Functor.leftUnitor (ED ⋙ DF)) (pr02BaseIso AB CB CD BF DF hcomm) :=
  rfl

/-- The projection functor `pr_{02}` sends an object of the iterated pullback to its `A`-component. -/
@[simp] theorem two_fibre_product_pr02_obj_fst (P : LeftAssoc) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).obj P).fst = P.fst.fst :=
  rfl

/-- The projection functor `pr_{02}` sends an object of the iterated pullback to its `E`-component. -/
@[simp] theorem two_fibre_product_pr02_obj_snd (P : LeftAssoc) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).obj P).snd = P.snd :=
  rfl

/-- On the first component, `pr_{02}` maps morphisms by the `A`-part of the iterated pullback
morphism. -/
@[simp] theorem two_fibre_product_pr02_map_fst {P Q : LeftAssoc} (f : P ⟶ Q) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).map f).fst = f.fst.fst :=
  rfl

/-- On the second component, `pr_{02}` maps morphisms by the `E`-part of the iterated pullback
morphism. -/
@[simp] theorem two_fibre_product_pr02_map_snd {P Q : LeftAssoc} (f : P ⟶ Q) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).map f).snd = f.snd :=
  rfl

end

end CategoryTheory.Limits

/-! ### Lemma_4_31_10 (from Chap04) -/
namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

noncomputable section

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

variable (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

local notation "LeftAssoc" => (π₂ F G) ⊡ H
local notation "RightAssoc" => F ⊡ (H ⋙ G)

/- Domain-style sampling for Lemma 4.31.10:
- primary domain: categorical pullbacks of functors and canonical comparison functors between
  pullback models;
- sampled owner abstractions:
  `CategoricalPullback`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `two_fibre_product_map`,
  `two_fibre_product_map_isEquivalence`;
- best owner abstraction: the source-facing main entry is the reassociation equivalence itself,
  assembled from the chapter's canonical pullback comparison equivalences;
- primitive data: the identity-square object of `CatCommSqOver (𝟭 C) H D`;
- derived API: the induced section
  `D ⥤ (𝟭 C) ⊡ H`, the projection equivalence
  `π₂ (𝟭 C) H : (𝟭 C) ⊡ H ⥤ D`, and the right-leg comparison functor built by
  `two_fibre_product_map`;
  that equivalence is upgraded by `two_fibre_product_map_isEquivalence`.

Source/core/bridge triage:
- `source-facing`: the canonical equivalence `((π₂ F G) ⊡ H) ≌ (F ⊡ (H ⋙ G))`;
- `core/canonical`: the specialized reassociation equivalence for
  `((A ×_B C) ×_C D) ≌ A ×_B ((𝟭 C) ×_C D)` together with the chapter owner
  `two_fibre_product_map`;
- `bridge/view`: the canonical identity square in `CatCommSqOver (𝟭 C) H D`, the induced section
  `D ⥤ (𝟭 C) ⊡ H`, and the induced right-leg transport functor on pullbacks. -/

local notation "IdPullback" => (𝟭 C) ⊡ H
local notation "TransportSource" => F ⊡ ((π₁ (𝟭 C) H) ⋙ G)

/-- The identity square over `(𝟭 C, H)` with cone point `D`. -/
private abbrev identityPullbackSquare : CatCommSqOver (𝟭 C) H D where
  fst := H
  snd := 𝟭 D
  iso := Functor.rightUnitor H ≪≫ (Functor.leftUnitor H).symm

/-- The canonical section of the identity pullback `(𝟭 C) ⊡ H`. -/
private abbrev identityPullbackSection : D ⥤ IdPullback :=
  (toFunctorToCategoricalPullback (𝟭 C) H D).obj (identityPullbackSquare H)

/-- Helper for Lemma 4.31.10: the right component of the specialized reassociation
`((A ×_B C) ×_C D) ⥤ A ×_B ((𝟭 C) ×_C D)`. -/
private abbrev assocToTransportSnd : LeftAssoc ⥤ IdPullback :=
  two_fibre_product_map
    (Functor.leftUnitor H ≪≫ (Functor.rightUnitor H).symm)
    (Iso.refl ((π₂ F G) ⋙ 𝟭 C))

/-- Helper for Lemma 4.31.10: the square inducing the forward reassociation to
`A ×_B ((𝟭 C) ×_C D)`. -/
private def assocToTransportSquare : CatCommSqOver F ((π₁ (𝟭 C) H) ⋙ G) LeftAssoc where
  fst := π₁ (π₂ F G) H ⋙ π₁ F G
  snd := assocToTransportSnd F G H
  iso := NatIso.ofComponents
    (fun X ↦ by
      -- The forward reassociation keeps the `A ×_B C` comparison unchanged.
      simpa using X.fst.iso)
    (fun {_ _} f ↦ by
      -- Naturality is exactly the compatibility relation of the inner pullback morphism.
      simpa [assocToTransportSnd] using f.fst.w)

/-- Helper for Lemma 4.31.10: the specialized reassociation
`((A ×_B C) ×_C D) ⥤ A ×_B ((𝟭 C) ×_C D)`. -/
private def assocToTransport : LeftAssoc ⥤ TransportSource :=
  (toFunctorToCategoricalPullback F ((π₁ (𝟭 C) H) ⋙ G) LeftAssoc).obj
    (assocToTransportSquare F G H)

/-- Helper for Lemma 4.31.10: the `A ×_B C` component of the inverse reassociation
`A ×_B ((𝟭 C) ×_C D) ⥤ ((A ×_B C) ×_C D)`. -/
private abbrev assocToTransportFst : TransportSource ⥤ F ⊡ G :=
  two_fibre_product_map
    ((Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm)
    (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)

/-- Helper for Lemma 4.31.10: the square inducing the inverse reassociation back to
`((A ×_B C) ×_C D)`. -/
private def assocToTransportInvSquare : CatCommSqOver (π₂ F G) H TransportSource where
  fst := assocToTransportFst F G H
  snd := π₂ F ((π₁ (𝟭 C) H) ⋙ G) ⋙ π₂ (𝟭 C) H
  iso := NatIso.ofComponents
    (fun X ↦ by
      -- The inverse reassociation keeps the `((𝟭 C) ×_C D)` comparison unchanged.
      simpa using X.snd.iso)
    (fun {_ _} f ↦ by
      -- Naturality is exactly the compatibility relation of the right pullback morphism.
      simpa [assocToTransportFst] using f.snd.w)

/-- Helper for Lemma 4.31.10: the explicit inverse of the specialized reassociation. -/
private abbrev assocToTransportInv : TransportSource ⥤ LeftAssoc :=
  (toFunctorToCategoricalPullback (π₂ F G) H TransportSource).obj
    (assocToTransportInvSquare F G H)

/-- Helper for Lemma 4.31.10: the forward and inverse reassociations compose to the identity on
`((A ×_B C) ×_C D)`. -/
private def assocToTransportUnitIso :
    𝟭 LeftAssoc ≅ assocToTransport F G H ⋙ assocToTransportInv F G H :=
  -- The unit is built projectionwise: identity on the outer `D`-component and identity on the two
  -- components of the inner `A ×_B C` pullback.
  CategoricalPullback.mkNatIso
    (CategoricalPullback.mkNatIso
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportFst, Functor.comp_map]))
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportFst, Functor.comp_map]))
      (by
        ext X
        -- The recomposed inner pullback keeps the original structural map.
        have hfst₁ :
            ((assocToTransport F G H ⋙ assocToTransportInv F G H).obj X).fst.iso.hom =
              ((assocToTransport F G H).obj X).iso.hom := by
          simpa [assocToTransportInv, assocToTransportInvSquare, assocToTransportFst] using
            (two_fibre_product_map_obj_iso_hom
              ((Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm)
              (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
              ((assocToTransport F G H).obj X))
        have hfst₂ :
            ((assocToTransport F G H).obj X).iso.hom = X.fst.iso.hom := by
          rfl
        have hmain :
            ((assocToTransport F G H ⋙ assocToTransportInv F G H).obj X).fst.iso.hom =
              X.fst.iso.hom :=
          hfst₁.trans hfst₂
        simpa [assocToTransport, assocToTransportInv, assocToTransportSquare, assocToTransportInvSquare,
          assocToTransportFst, Category.assoc] using hmain))
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
        assocToTransportInvSquare, Functor.comp_map]))
    (by
      ext X
      -- The outer structural map is the same one already stored in the original object.
      simpa [assocToTransport, assocToTransportInv, assocToTransportSquare, assocToTransportInvSquare,
        assocToTransportSnd] using
        (two_fibre_product_map_obj_iso_hom
          (Functor.leftUnitor H ≪≫ (Functor.rightUnitor H).symm)
          (Iso.refl ((π₂ F G) ⋙ 𝟭 C))
          X))

/-- Helper for Lemma 4.31.10: the inverse and forward reassociations compose to the identity on
`A ×_B ((𝟭 C) ×_C D)`. -/
private def assocToTransportCounitIso :
    assocToTransportInv F G H ⋙ assocToTransport F G H ≅ 𝟭 TransportSource :=
  -- The counit is built projectionwise: identity on the outer `A`-component and identity on the
  -- two components of the inner identity pullback.
  CategoricalPullback.mkNatIso
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
        assocToTransportInvSquare, assocToTransportFst, Functor.comp_map]))
    (CategoricalPullback.mkNatIso
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportSnd, Functor.comp_map]))
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportSnd, Functor.comp_map]))
      (by
        ext X
        -- The recomposed identity pullback keeps the original structural map.
        have hsnd₁ :
            ((assocToTransportSnd F G H).obj ((assocToTransportInv F G H).obj X)).iso.hom =
              ((assocToTransportInv F G H).obj X).iso.hom := by
          simpa [assocToTransportSnd] using
            (two_fibre_product_map_obj_iso_hom
              (Functor.leftUnitor H ≪≫ (Functor.rightUnitor H).symm)
              (Iso.refl ((π₂ F G) ⋙ 𝟭 C))
              ((assocToTransportInv F G H).obj X))
        have hsnd₂ :
            ((assocToTransportInv F G H).obj X).iso.hom = X.snd.iso.hom := by
          rfl
        have hmain :
            ((assocToTransportSnd F G H).obj ((assocToTransportInv F G H).obj X)).iso.hom =
              X.snd.iso.hom :=
          hsnd₁.trans hsnd₂
        simpa [assocToTransport, assocToTransportInv, assocToTransportSquare, assocToTransportInvSquare,
          assocToTransportSnd] using hmain.symm))
    (by
      ext X
      -- The outer structural map is the same one already stored in the original object.
      simpa [assocToTransportInv, assocToTransport, assocToTransportInvSquare, assocToTransportSquare,
        assocToTransportFst] using
        (two_fibre_product_map_obj_iso_hom
          ((Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm)
          (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
          X).symm)

/-- Helper for Lemma 4.31.10: the specialized reassociation is an equivalence. -/
private theorem assocToTransport_isEquivalence :
    (assocToTransport F G H).IsEquivalence := by
  -- The specialized reassociation is explicitly inverted by rebracketing in the opposite direction.
  exact
    Functor.IsEquivalence.mk'
      (assocToTransportInv F G H)
      (assocToTransportUnitIso F G H)
      (assocToTransportCounitIso F G H)

/-- Helper for Lemma 4.31.10: the forward reassociation preserves the outer-left component. -/
private theorem assocToTransport_functor_obj_fst (X : LeftAssoc) :
    ((assocToTransport F G H).obj X).fst = X.fst.fst := by
  -- The forward reassociation reads off the same `A`-component from the inner pullback.
  rfl

/-- Helper for Lemma 4.31.10: the canonical section of the identity pullback retracts the second
projection. -/
private def identityPullbackSectionProj₂Iso :
    identityPullbackSection H ⋙ π₂ (𝟭 C) H ≅ 𝟭 D := by
  -- The section was defined with second leg `𝟭 D`, so the composite is objectwise the identity.
  refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
  intro X Y f
  simp [identityPullbackSection]

/-- Helper for Lemma 4.31.10: every object of the identity pullback is canonically recovered from
its second component via the explicit section. -/
private def identityPullbackProj₂UnitIso :
    𝟭 IdPullback ≅ π₂ (𝟭 C) H ⋙ identityPullbackSection H := by
  -- Route correction: the unit is most stable objectwise.  Each pullback object is rebuilt from
  -- its second component using its structural isomorphism as the first comparison.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine CategoricalPullback.mkIso X.iso (.refl _) ?_
    simp [identityPullbackSection, identityPullbackSquare]
  · intro X Y f
    -- Naturality is exactly the compatibility relation already stored in `f.w`.
    ext
    · simpa [identityPullbackSection] using f.w
    · simp [identityPullbackSection]

/-- The second projection from the identity pullback `(𝟭 C) ⊡ H` is an equivalence, with inverse
given by the canonical section. -/
private theorem identityPullbackProj₂_isEquivalence :
    (π₂ (𝟭 C) H).IsEquivalence := by
  -- The section supplies a quasi-inverse, and the previous two isomorphisms are the unit/counit.
  exact
    Functor.IsEquivalence.mk'
      (identityPullbackSection H)
      (identityPullbackProj₂UnitIso H)
      (identityPullbackSectionProj₂Iso H)

/-- Helper for Lemma 4.31.10: the canonical right-leg comparison induced by the equivalence
`(𝟭 C) ⊡ H ≌ D`. -/
private def rightLegTransportIso :
    (π₂ (𝟭 C) H) ⋙ (H ⋙ G) ≅ ((π₁ (𝟭 C) H) ⋙ G) ⋙ 𝟭 B :=
  Functor.associator (π₂ (𝟭 C) H) H G ≪≫
    Functor.isoWhiskerRight (catCommSq (𝟭 C) H).iso.symm G ≪≫
    Functor.associator (π₁ (𝟭 C) H) (𝟭 C) G ≪≫
    Functor.isoWhiskerLeft (π₁ (𝟭 C) H) (Functor.leftUnitor G) ≪≫
    (Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm

/-- Helper for Lemma 4.31.10: the right-leg transport from
`A ×_B ((𝟭 C) ×_C D)` to `A ×_B D` is an equivalence because `π₂ : (𝟭 C) ×_C D ⥤ D`
is one. -/
private theorem rightLegTransport_isEquivalence :
    (two_fibre_product_map
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)).IsEquivalence := by
  let _ : (π₂ (𝟭 C) H).IsEquivalence :=
    identityPullbackProj₂_isEquivalence H
  simpa [rightLegTransportIso] using
    (two_fibre_product_map_isEquivalence
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm))

/-- Lemma 4.31.10: for a diagram `A ⥤ B ← C ← D`, the textbook's canonical isomorphism
`(A ×_B C) ×_C D ≅ A ×_B D` is formalized by the canonical equivalence of categories
`((π₂ F G) ⊡ H) ≌ (F ⊡ (H ⋙ G))`. -/
def categorical_pullback_assoc : LeftAssoc ≌ RightAssoc :=
  let _ : (assocToTransport F G H).IsEquivalence :=
    assocToTransport_isEquivalence F G H
  let transport : TransportSource ⥤ RightAssoc :=
    two_fibre_product_map
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
  let _ : transport.IsEquivalence :=
    rightLegTransport_isEquivalence F G H
  (assocToTransport F G H).asEquivalence.trans transport.asEquivalence

/-- The forward functor of `categorical_pullback_assoc` preserves the outer-left component. -/
-- Proof sketch: unfold `categorical_pullback_assoc` as the composite of the specialized
-- reassociation `((A ×_B C) ×_C D) ⥤ A ×_B ((𝟭 C) ×_C D)` with the transport equivalence induced
-- by `two_fibre_product_map`; the transport functor acts only on the right leg, so the first
-- component remains `X.fst.fst`.
theorem categorical_pullback_assoc_functor_obj_fst
    (X : LeftAssoc) :
    ((categorical_pullback_assoc F G H).functor.obj X).fst = X.fst.fst := by
  -- Unfold the textbook equivalence into specialized reassociation followed by right-leg transport.
  let _ : (assocToTransport F G H).IsEquivalence :=
    assocToTransport_isEquivalence F G H
  let transport : TransportSource ⥤ RightAssoc :=
    two_fibre_product_map
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
  let _ : transport.IsEquivalence :=
    rightLegTransport_isEquivalence F G H
  -- The transport step changes only the right leg, so the first component comes from reassociation.
  change (transport.obj ((assocToTransport F G H).obj X)).fst = X.fst.fst
  rw [two_fibre_product_map_obj_fst]
  simpa using assocToTransport_functor_obj_fst (F := F) (G := G) (H := H) X

end

end CategoryTheory.Limits
