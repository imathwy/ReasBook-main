import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap13.Situation_13_14_1
import stacks_proof.stacks_project.Chap13.Lemma_13_5_7
import stacks_proof.stacks_project.Chap13.Lemma_13_5_8
import stacks_proof.stacks_project.Chap13.Lemma_13_14_3
import stacks_proof.stacks_project.Chap13.Lemma_13_14_4
import stacks_proof.stacks_project.Chap13.Lemma_13_14_6
import stacks_proof.stacks_project.Chap13.Lemma_13_14_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open scoped ZeroObject

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- 
Domain-style sampling:
- primary domain: pointwise right-derived functors on a localization, restricted to the full
  subcategory where the pointwise construction is defined, together with its left-derived dual;
- relevant owner declarations reused here:
  `ObjectProperty.FullSubcategory`,
  `fullSubcategoryLocalizationSystem`,
  `fullSubcategoryLocalizationFunctor`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`,
  `rightDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `leftDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `rightDerivedValueMap`,
  `leftDerivedValueMap`.

Source/core/bridge triage:
- `source-facing`: the full subcategory `𝓔` and the restricted multiplicative system `S_𝓔`;
- `core/canonical`: the upstream object-property owners `rightDerivedDefinedObjectProperty` and
  `leftDerivedDefinedObjectProperty` from `Lemma_13_14_5`, the transport owners
  `Functor.hasPointwise...DerivedFunctorAt_iff_of_mem`, the Karoubian retract-stability owners
  from `Lemma_13_14_7`, together with the chapter owner `fullSubcategoryLocalizationSystem`;
- `bridge/view`: the restricted functors and localizations obtained from `𝓔` and `S_𝓔`.

Primitive data are the object property saying where the pointwise right-derived functor is
defined, and its left-derived analogue. The subcategories and restricted localization systems are
derived owners built from those primitive predicates and reused throughout the proposition.
-/

section Basic

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- The full subcategory `𝓔 ⊆ D` consisting of objects at which the pointwise right derived
functor of `F` with respect to `S` is defined. -/
abbrev rightDerivedDefinedSubcategory (F : D ⥤ D') (S : MorphismProperty D) :=
  (rightDerivedDefinedObjectProperty F S).FullSubcategory

/-- The restricted multiplicative system `S_𝓔` on the full subcategory `𝓔`. -/
abbrev rightDerivedDefinedLocalizationSystem (F : D ⥤ D') (S : MorphismProperty D) :
    MorphismProperty (rightDerivedDefinedSubcategory F S) :=
  fullSubcategoryLocalizationSystem (rightDerivedDefinedObjectProperty F S) S

notation "𝓔[" F ", " S "]" => rightDerivedDefinedSubcategory F S
notation "S_𝓔[" F ", " S "]" => rightDerivedDefinedLocalizationSystem F S

/- Proposition 13.14.8 companion recall: for a denominator `s : X ⟶ Y` in `S`, the source and
target belong to `𝓔[F, S]` simultaneously. This is exactly the source-facing clause that any
`s ∈ S` whose source or target lies in `𝓔` is already a morphism of `𝓔`. -/
recall Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem

/-- An object of the full subcategory `𝓔` canonically carries the hypothesis that `RF` is
pointwise defined there. -/
instance rightDerivedDefinedSubcategory_hasPointwiseRightDerivedFunctorAt
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔[F, S]) :
    F.HasPointwiseRightDerivedFunctorAt S X.obj :=
  X.property

/-- Helper for Proposition 13.14.8: the right-derived-defined object property is invariant along
ambient denominators. -/
theorem rightDerivedDefinedObjectProperty_iff_of_mem
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D} (s : X ⟶ Y) (hs : S s) :
    rightDerivedDefinedObjectProperty F S X ↔
      rightDerivedDefinedObjectProperty F S Y := by
  simpa [rightDerivedDefinedObjectProperty] using
    (Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem
      (F := F) (W := S) (w := s) (hw := hs))

/-- Helper for Proposition 13.14.8: reindexing the right-derived denominator category along the
localized identity fixes each indexing object. -/
theorem right_derived_identity_reindex_obj
    (S : MorphismProperty D) {X : D}
    (g : CostructuredArrow S.Q (S.Q.obj X)) :
    (CostructuredArrow.map (S.Q.map (𝟙 X))).obj g = g := by
  simpa using
    (CostructuredArrow.map_id (S := S.Q) (T := S.Q.obj X) (f := g))

/-- Helper for Proposition 13.14.8: reindexing the left-derived denominator category along the
localized identity fixes each indexing object. -/
theorem left_derived_identity_reindex_obj
    (S : MorphismProperty D) {X : D}
    (g : StructuredArrow (S.Q.obj X) S.Q) :
    (StructuredArrow.map (S.Q.map (𝟙 X))).obj g = g := by
  simpa using
    (StructuredArrow.map_id (S := S.Q.obj X) (T := S.Q) (f := g))

/-- Helper for Proposition 13.14.8: evaluating `rightDerivedValueMap` on a fixed denominator leg
recovers the reindexed leg on the target comma category. -/
theorem rightDerivedValueMap_leg_on_index_object
    (F : D ⥤ D') (S : MorphismProperty D)
    {X Y : D} [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    [HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)]
    [HasColimit (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)]
    (f : X ⟶ Y)
    (g : CostructuredArrow S.Q (S.Q.obj X)) :
    colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) g ≫ rightDerivedValueMap S F f =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
        ((CostructuredArrow.map (S.Q.map f)).obj g) := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let RY := CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F
  let _ : HasColimit RX := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let _ : HasColimit RY := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Y
  let c : Cocone RX :=
    Cocone.mk (rightDerivedValue S F Y)
      { app := fun g ↦ colimit.ι RY ((CostructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa [RX, RY] using
            colimit.w RY ((CostructuredArrow.map (S.Q.map f)).map φ) }
  -- Proof comment: this is the defining `colimit.desc` formula for `rightDerivedValueMap`,
  -- evaluated at the chosen denominator object `g`.
  simpa [RX, RY, c, rightDerivedValueMap] using
    colimit.ι_desc (F := RX) c g

/-- Helper for Proposition 13.14.8: evaluating `leftDerivedValueMap` on a fixed denominator
projection recovers the reindexed projection on the source comma category. -/
theorem leftDerivedValueMap_projection_on_index_object
    (F : D ⥤ D') (S : MorphismProperty D)
    {X Y : D} [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [HasLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)]
    [HasLimit (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F)]
    (f : X ⟶ Y)
    (g : StructuredArrow (S.Q.obj Y) S.Q) :
    leftDerivedValueMap S F f ≫
        limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F) g =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
        ((StructuredArrow.map (S.Q.map f)).obj g) := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  let _ : HasLimit LX := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let _ : HasLimit LY := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y
  let c : Cone LY :=
    Cone.mk (leftDerivedValue S F X)
      { app := fun g ↦ limit.π LX ((StructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa [LX, LY] using
            (limit.w LX ((StructuredArrow.map (S.Q.map f)).map φ)).symm }
  -- Proof comment: this is the dual `limit.lift` computation for `leftDerivedValueMap`,
  -- evaluated on the chosen denominator projection `g`.
  simpa [LX, LY, c, leftDerivedValueMap] using
    limit.lift_π (F := LY) c g

/-- Helper for Proposition 13.14.8: the restricted right-derived functor sends identity morphisms
to identity morphisms. -/
theorem rightDerivedDefinedFunctor_map_id
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔[F, S]) :
    rightDerivedValueMap S F (𝟙 X.obj) = 𝟙 (rightDerivedValue S F X.obj) := by
  let _ : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) :=
    Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X.obj
  -- Proof comment: compare the two maps on every denominator leg of `RF(X)` and use the
  -- identity reindexing formula in the costructured-arrow category.
  apply colimit.hom_ext
  intro g
  have hg :
      (CostructuredArrow.map (S.Q.map (𝟙 X.obj))).obj g = g := by
    simpa using right_derived_identity_reindex_obj (S := S) (g := g)
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F
  have h0 :
      colimit.ι RX g ≫
          rightDerivedValueMap S F (𝟙 X.obj) =
        colimit.ι RX
          ((CostructuredArrow.map (S.Q.map (𝟙 X.obj))).obj g) := by
    simpa using
      rightDerivedValueMap_leg_on_index_object
        (F := F) (S := S) (f := 𝟙 X.obj) (g := g)
  have h1 :
      colimit.ι RX ((CostructuredArrow.map (S.Q.map (𝟙 X.obj))).obj g) =
        colimit.ι RX g := by
    simpa [RX] using (colimit.w RX (eqToHom hg)).symm
  calc
    colimit.ι RX g ≫ rightDerivedValueMap S F (𝟙 X.obj) =
      colimit.ι RX g := h0.trans h1
    _ = colimit.ι RX g ≫
          𝟙 (rightDerivedValue S F X.obj) := by
      rw [Category.comp_id]

/-- Helper for Proposition 13.14.8: the restricted right-derived functor respects composition. -/
theorem rightDerivedDefinedFunctor_map_comp
    (F : D ⥤ D') (S : MorphismProperty D)
    {X Y Z : 𝓔[F, S]} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightDerivedValueMap S F ((f ≫ g).hom) =
      rightDerivedValueMap S F f.hom ≫ rightDerivedValueMap S F g.hom := by
  let _ : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) :=
    Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X.obj
  let _ : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj Y.obj) ⋙ F) :=
    Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Y.obj
  let _ : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj Z.obj) ⋙ F) :=
    Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Z.obj
  -- Proof comment: compare both morphisms on each denominator leg of `RF(X)` and collapse the
  -- nested reindexing objects by evaluating first along `f` and then along `g`.
  apply colimit.hom_ext
  intro h
  have hf :
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) h ≫
          rightDerivedValueMap S F f.hom =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y.obj) ⋙ F)
          ((CostructuredArrow.map (S.Q.map f.hom)).obj h) := by
    simpa using
      rightDerivedValueMap_leg_on_index_object
        (F := F) (S := S) (f := f.hom) (g := h)
  have hg :
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y.obj) ⋙ F)
          ((CostructuredArrow.map (S.Q.map f.hom)).obj h) ≫
            rightDerivedValueMap S F g.hom =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Z.obj) ⋙ F)
          ((CostructuredArrow.map (S.Q.map g.hom)).obj
            ((CostructuredArrow.map (S.Q.map f.hom)).obj h)) := by
    simpa using
      rightDerivedValueMap_leg_on_index_object
        (F := F) (S := S) (f := g.hom)
        (g := (CostructuredArrow.map (S.Q.map f.hom)).obj h)
  have hcomp :
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) h ≫
          rightDerivedValueMap S F ((f ≫ g).hom) =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Z.obj) ⋙ F)
          ((CostructuredArrow.map (S.Q.map g.hom)).obj
            ((CostructuredArrow.map (S.Q.map f.hom)).obj h)) := by
    let RZ := CostructuredArrow.proj S.Q (S.Q.obj Z.obj) ⋙ F
    have h0 :
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) h ≫
            rightDerivedValueMap S F ((f ≫ g).hom) =
          colimit.ι RZ ((CostructuredArrow.map (S.Q.map ((f ≫ g).hom))).obj h) := by
      simpa [RZ] using
        rightDerivedValueMap_leg_on_index_object
          (F := F) (S := S) (f := (f ≫ g).hom) (g := h)
    have hobj :
        (CostructuredArrow.map (S.Q.map ((f ≫ g).hom))).obj h =
          (CostructuredArrow.map (S.Q.map g.hom)).obj
            ((CostructuredArrow.map (S.Q.map f.hom)).obj h) := by
      simpa [Functor.map_comp] using
        (CostructuredArrow.map_comp
          (S := S.Q) (f := S.Q.map f.hom) (f' := S.Q.map g.hom) (h := h))
    have htransport :
        colimit.ι RZ ((CostructuredArrow.map (S.Q.map ((f ≫ g).hom))).obj h) =
          colimit.ι RZ
            ((CostructuredArrow.map (S.Q.map g.hom)).obj
              ((CostructuredArrow.map (S.Q.map f.hom)).obj h)) := by
      simpa [RZ] using (colimit.w RZ (eqToHom hobj)).symm
    exact h0.trans htransport
  have hmid :
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y.obj) ⋙ F)
          ((CostructuredArrow.map (S.Q.map f.hom)).obj h) ≫
            rightDerivedValueMap S F g.hom =
        (colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) h ≫
          rightDerivedValueMap S F f.hom) ≫ rightDerivedValueMap S F g.hom := by
    rw [hf]
    rfl
  have hright :
      (colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) h ≫
          rightDerivedValueMap S F f.hom) ≫ rightDerivedValueMap S F g.hom =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F) h ≫
          rightDerivedValueMap S F f.hom ≫ rightDerivedValueMap S F g.hom := by
    simp [Category.assoc]
  exact hcomp.trans (hg.symm.trans (hmid.trans hright))

/-- The functor `RF : 𝓔 ⥤ D'` obtained by restricting the pointwise right derived construction to
the full subcategory where it is defined. -/
noncomputable def rightDerivedDefinedFunctor (F : D ⥤ D') (S : MorphismProperty D) :
    𝓔[F, S] ⥤ D' where
  obj X :=
    rightDerivedValue S F X.obj
  map f :=
    rightDerivedValueMap S F f.hom
  map_id X :=
    rightDerivedDefinedFunctor_map_id (F := F) (S := S) X
  map_comp f g :=
    rightDerivedDefinedFunctor_map_comp (F := F) (S := S) f g

-- Proof sketch: if a morphism of `S_𝓔` lies over an ambient arrow `s ∈ S`, then the two objects
-- of `𝓔` remain in the right-derived domain and Lemma `13.14.4` identifies the induced map on
-- pointwise right-derived values as an isomorphism.
/-- Every denominator in the restricted multiplicative system `S_𝓔` is sent to an isomorphism by
the restricted functor `RF : 𝓔 ⥤ D'`. -/
theorem rightDerivedDefinedFunctor_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔[F, S]).IsInvertedBy (rightDerivedDefinedFunctor F S) := by
  intro X Y s hs
  -- Proof comment: the restricted denominator is the same ambient denominator, so the map on
  -- right-derived values should be an isomorphism.
  change IsIso (rightDerivedValueMap S F s.hom)
  -- TODO: deduce this from the denominator-inversion clause of Lemma `13.14.4` in the local
  -- pointwise-defined setting, after packaging the required `IsIso (rightDerivedValueMap ...)`
  -- owner theorem for morphisms of `S` between defined objects.
  sorry

/-- The localized right-derived functor `RF : S_𝓔^{-1}𝓔 ⥤ D'` induced by the restricted functor
`RF : 𝓔 ⥤ D'`. -/
noncomputable abbrev rightDerivedLocalizationFactorization
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔[F, S]).Localization ⥤ D' :=
  Localization.lift (rightDerivedDefinedFunctor F S)
    (rightDerivedDefinedFunctor_isInvertedBy F S) (S_𝓔[F, S]).Q

/-- The full subcategory `𝓔ₗ ⊆ D` consisting of objects at which the pointwise left derived
functor of `F` with respect to `S` is defined. -/
abbrev leftDerivedDefinedSubcategory (F : D ⥤ D') (S : MorphismProperty D) :=
  (leftDerivedDefinedObjectProperty F S).FullSubcategory

/-- The restricted multiplicative system `S_𝓔ₗ` on the full subcategory `𝓔ₗ`. -/
abbrev leftDerivedDefinedLocalizationSystem (F : D ⥤ D') (S : MorphismProperty D) :
    MorphismProperty (leftDerivedDefinedSubcategory F S) :=
  fullSubcategoryLocalizationSystem (leftDerivedDefinedObjectProperty F S) S

notation "𝓔ₗ[" F ", " S "]" => leftDerivedDefinedSubcategory F S
notation "S_𝓔ₗ[" F ", " S "]" => leftDerivedDefinedLocalizationSystem F S

/- Left-derived companion recall: a denominator `s : X ⟶ Y` in `S` has source in `𝓔ₗ[F, S]` if
and only if it has target in `𝓔ₗ[F, S]`. -/
recall Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem

/-- An object of the full subcategory `𝓔ₗ` canonically carries the hypothesis that `LF` is
pointwise defined there. -/
instance leftDerivedDefinedSubcategory_hasPointwiseLeftDerivedFunctorAt
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔ₗ[F, S]) :
    F.HasPointwiseLeftDerivedFunctorAt S X.obj :=
  X.property

/-- Helper for Proposition 13.14.8: the left-derived-defined object property is invariant along
ambient denominators. -/
theorem leftDerivedDefinedObjectProperty_iff_of_mem
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D} (s : X ⟶ Y) (hs : S s) :
    leftDerivedDefinedObjectProperty F S X ↔
      leftDerivedDefinedObjectProperty F S Y := by
  simpa [leftDerivedDefinedObjectProperty] using
    (Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem
      (F := F) (W := S) (w := s) (hw := hs))

/-- Helper for Proposition 13.14.8: the restricted left-derived functor sends identity morphisms
to identity morphisms. -/
theorem leftDerivedDefinedFunctor_map_id
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔ₗ[F, S]) :
    leftDerivedValueMap S F (𝟙 X.obj) = 𝟙 (leftDerivedValue S F X.obj) := by
  let _ : HasLimit (StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F) :=
    Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X.obj
  -- Proof comment: compare the two maps on every denominator projection of `LF(X)` and use the
  -- identity reindexing formula in the structured-arrow category.
  apply limit.hom_ext
  intro g
  have hg :
      (StructuredArrow.map (S.Q.map (𝟙 X.obj))).obj g = g := by
    simpa using left_derived_identity_reindex_obj (S := S) (g := g)
  let LX := StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F
  have h0 :
      leftDerivedValueMap S F (𝟙 X.obj) ≫
          limit.π LX g =
        limit.π LX
          ((StructuredArrow.map (S.Q.map (𝟙 X.obj))).obj g) := by
    simpa using
      leftDerivedValueMap_projection_on_index_object
        (F := F) (S := S) (f := 𝟙 X.obj) (g := g)
  have h1 :
      limit.π LX ((StructuredArrow.map (S.Q.map (𝟙 X.obj))).obj g) =
        limit.π LX g := by
    simpa [LX] using limit.w LX (eqToHom hg)
  calc
    leftDerivedValueMap S F (𝟙 X.obj) ≫ limit.π LX g =
      limit.π LX g := h0.trans h1
    _ = 𝟙 (leftDerivedValue S F X.obj) ≫ limit.π LX g := by
      rw [Category.id_comp]

/-- Helper for Proposition 13.14.8: the restricted left-derived functor respects composition. -/
theorem leftDerivedDefinedFunctor_map_comp
    (F : D ⥤ D') (S : MorphismProperty D)
    {X Y Z : 𝓔ₗ[F, S]} (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftDerivedValueMap S F ((f ≫ g).hom) =
      leftDerivedValueMap S F f.hom ≫ leftDerivedValueMap S F g.hom := by
  let _ : HasLimit (StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F) :=
    Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X.obj
  let _ : HasLimit (StructuredArrow.proj (S.Q.obj Y.obj) S.Q ⋙ F) :=
    Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y.obj
  let _ : HasLimit (StructuredArrow.proj (S.Q.obj Z.obj) S.Q ⋙ F) :=
    Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Z.obj
  -- Proof comment: compare both morphisms on every denominator projection of `LF(Z)` and
  -- collapse the nested structured-arrow reindexing by evaluating first along `g` and then `f`.
  apply limit.hom_ext
  intro h
  have hf :
      leftDerivedValueMap S F f.hom ≫
          limit.π (StructuredArrow.proj (S.Q.obj Y.obj) S.Q ⋙ F)
            ((StructuredArrow.map (S.Q.map g.hom)).obj h) =
        limit.π (StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F)
          ((StructuredArrow.map (S.Q.map f.hom)).obj
            ((StructuredArrow.map (S.Q.map g.hom)).obj h)) := by
    simpa using
      leftDerivedValueMap_projection_on_index_object
        (F := F) (S := S) (f := f.hom)
        (g := (StructuredArrow.map (S.Q.map g.hom)).obj h)
  have hg :
      leftDerivedValueMap S F g.hom ≫
          limit.π (StructuredArrow.proj (S.Q.obj Z.obj) S.Q ⋙ F) h =
        limit.π (StructuredArrow.proj (S.Q.obj Y.obj) S.Q ⋙ F)
          ((StructuredArrow.map (S.Q.map g.hom)).obj h) := by
    simpa using
      leftDerivedValueMap_projection_on_index_object
        (F := F) (S := S) (f := g.hom) (g := h)
  have hcomp :
      leftDerivedValueMap S F ((f ≫ g).hom) ≫
          limit.π (StructuredArrow.proj (S.Q.obj Z.obj) S.Q ⋙ F) h =
        limit.π (StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F)
          ((StructuredArrow.map (S.Q.map f.hom)).obj
            ((StructuredArrow.map (S.Q.map g.hom)).obj h)) := by
    let LX := StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F
    have h0 :
        leftDerivedValueMap S F ((f ≫ g).hom) ≫
            limit.π (StructuredArrow.proj (S.Q.obj Z.obj) S.Q ⋙ F) h =
          limit.π LX ((StructuredArrow.map (S.Q.map ((f ≫ g).hom))).obj h) := by
      simpa [LX] using
        leftDerivedValueMap_projection_on_index_object
          (F := F) (S := S) (f := (f ≫ g).hom) (g := h)
    have hobj :
        (StructuredArrow.map (S.Q.map ((f ≫ g).hom))).obj h =
          (StructuredArrow.map (S.Q.map f.hom)).obj
            ((StructuredArrow.map (S.Q.map g.hom)).obj h) := by
      simpa [Functor.map_comp] using
        (StructuredArrow.map_comp
          (T := S.Q) (f := S.Q.map f.hom) (f' := S.Q.map g.hom) (h := h))
    have htransport :
        limit.π LX ((StructuredArrow.map (S.Q.map ((f ≫ g).hom))).obj h) =
          limit.π LX
            ((StructuredArrow.map (S.Q.map f.hom)).obj
              ((StructuredArrow.map (S.Q.map g.hom)).obj h)) := by
      simpa [LX] using limit.w LX (eqToHom hobj)
    exact h0.trans htransport
  have hmid :
      leftDerivedValueMap S F f.hom ≫
          limit.π (StructuredArrow.proj (S.Q.obj Y.obj) S.Q ⋙ F)
            ((StructuredArrow.map (S.Q.map g.hom)).obj h) =
        leftDerivedValueMap S F f.hom ≫
          (leftDerivedValueMap S F g.hom ≫
            limit.π (StructuredArrow.proj (S.Q.obj Z.obj) S.Q ⋙ F) h) := by
    rw [hg.symm]
    rfl
  have hright :
      leftDerivedValueMap S F f.hom ≫
          (leftDerivedValueMap S F g.hom ≫
            limit.π (StructuredArrow.proj (S.Q.obj Z.obj) S.Q ⋙ F) h) =
        (leftDerivedValueMap S F f.hom ≫ leftDerivedValueMap S F g.hom) ≫
          limit.π (StructuredArrow.proj (S.Q.obj Z.obj) S.Q ⋙ F) h := by
    simp [Category.assoc]
  exact hcomp.trans (hf.symm.trans (hmid.trans hright))

/-- The functor `LF : 𝓔ₗ ⥤ D'` obtained by restricting the pointwise left derived construction to
the full subcategory where it is defined. -/
noncomputable def leftDerivedDefinedFunctor (F : D ⥤ D') (S : MorphismProperty D) :
    𝓔ₗ[F, S] ⥤ D' where
  obj X :=
    leftDerivedValue S F X.obj
  map f :=
    leftDerivedValueMap S F f.hom
  map_id X :=
    leftDerivedDefinedFunctor_map_id (F := F) (S := S) X
  map_comp f g :=
    leftDerivedDefinedFunctor_map_comp (F := F) (S := S) f g

-- Proof sketch: if a morphism of `S_𝓔ₗ` lies over an ambient arrow `s ∈ S`, then the two
-- objects of `𝓔ₗ` remain in the left-derived domain and Lemma `13.14.4` identifies the induced
-- map on pointwise left-derived values as an isomorphism.
/-- Every denominator in the restricted multiplicative system `S_𝓔ₗ` is sent to an isomorphism by
the restricted functor `LF : 𝓔ₗ ⥤ D'`. -/
theorem leftDerivedDefinedFunctor_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔ₗ[F, S]).IsInvertedBy (leftDerivedDefinedFunctor F S) := by
  intro X Y s hs
  -- Proof comment: the restricted denominator is the same ambient denominator, so the map on
  -- left-derived values should be an isomorphism.
  change IsIso (leftDerivedValueMap S F s.hom)
  -- TODO: deduce this from the denominator-inversion clause of Lemma `13.14.4` in the local
  -- pointwise-defined setting, after packaging the required `IsIso (leftDerivedValueMap ...)`
  -- owner theorem for morphisms of `S` between defined objects.
  sorry

/-- The localized left-derived functor `LF : S_𝓔ₗ^{-1}𝓔ₗ ⥤ D'` induced by the restricted functor
`LF : 𝓔ₗ ⥤ D'`. -/
noncomputable abbrev leftDerivedLocalizationFactorization
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔ₗ[F, S]).Localization ⥤ D' :=
  Localization.lift (leftDerivedDefinedFunctor F S)
    (leftDerivedDefinedFunctor_isInvertedBy F S) (S_𝓔ₗ[F, S]).Q

end Basic

section RestrictedLocalization

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/- The restricted system `S_𝓔[F, S]` inherits saturation directly from the owner instance
`fullSubcategoryLocalizationSystem_isSaturatedMultiplicativeSystem`; no local reexport is needed.
-/

/- The restricted system `S_𝓔ₗ[F, S]` likewise inherits saturation from
`fullSubcategoryLocalizationSystem_isSaturatedMultiplicativeSystem`.
-/

/-- Helper for Proposition 13.14.8: conjugating by isomorphisms gives a bijection on Hom-sets. -/
private theorem hom_transport_bijective_local {C : Type u₁} [Category.{v₁} C]
    {X₁ X₂ Y₁ Y₂ : C} (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂) :
    Function.Bijective (fun f : X₂ ⟶ Y₂ ↦ eX.hom ≫ f ≫ eY.inv) := by
  constructor
  · intro f g hfg
    -- Proof comment: apply the inverse transport on both sides to cancel the chosen isomorphisms.
    simpa [Category.assoc] using congrArg (fun k ↦ eX.inv ≫ k ≫ eY.hom) hfg
  · intro f
    -- Proof comment: the inverse transport is the opposite conjugation.
    refine ⟨eX.inv ≫ f ≫ eY.hom, ?_⟩
    simp [Category.assoc]

/-- Helper for Proposition 13.14.8: if `P` is invariant along arrows of `S`, then the restricted
system on `P.FullSubcategory` admits right fractions. -/
theorem fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_mem_iff_local
    {P : ObjectProperty D} [IsSaturatedMultiplicativeSystem S]
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y)) :
    HasRightCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := by
  refine
    { toIsMultiplicative := inferInstance
      exists_rightFraction := ?_
      ext := ?_ }
  · intro X Y φ
    obtain ⟨ψ, hψ⟩ :=
      (LeftFraction.mk φ.f.hom φ.s.hom
        (by simpa [fullSubcategoryLocalizationSystem] using φ.hs)).exists_rightFraction
    have hψX' : P ψ.X' := (hP ψ.s ψ.hs).2 X.property
    let Z : P.FullSubcategory := ⟨ψ.X', hψX'⟩
    let sZ : Z ⟶ X := ObjectProperty.homMk (P := P) ψ.s
    let fZ : Z ⟶ Y := ObjectProperty.homMk (P := P) ψ.f
    refine
      ⟨RightFraction.mk sZ
        (by
          change S sZ.hom
          simpa [sZ] using ψ.hs)
        fZ, ?_⟩
    -- Proof comment: forgetting to `D`, this is exactly the ambient right-fraction witness.
    apply P.ι.map_injective
    simpa [Z] using hψ
  · intro X Y Y' f₁ f₂ s hs hfs
    obtain ⟨X', t, ht, hfac⟩ :=
      HasRightCalculusOfFractions.ext f₁.hom f₂.hom s.hom
        (by simpa [fullSubcategoryLocalizationSystem] using hs)
        (by simpa using congrArg (fun k ↦ k.hom) hfs)
    have hX' : P X' := (hP t ht).2 X.property
    let Z : P.FullSubcategory := ⟨X', hX'⟩
    refine
      ⟨Z, ObjectProperty.homMk (P := P) t,
        by simpa [fullSubcategoryLocalizationSystem] using ht, ?_⟩
    -- Proof comment: the ambient cancellation equality already lives in the full subcategory.
    apply P.ι.map_injective
    simpa [Z] using hfac

/-- Helper for Proposition 13.14.8: forgetting the full-subcategory structure turns a restricted
roof into the ambient roof with the same numerator and denominator. -/
private abbrev fullSubcategory_rightFraction_toAmbient_local
    {P : ObjectProperty D} {X Y : P.FullSubcategory}
    (φ : (fullSubcategoryLocalizationSystem P S).RightFraction X Y) :
    S.RightFraction (P.ι.obj X) (P.ι.obj Y) :=
  RightFraction.mk φ.s.hom
    (by simpa [fullSubcategoryLocalizationSystem] using φ.hs) φ.f.hom

/-- Helper for Proposition 13.14.8: after transporting through the localizer comparison square,
the unfolded image of a restricted roof is the expected ambient numerator over denominator. -/
private theorem fullSubcategoryLocalizationFunctor_transport_map_of_right_fraction_data_local
    {P : ObjectProperty D}
    [IsSaturatedMultiplicativeSystem S] {X Y : P.FullSubcategory}
    (φ : (fullSubcategoryLocalizationSystem P S).RightFraction X Y)
    [IsIso (S.Q.map φ.s.hom)]
    [IsIso ((fullSubcategoryLocalizationFunctor P S).map
      ((fullSubcategoryLocalizationSystem P S).Q.map φ.s))] :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    eX.hom ≫ (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ eY.inv =
      inv (S.Q.map φ.s.hom) ≫ S.Q.map φ.f.hom := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eA : S.Q.obj (P.ι.obj φ.X') ≅ G.obj (W.Q.obj φ.X') := η.app φ.X'
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  have hs_nat :
      S.Q.map φ.s.hom ≫ eX.hom = eA.hom ≫ G.map (W.Q.map φ.s) := by
    -- Proof comment: naturality for the localizer comparison square identifies the denominators.
    simpa [W, G, η, Functor.comp_map] using NatTrans.naturality η.hom φ.s
  have hf_nat :
      S.Q.map φ.f.hom ≫ eY.hom = eA.hom ≫ G.map (W.Q.map φ.f) := by
    -- Proof comment: the same naturality relation transports the numerator.
    simpa [W, G, η, Functor.comp_map] using NatTrans.naturality η.hom φ.f
  have hsinv :
      eX.hom ≫ inv (G.map (W.Q.map φ.s)) =
        inv (S.Q.map φ.s.hom) ≫ eA.hom := by
    -- Proof comment: invert the denominator square once so the final computation is flat.
    apply (cancel_mono (G.map (W.Q.map φ.s))).1
    calc
      (eX.hom ≫ inv (G.map (W.Q.map φ.s))) ≫ G.map (W.Q.map φ.s)
          = eX.hom := by
              simp
      _ = inv (S.Q.map φ.s.hom) ≫ (S.Q.map φ.s.hom ≫ eX.hom) := by
              simp
      _ = inv (S.Q.map φ.s.hom) ≫ (eA.hom ≫ G.map (W.Q.map φ.s)) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ inv (S.Q.map φ.s.hom) ≫ k) hs_nat
      _ = (inv (S.Q.map φ.s.hom) ≫ eA.hom) ≫ G.map (W.Q.map φ.s) := by
              simp [Category.assoc]
  have htransport :
      eX.hom ≫ (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ eY.inv =
        inv (S.Q.map φ.s.hom) ≫ (S.Q.map φ.f.hom ≫ eY.hom) ≫ eY.inv := by
    -- Proof comment: rewrite the transported denominator and numerator once, then cancel `eY`.
    calc
      eX.hom ≫ (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ eY.inv
          = (eX.hom ≫ inv (G.map (W.Q.map φ.s))) ≫ G.map (W.Q.map φ.f) ≫ eY.inv := by
              simp [Category.assoc]
      _ = (inv (S.Q.map φ.s.hom) ≫ eA.hom) ≫ G.map (W.Q.map φ.f) ≫ eY.inv := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ G.map (W.Q.map φ.f) ≫ eY.inv) hsinv
      _ = inv (S.Q.map φ.s.hom) ≫ (eA.hom ≫ G.map (W.Q.map φ.f)) ≫ eY.inv := by
              simp [Category.assoc]
      _ = inv (S.Q.map φ.s.hom) ≫ (S.Q.map φ.f.hom ≫ eY.hom) ≫ eY.inv := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ inv (S.Q.map φ.s.hom) ≫ k ≫ eY.inv) hf_nat.symm
  simpa [Category.assoc] using htransport

/-- Helper for Proposition 13.14.8: after transporting through the localizer comparison square,
the image of a restricted right fraction is the corresponding ambient right fraction. -/
private theorem fullSubcategoryLocalizationFunctor_transport_rightFraction_local
    {P : ObjectProperty D}
    [IsSaturatedMultiplicativeSystem S] {X Y : P.FullSubcategory}
    (φ : (fullSubcategoryLocalizationSystem P S).RightFraction X Y) :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    eX.hom ≫ G.map (φ.map W.Q (Localization.inverts W.Q W)) ≫ eY.inv =
      (fullSubcategory_rightFraction_toAmbient_local (S := S) φ).map S.Q
        (Localization.inverts S.Q S) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  letI : IsIso (W.Q.map φ.s) := Localization.inverts W.Q W _ φ.hs
  letI : IsIso (S.Q.map φ.s.hom) := by
    simpa [W, fullSubcategoryLocalizationSystem] using
      (Localization.inverts S.Q S φ.s.hom φ.hs)
  letI : IsIso (G.map (W.Q.map φ.s)) := by infer_instance
  -- Proof comment: after unfolding `RightFraction.map`, the result is the transport identity above.
  simpa [fullSubcategory_rightFraction_toAmbient_local, MorphismProperty.RightFraction.map,
    Functor.map_comp, map_inv, Category.assoc] using
    (fullSubcategoryLocalizationFunctor_transport_map_of_right_fraction_data_local
      (S := S) (P := P) φ)

/-- Helper for Proposition 13.14.8: precomposing an ambient right fraction by an arrow of `S`
does not change the represented morphism in the ambient localization. -/
private theorem ambient_right_fraction_precompose_mem_eq_local
    [IsSaturatedMultiplicativeSystem S] {A B : D} (φ : S.RightFraction A B) {A' : D}
    (u : A' ⟶ φ.X') (hu : S u) :
    (RightFraction.mk (u ≫ φ.s) (S.comp_mem _ _ hu φ.hs) (u ≫ φ.f)).map S.Q
        (Localization.inverts S.Q S) =
      φ.map S.Q (Localization.inverts S.Q S) := by
  -- Proof comment: this is the canonical right-fraction refinement witness with identity on the old roof.
  symm
  exact (MorphismProperty.RightFraction.map_eq_iff S.Q S φ
    (RightFraction.mk (u ≫ φ.s) (S.comp_mem _ _ hu φ.hs) (u ≫ φ.f))).2
      ⟨A', u, 𝟙 _, by simp, by simp,
        by simpa [Category.assoc] using S.comp_mem _ _ hu φ.hs⟩

/-- Helper for Proposition 13.14.8: on localization objects coming directly from
`P.FullSubcategory`, the localized inclusion is surjective on Hom-sets once `P` is invariant
along arrows of `S`. -/
private theorem fullSubcategoryLocalizationFunctor_conjugated_map_surjective_on_Q_obj_local
    {P : ObjectProperty D} [IsSaturatedMultiplicativeSystem S]
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y))
    (X Y : P.FullSubcategory) :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    Function.Surjective
      (fun g : W.Q.obj X ⟶ W.Q.obj Y ↦ eX.hom ≫ G.map g ≫ eY.inv) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  letI : HasRightCalculusOfFractions W :=
    fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_mem_iff_local
      (S := S) (P := P) hP
  dsimp [W, G, η, eX, eY]
  intro f
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S f
  have hX' : P φ.X' := (hP φ.s φ.hs).2 X.property
  let Z : P.FullSubcategory := ⟨φ.X', hX'⟩
  let sZ : Z ⟶ X := ObjectProperty.homMk (P := P) φ.s
  let fZ : Z ⟶ Y := ObjectProperty.homMk (P := P) φ.f
  let ψ : W.RightFraction X Y :=
    RightFraction.mk sZ
      (by
        change S sZ.hom
        simpa [sZ] using φ.hs)
      fZ
  refine ⟨ψ.map W.Q (Localization.inverts W.Q W), ?_⟩
  calc
    eX.hom ≫ G.map (ψ.map W.Q (Localization.inverts W.Q W)) ≫ eY.inv
        =
      (fullSubcategory_rightFraction_toAmbient_local (S := S) ψ).map S.Q
        (Localization.inverts S.Q S) := by
          simpa [W, G, η, eX, eY] using
            fullSubcategoryLocalizationFunctor_transport_rightFraction_local
              (S := S) (P := P) ψ
    _ = φ.map S.Q (Localization.inverts S.Q S) := by
      -- Proof comment: the restricted roof is the ambient roof with the same data.
      simpa [ψ, Z, sZ, fZ, fullSubcategory_rightFraction_toAmbient_local] using
        (rfl : φ.map S.Q (Localization.inverts S.Q S) =
          φ.map S.Q (Localization.inverts S.Q S))
    _ = f := hφ.symm

/-- Helper for Proposition 13.14.8: on localization objects coming directly from
`P.FullSubcategory`, the localized inclusion is injective on Hom-sets once `P` is invariant
along arrows of `S`. -/
private theorem fullSubcategoryLocalizationFunctor_conjugated_map_injective_on_Q_obj_local
    {P : ObjectProperty D} [IsSaturatedMultiplicativeSystem S]
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y))
    (X Y : P.FullSubcategory) :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    Function.Injective
      (fun g : W.Q.obj X ⟶ W.Q.obj Y ↦ eX.hom ≫ G.map g ≫ eY.inv) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  letI : HasRightCalculusOfFractions W :=
    fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_mem_iff_local
      (S := S) (P := P) hP
  dsimp [W, G, η, eX, eY]
  intro g₁ g₂ hgg
  obtain ⟨φ₁, hφ₁⟩ := Localization.exists_rightFraction W.Q W g₁
  obtain ⟨φ₂, hφ₂⟩ := Localization.exists_rightFraction W.Q W g₂
  have hmapEq :
      (fullSubcategory_rightFraction_toAmbient_local (S := S) φ₁).map S.Q
          (Localization.inverts S.Q S)
        =
      (fullSubcategory_rightFraction_toAmbient_local (S := S) φ₂).map S.Q
          (Localization.inverts S.Q S) := by
    calc
      (fullSubcategory_rightFraction_toAmbient_local (S := S) φ₁).map S.Q
          (Localization.inverts S.Q S)
          =
        eX.hom ≫ G.map g₁ ≫ eY.inv := by
            simpa [W, G, η, eX, eY, hφ₁] using
              (fullSubcategoryLocalizationFunctor_transport_rightFraction_local
                (S := S) (P := P) φ₁).symm
      _ = eX.hom ≫ G.map g₂ ≫ eY.inv := hgg
      _ =
        (fullSubcategory_rightFraction_toAmbient_local (S := S) φ₂).map S.Q
          (Localization.inverts S.Q S) := by
            simpa [W, G, η, eX, eY, hφ₂] using
              fullSubcategoryLocalizationFunctor_transport_rightFraction_local
                (S := S) (P := P) φ₂
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff S.Q S
      (fullSubcategory_rightFraction_toAmbient_local (S := S) φ₁)
      (fullSubcategory_rightFraction_toAmbient_local (S := S) φ₂)).1 hmapEq
  have hZ : P Z := by
    simpa [fullSubcategory_rightFraction_toAmbient_local] using
      (hP (t₁ ≫ (fullSubcategory_rightFraction_toAmbient_local (S := S) φ₁).s) ht).2 X.property
  let Z' : P.FullSubcategory := ⟨Z, hZ⟩
  have hrel : MorphismProperty.RightFractionRel φ₁ φ₂ := by
    refine
      ⟨Z', ObjectProperty.homMk (P := P) t₁, ObjectProperty.homMk (P := P) t₂, ?_, ?_, ?_⟩
    · apply P.ι.map_injective
      simpa using hst
    · apply P.ι.map_injective
      simpa using hft
    · simpa [W, fullSubcategoryLocalizationSystem] using ht
  have hfracEq :
      φ₁.map W.Q (Localization.inverts W.Q W) =
        φ₂.map W.Q (Localization.inverts W.Q W) := by
    exact (MorphismProperty.RightFraction.map_eq_iff W.Q W φ₁ φ₂).2 hrel
  rw [hφ₁, hφ₂]
  exact hfracEq

/-- Helper for Proposition 13.14.8: on localization objects coming directly from
`P.FullSubcategory`, the localized inclusion is bijective on Hom-sets once `P` is invariant
along arrows of `S`. -/
private theorem fullSubcategoryLocalizationFunctor_map_bijective_on_Q_obj_local
    {P : ObjectProperty D} [IsSaturatedMultiplicativeSystem S]
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y))
    (X Y : P.FullSubcategory) :
    Function.Bijective
      ((fullSubcategoryLocalizationFunctor P S).map :
        ((fullSubcategoryLocalizationSystem P S).Q.obj X ⟶
            (fullSubcategoryLocalizationSystem P S).Q.obj Y) →
          ((fullSubcategoryLocalizationFunctor P S).obj
              ((fullSubcategoryLocalizationSystem P S).Q.obj X) ⟶
            (fullSubcategoryLocalizationFunctor P S).obj
              ((fullSubcategoryLocalizationSystem P S).Q.obj Y))) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  have hTarget :
      Function.Bijective
        (fun f : G.obj (W.Q.obj X) ⟶ G.obj (W.Q.obj Y) ↦ eX.hom ≫ f ≫ eY.inv) :=
    hom_transport_bijective_local eX eY
  have hConjugated :
      Function.Bijective
        (fun g : W.Q.obj X ⟶ W.Q.obj Y ↦ eX.hom ≫ G.map g ≫ eY.inv) := by
    refine ⟨?_, ?_⟩
    · simpa [W, G, η, eX, eY] using
        fullSubcategoryLocalizationFunctor_conjugated_map_injective_on_Q_obj_local
          (S := S) (P := P) hP X Y
    · simpa [W, G, η, eX, eY] using
        fullSubcategoryLocalizationFunctor_conjugated_map_surjective_on_Q_obj_local
          (S := S) (P := P) hP X Y
  exact (Function.Bijective.of_comp_iff' hTarget _).mp hConjugated

/-- Helper for Proposition 13.14.8: if `P` is invariant along arrows of `S`, then the localized
inclusion of `P.FullSubcategory` into `S.Localization` is fully faithful. -/
noncomputable def fullSubcategoryLocalizationFunctor_fullyFaithful_of_mem_iff_local
    {P : ObjectProperty D} [IsSaturatedMultiplicativeSystem S]
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y)) :
    (fullSubcategoryLocalizationFunctor P S).FullyFaithful := by
  classical
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  letI : HasRightCalculusOfFractions W :=
    fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_mem_iff_local
      (S := S) (P := P) hP
  have hFF : Nonempty G.FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    let X' : P.FullSubcategory := W.Q.objPreimage X
    let Y' : P.FullSubcategory := W.Q.objPreimage Y
    let eX : W.Q.obj X' ≅ X := W.Q.objObjPreimageIso X
    let eY : W.Q.obj Y' ≅ Y := W.Q.objObjPreimageIso Y
    let eGX : G.obj (W.Q.obj X') ≅ G.obj X := G.mapIso eX
    let eGY : G.obj (W.Q.obj Y') ≅ G.obj Y := G.mapIso eY
    have hSource :
        Function.Bijective
          (fun f : X ⟶ Y ↦ eX.hom ≫ f ≫ eY.inv) :=
      hom_transport_bijective_local eX eY
    have hTarget :
        Function.Bijective
          (fun f : G.obj X ⟶ G.obj Y ↦ eGX.hom ≫ f ≫ eGY.inv) :=
      hom_transport_bijective_local eGX eGY
    have hQobj :
        Function.Bijective
          (G.map :
            (W.Q.obj X' ⟶ W.Q.obj Y') →
              (G.obj (W.Q.obj X') ⟶ G.obj (W.Q.obj Y'))) :=
      fullSubcategoryLocalizationFunctor_map_bijective_on_Q_obj_local
        (S := S) (P := P) hP X' Y'
    have hTransportedModel :
        Function.Bijective
          (((G.map) :
              (W.Q.obj X' ⟶ W.Q.obj Y') →
                (G.obj (W.Q.obj X') ⟶ G.obj (W.Q.obj Y'))) ∘
            fun f : X ⟶ Y ↦ eX.hom ≫ f ≫ eY.inv) :=
      Function.Bijective.comp hQobj hSource
    have hcomp :
        ((G.map) ∘ fun f : X ⟶ Y ↦ eX.hom ≫ f ≫ eY.inv) =
          (fun f : X ⟶ Y ↦ eGX.hom ≫ G.map f ≫ eGY.inv) := by
      -- Proof comment: functoriality matches the source and target transports through `G`.
      funext f
      simp [Function.comp, eGX, eGY, Functor.map_comp]
    have hTransported :
        Function.Bijective
          (fun f : X ⟶ Y ↦ eGX.hom ≫ G.map f ≫ eGY.inv) := by
      simpa [hcomp] using hTransportedModel
    exact (Function.Bijective.of_comp_iff' hTarget _).mp hTransported
  exact Classical.choice hFF

end RestrictedLocalization

section Triangulated

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D]
  [HasShift D ℤ]
  [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  [IsTriangulated D]
  (F : D ⥤ D') (S : MorphismProperty D)

/-- Helper for Proposition 13.14.8: the zero object belongs to the right-derived-defined object
property. -/
theorem rightDerivedDefinedObjectProperty_zero
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    rightDerivedDefinedObjectProperty F S (0 : D) := by
  let _ := (inferInstance : IsTriangulated D)
  let _ := hzero'
  let _ := hshift'
  let _ := hpreadd'
  let _ := hadd'
  let _ := hpretri'
  let _ := htri'
  let _ := hcomm
  let _ := hexact
  letI : Limits.HasZeroObject S.Localization := inferInstance
  let hQ0 : Limits.IsZero (S.Q.obj (0 : D)) := S.Q.map_isZero (Limits.isZero_zero D)
  let T :
      Limits.IsTerminal
        (CostructuredArrow.mk (𝟙 (S.Q.obj (0 : D))) :
          CostructuredArrow S.Q (S.Q.obj (0 : D))) := by
    -- Proof comment: every denominator into `S.Q.obj 0` is uniquely the zero map because the
    -- target is a zero object in the localization.
    letI :
        ∀ g : CostructuredArrow S.Q (S.Q.obj (0 : D)),
          Unique
            (g ⟶
              (CostructuredArrow.mk (𝟙 (S.Q.obj (0 : D))) :
                CostructuredArrow S.Q (S.Q.obj (0 : D)))) :=
      fun g ↦
        { default :=
            CostructuredArrow.homMk (0 : g.left ⟶ (0 : D))
              (by
                exact hQ0.eq_of_tgt _ _)
          uniq := fun f ↦ by
            apply CostructuredArrow.hom_ext
            exact (Limits.isZero_zero D).eq_of_tgt _ _ }
    exact Limits.IsTerminal.ofUnique _
  let D0 := CostructuredArrow.proj S.Q (S.Q.obj (0 : D)) ⋙ F
  -- Proof comment: once the right comma category has a terminal object, its diagram has the
  -- canonical terminal-object colimit.
  refine ⟨?_⟩
  change Limits.HasColimit D0
  exact ⟨⟨Limits.coconeOfDiagramTerminal T D0, Limits.colimitOfDiagramTerminal T D0⟩⟩

-- Proof sketch: apply Lemmas `13.14.4`, `13.14.6`, and `13.14.7` to show that the object
-- property “`RF` is defined” is closed under isomorphisms, shifts, cones, and the zero object;
-- this is exactly the canonical `ObjectProperty.IsTriangulated` interface.
/-- Proposition 13.14.8: the full subcategory `𝓔 ⊆ D` consisting of objects at which the
pointwise right derived functor of `F` with respect to `S` is defined is strictly full and
triangulated. The companion declarations below record the restricted functor `RF : 𝓔 ⥤ D'`, the
restricted multiplicative system `S_𝓔`, its localization factorization, and the Karoubian
saturation conclusion. -/
@[stacks 05SE]
instance rightDerivedDefinedObjectProperty_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedObjectProperty F S).IsTriangulated := by
  -- Proof comment: `ObjectProperty.IsTriangulated` is exactly the package of a zero-object
  -- witness, shift stability, and the closed₂ clause. The latter two are owner instances from
  -- Lemmas `13.14.5` and `13.14.6`, so only the zero-object witness remains local.
  refine
    { toContainsZero := ?_
      toIsStableUnderShift := inferInstance
      toIsTriangulatedClosed₂ := inferInstance }
  exact ⟨0, Limits.isZero_zero D, rightDerivedDefinedObjectProperty_zero (F := F) (S := S)⟩

/-- The restricted right-derived functor `RF : 𝓔[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance rightDerivedDefinedFunctor_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedFunctor F S).CommShift ℤ := by
  -- Proof comment: the restricted right-derived functor inherits shift compatibility from the
  -- pointwise comparison isomorphisms supplied by Lemma `13.14.5`.
  -- TODO: build the `CommShift` structure from the pointwise isomorphisms
  -- `rightDerivedValueShiftIso`, checking naturality against `rightDerivedValueMap`.
  sorry

/-- The restricted right-derived functor `RF : 𝓔[F, S] ⥤ D'` is exact. -/
instance rightDerivedDefinedFunctor_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedFunctor F S).IsTriangulated := by
  -- Proof comment: once the restricted functor is equipped with its shift structure, exactness is
  -- the distinguished-triangle statement from Lemma `13.14.6` applied in the ambient category.
  -- TODO: use `rightDerivedDefinedFunctor_commShift` and
  -- `right_derived_triangle_distinguished` to package exactness on the full subcategory.
  sorry

-- Strict fullness is already the owner instance
-- `rightDerivedDefinedObjectProperty_isClosedUnderIsomorphisms` from `Lemma_13_14_5`.

/- Once `rightDerivedDefinedObjectProperty F S` is triangulated, the restricted system `S_𝓔[F, S]`
inherits `IsCompatibleWithTriangulation` from the generic owner instance
`fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation`.
-/

local instance rightDerivedDefinedLocalization_hasZeroObject
    [htriE : (rightDerivedDefinedObjectProperty F S).IsTriangulated]
    [HasLeftCalculusOfFractions (S_𝓔[F, S])] :
    Limits.HasZeroObject (S_𝓔[F, S]).Localization := by
  let P := rightDerivedDefinedObjectProperty F S
  letI : P.IsTriangulated := by
    simpa [P] using htriE
  letI : HasLeftCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := by
    simpa [P, rightDerivedDefinedLocalizationSystem] using
      (inferInstance : HasLeftCalculusOfFractions (S_𝓔[F, S]))
  change Limits.HasZeroObject (fullSubcategoryLocalizationSystem P S).Localization
  infer_instance

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is fully faithful. -/
instance rightDerivedDefinedLocalizationFunctor_full
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).Full := by
  -- Proof comment: this is the source-facing fully-faithfulness clause for the restricted
  -- localization inclusion.
  let hFF :=
    fullSubcategoryLocalizationFunctor_fullyFaithful_of_mem_iff_local
      (S := S) (P := rightDerivedDefinedObjectProperty F S)
      (fun s hs ↦ rightDerivedDefinedObjectProperty_iff_of_mem (F := F) (S := S) s hs)
  exact hFF.full

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is faithful. -/
instance rightDerivedDefinedLocalizationFunctor_faithful
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).Faithful := by
  -- Proof comment: faithfulness is the second half of the same localized inclusion statement.
  let hFF :=
    fullSubcategoryLocalizationFunctor_fullyFaithful_of_mem_iff_local
      (S := S) (P := rightDerivedDefinedObjectProperty F S)
      (fun s hs ↦ rightDerivedDefinedObjectProperty_iff_of_mem (F := F) (S := S) s hs)
  exact hFF.faithful

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` commutes with shifts. -/
noncomputable instance rightDerivedDefinedLocalizationFunctor_commShift
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (rightDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).CommShift ℤ := by
  -- Proof comment: this is the canonical shift-commuting structure on the localized inclusion
  -- from Lemma `13.5.8`, specialized to the right-derived domain object property.
  let P := rightDerivedDefinedObjectProperty F S
  let F' : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy F' := by
    intro X Y f hf
    exact Localization.inverts S.Q S _ hf
  -- Proof comment: view the localized inclusion as the canonical localization lift of
  -- `P.ι ⋙ S.Q` and use the generic shift-compatibility owner from Lemma `13.5.7`.
  simpa [F', fullSubcategoryLocalizationFunctor] using
    (show (Localization.lift F' hF (fullSubcategoryLocalizationSystem P S).Q).CommShift ℤ from
      inferInstance)

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is exact. -/
noncomputable instance rightDerivedDefinedLocalizationFunctor_isTriangulated
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (rightDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation]
    [HasLeftCalculusOfFractions (S_𝓔[F, S])] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).IsTriangulated := by
  -- Proof comment: the exactness of the localized inclusion is the generic exact factorization
  -- theorem already proved for triangulated full subcategories.
  let P := rightDerivedDefinedObjectProperty F S
  let F' : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy F' := by
    intro X Y f hf
    exact Localization.inverts S.Q S _ hf
  letI : P.IsTriangulated := by
    simpa [P] using htriE
  letI : HasLeftCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := by
    simpa [P, rightDerivedDefinedLocalizationSystem] using
      (inferInstance : HasLeftCalculusOfFractions (S_𝓔[F, S]))
  -- Proof comment: this is exactly the owner proof from Lemma `13.5.8`, specialized to the
  -- right-derived domain.
  simpa [F', fullSubcategoryLocalizationFunctor] using
    (exact_factorization_isTriangulated
      (S := fullSubcategoryLocalizationSystem P S) (F := F') hF)

/-- The localized right-derived functor `RF : S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance rightDerivedLocalizationFactorization_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation]
    [HasLeftCalculusOfFractions (S_𝓔[F, S])] :
    (rightDerivedLocalizationFactorization F S).CommShift ℤ :=
  Functor.commShiftOfLocalization (S_𝓔[F, S]).Q (S_𝓔[F, S]) ℤ
    (rightDerivedDefinedFunctor F S) (rightDerivedLocalizationFactorization F S)

/-- The localized right-derived functor `RF : S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ D'` is exact. -/
instance rightDerivedLocalizationFactorization_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation]
    [HasLeftCalculusOfFractions (S_𝓔[F, S])] :
    (rightDerivedLocalizationFactorization F S).IsTriangulated := by
  -- Proof comment: once the restricted functor is exact and inverts the restricted system, the
  -- localized factor inherits exactness from the generic factorization theorem.
  simpa [rightDerivedLocalizationFactorization] using
    (exact_factorization_isTriangulated
      (S := S_𝓔[F, S]) (F := rightDerivedDefinedFunctor F S)
      (rightDerivedDefinedFunctor_isInvertedBy F S))

-- Proof sketch: if `RF` is defined at a biproduct `X ⊞ Y`, Lemma `13.14.7` shows that in a
-- Karoubian target the two direct summands also lie in the domain. This is exactly stability
-- under retracts of the corresponding object property.
/- Proposition 13.14.8 companion recall: if `D'` is Karoubian, then the right-derived-defined
object property is stable under retracts. Together with
`rightDerivedDefinedObjectProperty_isTriangulated`, this is exactly the source-facing statement
that `𝓔[F, S]` is a saturated triangulated subcategory. -/
recall rightDerivedDefinedObjectProperty_isStableUnderRetracts

-- Proof sketch: apply the left-derived clauses of Lemmas `13.14.4`, `13.14.6`, and `13.14.7` to
-- show that the object property “`LF` is defined” is closed under isomorphisms, shifts, cones,
-- and the zero object; this is exactly the canonical `ObjectProperty.IsTriangulated` interface.
/-- Helper for Proposition 13.14.8: the zero object belongs to the left-derived-defined object
property. -/
theorem leftDerivedDefinedObjectProperty_zero
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    leftDerivedDefinedObjectProperty F S (0 : D) := by
  let _ := (inferInstance : IsTriangulated D)
  let _ := hzero'
  let _ := hshift'
  let _ := hpreadd'
  let _ := hadd'
  let _ := hpretri'
  let _ := htri'
  let _ := hcomm
  let _ := hexact
  letI : Limits.HasZeroObject S.Localization := inferInstance
  let hQ0 : Limits.IsZero (S.Q.obj (0 : D)) := S.Q.map_isZero (Limits.isZero_zero D)
  let T :
      Limits.IsInitial
        (StructuredArrow.mk (𝟙 (S.Q.obj (0 : D))) :
          StructuredArrow (S.Q.obj (0 : D)) S.Q) := by
    -- Proof comment: dually, every denominator out of `S.Q.obj 0` is uniquely the zero map
    -- because the source is a zero object in the localization.
    letI :
        ∀ g : StructuredArrow (S.Q.obj (0 : D)) S.Q,
          Unique
            ((StructuredArrow.mk (𝟙 (S.Q.obj (0 : D))) :
                StructuredArrow (S.Q.obj (0 : D)) S.Q) ⟶
              g) :=
      fun g ↦
        { default :=
            StructuredArrow.homMk (0 : (0 : D) ⟶ g.right)
              (by
                exact hQ0.eq_of_src _ _)
          uniq := fun f ↦ by
            apply StructuredArrow.hom_ext
            exact (Limits.isZero_zero D).eq_of_src _ _ }
    exact Limits.IsInitial.ofUnique _
  let D0 := StructuredArrow.proj (S.Q.obj (0 : D)) S.Q ⋙ F
  -- Proof comment: an initial object in the left comma category yields the canonical limit cone
  -- computing the left-derived value at zero.
  refine ⟨?_⟩
  change Limits.HasLimit D0
  exact ⟨⟨Limits.coneOfDiagramInitial T D0, Limits.limitOfDiagramInitial T D0⟩⟩

/-- The full subcategory `𝓔ₗ ⊆ D` consisting of objects at which the pointwise left derived
functor of `F` with respect to `S` is defined is strictly full and triangulated, with the same
localized-factorization companion picture as on the right-derived side. -/
instance leftDerivedDefinedObjectProperty_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedObjectProperty F S).IsTriangulated := by
  -- Proof comment: the dual packaging uses the same canonical fields: a zero-object witness,
  -- shift stability, and the closed₂ clause.
  refine
    { toContainsZero := ?_
      toIsStableUnderShift := inferInstance
      toIsTriangulatedClosed₂ := inferInstance }
  exact ⟨0, Limits.isZero_zero D, leftDerivedDefinedObjectProperty_zero (F := F) (S := S)⟩

/-- The restricted left-derived functor `LF : 𝓔ₗ[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance leftDerivedDefinedFunctor_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedFunctor F S).CommShift ℤ := by
  -- Proof comment: the restricted left-derived functor inherits the ambient shift compatibility
  -- from the canonical pointwise left-derived shift isomorphisms.
  -- TODO: build the dual `CommShift` structure from `leftDerivedValueShiftIso` and its
  -- naturality with respect to `leftDerivedValueMap`.
  sorry

/-- The restricted left-derived functor `LF : 𝓔ₗ[F, S] ⥤ D'` is exact. -/
instance leftDerivedDefinedFunctor_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedFunctor F S).IsTriangulated := by
  -- Proof comment: once the restricted left-derived functor is equipped with its shift
  -- compatibility, exactness is the dual distinguished-triangle statement from Lemma `13.14.6`.
  -- TODO: package exactness from `leftDerivedDefinedFunctor_commShift` and
  -- `left_derived_triangle_distinguished`.
  sorry

-- Strict fullness is already the owner instance
-- `leftDerivedDefinedObjectProperty_isClosedUnderIsomorphisms` from `Lemma_13_14_5`.

/- Once `leftDerivedDefinedObjectProperty F S` is triangulated, the restricted system `S_𝓔ₗ[F, S]`
inherits `IsCompatibleWithTriangulation` from
`fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation`.
-/

local instance leftDerivedDefinedLocalization_hasZeroObject
    [htriE : (leftDerivedDefinedObjectProperty F S).IsTriangulated]
    [HasLeftCalculusOfFractions (S_𝓔ₗ[F, S])] :
    Limits.HasZeroObject (S_𝓔ₗ[F, S]).Localization := by
  let P := leftDerivedDefinedObjectProperty F S
  letI : P.IsTriangulated := by
    simpa [P] using htriE
  letI : HasLeftCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := by
    simpa [P, leftDerivedDefinedLocalizationSystem] using
      (inferInstance : HasLeftCalculusOfFractions (S_𝓔ₗ[F, S]))
  change Limits.HasZeroObject (fullSubcategoryLocalizationSystem P S).Localization
  infer_instance

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is fully faithful. -/
instance leftDerivedDefinedLocalizationFunctor_full
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).Full := by
  -- Proof comment: this is the left-derived analogue of the localized full-faithfulness clause.
  let hFF :=
    fullSubcategoryLocalizationFunctor_fullyFaithful_of_mem_iff_local
      (S := S) (P := leftDerivedDefinedObjectProperty F S)
      (fun s hs ↦ leftDerivedDefinedObjectProperty_iff_of_mem (F := F) (S := S) s hs)
  exact hFF.full

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is faithful. -/
instance leftDerivedDefinedLocalizationFunctor_faithful
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).Faithful := by
  -- Proof comment: faithfulness is the dual half of the same localized inclusion statement.
  let hFF :=
    fullSubcategoryLocalizationFunctor_fullyFaithful_of_mem_iff_local
      (S := S) (P := leftDerivedDefinedObjectProperty F S)
      (fun s hs ↦ leftDerivedDefinedObjectProperty_iff_of_mem (F := F) (S := S) s hs)
  exact hFF.faithful

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` commutes with shifts. -/
noncomputable instance leftDerivedDefinedLocalizationFunctor_commShift
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (leftDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).CommShift ℤ := by
  -- Proof comment: this is the canonical shift-commuting structure on the localized inclusion
  -- from Lemma `13.5.8`, specialized to the left-derived domain object property.
  let P := leftDerivedDefinedObjectProperty F S
  let F' : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy F' := by
    intro X Y f hf
    exact Localization.inverts S.Q S _ hf
  -- Proof comment: again treat the localized inclusion as the canonical localization lift of
  -- `P.ι ⋙ S.Q`.
  simpa [F', fullSubcategoryLocalizationFunctor] using
    (show (Localization.lift F' hF (fullSubcategoryLocalizationSystem P S).Q).CommShift ℤ from
      inferInstance)

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is exact. -/
noncomputable instance leftDerivedDefinedLocalizationFunctor_isTriangulated
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (leftDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation]
    [HasLeftCalculusOfFractions (S_𝓔ₗ[F, S])] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).IsTriangulated := by
  -- Proof comment: the exactness of the localized inclusion is the dual instance already
  -- available for triangulated full subcategories.
  let P := leftDerivedDefinedObjectProperty F S
  let F' : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy F' := by
    intro X Y f hf
    exact Localization.inverts S.Q S _ hf
  letI : P.IsTriangulated := by
    simpa [P] using htriE
  letI : HasLeftCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := by
    simpa [P, leftDerivedDefinedLocalizationSystem] using
      (inferInstance : HasLeftCalculusOfFractions (S_𝓔ₗ[F, S]))
  -- Proof comment: this is the same exact-factorization step on the left-derived domain.
  simpa [F', fullSubcategoryLocalizationFunctor] using
    (exact_factorization_isTriangulated
      (S := fullSubcategoryLocalizationSystem P S) (F := F') hF)

/-- The localized left-derived functor `LF : S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance leftDerivedLocalizationFactorization_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation]
    [HasLeftCalculusOfFractions (S_𝓔ₗ[F, S])] :
    (leftDerivedLocalizationFactorization F S).CommShift ℤ :=
  Functor.commShiftOfLocalization (S_𝓔ₗ[F, S]).Q (S_𝓔ₗ[F, S]) ℤ
    (leftDerivedDefinedFunctor F S) (leftDerivedLocalizationFactorization F S)

/-- The localized left-derived functor `LF : S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ D'` is exact. -/
instance leftDerivedLocalizationFactorization_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation]
    [HasLeftCalculusOfFractions (S_𝓔ₗ[F, S])] :
    (leftDerivedLocalizationFactorization F S).IsTriangulated := by
  -- Proof comment: once the restricted functor is exact and inverts the restricted system, the
  -- localized factor is exact by the generic localization-factorization theorem.
  simpa [leftDerivedLocalizationFactorization] using
    (exact_factorization_isTriangulated
      (S := S_𝓔ₗ[F, S]) (F := leftDerivedDefinedFunctor F S)
      (leftDerivedDefinedFunctor_isInvertedBy F S))

-- Proof sketch: if `LF` is defined at a biproduct `X ⊞ Y`, Lemma `13.14.7` shows that in a
-- Karoubian target the two direct summands also lie in the domain. This is exactly stability
-- under retracts of the corresponding object property.
/- Left-derived companion recall: if `D'` is Karoubian, then the left-derived-defined object
property is stable under retracts, so `𝓔ₗ[F, S]` is saturated once it is triangulated. -/
recall leftDerivedDefinedObjectProperty_isStableUnderRetracts

end Triangulated

end CategoryTheory
