import StacksProject_2024.Chap08.Lemma_8_4_6.FixedCoverEquivalenceBridge

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open InducedCategory.Hom
open CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackOver J}

/-- Helper for Lemma 8.4.6: the left fixed-cover projection acts objectwise by taking the left
component of each explicit pullback object; on underlying total objects this is definitionally
the left component of the stored pullback object. -/
theorem explicit_two_fibre_product_cover_descent_left_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T).obj D).obj I).1 =
      (((D.obj I).1).obj.fst).1 := by
  -- Forgetting the fiber packaging leaves the definitional left component of the explicit object.
  rfl

/-- Helper for Lemma 8.4.6: the right fixed-cover projection acts objectwise by taking the right
component of each explicit pullback object; on underlying total objects this is definitionally
the right component of the stored pullback object. -/
theorem explicit_two_fibre_product_cover_descent_right_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_right_projection
        (J := J) F G T).obj D).obj I).1 =
      (((D.obj I).1).obj.snd).1 := by
  -- Forgetting the fiber packaging leaves the definitional right component of the explicit object.
  rfl

/-- Helper for Lemma 8.4.6: after taking the left projection and then applying `F`, the
resulting `S`-fiber object on a cover leg has the expected underlying total object. -/
theorem explicit_two_fibre_product_cover_descent_left_composite_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor F) T).obj
      ((explicit_two_fibre_product_cover_descent_left_projection
          (J := J) F G T).obj D)).obj I).1 =
      (FibredCategoryMor.toFunctor (toFibredCategoryMor F)).obj
        (((((D.obj I).1).obj.fst)).1) := by
  -- Forgetting the fiber packaging leaves the expected left leg of the stored explicit pullback
  -- object, now viewed in `S` through the fiber functor of `F`.
  rfl

/-- Helper for Lemma 8.4.6: the structural isomorphism in the categorical pullback of fixed-cover
descent data induces the corresponding component isomorphism on each cover leg. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_hom_inv_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    (Q.iso.hom.hom I) ≫ (Q.iso.inv.hom I) =
      𝟙 ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor F) I.Y).obj (Q.fst.obj I)) := by
  -- Read the component inverse law of `Q.iso` on the fixed cover leg `I`.
  simpa only using congrArg (fun φ ↦ φ.hom I) Q.iso.hom_inv_id

/-- Helper for Lemma 8.4.6: the inverse component of the structural fixed-cover comparison also
satisfies the second inverse law on each cover leg. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_inv_hom_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    (Q.iso.inv.hom I) ≫ (Q.iso.hom.hom I) =
      𝟙 ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor G) I.Y).obj (Q.snd.obj I)) := by
  -- This is the symmetric component inverse law of the categorical-pullback isomorphism.
  simpa only using congrArg (fun φ ↦ φ.hom I) Q.iso.inv_hom_id

/-- Helper for Lemma 8.4.6: the structural comparison in the categorical pullback of fixed-cover
descent data restricts to a literal isomorphism between the `I`-components. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor F) I.Y).obj (Q.fst.obj I)) ≅
      ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor G) I.Y).obj (Q.snd.obj I)) :=
  { hom := Q.iso.hom.hom I
    inv := Q.iso.inv.hom I
    hom_inv_id :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_hom_inv_id
        (J := J) F G T Q I
    inv_hom_id :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_inv_hom_id
        (J := J) F G T Q I }

/-- Helper for Lemma 8.4.6: on each cover leg `I`, an object of the ordinary categorical
pullback of the projected fixed-cover descent-data categories already determines the corresponding
object of the pullback of fibre categories over `I.Y`. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    ((fiberFunctor F I.Y) ⊡ (fiberFunctor G I.Y)) where
  fst := Q.fst.obj I
  snd := Q.snd.obj I
  iso :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
      (J := J) F G T Q I

/-- Helper for Lemma 8.4.6: the Chapter 4 fibre equivalence reconstructs from that componentwise
pullback datum a fibre object of the explicit stack-level `2`-fibre product over the same cover
leg. This is the object part of the source-faithful inverse route. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_leg
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber I.Y :=
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  eI.inverse.obj
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component
      (J := J) F G T Q I)

/-- Helper for Lemma 8.4.6: after choosing a pullback arrow `f : V ⟶ I.Y`, pull back the two
projected legs of `Q` separately and transport the midpoint comparison by the canonical
pullback-comparison isomorphisms for `F` and `G`. This is the named target object for the missing
transport comparison. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    ((fiberFunctor F V) ⊡ (fiberFunctor G V)) where
  fst := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj (Q.fst.obj I)
  snd := ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj (Q.snd.obj I)
  iso :=
    (FibredCategoryMor.pullbackComparison
      (toFibredCategoryMor F) f (Q.fst.obj I)).symm ≪≫
      (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
          (J := J) F G T Q I)) ≪≫
      (FibredCategoryMor.pullbackComparison
        (toFibredCategoryMor G) f (Q.snd.obj I))

/-- Helper for Lemma 8.4.6: the left leg of the named componentwise pullback object is literally
the canonical pullback of the left projected descent component along `f`. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
      (J := J) F G T Q I f).fst =
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj (Q.fst.obj I) := by
  -- Unfold the named componentwise pullback object once; the left leg is definitional.
  simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback]

/-- Helper for Lemma 8.4.6: the right leg of the named componentwise pullback object is literally
the canonical pullback of the right projected descent component along `f`. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
      (J := J) F G T Q I f).snd =
      ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj (Q.snd.obj I) := by
  -- The right leg is fixed by the same one-step unfolding.
  simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback]

/-- Helper for Lemma 8.4.6: the midpoint isomorphism of the named componentwise pullback object
is exactly the comparison obtained by pulling back `Q.iso.app I` and conjugating by the two
pullback-comparison isomorphisms. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
      (J := J) F G T Q I f).iso.hom =
      (FibredCategoryMor.pullbackComparison
        (toFibredCategoryMor F) f (Q.fst.obj I)).inv ≫
        ((((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
            (J := J) F G T Q I)).hom) ≫
        (FibredCategoryMor.pullbackComparison
          (toFibredCategoryMor G) f (Q.snd.obj I)).hom := by
  -- Expand the midpoint field once so later transport lemmas can rewrite to this literal shell.
  rfl

/-- Helper for Lemma 8.4.6: applying the forward fibre equivalence back to the reconstructed leg
recovers the original componentwise pullback datum. This freezes the object reconstruction and
isolates the remaining overlap-transport step. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).functor.obj
      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I)) ≅
      explicit_two_fibre_product_cover_descent_pullback_inverse_component
        (J := J) F G T Q I :=
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  eI.counitIso.app
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component
      (J := J) F G T Q I)

/-- Helper for Lemma 8.4.6: a morphism in the fixed-cover categorical pullback induces the
corresponding componentwise morphism between the owner-side pullback-of-fibres objects over a
cover leg `I`. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component
      (J := J) F G T Q₁ I) ⟶
      (explicit_two_fibre_product_cover_descent_pullback_inverse_component
        (J := J) F G T Q₂ I) :=
  ⟨φ.fst.hom I, φ.snd.hom I, by
    -- Read the pullback compatibility of `φ` on the fixed cover leg `I`.
    simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_component,
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso] using
      congrArg (fun α ↦ α.hom I) φ.w⟩

/-- Helper for Lemma 8.4.6: the first projection of the owner-side component map is literally the
left component of the fixed-cover pullback morphism. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
      (J := J) F G T φ I).fst =
      φ.fst.hom I := by
  -- Unfold the packaged owner-side component map once and read off its left projection.
  rfl

/-- Helper for Lemma 8.4.6: the second projection of the owner-side component map is literally the
right component of the fixed-cover pullback morphism. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
      (J := J) F G T φ I).snd =
      φ.snd.hom I := by
  -- The right projection is equally definitional after unfolding the owner-side map.
  rfl

/-- Helper for Lemma 8.4.6: the owner-side component map preserves identities on each cover leg,
so the later inverse functor can inherit `map_id` componentwise from the fibre equivalence. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T (𝟙 Q) I =
      𝟙 _ := by
  -- Identity in the categorical pullback is componentwise identity on the two projected descent
  -- data, so the owner-side component map is also componentwise identity.
  apply CategoricalPullback.hom_ext
  · rfl
  · rfl

/-- Helper for Lemma 8.4.6: the owner-side component map preserves composition on each cover leg,
again reducing the later inverse-functor composition law to the owner equivalence functoriality. -/
theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_comp
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ Q₃ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (ψ : Q₂ ⟶ Q₃) (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T (φ ≫ ψ) I =
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
          (J := J) F G T φ I ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
          (J := J) F G T ψ I := by
  -- Composition in the categorical pullback is computed componentwise on the two projected
  -- descent-data morphisms.
  apply CategoricalPullback.hom_ext
  · rfl
  · rfl

/-- Helper for Lemma 8.4.6: transport the owner-side component map back through the Chapter 4
fibre equivalence over `I.Y`. This is the legwise map used by the missing inverse functor. -/
noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q₁ I) ⟶
      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q₂ I) :=
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  eI.inverse.map
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
      (J := J) F G T φ I)

end CategoryTheory
