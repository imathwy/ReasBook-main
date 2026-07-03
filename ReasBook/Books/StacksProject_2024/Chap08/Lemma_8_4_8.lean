import stacks_project.Chap04.Definition_4_32_1
import stacks_project.Chap04.Definition_4_33_9
import stacks_project.Chap04.Lemma_4_35_9
import stacks_project.Chap08.Definition_8_4_5
import stacks_project.Chap08.Lemma_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open InducedCategory.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver J}

section

variable {Xf Yf : FibredCategoryOver C}

attribute [local instance] FibredCategoryOver.isFibred

namespace FibredCategoryMor

/-- Helper for Lemma 8.4.8: a morphism of fibred categories carries a strongly cartesian lift
over `f` to a strongly cartesian lift over the same base arrow in the target. -/
theorem map_stronglyCartesian_of_lift
    (F : Xf ⟶ Yf) {a b : Xf.S} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : Xf.p.IsStronglyCartesian f φ) :
    Yf.p.IsStronglyCartesian f (F.toHom.map φ) := by
  -- Normalize the source lift to the projected base arrow before invoking the owner API.
  letI : Xf.p.IsHomLift f φ := hφ.toIsHomLift
  have hφ' : Xf.p.IsStronglyCartesian (Xf.p.map φ) φ := by
    subst_hom_lift Xf.p f φ
    simpa using hφ
  letI : Yf.p.IsHomLift f (F.toHom.map φ) := by
    infer_instance
  have hY :
      Yf.p.IsStronglyCartesian (Yf.p.map (F.toHom.map φ)) (F.toHom.map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  -- Transport the target statement back to the original base arrow `f`.
  subst_hom_lift Yf.p f (F.toHom.map φ)
  exact hY

/-- Helper for Lemma 8.4.8: a morphism of fibred categories admits the canonical comparison
isomorphism between pulling back after mapping and mapping after pulling back. -/
theorem pullbackComparison_exists
    (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    ∃ e :
      f ^*[canonicalPullbackChoice Yf.p] ((F.toHom).fiberFunctor U).obj x ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice Xf.p] x),
      e.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
        (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) := by
  let hcX := canonicalPullbackChoice Xf.p
  let hcY := canonicalPullbackChoice Yf.p
  let φ :
      (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    F.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    hcY.map f (((F.toHom).fiberFunctor U).obj x)
  have hφ : Yf.p.IsStronglyCartesian f φ :=
    FibredCategoryMor.map_stronglyCartesian_of_lift F f (hcX.map f x)
      (hcX.isStronglyCartesian f x)
  have hψ : Yf.p.IsStronglyCartesian f ψ :=
    hcY.isStronglyCartesian f (((F.toHom).fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ≅
        (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso Yf.p hf φ ψ
  letI : Yf.p.IsHomLift (𝟙 V) e.hom := by
    -- The comparison hom lies over the identity of the pullback base.
    change Yf.p.IsHomLift (Iso.refl V).hom e.hom
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift Yf.p hf φ ψ
  letI : Yf.p.IsHomLift (𝟙 V) e.inv := by
    -- The inverse component is vertical for the same reason.
    change Yf.p.IsHomLift (Iso.refl V).inv e.inv
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift Yf.p hf φ ψ
  let ehom :
      f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) ⟶
        ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) :=
    Functor.Fiber.homMk Yf.p V e.hom
  let einv :
      ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) ⟶
        f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) :=
    Functor.Fiber.homMk Yf.p V e.inv
  have hhom_inv : ehom ≫ einv = 𝟙 _ := by
    -- Forget the fiber packaging and use the inverse law of the owner comparison iso.
    apply Functor.Fiber.hom_ext
    change e.hom ≫ e.inv = 𝟙 _
    exact e.hom_inv_id
  have hinv_hom : einv ≫ ehom = 𝟙 _ := by
    -- The second inverse law is identical after forgetting the fiber wrapper.
    apply Functor.Fiber.hom_ext
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id
  let eFiber :
      f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) :=
    { hom := ehom
      inv := einv
      hom_inv_id := hhom_inv
      inv_hom_id := hinv_hom }
  refine ⟨eFiber, ?_⟩
  -- Read off the defining factorization identity from the owner comparison construction.
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso Yf.p hf φ ψ).hom ≫ φ = ψ
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac Yf.p f φ hf ψ

/-- Helper for Lemma 8.4.8: the chosen canonical comparison identifies the pullback of `F(x)`
with the image under `F` of the chosen pullback of `x`. -/
noncomputable def pullbackComparison
    (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    f ^*[canonicalPullbackChoice Yf.p] ((F.toHom).fiberFunctor U).obj x ≅
      ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice Xf.p] x) :=
  Classical.choose (pullbackComparison_exists F f x)

/-- Helper for Lemma 8.4.8: postcomposing the hom part of the pullback-comparison isomorphism
with the image of the chosen source pullback arrow recovers the chosen target pullback arrow. -/
theorem pullbackComparison_hom_postcompose
    (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    (pullbackComparison F f x).hom.1 ≫
        F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
      (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) := by
  -- Unfold the chosen comparison only to expose the factorization identity proved above.
  change (Classical.choose (pullbackComparison_exists F f x)).hom.1 ≫
      F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
    (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x)
  exact Classical.choose_spec (pullbackComparison_exists F f x)

end FibredCategoryMor

end

/-- Helper for Lemma 8.4.8: use the canonical pullback system on a fibred projection so the local
essential-image condition can be stated with an explicit pullback choice. -/
private noncomputable abbrev localCanonicalPullbackChoice
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered] :
    PullbackChoice p :=
  let _ : HasFibers p := HasFibers.canonical p
  canonicalPullbackChoice p

/-- Helper for Lemma 8.4.8: a fully faithful morphism of stacks induces fully faithful functors on
every fiber. -/
private theorem fiber_functor_fullyFaithful_of_fullyFaithful
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful) :
    ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := by
  -- Restrict the ambient fully faithful morphism to each fiber by the Chapter 4 fiberwise
  -- criterion for morphisms of fibred categories.
  simpa using
    (FibredCategoryMor.fullyFaithful_iff_fiberwise
      (F := toFibredCategoryMor F)).1 hff

/-- Helper for Lemma 8.4.8: fiberwise equivalences already imply that the underlying functor on
total categories is an equivalence. -/
private theorem total_functor_isEquivalence_of_fiberwise_isEquivalence
    (F : X ⟶ Y)
    (hFiber : ∀ U : C, (fiberFunctor F U).IsEquivalence) :
    (G F).IsEquivalence := by
  have hFiberFullyFaithful :
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := by
    intro U
    let _ : (fiberFunctor F U).IsEquivalence := hFiber U
    exact ⟨Functor.FullyFaithful.ofFullyFaithful (fiberFunctor F U)⟩
  have hGlobalFullyFaithful :
      Nonempty (toBasedFunctor F).FullyFaithful :=
    (FibredCategoryMor.fullyFaithful_iff_fiberwise
      (F := toFibredCategoryMor F)).2 hFiberFullyFaithful
  have hBij :
      ∀ a b : X.S, Function.Bijective
        ((G F).map : (a ⟶ b) → ((G F).obj a ⟶ (G F).obj b)) := by
    rcases hGlobalFullyFaithful with ⟨hFF⟩
    intro a b
    -- Restrict the global full faithfulness statement to the underlying total functor.
    change Function.Bijective
      ((toBasedFunctor F).toFunctor.map :
        (a ⟶ b) → ((toBasedFunctor F).toFunctor.obj a ⟶ (toBasedFunctor F).toFunctor.obj b))
    exact hFF.map_bijective a b
  have hEss : (G F).EssSurj := by
    refine ⟨?_⟩
    intro y
    let FI := fiberFunctor F (Y.p.obj y)
    have hFI : FI.IsEquivalence := hFiber (Y.p.obj y)
    let _ : FI.IsEquivalence := hFI
    let _ : FI.EssSurj := by infer_instance
    -- Choose a preimage in the fiber containing `y`, then forget back to the total category.
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (F := FI) ⟨y, rfl⟩
    refine ⟨x.1, ?_⟩
    change Nonempty ((G F).obj x.1 ≅ y)
    exact
      ⟨(Functor.Fiber.fiberInclusion : Y.p.Fiber (Y.p.obj y) ⥤ Y.S).mapIso e⟩
  -- Combine total full faithfulness and total essential surjectivity.
  exact
    (Functor.isEquivalence_iff_full_faithful_essSurj (G F)).2
      ⟨hBij, hEss⟩

/-- Helper for Lemma 8.4.8: a fiberwise equivalence picks, for every target object in the fiber
over `U`, a source object in the same fiber whose image is isomorphic to it. -/
private theorem fiber_preimage_of_fiberwise_isEquivalence
    (F : X ⟶ Y)
    (hFiber : ∀ U : C, (fiberFunctor F U).IsEquivalence)
    (U : C) (y : Y.p.Fiber U) :
    ∃ x : X.p.Fiber U, Nonempty (y ≅ (fiberFunctor F U).obj x) := by
  letI : (fiberFunctor F U).IsEquivalence := hFiber U
  -- Use the canonical preimage object supplied by the fiber equivalence.
  refine ⟨(fiberFunctor F U).objPreimage y, ?_⟩
  exact ⟨((fiberFunctor F U).objObjPreimageIso y).symm⟩

/-- Helper for Lemma 8.4.8: cancel a transport pair on the left of a morphism in the base
category. -/
private theorem eqToHom_symm_comp_eqToHom_assoc
    {A B D : C} (h : A = B) (f : B ⟶ D) :
    eqToHom h.symm ≫ (eqToHom h ≫ f) = f := by
  -- Reduce the transport equality to reflexivity so both `eqToHom` factors become identities.
  cases h
  simp

/-- Helper for Lemma 8.4.8: cancel a transport pair on the right of a morphism in the base
category. -/
private theorem comp_eqToHom_symm_assoc_eqToHom
    {A B D : C} (f : A ⟶ B) (h : D = B) :
    (f ≫ eqToHom h.symm) ≫ eqToHom h = f := by
  -- The right-hand transport pair collapses after reducing the equality witness to reflexivity.
  cases h
  simp

/-- Helper for Lemma 8.4.8: the residual base transport coming from the identity functor object
equation is the identity morphism. -/
private theorem identity_functor_object_transport_eq_id
    {U : C} (q : U = U) :
    eqToHom q = 𝟙 U := by
  -- Equality proofs of an object with itself are propositionally irrelevant, so the induced
  -- transport morphism is definitionally the identity after reducing to reflexivity.
  cases q
  rfl

/-- Helper for Lemma 8.4.8: an objectwise lift whose comparison with the identity is vertical in
each fiber already commutes strictly with the base projections. -/
private theorem same_fiber_lift_commutes_with_base_transport
    (F : X ⟶ Y)
    {j : Y.S ⥤ X.S} (α : 𝟭 Y.S ≅ j ⋙ G F)
    (hjBaseObj : ∀ y : Y.S, X.p.obj (j.obj y) = Y.p.obj y)
    (hαLift : ∀ y : Y.S, Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.hom.app y)) :
    ∀ {y y'} (g : y ⟶ y'),
      X.p.map (j.map g) =
        eqToHom (hjBaseObj y) ≫ Y.p.map g ≫ eqToHom (hjBaseObj y').symm := by
  -- Route correction: the remaining blocker is exactly the owner-surface normalization of the
  -- extra left `eqToHom` in `IsHomLift.fac'`. The new helper
  -- `identity_functor_object_transport_eq_id` isolates that normalization, after which the
  -- Chapter 4 `hyVert`/`hleft`/`hcomm` calculation should port directly.
  intro y y' g
  let hyEq := Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)) (hjBaseObj y)
  let hy'Eq := Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) (hjBaseObj y')
  have hyBase :
      IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj y)) (α.hom.app y) =
        hyEq := by
    apply Subsingleton.elim
  have hyDom :
      IsHomLift.domain_eq Y.p (𝟙 (Y.p.obj y)) (α.hom.app y) = rfl := by
    apply Subsingleton.elim
  have hy'Base :
      IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj y')) (α.hom.app y') =
        hy'Eq := by
    apply Subsingleton.elim
  have hy'Dom :
      IsHomLift.domain_eq Y.p (𝟙 (Y.p.obj y')) (α.hom.app y') = rfl := by
    apply Subsingleton.elim
  have hyVert :
      Y.p.map (α.hom.app y) = eqToHom hyEq.symm := by
    -- Rewrite the base arrow of the vertical comparison `α.hom.app y` to the concrete
    -- object-equality used by the lift packaging.
    have hfac := IsHomLift.fac' Y.p (𝟙 (Y.p.obj y)) (α.hom.app y)
    rw [hyDom, hyBase] at hfac
    calc
      Y.p.map (α.hom.app y) = eqToHom rfl ≫ eqToHom hyEq.symm := by
        simpa only [Category.id_comp] using hfac
      _ = eqToHom hyEq.symm := by
        rw [identity_functor_object_transport_eq_id (q := rfl)]
        exact Category.id_comp _
  have hy'Vert :
      Y.p.map (α.hom.app y') = eqToHom hy'Eq.symm := by
    -- The codomain transport for `y'` is normalized in the same way.
    have hfac := IsHomLift.fac' Y.p (𝟙 (Y.p.obj y')) (α.hom.app y')
    rw [hy'Dom, hy'Base] at hfac
    calc
      Y.p.map (α.hom.app y') = eqToHom rfl ≫ eqToHom hy'Eq.symm := by
        simpa only [Category.id_comp] using hfac
      _ = eqToHom hy'Eq.symm := by
        rw [identity_functor_object_transport_eq_id (q := rfl)]
        exact Category.id_comp _
  have hnat := congrArg (Functor.map Y.p) (α.hom.naturality g)
  rw [Functor.map_comp, Functor.map_comp, hyVert, hy'Vert] at hnat
  have hleft :
      eqToHom hyEq ≫ Y.p.map g ≫ eqToHom hy'Eq.symm =
      Y.p.map ((G F).map (j.map g)) := by
    -- Naturality becomes the desired base equality once the left vertical comparison is moved
    -- across by composition with the inverse transport.
    have h0 :
        Y.p.map g ≫ eqToHom hy'Eq.symm =
          eqToHom hyEq.symm ≫
            Y.p.map ((G F).map (j.map g)) := by
      simpa only [Functor.comp_map, Functor.id_map] using hnat
    have h1 := congrArg
      (fun k ↦ eqToHom hyEq ≫ k)
      h0
    have h1' :
        eqToHom hyEq ≫ Y.p.map g ≫ eqToHom hy'Eq.symm =
          eqToHom hyEq ≫ eqToHom hyEq.symm ≫ Y.p.map ((G F).map (j.map g)) := by
      simpa only [Category.assoc] using h1
    have hcancel :
        eqToHom hyEq ≫ eqToHom hyEq.symm =
          𝟙 (Y.p.obj ((G F).obj (j.obj y))) := by
      rw [eqToHom_trans]
      exact identity_functor_object_transport_eq_id (Eq.trans hyEq hyEq.symm)
    calc
      eqToHom hyEq ≫ Y.p.map g ≫ eqToHom hy'Eq.symm =
          eqToHom hyEq ≫ eqToHom hyEq.symm ≫ Y.p.map ((G F).map (j.map g)) := h1'
      _ = Y.p.map ((G F).map (j.map g)) := by
        rw [← Category.assoc, hcancel, Category.id_comp]
  have hcomm :
      X.p.map (j.map g) =
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
          Y.p.map ((G F).map (j.map g)) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := by
    -- Rewrite the image of `j.map g` under `F` using the defining over-base compatibility of
    -- the stack morphism itself.
    have hcomm' :
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
            Y.p.map ((G F).map (j.map g)) ≫
              eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) =
          X.p.map (j.map g) := by
      calc
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
            Y.p.map ((G F).map (j.map g)) ≫
              eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) =
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
              (eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)) ≫
                X.p.map (j.map g) ≫
                  eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')).symm) ≫
                eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := by
              change
                eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
                    Y.toFibredCategoryOver.toBasedCategory.p.map ((toBasedFunctor F).map (j.map g)) ≫
                      eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) =
                  eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
                    (eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)) ≫
                      X.toFibredCategoryOver.toBasedCategory.p.map (j.map g) ≫
                        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')).symm) ≫
                      eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y'))
              exact
                congrArg
                  (fun k ↦
                    eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
                      k ≫
                        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')))
                  (Functor.congr_hom (toBasedFunctor F).w (j.map g))
        _ = X.p.map (j.map g) := by
              calc
                eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
                    (eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)) ≫
                      X.p.map (j.map g) ≫
                        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')).symm) ≫
                    eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) =
                  (eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
                      eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)) ≫
                        X.p.map (j.map g) ≫
                          eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')).symm) ≫
                    eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := by
                        repeat rw [Category.assoc]
                _ = (X.p.map (j.map g) ≫
                    eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')).symm) ≫
                      eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := by
                        rw [eqToHom_symm_comp_eqToHom_assoc
                          (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y))
                          (X.p.map (j.map g) ≫
                            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')).symm)]
                _ = X.p.map (j.map g) := by
                      exact
                        comp_eqToHom_symm_assoc_eqToHom
                          (X.p.map (j.map g))
                          (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y'))
    exact hcomm'.symm
  have hleftTransport :
      eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫ eqToHom hyEq =
        eqToHom (hjBaseObj y) := by
    have hEq :
        Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm hyEq =
          hjBaseObj y := by
      apply Subsingleton.elim
    rw [eqToHom_trans, hEq]
  have hrightTransport :
      eqToHom hy'Eq.symm ≫ eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) =
        eqToHom (hjBaseObj y').symm := by
    have hEq :
        Eq.trans hy'Eq.symm (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) =
          (hjBaseObj y').symm := by
      apply Subsingleton.elim
    rw [eqToHom_trans, hEq]
  calc
    X.p.map (j.map g) =
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
          Y.p.map ((G F).map (j.map g)) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := hcomm
    _ =
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
          (eqToHom hyEq ≫ Y.p.map g ≫ eqToHom hy'Eq.symm) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := by
          have h' := congrArg
            (fun k ↦
              eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
                k ≫
                  eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')))
            hleft
          simpa only [Category.assoc] using h'.symm
    _ =
        (eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
            eqToHom hyEq) ≫
          Y.p.map g ≫
            (eqToHom hy'Eq.symm ≫
              eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y'))) := by
          repeat rw [Category.assoc]
    _ = eqToHom (hjBaseObj y) ≫ Y.p.map g ≫ eqToHom (hjBaseObj y').symm := by
      -- Each residual transport pair collapses to the identity transport on the common base
      -- object, which is then rewritten away by the dedicated normalization lemma.
      rw [hleftTransport, hrightTransport]

/-- Helper for Lemma 8.4.8: an objectwise lift whose comparison with the identity is vertical in
each fiber already commutes strictly with the base projections. -/
private theorem same_fiber_lift_commutes_with_base
    (F : X ⟶ Y)
    {j : Y.S ⥤ X.S} (α : 𝟭 Y.S ≅ j ⋙ G F)
    (hjBaseObj : ∀ y : Y.S, X.p.obj (j.obj y) = Y.p.obj y)
    (hαLift : ∀ y : Y.S, Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.hom.app y)) :
    j ⋙ X.p = Y.p := by
  -- Compare the two projection functors objectwise, then delegate the morphism computation to
  -- the transport-normalized base-map lemma proved just above.
  refine CategoryTheory.Functor.ext hjBaseObj ?_
  intro y y' g
  exact same_fiber_lift_commutes_with_base_transport
    (F := F) α hjBaseObj hαLift g

/-- Helper for Lemma 8.4.8: once every fiber functor is an equivalence, the stack morphism is an
equivalence over the base. -/
private theorem isEquivalenceOverBase_of_fiberwise_isEquivalence
    (F : X ⟶ Y)
    (hFiber : ∀ U : C, (fiberFunctor F U).IsEquivalence) :
    IsEquivalenceOverBase F := by
  classical
  change BasedFunctor.IsEquivalenceOverBase (toBasedFunctor F)
  -- Route correction: the packaging step is the Chapter 4 based quasi-inverse argument, now with
  -- the `StackOver` base-commutation proof stabilized by `same_fiber_lift_commutes_with_base`.
  let jFiber : ∀ y : Y.S, X.p.Fiber (Y.p.obj y) :=
    fun y ↦
      Classical.choose
        (fiber_preimage_of_fiberwise_isEquivalence (F := F) hFiber (Y.p.obj y) ⟨y, rfl⟩)
  let iFiber :
      ∀ y : Y.S, ⟨y, rfl⟩ ≅ (fiberFunctor F (Y.p.obj y)).obj (jFiber y) :=
    fun y ↦
      Classical.choice
        (Classical.choose_spec
          (fiber_preimage_of_fiberwise_isEquivalence (F := F) hFiber (Y.p.obj y) ⟨y, rfl⟩))
  let jObj : Y.S → X.S := fun y ↦ (jFiber y).1
  let i : ∀ y : Y.S, y ≅ (G F).obj (jObj y) := fun y ↦ by
    simpa [jObj, G, fiberFunctor] using
      (Functor.Fiber.fiberInclusion : Y.p.Fiber (Y.p.obj y) ⥤ Y.S).mapIso (iFiber y)
  have hFiberFullyFaithful :
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := by
    intro U
    let _ : (fiberFunctor F U).IsEquivalence := hFiber U
    exact ⟨Functor.FullyFaithful.ofFullyFaithful (fiberFunctor F U)⟩
  have hGlobalFullyFaithful :
      Nonempty (toBasedFunctor F).FullyFaithful :=
    (FibredCategoryMor.fullyFaithful_iff_fiberwise
      (F := toFibredCategoryMor F)).2 hFiberFullyFaithful
  let hFF : (toBasedFunctor F).FullyFaithful := Classical.choice hGlobalFullyFaithful
  letI : (G F).Faithful := by
    refine ⟨?_⟩
    intro a b φ ψ hφψ
    exact hFF.map_injective hφψ
  letI : (G F).Full := by
    refine ⟨?_⟩
    intro a b φ
    refine ⟨hFF.preimage φ, ?_⟩
    exact hFF.map_preimage φ
  rcases (Functor.fully_faithful_objwise_iso_existsUnique_lift (F := G F) jObj i) with
    ⟨j, ⟨hjObj, α, hα⟩, _⟩
  have hjBaseObj : ∀ y : Y.S, X.p.obj (j.obj y) = Y.p.obj y := by
    intro y
    rw [hjObj y]
    exact (jFiber y).2
  have hαLift : ∀ y : Y.S, Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.hom.app y) := by
    intro y
    have hiLift : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (i y).hom := by
      simpa [i] using
        (show Y.p.IsHomLift (𝟙 (Y.p.obj y)) (iFiber y).hom.1 from (iFiber y).hom.2)
    simpa [hα y, hjObj y] using hiLift
  have hjBase : j ⋙ X.p = Y.p :=
    same_fiber_lift_commutes_with_base (F := F) α hjBaseObj hαLift
  let jBased : Y.toBasedCategory ⥤ᵇ X.toBasedCategory :=
    { toFunctor := j
      w := hjBase }
  have hCounitLift : ∀ y : Y.S, Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.inv.app y) := by
    intro y
    letI : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.app y).hom := by simpa using hαLift y
    have : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.app y).inv := by infer_instance
    simpa using this
  have eps : BasedFunctor.comp jBased (toBasedFunctor F) ≅ BasedFunctor.id Y.toBasedCategory := by
    simpa [jBased] using BasedNatIso.mkNatIso α.symm hCounitLift
  let compIso : (𝟭 X.S) ⋙ G F ≅ ((G F) ⋙ j) ⋙ G F :=
    (Functor.leftUnitor (G F)).symm ≪≫
      (Functor.rightUnitor (G F)).symm ≪≫
      Functor.isoWhiskerLeft (G F) α ≪≫
      (Functor.associator (G F) j (G F)).symm
  let ηNat : 𝟭 X.S ≅ (G F) ⋙ j :=
    Functor.fullyFaithfulCancelRight (G F) compIso
  have hηLift : ∀ x : X.S, X.p.IsHomLift (𝟙 (X.p.obj x)) (ηNat.hom.app x) := by
    intro x
    have hcompRaw :
        Y.p.IsHomLift (𝟙 (Y.p.obj ((G F).obj x))) (compIso.hom.app x) := by
      -- The whiskered comparison has the same component as `α` after the standard coherence
      -- isomorphisms in `Cat`.
      simpa [compIso, Category.assoc] using hαLift ((G F).obj x)
    have hcomp :
        Y.p.IsHomLift (𝟙 (X.p.obj x)) (compIso.hom.app x) := by
      -- Transport the base identity along the over-base equality of `F` at `x`.
      have :
          Y.p.IsHomLift
            (eqToHom (BasedFunctor.w_obj (toBasedFunctor F) x).symm ≫
              𝟙 (Y.p.obj ((G F).obj x)) ≫
                eqToHom (BasedFunctor.w_obj (toBasedFunctor F) x))
            (compIso.hom.app x) := by
        exact inferInstance
      simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id] using this
    have hmap : Y.p.IsHomLift (𝟙 (X.p.obj x)) ((G F).map (ηNat.hom.app x)) := by
      -- `fullyFaithfulCancelRight` is defined by taking the preimage of the whiskered component.
      simpa [ηNat, Functor.fullyFaithfulCancelRight_hom_app] using hcomp
    exact ((toBasedFunctor F).isHomLift_iff (𝟙 (X.p.obj x)) (ηNat.hom.app x)).1 hmap
  have eta :
      BasedFunctor.id X.toBasedCategory ≅ BasedFunctor.comp (toBasedFunctor F) jBased := by
    simpa [jBased, BasedFunctor.comp_assoc] using BasedNatIso.mkNatIso ηNat hηLift
  exact BasedFunctor.IsEquivalenceOverBase.mkPrime jBased eta eps

/-- Helper for Lemma 8.4.8: for a fixed cover, the canonical descent functor of a stack is an
equivalence. -/
private theorem canonical_descent_functor_isEquivalence
    (S : StackOver J) {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor S.p).toDescentData
      (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  -- Reuse Lemma `8.4.2` directly on the chosen cover rather than rebuilding the stack condition
  -- for this family by hand.
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := S.p)).1 inferInstance U T

/-- Helper for Lemma 8.4.8: on one fixed cover, transport one overlap morphism in `X` to the
corresponding overlap morphism in `Y` by conjugating with the pullback-comparison isomorphisms of
the stack morphism. -/
private noncomputable abbrev local_cover_descent_data_functor_hom
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.obj
        ((fiberFunctor F I₁.Y).obj (D.obj I₁))) ⟶
      (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.obj
        ((fiberFunctor F I₂.Y).obj (D.obj I₂))) :=
  (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (D.obj I₁)).hom ≫
    (fiberFunctor F V).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (D.obj I₂)).inv

/-- Helper for Lemma 8.4.8: the transported self-overlap morphism is the identity after the
middle source map is rewritten to the identity. -/
private theorem local_cover_descent_data_functor_hom_self_map_id
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I : T.Arrow} (g : V ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    (fiberFunctor F V).map (D.hom q g g hg hg) =
      𝟙
        ((fiberFunctor F V).obj
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.obj
            (D.obj I))) := by
  -- Rewrite the source self-overlap relation before mapping through the fiber functor.
  calc
    (fiberFunctor F V).map (D.hom q g g hg hg) =
      (fiberFunctor F V).map
        (𝟙
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.obj
            (D.obj I))) := by
          rw [D.hom_self q g hg]
    _ =
      𝟙
        ((fiberFunctor F V).obj
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.obj
            (D.obj I))) := by
          exact (fiberFunctor F V).map_id _

/-- Helper for Lemma 8.4.8: transporting a self-overlap morphism along `F` gives the identity in
the target descent datum. -/
private theorem local_cover_descent_data_functor_hom_self
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I : T.Arrow} (g : V ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    local_cover_descent_data_functor_hom (F := F) T D q g g hg hg = 𝟙 _ := by
  let e := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g (D.obj I)
  -- Route correction: normalize to the literal comparison-conjugated identity before cancelling
  -- the comparison isomorphism.
  calc
    local_cover_descent_data_functor_hom (F := F) T D q g g hg hg =
      e.hom ≫ (fiberFunctor F V).map (D.hom q g g hg hg) ≫ e.inv := by
        rfl
    _ =
      e.hom ≫
        𝟙
          ((fiberFunctor F V).obj
            (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.obj
              (D.obj I))) ≫
        e.inv := by
          exact
            congrArg
              (fun k ↦ e.hom ≫ k ≫ e.inv)
              (local_cover_descent_data_functor_hom_self_map_id
                (F := F) T D q g hg)
    _ = 𝟙 _ := by
      convert (congrArg (fun k ↦ k ≫ e.inv) (Category.comp_id e.hom)).trans e.hom_inv_id
      · simp only [Category.comp_id]
      · convert Category.id_comp e.inv

/-- Helper for Lemma 8.4.8: transporting the cocycle relation in `X` through the
pullback-comparison shells gives the corresponding cocycle relation in `Y`. -/
private theorem local_cover_descent_data_functor_hom_comp
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    local_cover_descent_data_functor_hom (F := F) T D q f₁ f₂ hf₁ hf₂ ≫
      local_cover_descent_data_functor_hom (F := F) T D q f₂ f₃ hf₂ hf₃ =
      local_cover_descent_data_functor_hom (F := F) T D q f₁ f₃ hf₁ hf₃ := by
  let FY := fiberFunctor F V
  let e₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (D.obj I₂)
  let e₃ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (D.obj I₃)
  let d₁₂ := D.hom q f₁ f₂ hf₁ hf₂
  let d₂₃ := D.hom q f₂ f₃ hf₂ hf₃
  let d₁₃ := D.hom q f₁ f₃ hf₁ hf₃
  -- Reassociate to the common comparison-conjugated normal form before invoking the source
  -- cocycle relation.
  have hnormalize :
      local_cover_descent_data_functor_hom (F := F) T D q f₁ f₂ hf₁ hf₂ ≫
          local_cover_descent_data_functor_hom (F := F) T D q f₂ f₃ hf₂ hf₃ =
        e₁.hom ≫ FY.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ FY.map d₂₃ ≫ e₃.inv := by
    change ((e₁.hom ≫ FY.map d₁₂ ≫ e₂.inv) ≫ (e₂.hom ≫ FY.map d₂₃ ≫ e₃.inv)) =
      e₁.hom ≫ FY.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ FY.map d₂₃ ≫ e₃.inv
    simp only [Category.assoc]
  have hassoc_cancel :
      e₁.hom ≫ FY.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ FY.map d₂₃ ≫ e₃.inv =
        ((e₁.hom ≫ FY.map d₁₂) ≫ (e₂.inv ≫ e₂.hom)) ≫ FY.map d₂₃ ≫ e₃.inv := by
    simp only [Category.assoc]
  have hcancel₁ :
      ((e₁.hom ≫ FY.map d₁₂) ≫ (e₂.inv ≫ e₂.hom)) ≫ FY.map d₂₃ ≫ e₃.inv =
        ((e₁.hom ≫ FY.map d₁₂) ≫ 𝟙 _) ≫ FY.map d₂₃ ≫ e₃.inv := by
    simpa only [FY] using
      congrArg
        (fun k ↦ ((e₁.hom ≫ FY.map d₁₂) ≫ k) ≫ FY.map d₂₃ ≫ e₃.inv)
        e₂.inv_hom_id
  have hcancel₂ :
      ((e₁.hom ≫ FY.map d₁₂) ≫ 𝟙 _) ≫ FY.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ FY.map d₁₂ ≫ FY.map d₂₃ ≫ e₃.inv := by
    simp only [Category.id_comp, Category.assoc]
  have hcancel :
      e₁.hom ≫ FY.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ FY.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ FY.map d₁₂ ≫ FY.map d₂₃ ≫ e₃.inv := by
    exact hassoc_cancel.trans (hcancel₁.trans hcancel₂)
  have hmap_comp :
      FY.map d₁₂ ≫ FY.map d₂₃ = FY.map d₁₃ := by
    -- First map the source cocycle equation, then normalize the resulting functorial composite.
    have hmap_raw := congrArg FY.map (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
    rw [← Functor.map_comp]
    exact hmap_raw
  have hassoc_map :
      e₁.hom ≫ FY.map d₁₂ ≫ FY.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ (FY.map d₁₂ ≫ FY.map d₂₃) ≫ e₃.inv := by
    simp only [Category.assoc]
  have hmap :
      e₁.hom ≫ (FY.map d₁₂ ≫ FY.map d₂₃) ≫ e₃.inv =
        e₁.hom ≫ FY.map d₁₃ ≫ e₃.inv := by
    exact congrArg (fun k ↦ e₁.hom ≫ k ≫ e₃.inv) hmap_comp
  have hfinal :
      e₁.hom ≫ FY.map d₁₃ ≫ e₃.inv =
        local_cover_descent_data_functor_hom (F := F) T D q f₁ f₃ hf₁ hf₃ := by
    rfl
  exact hnormalize.trans (hcancel.trans (hassoc_map.trans (hmap.trans hfinal)))

/-- Helper for Lemma 8.4.8: the owner-level pullback functor factors a vertical morphism through
the chosen pullback arrow. This local copy is placed before the comparison naturality proof so the
dependency order in this item-per-file target stays acyclic. -/
private theorem canonical_pullbackFunctor_map_fac_owner
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice p).map f y =
      (canonicalPullbackChoice p).map f x ≫ φ.1 := by
  -- Compare the chosen pullback arrow of `y` with the universal factorization induced by `φ`.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f x) :=
    (canonicalPullbackChoice p).isStronglyCartesian f x
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x) := hpull.toIsHomLift
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f ((canonicalPullbackChoice p).map f x) U φ.1
  letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f y) :=
    (canonicalPullbackChoice p).isStronglyCartesian f y
  change
      Functor.IsStronglyCartesian.map p f ((canonicalPullbackChoice p).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice p).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice p).map f y =
        (canonicalPullbackChoice p).map f x ≫ φ.1
  exact
    Functor.IsStronglyCartesian.fac p f ((canonicalPullbackChoice p).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice p).map f x ≫ φ.1)

/-- Helper for Lemma 8.4.8: after postcomposing with the chosen target pullback arrow, the mapped
source pullback factorization becomes the target pullback factorization for the image morphism. -/
private theorem map_canonical_pullbackFunctor_map_fac_owner
    {A B : StackOver J} (H : A ⟶ B) {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
        (toFibredCategoryMor H).toHom.map φ.1 =
      (toFibredCategoryMor H).toHom.map
          ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Apply `H` to the source pullback factorization and normalize the mapped composite.
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hfac :
      ((canonicalPullbackChoice A.p).map f x) ≫ φ.1 =
        ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (canonicalPullbackChoice A.p).map f y := by
    exact
      (canonical_pullbackFunctor_map_fac_owner
        (p := A.p) (f := f) (x := x) (y := y) (φ := φ)).symm
  exact congrArg (fun k ↦ (toFibredCategoryMor H).toHom.map k) hfac

/-- Helper for Lemma 8.4.8: after postcomposing both owner-level comparison candidates with the
mapped chosen source pullback arrow, the pullback-comparison square reduces to the standard
pullback factorization identity. -/
private theorem stack_morphism_pullbackComparison_hom_postcompose_eq_owner
    {A B : StackOver J} (H : A ⟶ B) {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ))).1 ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom.1 ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
      ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
          ((fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Compare the two candidates only after postcomposing with the common strongly cartesian
  -- target arrow over `f`.
  let lhs :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ))).1 ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom.1 ≫
      (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ))).1 ≫
      (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj x) ≫
      ((fiberFunctor H U).map φ).1
  let mid₃ :=
    ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
      ((fiberFunctor H U).map φ).1
  let mid₄ :=
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
      ((fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
      (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let rhs :=
    ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
        ((fiberFunctor H V).map
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
      (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  have h₁ : lhs = mid₁ := by
    -- Rewrite the comparison at `y` to the canonical target pullback arrow.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((fiberFunctor H U).map φ))).1 ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom.1 ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
            ((fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj y)
    exact
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
              ((fiberFunctor H U).map φ))).1 ≫ k)
        (FibredCategoryMor.pullbackComparison_hom_postcompose (toFibredCategoryMor H) f y)
  have h₂ : mid₁ = mid₂ := by
    -- Pullback in the target fiber is already natural on the vertical morphism `H.map φ`.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj y) =
        (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj x) ≫
          ((fiberFunctor H U).map φ).1
    exact
      canonical_pullbackFunctor_map_fac_owner
        (p := B.p) (f := f) (φ := (fiberFunctor H U).map φ)
  have h₃ : mid₂ = mid₃ := by
    -- Rewrite the target pullback arrow at `x` back through the comparison isomorphism.
    change
      (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj x) ≫
          ((fiberFunctor H U).map φ).1 =
        (((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
          ((fiberFunctor H U).map φ).1)
    exact
      (congrArg
        (fun k ↦ k ≫ ((fiberFunctor H U).map φ).1)
        (FibredCategoryMor.pullbackComparison_hom_postcompose
          (toFibredCategoryMor H) f x)).symm
  have h₄ : mid₃ = mid₄ := by
    -- Map the source pullback factorization across `H` and reassociate once.
    calc
      (((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
        ((fiberFunctor H U).map φ).1) =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
              ((fiberFunctor H U).map φ).1) := by
            rw [Category.assoc]
      _ =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((toFibredCategoryMor H).toHom.map
                ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
              (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)) := by
            exact
              congrArg
                (fun k ↦
                  (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫ k)
                (map_canonical_pullbackFunctor_map_fac_owner
                  (H := H) (f := f) (φ := φ))
      _ =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
            (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
            rfl
  have h₅ : mid₄ = rhs := by
    -- Reassociate the right-hand composite into the packaged naturality shape.
    change
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
          ((fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.4.8: after forgetting to total categories, the pullback-comparison
isomorphism intertwines pullback of vertical morphisms with the image of the pulled-back source
morphism. -/
private theorem stack_morphism_pullbackComparison_hom_naturality_over_vertical_owner
    {A B : StackOver J} (H : A ⟶ B) {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ))).1 ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom.1 =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
          ((fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 := by
  -- Compare the two ambient arrows after postcomposing with the common strongly cartesian image
  -- of the chosen source pullback arrow.
  let ex := FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x
  let ey := FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y
  let η :
      ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
          ((fiberFunctor H U).obj x) ⟶
        ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
          ((fiberFunctor H U).obj y) :=
    ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((fiberFunctor H U).map φ)
  let θ :
      ((fiberFunctor H V).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)) ⟶
        ((fiberFunctor H V).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) :=
    ((fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ))
  let φH :
      (((fiberFunctor H V).obj (f ^*[canonicalPullbackChoice A.p] y)).1 ⟶
        (((fiberFunctor H U).obj y).1)) :=
    (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  have hφH : B.p.IsStronglyCartesian f φH := by
    -- Transport the chosen source pullback lift across the stack morphism.
    change
      B.p.IsStronglyCartesian f
        ((toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (toFibredCategoryMor H) f
        ((canonicalPullbackChoice A.p).map f y)
        ((canonicalPullbackChoice A.p).isStronglyCartesian f y)
  letI : B.p.IsStronglyCartesian f φH := hφH
  letI : B.p.IsHomLift (𝟙 V) η.1 := by
    exact η.2
  letI : B.p.IsHomLift (𝟙 V) θ.1 := by
    exact θ.2
  letI : B.p.IsHomLift (𝟙 V) ex.hom.1 := by
    exact ex.hom.2
  letI : B.p.IsHomLift (𝟙 V) ey.hom.1 := by
    exact ey.hom.2
  letI : B.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ B.p _ _ _ _ _
      (𝟙 V) η.1 η.2 V ey.hom.1 ey.hom.2
  letI : B.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ B.p _ _ _ _ _
      (𝟙 V) ex.hom.1 ex.hom.2 V θ.1 θ.2
  have hcomp :
      η.1 ≫ ey.hom.1 ≫ φH = (ex.hom.1 ≫ θ.1) ≫ φH := by
    simpa only [η, θ, φH, Category.assoc] using
      stack_morphism_pullbackComparison_hom_postcompose_eq_owner H f φ
  have hηey : B.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by infer_instance
  have hexθ : B.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by infer_instance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ B.p _ _ _ _
      f φH inferInstance _ _ (𝟙 V) (η.1 ≫ ey.hom.1) (ex.hom.1 ≫ θ.1) hηey hexθ <| by
        rw [Category.assoc]
        exact hcomp

/-- Helper for Lemma 8.4.8: the pullback-comparison isomorphism for a stack morphism is fiberwise
natured on vertical morphisms. -/
private theorem stack_morphism_pullbackComparison_naturality_over_vertical
    {A B : StackOver J} (H : A ⟶ B) {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ)) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom ≫
          (fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) := by
  -- Reduce the fiber statement to the owner-level equality above with `Functor.Fiber.hom_ext`.
  apply Functor.Fiber.hom_ext
  exact stack_morphism_pullbackComparison_hom_naturality_over_vertical_owner H f φ

/-- Helper for Lemma 8.4.8: the inverse pullback-comparison isomorphism carries the vertical
naturality square into the conjugation form needed for fixed-cover descent-data transport. -/
private theorem stack_morphism_pullbackComparison_inv_naturality_over_vertical
    {A B : StackOver J} (H : A ⟶ B) {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).inv =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).inv ≫
          (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
            ((fiberFunctor H U).map φ)) := by
  -- Route correction: move the already proved hom-side square across the two comparison inverses.
  let ex := FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x
  let ey := FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y
  let η :=
    ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((fiberFunctor H U).map φ)
  let θ :=
    (fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)
  have hhom : η ≫ ey.hom = ex.hom ≫ θ := by
    simpa only [ex, ey, η, θ] using
      stack_morphism_pullbackComparison_naturality_over_vertical H f φ
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Precompose by `ex.inv` so the left comparison isomorphism cancels immediately.
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
              ((fiberFunctor H U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.4.8: once the cocycle composite is reassociated to the literal
`comparison.inv ≫ comparison.hom` shell, the middle comparison pair cancels before the remaining
tail. -/
private theorem stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
    {A B : StackOver J} (H : A ⟶ B) {U Y : C} (g : Y ⟶ U) (x : A.p.Fiber U)
    {z : B.p.Fiber Y}
    (k :
      (fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj x) ⟶ z) :
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) g x).inv ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) g x).hom ≫
      k = k := by
  -- Use iso cancellation in exactly the postcomposed shape that appears in the cocycle proof.
  let e := FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) g x
  change e.inv ≫ e.hom ≫ k = k
  simpa only [Category.assoc] using Iso.inv_hom_id_assoc e k

/-- Helper for Lemma 8.4.8: a componentwise map of source descent data remains compatible with the
transported target overlap maps. -/
private theorem local_cover_descent_data_functor_morphism_comm
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    {D₁ D₂ :
      ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
        ((fiberFunctor F I₁.Y).map (φ.hom I₁))) ≫
      local_cover_descent_data_functor_hom (F := F) T D₂ q f₁ f₂ hf₁ hf₂ =
      local_cover_descent_data_functor_hom (F := F) T D₁ q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          ((fiberFunctor F I₂.Y).map (φ.hom I₂))) := by
  let FY := fiberFunctor F V
  let α₁ :=
    ((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
      ((fiberFunctor F I₁.Y).map (φ.hom I₁))
  let α₂ :=
    ((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
      ((fiberFunctor F I₂.Y).map (φ.hom I₂))
  let β₁ :=
    FY.map
      (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁))
  let β₂ :=
    FY.map
      (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂))
  let e₁₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (D₁.obj I₁)
  let e₁₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (D₂.obj I₁)
  let e₂₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (D₁.obj I₂)
  let e₂₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (D₂.obj I₂)
  let d₁ := D₁.hom q f₁ f₂ hf₁ hf₂
  let d₂ := D₂.hom q f₁ f₂ hf₁ hf₂
  have hleft :
      α₁ ≫ e₁₂.hom = e₁₁.hom ≫ β₁ := by
    -- Transport the left comparison shell across the vertical morphism on the source cover.
    simpa only [α₁, β₁, e₁₁, e₁₂] using
      stack_morphism_pullbackComparison_naturality_over_vertical
        (H := F) (f := f₁) (φ := φ.hom I₁)
  have hmid :
      β₁ ≫ FY.map d₂ = FY.map d₁ ≫ β₂ := by
    -- The middle square is the source descent-data compatibility of `φ`, mapped into the target
    -- fiber over `V`.
    change
      FY.map (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁)) ≫
          FY.map d₂ =
        FY.map d₁ ≫
          FY.map (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg FY.map (φ.comm q f₁ f₂ hf₁ hf₂)
  have hright :
      β₂ ≫ e₂₂.inv = e₂₁.inv ≫ α₂ := by
    -- Move the right comparison inverse across the mapped source vertical morphism.
    simpa only [α₂, β₂, e₂₁, e₂₂] using
      stack_morphism_pullbackComparison_inv_naturality_over_vertical
        (H := F) (f := f₂) (φ := φ.hom I₂)
  -- Rewrite both sides into the shared comparison-conjugated normal form.
  have hnormalize_left :
      (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          ((fiberFunctor F I₁.Y).map (φ.hom I₁))) ≫
        local_cover_descent_data_functor_hom (F := F) T D₂ q f₁ f₂ hf₁ hf₂ =
      (α₁ ≫ e₁₂.hom) ≫ FY.map d₂ ≫ e₂₂.inv := by
    change α₁ ≫ (e₁₂.hom ≫ FY.map d₂ ≫ e₂₂.inv) =
      (α₁ ≫ e₁₂.hom) ≫ FY.map d₂ ≫ e₂₂.inv
    simp only [Category.assoc]
  have hleft' :
      (α₁ ≫ e₁₂.hom) ≫ FY.map d₂ ≫ e₂₂.inv =
        (e₁₁.hom ≫ β₁) ≫ FY.map d₂ ≫ e₂₂.inv := by
    exact congrArg (fun k ↦ k ≫ FY.map d₂ ≫ e₂₂.inv) hleft
  have hassoc_left :
      (e₁₁.hom ≫ β₁) ≫ FY.map d₂ ≫ e₂₂.inv =
        e₁₁.hom ≫ (β₁ ≫ FY.map d₂) ≫ e₂₂.inv := by
    simp only [Category.assoc]
  have hmid' :
      e₁₁.hom ≫ (β₁ ≫ FY.map d₂) ≫ e₂₂.inv =
        e₁₁.hom ≫ (FY.map d₁ ≫ β₂) ≫ e₂₂.inv := by
    exact congrArg (fun k ↦ e₁₁.hom ≫ k ≫ e₂₂.inv) hmid
  have hassoc_mid :
      e₁₁.hom ≫ (FY.map d₁ ≫ β₂) ≫ e₂₂.inv =
        e₁₁.hom ≫ FY.map d₁ ≫ (β₂ ≫ e₂₂.inv) := by
    simp only [Category.assoc]
  have hright' :
      e₁₁.hom ≫ FY.map d₁ ≫ (β₂ ≫ e₂₂.inv) =
        e₁₁.hom ≫ FY.map d₁ ≫ (e₂₁.inv ≫ α₂) := by
    exact congrArg (fun k ↦ e₁₁.hom ≫ FY.map d₁ ≫ k) hright
  have hnormalize_right :
      e₁₁.hom ≫ FY.map d₁ ≫ (e₂₁.inv ≫ α₂) =
        local_cover_descent_data_functor_hom (F := F) T D₁ q f₁ f₂ hf₁ hf₂ ≫ α₂ := by
    change e₁₁.hom ≫ FY.map d₁ ≫ (e₂₁.inv ≫ α₂) =
      (e₁₁.hom ≫ FY.map d₁ ≫ e₂₁.inv) ≫ α₂
    simp only [Category.assoc]
  exact
    hnormalize_left.trans
      (hleft'.trans (hassoc_left.trans (hmid'.trans (hassoc_mid.trans (hright'.trans
        hnormalize_right)))))

/-- Helper for Lemma 8.4.8: a functor maps a visible threefold composite to the corresponding
threefold composite of mapped arrows. -/
private theorem canonical_pullbackFunctor_map_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice p).map f y =
      (canonicalPullbackChoice p).map f x ≫ φ.1 := by
  -- Compare the chosen pullback arrow of `y` with the universal factorization induced by `φ`.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f x) :=
    (canonicalPullbackChoice p).isStronglyCartesian f x
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x) := hpull.toIsHomLift
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f ((canonicalPullbackChoice p).map f x) U φ.1
  letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f y) :=
    (canonicalPullbackChoice p).isStronglyCartesian f y
  change
      Functor.IsStronglyCartesian.map p f ((canonicalPullbackChoice p).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice p).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice p).map f y =
        (canonicalPullbackChoice p).map f x ≫ φ.1
  exact
    Functor.IsStronglyCartesian.fac p f ((canonicalPullbackChoice p).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice p).map f x ≫ φ.1)

/-- Helper for Lemma 8.4.8: after postcomposing with the chosen target pullback arrow, the mapped
source pullback factorization becomes the target pullback factorization for the image morphism. -/
private theorem map_canonical_pullbackFunctor_map_fac
    {A B : StackOver J} (H : A ⟶ B) {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
        (toFibredCategoryMor H).toHom.map φ.1 =
      (toFibredCategoryMor H).toHom.map
          ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Apply `H` to the source pullback factorization and normalize the mapped composite.
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hfac :
      ((canonicalPullbackChoice A.p).map f x) ≫ φ.1 =
        ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (canonicalPullbackChoice A.p).map f y := by
    exact
      (canonical_pullbackFunctor_map_fac
        (p := A.p) (f := f) (x := x) (y := y) (φ := φ)).symm
  exact congrArg (fun k ↦ (toFibredCategoryMor H).toHom.map k) hfac

/-- Helper for Lemma 8.4.8: after postcomposing both candidate owner-level comparison squares with
the mapped chosen source pullback arrow, the pullback-comparison square reduces to the standard
pullback factorization identity. -/
private theorem stack_morphism_pullbackComparison_hom_postcompose_eq
    {A B : StackOver J} (H : A ⟶ B) {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ))).1 ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom.1 ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
      ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
          ((fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Compare the two candidates only after postcomposing with the common strongly cartesian
  -- target arrow over `f`.
  let lhs :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ))).1 ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom.1 ≫
      (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor H U).map φ))).1 ≫
      (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj x) ≫
      ((fiberFunctor H U).map φ).1
  let mid₃ :=
    ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
        (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
      ((fiberFunctor H U).map φ).1
  let mid₄ :=
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
      ((fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
      (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let rhs :=
    ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
        ((fiberFunctor H V).map
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
      (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  have h₁ : lhs = mid₁ := by
    -- Rewrite the comparison at `y` to the canonical target pullback arrow.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((fiberFunctor H U).map φ))).1 ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f y).hom.1 ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
            ((fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj y)
    exact
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
              ((fiberFunctor H U).map φ))).1 ≫ k)
        (FibredCategoryMor.pullbackComparison_hom_postcompose (toFibredCategoryMor H) f y)
  have h₂ : mid₁ = mid₂ := by
    -- Pullback in the target fiber is already natural on the vertical morphism `H.map φ`.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj y) =
        (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj x) ≫
          ((fiberFunctor H U).map φ).1
    exact
      canonical_pullbackFunctor_map_fac
        (p := B.p) (f := f) (φ := (fiberFunctor H U).map φ)
  have h₃ : mid₂ = mid₃ := by
    -- Rewrite the target pullback arrow at `x` back through the comparison isomorphism.
    change
      (canonicalPullbackChoice B.p).map f ((fiberFunctor H U).obj x) ≫
          ((fiberFunctor H U).map φ).1 =
        (((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
          ((fiberFunctor H U).map φ).1)
    exact
      (congrArg
        (fun k ↦ k ≫ ((fiberFunctor H U).map φ).1)
        (FibredCategoryMor.pullbackComparison_hom_postcompose
          (toFibredCategoryMor H) f x)).symm
  have h₄ : mid₃ = mid₄ := by
    -- Map the source pullback factorization across `H` and reassociate once.
    calc
      (((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
        ((fiberFunctor H U).map φ).1) =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
              ((fiberFunctor H U).map φ).1) := by
            rw [Category.assoc]
      _ =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((toFibredCategoryMor H).toHom.map
                ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
              (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)) := by
            exact
              congrArg
                (fun k ↦
                  (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫ k)
                (map_canonical_pullbackFunctor_map_fac
                  (H := H) (f := f) (φ := φ))
      _ =
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
            (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
            rfl
  have h₅ : mid₄ = rhs := by
    -- Reassociate the right-hand composite into the packaged naturality shape.
    change
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
          ((fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor H) f x).hom.1 ≫
            ((fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
          (toFibredCategoryMor H).toHom.map ((canonicalPullbackChoice A.p).map f y)
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.4.8: a functor maps a visible threefold composite to the corresponding
threefold composite of mapped arrows. -/
private theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to the locally discrete opposite.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.4.8: a functor maps a visible threefold composite to the corresponding
threefold composite of mapped arrows. -/
private theorem functor_map_threefold_comp
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {W X Y Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  -- Split the threefold composite into the two ordinary functoriality steps.
  rw [Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 8.4.8: the hom component of the canonical pullback-composition comparison
for the fiber pseudofunctor factors through the chosen composite pullback arrow. -/
private theorem canonicalFiberPseudofunctor_mapComp'_hom_app_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x =
      (canonicalPullbackChoice p).map gf x := by
  -- Reduce the flexible comparison to the chosen pullback-composition comparison.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_fac f g x

/-- Helper for Lemma 8.4.8: the inverse component of the canonical pullback-composition
comparison factors the composite pullback arrow through the iterated chosen pullbacks. -/
private theorem canonicalFiberPseudofunctor_mapComp'_inv_app_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map gf x =
      (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x := by
  -- Read the same comparison component in the inverse direction.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_inv_fac f g x

/-- Helper for Lemma 8.4.8: postcomposing the inverse pullback-comparison morphism with the
chosen target pullback arrow recovers the mapped chosen source pullback arrow. -/
private theorem fibredCategoryMor_pullbackComparison_inv_postcompose_owner
    {Xf Yf : FibredCategoryOver C} (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison F f x).inv.1 ≫
        (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) =
      F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) := by
  -- Cancel the comparison isomorphism against its hom part before reading off the source map.
  have hid :
      (FibredCategoryMor.pullbackComparison F f x).inv.1 ≫
          (FibredCategoryMor.pullbackComparison F f x).hom.1 =
        𝟙 ((((F.toHom).fiberFunctor V).obj
          (f ^*[canonicalPullbackChoice Xf.p] x)).1) := by
    exact congrArg (fun k ↦ k.1) (FibredCategoryMor.pullbackComparison F f x).inv_hom_id
  have hid_postcompose :
      ((FibredCategoryMor.pullbackComparison F f x).inv.1 ≫
          (FibredCategoryMor.pullbackComparison F f x).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
        F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) := by
    rw [hid, Category.id_comp]
    rfl
  have hcompose :
      (FibredCategoryMor.pullbackComparison F f x).inv.1 ≫
          (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) =
        ((FibredCategoryMor.pullbackComparison F f x).inv.1 ≫
            (FibredCategoryMor.pullbackComparison F f x).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) := by
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦ (FibredCategoryMor.pullbackComparison F f x).inv.1 ≫ k)
        (FibredCategoryMor.pullbackComparison_hom_postcompose F f x).symm
  exact hcompose.trans hid_postcompose

/-- Helper for Lemma 8.4.8: after postcomposing the raw left `pullHom` boundary and the strict
composite-leg left boundary with the chosen target pullback arrows over `g` and then `f`, both
owner-level composites reduce to the same composite-leg chosen pullback arrow. -/
private theorem local_cover_descent_data_functor_pullHom_left_boundary_postcompose_g_then_f_target
    (F : X ⟶ Y) {U V V' : C}
    (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U) (hgf : g ≫ f = gf)
    (x : X.p.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((fiberFunctor F U).obj x)) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom)
    let strict :=
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf x).hom ≫
        (fiberFunctor F V').map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)).inv
    let tailg :=
      (canonicalPullbackChoice Y.p).map g
        ((fiberFunctor F V).obj
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
    let tailf := (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map f x)
    raw.1 ≫ tailg ≫ tailf = strict.1 ≫ tailg ≫ tailf := by
  let raw :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((fiberFunctor F U).obj x)) ≫
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf x).hom ≫
      (fiberFunctor F V').map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tailg :=
    (canonicalPullbackChoice Y.p).map g
      ((fiberFunctor F V).obj
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
  let tailf := (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map f x)
  let e := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf x
  let cg :=
    FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)
  let ef := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x
  let leftRaw :=
    ((canonicalFiberPseudofunctor Y.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((fiberFunctor F U).obj x)
  let leftSource :=
    ((canonicalFiberPseudofunctor X.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      x
  have hraw_expand :
      raw.1 =
        leftRaw.1 ≫
          ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.hom)).1 := by
    rfl
  have hstrict_expand :
      strict.1 =
        e.hom.1 ≫ ((fiberFunctor F V').map leftSource).1 ≫ cg.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice Y.p).map gf ((fiberFunctor F U).obj x) := by
    have hraw_flank :
        (leftRaw.1 ≫
            (canonicalPullbackChoice Y.p).map g
              (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
                ((fiberFunctor F U).obj x))) ≫
            (canonicalPullbackChoice Y.p).map f
              ((fiberFunctor F U).obj x) =
          (canonicalPullbackChoice Y.p).map gf
            ((fiberFunctor F U).obj x) := by
      simpa [leftRaw, Category.assoc] using
        canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (p := Y.p) (f := f) (g := g) (gf := gf) (hgf := hgf) ((fiberFunctor F U).obj x)
    -- Normalize the raw shell to the chosen pullback arrow over the composite leg `gf`.
    calc
      raw.1 ≫ tailg ≫ tailf =
          leftRaw.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
            tailg ≫
            tailf := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
              tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((canonicalPullbackChoice Y.p).map g
                (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
                  ((fiberFunctor F U).obj x))) ≫
              ef.hom.1) ≫
            tailf := by
              exact
                congrArg (fun t ↦ leftRaw.1 ≫ t ≫ tailf)
                  (canonical_pullbackFunctor_map_fac (p := Y.p) (f := g) (φ := ef.hom))
      _ =
          leftRaw.1 ≫
            (canonicalPullbackChoice Y.p).map g
              (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
                ((fiberFunctor F U).obj x)) ≫
            ef.hom.1 ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          (canonicalPullbackChoice Y.p).map gf
            ((fiberFunctor F U).obj x) := by
              have hpostf :
                  leftRaw.1 ≫
                      (canonicalPullbackChoice Y.p).map g
                        (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
                          ((fiberFunctor F U).obj x)) ≫
                      ef.hom.1 ≫
                      tailf =
                    (leftRaw.1 ≫
                      (canonicalPullbackChoice Y.p).map g
                        (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
                          ((fiberFunctor F U).obj x))) ≫
                      (canonicalPullbackChoice Y.p).map f
                        ((fiberFunctor F U).obj x) := by
                simpa only [Category.assoc] using
                  congrArg
                    (fun t ↦
                      leftRaw.1 ≫
                        (canonicalPullbackChoice Y.p).map g
                          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
                            ((fiberFunctor F U).obj x)) ≫
                        t)
                    (FibredCategoryMor.pullbackComparison_hom_postcompose
                      (toFibredCategoryMor F) f x)
              exact hpostf.trans hraw_flank
  have hstrict :
      strict.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice Y.p).map gf
          ((fiberFunctor F U).obj x) := by
    have hpostg :
        cg.inv.1 ≫ tailg =
          (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map g
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)) := by
      -- Read the inverse comparison against the chosen target pullback arrow on the common `g` leg.
      change
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)).inv.1 ≫
          (canonicalPullbackChoice Y.p).map g
            ((fiberFunctor F V).obj
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)) =
        (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map g
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
      exact fibredCategoryMor_pullbackComparison_inv_postcompose_owner
        (F := toFibredCategoryMor F) (f := g)
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)
    have hpostg' :
        (cg.inv.1 ≫ tailg) ≫ tailf =
          (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map g
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hpostg
    -- Normalize the strict shell by canceling the inverse comparison on the common `g` leg.
    calc
      strict.1 ≫ tailg ≫ tailf =
          e.hom.1 ≫ ((fiberFunctor F V').map leftSource).1 ≫
            cg.inv.1 ≫
            tailg ≫
            tailf := by
              rw [hstrict_expand]
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((fiberFunctor F V').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((fiberFunctor F V').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg ≫ tailf) := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((fiberFunctor F V').map leftSource).1 ≫
            ((toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map g
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)) ≫
              tailf) := by
              simpa only [Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ ((fiberFunctor F V').map leftSource).1 ≫ t)
                  hpostg'
      _ =
          e.hom.1 ≫
            (toFibredCategoryMor F).toHom.map
              (leftSource.1 ≫
                (canonicalPullbackChoice X.p).map g
                  (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x) ≫
                (canonicalPullbackChoice X.p).map f x) := by
              simpa only [tailf, Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ t)
                  (functor_map_threefold_comp
                    (toFibredCategoryMor F).toHom.toFunctor leftSource.1
                    ((canonicalPullbackChoice X.p).map g
                      (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
                    ((canonicalPullbackChoice X.p).map f x)).symm
      _ =
          e.hom.1 ≫ (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map gf x) := by
              exact
                congrArg (fun t ↦ e.hom.1 ≫ (toFibredCategoryMor F).toHom.map t)
                  (canonicalFiberPseudofunctor_mapComp'_hom_app_fac
                    (p := X.p) (f := f) (g := g) (gf := gf) (hgf := hgf) x)
      _ =
          (canonicalPullbackChoice Y.p).map gf
            ((fiberFunctor F U).obj x) := by
              exact FibredCategoryMor.pullbackComparison_hom_postcompose
                (toFibredCategoryMor F) gf x
  -- Both shells reduce to the same composite-leg chosen pullback arrow.
  exact hraw.trans hstrict.symm

/-- Helper for Lemma 8.4.8: after postcomposing the raw left `pullHom` boundary and the strict
composite-leg left boundary with the chosen target pullback arrow over `g`, the two owner-level
composites already agree. -/
private theorem local_cover_descent_data_functor_pullHom_left_boundary_postcompose_g_target
    (F : X ⟶ Y) {U V V' : C}
    (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U) (hgf : g ≫ f = gf)
    (x : X.p.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((fiberFunctor F U).obj x)) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom)
    let strict :=
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf x).hom ≫
        (fiberFunctor F V').map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)).inv
    let tail :=
      (canonicalPullbackChoice Y.p).map g
        ((fiberFunctor F V).obj
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((fiberFunctor F U).obj x)) ≫
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf x).hom ≫
      (fiberFunctor F V').map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice Y.p).map g
      ((fiberFunctor F V).obj
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
  let tailf := (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map f x)
  have htailf : Y.p.IsStronglyCartesian f tailf := by
    -- Transport the chosen source pullback lift over `f` across the stack morphism.
    change Y.p.IsStronglyCartesian f
      ((toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map f x))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (toFibredCategoryMor F) f
        ((canonicalPullbackChoice X.p).map f x)
        ((canonicalPullbackChoice X.p).isStronglyCartesian f x)
  have htail : Y.p.IsHomLift g tail := by
    change
      Y.p.IsHomLift g
        ((canonicalPullbackChoice Y.p).map g
          ((fiberFunctor F V).obj
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)))
    exact
      ((canonicalPullbackChoice Y.p).isStronglyCartesian g
        ((fiberFunctor F V).obj
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))).toIsHomLift
  letI : Y.p.IsStronglyCartesian f tailf := htailf
  letI : Y.p.IsHomLift (𝟙 V') raw.1 := raw.2
  letI : Y.p.IsHomLift (𝟙 V') strict.1 := strict.2
  letI : Y.p.IsHomLift g tail := htail
  have hrawtail : Y.p.IsHomLift g (raw.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
      V' raw.1 raw.2 _ _ g tail htail
  have hstricttail : Y.p.IsHomLift g (strict.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
      V' strict.1 strict.2 _ _ g tail htail
  have hpost : (raw.1 ≫ tail) ≫ tailf = (strict.1 ≫ tail) ≫ tailf := by
    -- Compare after composing with the common strongly cartesian leg over `f`.
    simpa only [Category.assoc] using
      local_cover_descent_data_functor_pullHom_left_boundary_postcompose_g_then_f_target
        (F := F) f g gf hgf x
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      f tailf htailf _ _ g (raw.1 ≫ tail) (strict.1 ≫ tail) hrawtail hstricttail hpost

/-- Helper for Lemma 8.4.8: the raw left `pullHom` boundary is exactly the strict composite-leg
comparison shell after passing back to the fiber over the domain of `gf`. -/
private theorem local_cover_descent_data_functor_pullHom_left_boundary
    (F : X ⟶ Y) {U V V' : C}
    (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U) (hgf : g ≫ f = gf)
    (x : X.p.Fiber U) :
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((fiberFunctor F U).obj x)) ≫
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom) =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf x).hom ≫
        (fiberFunctor F V').map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)).inv := by
  let raw :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((fiberFunctor F U).obj x)) ≫
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf x).hom ≫
      (fiberFunctor F V').map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice Y.p).map g
      ((fiberFunctor F V).obj
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
  have htail : Y.p.IsStronglyCartesian g tail := by
    change
      Y.p.IsStronglyCartesian g
        ((canonicalPullbackChoice Y.p).map g
          ((fiberFunctor F V).obj
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)))
    exact
      (canonicalPullbackChoice Y.p).isStronglyCartesian g
        ((fiberFunctor F V).obj
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x))
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level comparison after composing with the `g`-leg.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact local_cover_descent_data_functor_pullHom_left_boundary_postcompose_g_target
      (F := F) f g gf hgf x
  -- Compare the two fiber morphisms via the common strongly cartesian arrow over `g`.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      g tail htail _ _ (𝟙 V') raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.4.8: after postcomposing the raw right `pullHom` boundary and the strict
composite-leg right boundary with the chosen `gf`-pullback arrow, both owner-level composites
reduce to the same mapped source composite-leg factorization. -/
private theorem local_cover_descent_data_functor_pullHom_right_boundary_postcompose_target
    (F : X ⟶ Y) {U V V' : C}
    (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U) (hgf : g ≫ f = gf)
    (y : X.p.Fiber U) :
    let raw :=
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f y).inv) ≫
        (((canonicalFiberPseudofunctor Y.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          ((fiberFunctor F U).obj y))
    let strict :=
      (fiberFunctor F V').map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf y).inv
    let tail :=
      (canonicalPullbackChoice Y.p).map gf
        ((fiberFunctor F U).obj y)
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f y).inv) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((fiberFunctor F U).obj y))
  let strict :=
    (fiberFunctor F V').map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf y).inv
  let tail :=
    (canonicalPullbackChoice Y.p).map gf
      ((fiberFunctor F U).obj y)
  let e := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf y
  let cg :=
    FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)
  let ef := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f y
  let tailg :=
    (canonicalPullbackChoice Y.p).map g
      (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
        ((fiberFunctor F U).obj y))
  let tailf := (canonicalPullbackChoice Y.p).map f ((fiberFunctor F U).obj y)
  let sourceTailg :=
    (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map g
      (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y))
  let sourceTailf := (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map f y)
  let rightSource :=
    ((canonicalFiberPseudofunctor X.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
      y
  have hraw_expand :
      raw.1 =
        cg.inv.1 ≫
          ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
          (((canonicalFiberPseudofunctor Y.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
            ((fiberFunctor F U).obj y)).1 := by
    rfl
  have hstrict_expand :
      strict.1 = ((fiberFunctor F V').map rightSource).1 ≫ e.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hmap_tailg :
        ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            tailg =
          (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 := by
      -- Specialize pullback-functor naturality to the inverse comparison over the leg `g`.
      change
        (((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f y).inv)).1) ≫
            (canonicalPullbackChoice Y.p).map g
              (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
                ((fiberFunctor F U).obj y)) =
          (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
            (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f y).inv.1
      exact canonical_pullbackFunctor_map_fac (p := Y.p) (f := g) (φ := ef.inv)
    have hsourceTailg :
        cg.inv.1 ≫
            (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) =
          sourceTailg := by
      -- Read the inverse comparison against the chosen target pullback arrow on the common `g` leg.
      change
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)).inv.1 ≫
          (canonicalPullbackChoice Y.p).map g
            ((fiberFunctor F V).obj
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) =
        sourceTailg
      exact fibredCategoryMor_pullbackComparison_inv_postcompose_owner
        (F := toFibredCategoryMor F) (f := g)
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)
    have hmap_tailg' :
        (((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫ tailg) ≫
            tailf =
          ((canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hmap_tailg
    have hsourceTailg' :
        (cg.inv.1 ≫
            (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf =
          sourceTailg ≫ sourceTailf := by
      exact congrArg (fun t ↦ t ≫ sourceTailf) hsourceTailg
    have hraw_mid :
        raw.1 ≫ tail =
          (cg.inv.1 ≫
            (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
      -- Normalize the raw inverse shell to the source composite-leg factorization transported by `F`.
      calc
      raw.1 ≫ tail =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (((canonicalFiberPseudofunctor Y.p).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((fiberFunctor F U).obj y)).1 ≫
            tail := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            ((((canonicalFiberPseudofunctor Y.p).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((fiberFunctor F U).obj y)).1 ≫
              tail) := by
              rfl
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (tailg ≫ tailf) := by
              exact
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      ((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                      t)
                  (canonicalFiberPseudofunctor_mapComp'_inv_app_fac
                    (p := Y.p) (f := f) (g := g) (gf := gf) (hgf := hgf)
                    ((fiberFunctor F U).obj y))
      _ =
          cg.inv.1 ≫
            (((((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
              tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (((canonicalPullbackChoice Y.p).map g
                ((fiberFunctor F V).obj
                  (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y))) ≫
              ef.inv.1) ≫ tailf := by
              simpa only [Category.assoc] using congrArg (fun t ↦ cg.inv.1 ≫ t) hmap_tailg'
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
            sourceTailf := by
              simpa only [sourceTailf, Category.assoc] using
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      (canonicalPullbackChoice Y.p).map g
                        ((fiberFunctor F V).obj
                          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
                      t)
                  (fibredCategoryMor_pullbackComparison_inv_postcompose_owner
                    (toFibredCategoryMor F) f y)
      _ =
          (cg.inv.1 ≫
            (canonicalPullbackChoice Y.p).map g
              ((fiberFunctor F V).obj
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
              simp only [Category.assoc]
    exact hraw_mid.trans hsourceTailg'
  have hstrict :
      strict.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hstrict_tail :
        (toFibredCategoryMor F).toHom.toFunctor.map rightSource.1 ≫
            (toFibredCategoryMor F).toHom.toFunctor.map ((canonicalPullbackChoice X.p).map gf y) =
          sourceTailg ≫ sourceTailf := by
      rw [← Functor.map_comp]
      rw [show rightSource.1 ≫ (canonicalPullbackChoice X.p).map gf y =
          ((canonicalPullbackChoice X.p).map g
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
            (canonicalPullbackChoice X.p).map f y by
            exact
              canonicalFiberPseudofunctor_mapComp'_inv_app_fac
                (p := X.p) (f := f) (g := g) (gf := gf) (hgf := hgf) y]
      change
        (toFibredCategoryMor F).toHom.toFunctor.map
            (((canonicalPullbackChoice X.p).map g
                (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) ≫
              (canonicalPullbackChoice X.p).map f y) =
          sourceTailg ≫ sourceTailf
      rw [Functor.map_comp]
      rfl
    have hstrict_mid :
        strict.1 ≫ tail =
          (toFibredCategoryMor F).toHom.toFunctor.map rightSource.1 ≫
            (toFibredCategoryMor F).toHom.toFunctor.map ((canonicalPullbackChoice X.p).map gf y) := by
      -- The strict inverse shell reduces to the same mapped source composite-leg factorization.
      calc
      strict.1 ≫ tail =
          ((fiberFunctor F V').map rightSource).1 ≫
            e.inv.1 ≫
            tail := by
            rw [hstrict_expand]
            simp only [Category.assoc]
      _ =
          ((fiberFunctor F V').map rightSource).1 ≫
            (e.inv.1 ≫ tail) := by
            rfl
      _ =
          (toFibredCategoryMor F).toHom.toFunctor.map rightSource.1 ≫
            (toFibredCategoryMor F).toHom.toFunctor.map ((canonicalPullbackChoice X.p).map gf y) := by
              exact
                congrArg (fun t ↦ (toFibredCategoryMor F).toHom.toFunctor.map rightSource.1 ≫ t)
                  (fibredCategoryMor_pullbackComparison_inv_postcompose_owner
                    (toFibredCategoryMor F) gf y)
    exact hstrict_mid.trans hstrict_tail
  exact hraw.trans hstrict.symm

/-- Helper for Lemma 8.4.8: the raw right `pullHom` boundary is exactly the strict
composite-leg right shell after passing back to the fiber over the domain of `gf`. -/
private theorem local_cover_descent_data_functor_pullHom_right_boundary
    (F : X ⟶ Y) {U V V' : C}
    (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U) (hgf : g ≫ f = gf)
    (y : X.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f y).inv) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((fiberFunctor F U).obj y)) =
    (fiberFunctor F V').map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf y).inv := by
  let raw :=
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f y).inv) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((fiberFunctor F U).obj y))
  let strict :=
    (fiberFunctor F V').map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf y).inv
  let tail :=
    (canonicalPullbackChoice Y.p).map gf
      ((fiberFunctor F U).obj y)
  have htail : Y.p.IsStronglyCartesian gf tail := by
    change
      Y.p.IsStronglyCartesian gf
        ((canonicalPullbackChoice Y.p).map gf
          ((fiberFunctor F U).obj y))
    exact
      (canonicalPullbackChoice Y.p).isStronglyCartesian gf
        ((fiberFunctor F U).obj y)
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level postcomposed inverse-shell comparison.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact local_cover_descent_data_functor_pullHom_right_boundary_postcompose_target
      (F := F) f g gf hgf y
  -- Compare the two fiber morphisms via the common strongly cartesian arrow over `gf`.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      gf tail htail _ _ (𝟙 V') raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.4.8: the fixed-cover transport `pullHom` computation reduces to a single
comparison-conjugated shell over the common refinement leg. -/
private theorem local_cover_descent_data_functor_pullHom_middle_conjugation
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
        (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          ((fiberFunctor F V).map (D.hom q f₁ f₂ hf₁ hf₂))) =
      (fiberFunctor F V').map
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv := by
  -- Move the source overlap morphism across the `g`-leg pullback comparisons before the right
  -- boundary is normalized.
  simpa only using
    (stack_morphism_pullbackComparison_inv_naturality_over_vertical
      (H := F) (f := g) (φ := D.hom q f₁ f₂ hf₁ hf₂)).symm

/-- Helper for Lemma 8.4.8: after the left and right boundaries are normalized, the three strict
source-side pieces fold back to the source `pullHom` shell under the fiber functor. -/
private theorem local_cover_descent_data_functor_pullHom_source_shell_map
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftSource :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
    let rightSource :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
    (fiberFunctor F V').map leftSource ≫
        (fiberFunctor F V').map
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (fiberFunctor F V').map rightSource =
      (fiberFunctor F V').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) := by
  -- The source `pullHom` shell is definitionally the visible threefold composite.
  let leftSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  change
    (fiberFunctor F V').map leftSource ≫
        (fiberFunctor F V').map
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (fiberFunctor F V').map rightSource =
      (fiberFunctor F V').map
        (leftSource ≫
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
          rightSource)
  rw [functor_map_threefold_comp]

/-- Helper for Lemma 8.4.8: unfolding the fixed-cover transported overlap map exposes the single
middle `map` of the transported source overlap morphism before boundary normalization. -/
private theorem local_cover_descent_data_functor_pullHom_unfolded
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (local_cover_descent_data_functor_hom
          (F := F) T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((fiberFunctor F I₁.Y).obj (D.obj I₁))) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          ((FibredCategoryMor.pullbackComparison
              (toFibredCategoryMor F) f₁ (D.obj I₁)).hom ≫
            (fiberFunctor F V).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
            (FibredCategoryMor.pullbackComparison
              (toFibredCategoryMor F) f₂ (D.obj I₂)).inv)) ≫
        (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((fiberFunctor F I₂.Y).obj (D.obj I₂))) := by
  -- Expand only the transported overlap map and the pseudofunctorial `pullHom`; this isolates
  -- the single mapped middle composite before the owner-level boundary reassociations begin.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, local_cover_descent_data_functor_hom]
  rfl

/-- Helper for Lemma 8.4.8: the fixed-cover transport `pullHom` computation reduces to a single
comparison-conjugated shell over the common refinement leg. -/
private theorem local_cover_descent_data_functor_pullHom_hom_normalized_shell
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (local_cover_descent_data_functor_hom
          (F := F) T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (FibredCategoryMor.pullbackComparison
          (toFibredCategoryMor F) gf₁ (D.obj I₁)).hom ≫
        (fiberFunctor F V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
        (FibredCategoryMor.pullbackComparison
          (toFibredCategoryMor F) gf₂ (D.obj I₂)).inv := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (D.obj I₂)
  let eg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (D.obj I₁)
  let eg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (D.obj I₂)
  let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))
  let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((fiberFunctor F I₁.Y).obj (D.obj I₁)))
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((fiberFunctor F I₂.Y).obj (D.obj I₂)))
  let leftSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (local_cover_descent_data_functor_hom
            (F := F) T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        leftTarget ≫ FYg.map (e₁.hom ≫ (fiberFunctor F V).map d ≫ e₂.inv) ≫ rightTarget := by
    -- Expand only the transported overlap map before the owner-level reassociation begins.
    simpa only [FYg, d, e₁, e₂, leftTarget, rightTarget] using
      local_cover_descent_data_functor_pullHom_unfolded
        (F := F) T D g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmap :
      FYg.map (e₁.hom ≫ (fiberFunctor F V).map d ≫ e₂.inv) =
        FYg.map e₁.hom ≫ FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv := by
    -- The middle transported composite is the visible threefold shell under `FYg`.
    simpa only [FYg, d, e₁, e₂] using
      functor_map_threefold_comp FYg e₁.hom ((fiberFunctor F V).map d) e₂.inv
  have hleft :
      leftTarget ≫ FYg.map e₁.hom =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv := by
    -- Normalize the left boundary to the common refinement leg `gf₁`.
    simpa only [FYg, e₁, eg₁, cg₁, leftTarget, leftSource] using
      local_cover_descent_data_functor_pullHom_left_boundary
        (F := F) f₁ g gf₁ hgf₁ (D.obj I₁)
  have hmid :
      cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d) =
        (fiberFunctor F V').map (FXg.map d) ≫ cg₂.inv := by
    -- Move the source overlap morphism across the `g`-leg comparison shell.
    simpa only [FYg, FXg, d, cg₁, cg₂] using
      local_cover_descent_data_functor_pullHom_middle_conjugation
        (F := F) T D g q f₁ f₂ hf₁ hf₂
  have hright :
      cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        (fiberFunctor F V').map rightSource ≫ eg₂.inv := by
    -- Normalize the right boundary to the common refinement leg `gf₂`.
    simpa only [FYg, e₂, eg₂, cg₂, rightTarget, rightSource] using
      local_cover_descent_data_functor_pullHom_right_boundary
        (F := F) f₂ g gf₂ hgf₂ (D.obj I₂)
  have hfold :
      (fiberFunctor F V').map leftSource ≫
          (fiberFunctor F V').map (FXg.map d) ≫
          (fiberFunctor F V').map rightSource =
        (fiberFunctor F V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) := by
    -- Fold the three normalized source-side pieces back into the source `pullHom` shell.
    simpa only [FXg, d, leftSource, rightSource] using
      local_cover_descent_data_functor_pullHom_source_shell_map
        (F := F) T D g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hright' :
      eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
        (cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget) =
      eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
        ((fiberFunctor F V').map rightSource ≫ eg₂.inv) := by
    -- Freeze the normalized left and middle factors while replacing the right boundary shell.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦ eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫
          (fiberFunctor F V').map (FXg.map d) ≫ k)
        hright
  have hmap' :
      leftTarget ≫ FYg.map (e₁.hom ≫ (fiberFunctor F V).map d ≫ e₂.inv) ≫ rightTarget =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((fiberFunctor F V).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
    -- Freeze the left and right transport boundaries while expanding the middle mapped shell.
    calc
      leftTarget ≫ FYg.map (e₁.hom ≫ (fiberFunctor F V).map d ≫ e₂.inv) ≫ rightTarget =
        leftTarget ≫ (FYg.map e₁.hom ≫ FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv) ≫
          rightTarget := by
            exact congrArg (fun k ↦ leftTarget ≫ k ≫ rightTarget) hmap
      _ =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget := by
            simp only [Category.assoc]
  have hleft' :
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Replace the left boundary with the normalized comparison shell over `gf₁`.
    calc
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget =
        (leftTarget ≫ FYg.map e₁.hom) ≫ FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget := by
            simp only [Category.assoc]
      _ =
        (eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv) ≫
          FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun k ↦ k ≫ FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫ rightTarget)
              hleft
      _ =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hmid' :
      eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Replace the middle shell with the normalized `g`-transported source overlap map.
    calc
      eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((fiberFunctor F V).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫
          (cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d)) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫
          ((fiberFunctor F V').map (FXg.map d) ≫ cg₂.inv) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun k ↦ eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ k ≫
                FYg.map e₂.inv ≫ rightTarget)
              hmid
      _ =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hstep_source_flat :
      eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
          (fiberFunctor F V').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          (fiberFunctor F V').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
    -- After flattening associations, the source shell folds directly by `hfold`.
    calc
      eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
          (fiberFunctor F V').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          ((fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
            (fiberFunctor F V').map rightSource) ≫
          eg₂.inv := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫
          (fiberFunctor F V').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
            exact congrArg (fun k ↦ eg₁.hom ≫ k ≫ eg₂.inv) hfold
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (local_cover_descent_data_functor_hom
            (F := F) T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        eg₁.hom ≫ (fiberFunctor F V').map leftSource ≫ (fiberFunctor F V').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Chain the unfolded shell expansion with the flattened left and middle normalization steps.
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  exact
    hprefix.trans
      (hright'.trans
        (hstep_source_flat.trans rfl))

/-- Helper for Lemma 8.4.8: the fixed-cover transport overlap maps are compatible with further
pullback once the raw shell is normalized to the common refinement leg. -/
private theorem local_cover_descent_data_functor_pullHom_hom
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (local_cover_descent_data_functor_hom
          (F := F) T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      local_cover_descent_data_functor_hom
        (F := F) T D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let e₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (D.obj I₂)
  -- Normalize the full transported shell once, then replace the middle factor by the source
  -- descent-data pullback law.
  have hnormalize :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (local_cover_descent_data_functor_hom
            (F := F) T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        e₁.hom ≫
          (fiberFunctor F V').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv := by
    simpa only [e₁, e₂] using
      local_cover_descent_data_functor_pullHom_hom_normalized_shell
        (F := F) T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmiddle :
      e₁.hom ≫
          (fiberFunctor F V').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv =
        e₁.hom ≫
          (fiberFunctor F V').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv := by
    exact congrArg (fun k ↦ e₁.hom ≫ (fiberFunctor F V').map k ≫ e₂.inv)
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  have hfinal :
      e₁.hom ≫
          (fiberFunctor F V').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv =
        local_cover_descent_data_functor_hom
          (F := F) T D q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
    rfl
  exact hnormalize.trans (hmiddle.trans hfinal)

/-- Helper for Lemma 8.4.8: the fixed-cover transport on descent data induced by a stack morphism
acts componentwise on objects and conjugates overlap morphisms by the pullback-comparison
isomorphisms. -/
private noncomputable abbrev local_cover_descent_data_functor
    (F : X ⟶ Y) {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor Y.p).DescentData (fun I : T.Arrow ↦ I.f)) where
  obj D :=
    { obj := fun I ↦ (fiberFunctor F I.Y).obj (D.obj I)
      hom := fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
        local_cover_descent_data_functor_hom
          (F := F) T D q f₁ f₂ hf₁ hf₂
      pullHom_hom := by
        intro V' V g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        -- Delegate the only remaining object-field transport identity to the dedicated helper.
        simpa using
          local_cover_descent_data_functor_pullHom_hom
            (F := F) T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self := by
        intro V q I g hg
        -- The transported self-overlap map is already normalized by the dedicated cancellation
        -- lemma above.
        simpa using
          local_cover_descent_data_functor_hom_self
            (F := F) T D q g hg
      hom_comp := by
        intro V q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        -- The source cocycle relation transports directly through the comparison shells.
        exact
          local_cover_descent_data_functor_hom_comp
            (F := F) T D q f₁ f₂ f₃ hf₁ hf₂ hf₃ }
  map {D₁ D₂} φ :=
    { hom := fun I ↦ (fiberFunctor F I.Y).map (φ.hom I)
      comm := by
        intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
        -- Compatibility of a mapped descent morphism is exactly the conjugation square proved
        -- above.
        exact
          local_cover_descent_data_functor_morphism_comm
            (F := F) T φ (q := q)
            (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
            (hf₁ := hf₁) (hf₂ := hf₂) }
  map_id X := by
    -- Identities are preserved componentwise by the fiber functors.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    exact (fiberFunctor F I.Y).map_id (X.obj I)
  map_comp f g := by
    -- Composition is likewise preserved componentwise.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    exact (fiberFunctor F I.Y).map_comp (f.hom I) (g.hom I)

/-- Helper for Lemma 8.4.8: the right leg of the canonical target overlap is the specialized
left-boundary shell whose target comparison lives over the common map `q`. -/
private theorem canonical_target_descent_right_leg_postcompose
    (F : X ⟶ Y) {U : C} (T : J.Cover U) (x : X.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₂ : T.Arrow}
    (f₂ : V ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
        ((fiberFunctor F U).obj x)) ≫
      (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).hom) =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) q x).hom ≫
        (fiberFunctor F V).map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂
          (((canonicalFiberPseudofunctor X.p).map I₂.f.op.toLoc).toFunctor.obj x)).inv := by
  -- This is exactly the specialized left-boundary normalization for the canonical target shell.
  simpa only [Category.id_comp] using
    local_cover_descent_data_functor_pullHom_left_boundary
      (F := F) (f := I₂.f) (g := f₂) (gf := q) (hgf := hf₂) x

/-- Helper for Lemma 8.4.8: the left leg of the canonical target overlap is the specialized
right-boundary shell whose target comparison lives over the common map `q`. -/
private theorem canonical_target_descent_left_leg_normalized
    (F : X ⟶ Y) {U : C} (T : J.Cover U) (x : X.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ : T.Arrow}
    (f₁ : V ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁
        (((canonicalFiberPseudofunctor X.p).map I₁.f.op.toLoc).toFunctor.obj x)).inv ≫
      (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).inv) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
        ((fiberFunctor F U).obj x)) =
    (fiberFunctor F V).map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) q x).inv := by
  -- This is exactly the specialized right-boundary normalization for the canonical target shell.
  simpa only [Category.id_comp] using
    local_cover_descent_data_functor_pullHom_right_boundary
      (F := F) (f := I₁.f) (g := f₁) (gf := q) (hgf := hf₁) x

/-- Helper for Lemma 8.4.8: before cancelling the final mapped `I₂`-comparison, the canonical
target overlap already agrees with the grouped comparison-conjugate shell on the fixed cover. -/
private theorem canonical_target_descent_component_comm_rhs_owner_normal_form
    (F : X ⟶ Y) {U : C} (T : J.Cover U) (x : X.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
        ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).hom) =
    ((((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).hom) ≫
        ((local_cover_descent_data_functor (F := F) T).obj
          (((canonicalFiberPseudofunctor X.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).inv)) ≫
      (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).hom) := by
  let F₁ := ((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor
  let F₂ := ((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor
  let D :=
    ((canonicalFiberPseudofunctor X.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj x
  let e₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x
  let e₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x
  let eq₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁
    (((canonicalFiberPseudofunctor X.p).map I₁.f.op.toLoc).toFunctor.obj x)
  let eq₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂
    (((canonicalFiberPseudofunctor X.p).map I₂.f.op.toLoc).toFunctor.obj x)
  let eqq := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) q x
  let leftSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)
  let targetLeft :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
      ((fiberFunctor F U).obj x))
  let targetRight :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
      ((fiberFunctor F U).obj x))
  let core :=
    F₁.map e₁.hom ≫
      ((local_cover_descent_data_functor (F := F) T).obj D).hom q f₁ f₂ hf₁ hf₂
  have hleft_raw :
      eq₁.inv ≫ F₁.map e₁.inv ≫ targetLeft =
        (fiberFunctor F V).map leftSource ≫ eqq.inv := by
    simpa only [F₁, eq₁, e₁, leftSource, eqq, targetLeft] using
      canonical_target_descent_left_leg_normalized
        (F := F) T x (q := q)
        (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
  have hleft_cancel₁ :
      F₁.map e₁.inv ≫ targetLeft =
        eq₁.hom ≫ ((fiberFunctor F V).map leftSource ≫ eqq.inv) := by
    exact (Iso.inv_comp_eq eq₁).1 (by simpa only [Category.assoc] using hleft_raw)
  have hleft :
      targetLeft =
        F₁.map e₁.hom ≫ eq₁.hom ≫ (fiberFunctor F V).map leftSource ≫ eqq.inv := by
    exact
      (Iso.inv_comp_eq (F₁.mapIso e₁)).1 <| by
        simpa only [Category.assoc] using hleft_cancel₁
  have hright :
      targetRight ≫ F₂.map e₂.hom =
        eqq.hom ≫ (fiberFunctor F V).map rightSource ≫ eq₂.inv := by
    simpa only [F₂, e₂, eqq, rightSource, eq₂] using
      canonical_target_descent_right_leg_postcompose
        (F := F) T x (q := q)
        (I₂ := I₂) (f₂ := f₂) (hf₂ := hf₂)
  have hq_cancel :
      eqq.inv ≫ eqq.hom ≫ ((fiberFunctor F V).map rightSource ≫ eq₂.inv) =
        (fiberFunctor F V).map rightSource ≫ eq₂.inv := by
    simpa only [Category.assoc] using
      stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
        (H := F) (g := q) (x := x)
        (k := (fiberFunctor F V).map rightSource ≫ eq₂.inv)
  have hcore :
      ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        core := by
    let lhsOwner :=
      ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        F₂.map e₂.hom
    have hstart :
        lhsOwner = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
      calc
        lhsOwner = (targetLeft ≫ targetRight) ≫ F₂.map e₂.hom := by
          rfl
        _ = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
          simp only [Category.assoc]
    have hstep_right :
        lhsOwner = targetLeft ≫ (eqq.hom ≫ (fiberFunctor F V).map rightSource ≫ eq₂.inv) := by
      exact hstart.trans (congrArg (fun k ↦ targetLeft ≫ k) hright)
    have hstep_left :
        lhsOwner =
          (F₁.map e₁.hom ≫ eq₁.hom ≫ (fiberFunctor F V).map leftSource ≫ eqq.inv) ≫
            (eqq.hom ≫ (fiberFunctor F V).map rightSource ≫ eq₂.inv) := by
      exact hstep_right.trans <|
        congrArg
          (fun k ↦ k ≫ (eqq.hom ≫ (fiberFunctor F V).map rightSource ≫ eq₂.inv))
          hleft
    have hstep_flat :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((fiberFunctor F V).map leftSource ≫ eqq.inv ≫ eqq.hom ≫
              (fiberFunctor F V).map rightSource ≫ eq₂.inv) := by
      simpa only [Category.assoc] using hstep_left
    have hstep_cancel :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((fiberFunctor F V).map leftSource ≫
              ((fiberFunctor F V).map rightSource ≫ eq₂.inv)) := by
      exact hstep_flat.trans <|
        congrArg
          (fun k ↦
            F₁.map e₁.hom ≫ eq₁.hom ≫ ((fiberFunctor F V).map leftSource ≫ k))
          hq_cancel
    have hstep_map :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            (fiberFunctor F V).map (leftSource ≫ rightSource) ≫ eq₂.inv := by
      have hstep_grouped :
          lhsOwner =
            F₁.map e₁.hom ≫ eq₁.hom ≫
              ((fiberFunctor F V).map leftSource ≫
                (fiberFunctor F V).map rightSource) ≫ eq₂.inv := by
        simpa only [Category.assoc] using hstep_cancel
      exact hstep_grouped.trans <|
        congrArg
          (fun k ↦ F₁.map e₁.hom ≫ eq₁.hom ≫ k ≫ eq₂.inv)
          ((fiberFunctor F V).map_comp leftSource rightSource).symm
    simpa only [lhsOwner] using hstep_map.trans rfl
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
          exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
          rw [F₂.map_id]
  have hinsert :
      core =
        ((((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).hom) ≫
            ((local_cover_descent_data_functor (F := F) T).obj
              (((canonicalFiberPseudofunctor X.p).toDescentData
                (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).inv)) ≫
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).hom) := by
    calc
      core = core ≫ 𝟙 _ := by
        rw [Category.comp_id]
      _ = core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
        exact congrArg (fun k ↦ core ≫ k) htail.symm
      _ = (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
        simp only [Category.assoc]
      _ =
          ((((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).hom) ≫
              ((local_cover_descent_data_functor (F := F) T).obj
                (((canonicalFiberPseudofunctor X.p).toDescentData
                  (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).inv)) ≫
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).hom) := by
            simpa only [core, D, F₁, F₂, e₁, e₂, Category.assoc]
  exact hcore.trans hinsert

/-- Helper for Lemma 8.4.8: the canonical target overlap morphism is the comparison-conjugate of
the transported canonical source overlap morphism on a fixed cover. -/
private theorem canonical_target_descent_hom_eq_comparison_conjugate
    (F : X ⟶ Y) {U : C} (T : J.Cover U) (x : X.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
        ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
      (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).hom) ≫
        ((local_cover_descent_data_functor (F := F) T).obj
          (((canonicalFiberPseudofunctor X.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).inv) := by
  let F₂ := ((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor
  let e₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x
  -- Cancel the final mapped `I₂`-comparison in the grouped owner normal form.
  exact
    (Iso.cancel_iso_hom_right _ _ (F₂.mapIso e₂)).1 <| by
      change
        ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
              ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
            F₂.map e₂.hom =
          ((((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).hom) ≫
              ((local_cover_descent_data_functor (F := F) T).obj
                (((canonicalFiberPseudofunctor X.p).toDescentData
                  (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              F₂.map e₂.inv) ≫
            F₂.map e₂.hom
      -- The dedicated owner normal form already records the postcomposed comparison shell.
      simpa only [F₂, e₂, Category.assoc] using
        canonical_target_descent_component_comm_rhs_owner_normal_form
          (F := F) T x (q := q)
          (I₁ := I₁) (I₂ := I₂)
          (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)

/-- Helper for Lemma 8.4.8: on one fixed cover, the pullback-comparison components identify the
image of the canonical source descent datum of `x` with the canonical target descent datum of
`F(x)`. -/
private theorem local_cover_descent_data_functor_component_comm
    (F : X ⟶ Y) {U : C} (T : J.Cover U) (x : X.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).hom) ≫
      ((local_cover_descent_data_functor (F := F) T).obj
        (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj x)).hom
          q f₁ f₂ hf₁ hf₂ =
      ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
          ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x).hom) := by
  let F₂ := ((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor
  let e₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₂.f x
  let core :=
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I₁.f x).hom) ≫
      ((local_cover_descent_data_functor (F := F) T).obj
        (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂
  have hstrong :
      ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
        core ≫ F₂.map e₂.inv := by
    -- Reassociate the strong comparison-conjugate theorem to the `core ≫ map(inv)` form.
    simpa only [core, F₂, e₂, Category.assoc] using
      canonical_target_descent_hom_eq_comparison_conjugate
        (F := F) T x (q := q)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hpost :
      ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
    -- Postcompose the strong comparison-conjugate identity by the mapped right comparison hom.
    exact congrArg (fun k ↦ k ≫ F₂.map e₂.hom) hstrong
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The mapped right comparison pair cancels by functoriality.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have hcancel : (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom = core := by
    -- The mapped right comparison pair cancels in one step.
    calc
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
          core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
            simp only [Category.assoc]
      _ = core ≫ 𝟙 _ := by
            exact congrArg (fun k ↦ core ≫ k) htail
      _ = core := by
            rw [Category.comp_id]
  have hpost' :
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
        ((((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
              ((fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom := by
    exact hpost.symm
  exact hcancel.symm.trans hpost'

/-- Helper for Lemma 8.4.8: the fixed-cover transport functor carries the canonical descent datum
of `x` in `X` to the canonical descent datum of `F(x)` in `Y`, with components given by the
pullback-comparison isomorphisms. -/
private noncomputable abbrev local_cover_descent_data_functor_toDescentData_iso
    (F : X ⟶ Y) {U : C} (T : J.Cover U) :
    (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : T.Arrow ↦ I.f)) ⋙
      local_cover_descent_data_functor (F := F) T) ≅
      ((fiberFunctor F U) ⋙
        ((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f))) := by
  let η :
      ((fiberFunctor F U) ⋙
          ((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f))) ≅
        (((canonicalFiberPseudofunctor X.p).toDescentData (fun I : T.Arrow ↦ I.f)) ⋙
          local_cover_descent_data_functor (F := F) T) :=
    NatIso.ofComponents
      (fun x ↦
        -- The fixed-cover comparison isomorphism is built componentwise from the pullback
        -- comparisons along the cover legs.
        Pseudofunctor.DescentData.isoMk
          (fun I ↦ FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f x)
          (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
            local_cover_descent_data_functor_component_comm
              (F := F) T x (q := q)
              (I₁ := I₁) (I₂ := I₂)
              (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)))
      (fun φ ↦ by
        -- Naturality is exactly the hom-side pullback-comparison square on the fixed cover legs.
        apply Pseudofunctor.DescentData.hom_ext
        intro I
        rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
        simpa only [Functor.comp_map, local_cover_descent_data_functor] using
          stack_morphism_pullbackComparison_naturality_over_vertical
            (H := F) (f := I.f) (φ := φ))
  exact η.symm

/-- Helper for Lemma 8.4.8: reflect the canonical target overlap shell through the fully faithful
fiber functor over `V`. -/
private noncomputable abbrev source_descent_overlap_hom_of_local_preimages
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁)) ⟶
      (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂)) :=
  let hffV : (fiberFunctor F V).FullyFaithful :=
    Classical.choice (fiber_functor_fullyFaithful_of_fullyFaithful (F := F) hff V)
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
  let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
  hffV.preimage
    (c₁.inv ≫
      (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
      Dy.hom q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
      c₂.hom)

/-- Helper for Lemma 8.4.8: mapping the reflected source overlap morphism recovers the
comparison-conjugated target shell. -/
private theorem source_descent_overlap_hom_map
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (fiberFunctor F V).map
        (source_descent_overlap_hom_of_local_preimages
          (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂) =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
        ((((canonicalFiberPseudofunctor Y.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)).hom := by
  let hffV : (fiberFunctor F V).FullyFaithful :=
    Classical.choice (fiber_functor_fullyFaithful_of_fullyFaithful (F := F) hff V)
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
  let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
  -- The reflected overlap morphism was defined as the unique preimage of this target shell.
  simpa only [source_descent_overlap_hom_of_local_preimages, hffV, Dy, c₁, c₂] using
    hffV.map_preimage
      (c₁.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
        Dy.hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
        c₂.hom)

/-- Helper for Lemma 8.4.8: the reflected source overlap is the identity on a self-overlap. -/
private theorem source_descent_datum_of_local_preimages_hom_self
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I : T.Arrow}
    (g : V ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    source_descent_overlap_hom_of_local_preimages
      (F := F) hff T y xI eI' q g g hg hg = 𝟙 _ := by
  let hffV : (fiberFunctor F V).FullyFaithful :=
    Classical.choice (fiber_functor_fullyFaithful_of_fullyFaithful (F := F) hff V)
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let c := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g (xI I)
  let eg :=
    (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.mapIso (eI' I))
  -- Reflect the equality through the fully faithful fiber functor over `V`.
  apply hffV.map_injective
  calc
    (fiberFunctor F V).map
        (source_descent_overlap_hom_of_local_preimages
          (F := F) hff T y xI eI' q g g hg hg) =
      c.inv ≫ eg.hom ≫ Dy.hom q g g hg hg ≫ eg.inv ≫ c.hom := by
        -- Unfold the reflected overlap exactly once to expose the comparison-conjugated shell.
        simpa only [Dy, c, eg, Category.assoc] using
          source_descent_overlap_hom_map
            (F := F) hff T y xI eI' (q := q) (I₁ := I) (I₂ := I)
            (f₁ := g) (f₂ := g) (hf₁ := hg) (hf₂ := hg)
    _ = c.inv ≫ eg.hom ≫ 𝟙 _ ≫ eg.inv ≫ c.hom := by
      -- The canonical target descent datum has identity self-overlap.
      simpa only [Dy] using
        congrArg
          (fun k ↦ c.inv ≫ eg.hom ≫ k ≫ eg.inv ≫ c.hom)
          (Dy.hom_self q g hg)
    _ = 𝟙 _ := by
      -- First cancel the pulled-back local component isomorphism, then cancel the comparison
      -- isomorphism over `g`.
      calc
        c.inv ≫ eg.hom ≫ 𝟙 _ ≫ eg.inv ≫ c.hom =
          c.inv ≫ (eg.hom ≫ eg.inv) ≫ c.hom := by
            simp only [Category.assoc, Category.id_comp]
        _ = c.inv ≫ 𝟙 _ ≫ c.hom := by
            exact congrArg (fun k ↦ c.inv ≫ k ≫ c.hom) eg.hom_inv_id
        _ = c.inv ≫ c.hom := by
            simp only [Category.id_comp]
        _ = 𝟙 _ := by
            exact c.inv_hom_id
    _ = (fiberFunctor F V).map (𝟙 _) := by
      rw [Functor.map_id]

/-- Helper for Lemma 8.4.8: the reflected source overlaps satisfy the cocycle identity after
mapping to the target fiber in the canonical comparison-conjugated shell. -/
private theorem source_descent_overlap_hom_map_middle_cancellation_normalized
    (F : X ⟶ Y)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    let Dy :=
      (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
    let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
    let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
    let c₃ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)
    let eg₁ :=
      (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.mapIso (eI' I₁))
    let eg₂ :=
      (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.mapIso (eI' I₂))
    let eg₃ :=
      (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.mapIso (eI' I₃))
    (c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ eg₂.inv ≫ c₂.hom) ≫
        (c₂.inv ≫ eg₂.hom ≫ Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom) =
      c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₃ hf₁ hf₃ ≫ eg₃.inv ≫ c₃.hom := by
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
  let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
  let c₃ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)
  let eg₁ :=
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.mapIso (eI' I₁))
  let eg₂ :=
    (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.mapIso (eI' I₂))
  let eg₃ :=
    (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.mapIso (eI' I₃))
  -- Cancel the literal middle comparison shells first, then apply the target cocycle identity.
  calc
    (c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ eg₂.inv ≫ c₂.hom) ≫
        (c₂.inv ≫ eg₂.hom ≫ Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom) =
      c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ eg₂.inv ≫
        (c₂.hom ≫ c₂.inv) ≫ eg₂.hom ≫
        Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom := by
          simp only [Category.assoc]
    _ =
      c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ eg₂.inv ≫
        𝟙 _ ≫ eg₂.hom ≫
        Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom := by
          exact congrArg
            (fun k ↦
              c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ eg₂.inv ≫
                k ≫ eg₂.hom ≫ Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom)
            c₂.hom_inv_id
    _ =
      c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫
        (eg₂.inv ≫ eg₂.hom) ≫
        Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom := by
          simp only [Category.assoc, Category.id_comp]
    _ =
      c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ 𝟙 _ ≫
        Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom := by
          exact congrArg
            (fun k ↦
              c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫
                k ≫ Dy.hom q f₂ f₃ hf₂ hf₃ ≫ eg₃.inv ≫ c₃.hom)
            eg₂.inv_hom_id
    _ =
      c₁.inv ≫ eg₁.hom ≫
        (Dy.hom q f₁ f₂ hf₁ hf₂ ≫ Dy.hom q f₂ f₃ hf₂ hf₃) ≫
        eg₃.inv ≫ c₃.hom := by
          simp only [Category.assoc, Category.id_comp]
    _ =
      c₁.inv ≫ eg₁.hom ≫ Dy.hom q f₁ f₃ hf₁ hf₃ ≫ eg₃.inv ≫ c₃.hom := by
          exact congrArg
            (fun k ↦ c₁.inv ≫ eg₁.hom ≫ k ≫ eg₃.inv ≫ c₃.hom)
            (Dy.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Helper for Lemma 8.4.8: the reflected source overlaps satisfy the cocycle identity after
mapping to the target fiber in the canonical comparison-conjugated shell. -/
private theorem source_descent_overlap_hom_map_cocycle_flat
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    (fiberFunctor F V).map
        (source_descent_overlap_hom_of_local_preimages
          (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂ ≫
          source_descent_overlap_hom_of_local_preimages
            (F := F) hff T y xI eI' q f₂ f₃ hf₂ hf₃) =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
        ((((canonicalFiberPseudofunctor Y.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₃ hf₁ hf₃) ≫
        (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.map (eI' I₃).inv) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)).hom := by
  let h₁₂ :=
    source_descent_overlap_hom_of_local_preimages
      (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂
  let h₂₃ :=
    source_descent_overlap_hom_of_local_preimages
      (F := F) hff T y xI eI' q f₂ f₃ hf₂ hf₃
  have hmap₁₂ :
      (fiberFunctor F V).map h₁₂ =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₂ hf₁ hf₂) ≫
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)).hom := by
    -- Expose the first reflected overlap in its literal target shell.
    simpa only [h₁₂] using
      source_descent_overlap_hom_map
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hmap₂₃ :
      (fiberFunctor F V).map h₂₃ =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q f₂ f₃ hf₂ hf₃) ≫
          (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.map (eI' I₃).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)).hom := by
    -- Expose the second reflected overlap in the same literal target shell syntax.
    simpa only [h₂₃] using
      source_descent_overlap_hom_map
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₂) (I₂ := I₃)
        (f₁ := f₂) (f₂ := f₃) (hf₁ := hf₂) (hf₂ := hf₃)
  -- Route correction: package both mapped source overlaps first, then cancel the middle
  -- comparison shells explicitly before invoking the target cocycle identity.
  calc
    (fiberFunctor F V).map (h₁₂ ≫ h₂₃) =
      (fiberFunctor F V).map h₁₂ ≫ (fiberFunctor F V).map h₂₃ := by
        rw [Functor.map_comp]
    _ =
      ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₂ hf₁ hf₂) ≫
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)).hom) ≫
        ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q f₂ f₃ hf₂ hf₃) ≫
          (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.map (eI' I₃).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)).hom) := by
            exact congrArg₂ (fun a b ↦ a ≫ b) hmap₁₂ hmap₂₃
    _ =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
        ((((canonicalFiberPseudofunctor Y.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₃ hf₁ hf₃) ≫
        (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.map (eI' I₃).inv) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)).hom := by
          simpa only using
            source_descent_overlap_hom_map_middle_cancellation_normalized
              (F := F) T y xI eI'
              (q := q) (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
              (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
              (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃)

/-- Helper for Lemma 8.4.8: the reflected source overlaps satisfy the cocycle identity after
mapping to the target fiber. -/
private theorem source_descent_datum_of_local_preimages_hom_comp
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    source_descent_overlap_hom_of_local_preimages
        (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂ ≫
      source_descent_overlap_hom_of_local_preimages
        (F := F) hff T y xI eI' q f₂ f₃ hf₂ hf₃ =
      source_descent_overlap_hom_of_local_preimages
        (F := F) hff T y xI eI' q f₁ f₃ hf₁ hf₃ := by
  let hffV : (fiberFunctor F V).FullyFaithful :=
    Classical.choice (fiber_functor_fullyFaithful_of_fullyFaithful (F := F) hff V)
  -- Reflect the cocycle law through the fully faithful fiber functor over `V`.
  apply hffV.map_injective
  have hleft :
      (fiberFunctor F V).map
          (source_descent_overlap_hom_of_local_preimages
            (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂ ≫
            source_descent_overlap_hom_of_local_preimages
              (F := F) hff T y xI eI' q f₂ f₃ hf₂ hf₃) =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₃ hf₁ hf₃) ≫
          (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.map (eI' I₃).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)).hom := by
    -- Package the mapped two-step source cocycle into the final target shell at `(f₁, f₃)`.
    simpa only [Category.assoc] using
      source_descent_overlap_hom_map_cocycle_flat
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
        (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
        (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃)
  have hright :
      (fiberFunctor F V).map
          (source_descent_overlap_hom_of_local_preimages
            (F := F) hff T y xI eI' q f₁ f₃ hf₁ hf₃) =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₃ hf₁ hf₃) ≫
          (((canonicalFiberPseudofunctor Y.p).map f₃.op.toLoc).toFunctor.map (eI' I₃).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₃ (xI I₃)).hom := by
    -- The one-step reflected overlap already has the same normalized target shell.
    simpa only [Category.assoc] using
      source_descent_overlap_hom_map
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₁) (I₂ := I₃)
        (f₁ := f₁) (f₂ := f₃) (hf₁ := hf₁) (hf₂ := hf₃)
  exact hleft.trans hright.symm

/-- Helper for Lemma 8.4.8: at the common refinement leg, the mapped reflected overlap already
has the normalized target shell that the pullback-compatibility proof must match. -/
private theorem source_descent_overlap_hom_map_common_refinement
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' : C} (q' : V' ⟶ U) {I₁ I₂ : T.Arrow}
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁q : gf₁ ≫ I₁.f = q' := by cat_disch) (hgf₂q : gf₂ ≫ I₂.f = q' := by cat_disch) :
    (fiberFunctor F V').map
        (source_descent_overlap_hom_of_local_preimages
          (F := F) hff T y xI eI' q' gf₁ gf₂ hgf₁q hgf₂q) =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
        ((((canonicalFiberPseudofunctor Y.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj y).hom q' gf₁ gf₂ hgf₁q hgf₂q) ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)).hom := by
  -- Specialize the reflected-shell formula to the common-refinement overlap `q'`.
  simpa only [Category.assoc] using
    source_descent_overlap_hom_map
      (F := F) hff T y xI eI'
      (q := q') (I₁ := I₁) (I₂ := I₂)
      (f₁ := gf₁) (f₂ := gf₂) (hf₁ := hgf₁q) (hf₂ := hgf₂q)

/-- Helper for Lemma 8.4.8: the raw left owner-side comparison shell can be canceled before the
local component isomorphism is whiskered across the common refinement leg. -/
private theorem source_descent_overlap_left_boundary_postcompose_inv_normalized
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    {V' V : C} (g : V' ⟶ V)
    {I₁ : T.Arrow} (f₁ : V ⟶ I₁.Y) (gf₁ : V' ⟶ I₁.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((fiberFunctor F I₁.Y).obj (xI I₁)))
    let leftSource :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          (xI I₁))
    let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
    let cgf₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)
    let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
    cgf₁.inv ≫ leftTarget =
      ((fiberFunctor F V').map leftSource ≫ cg₁.inv) ≫ FYg.map c₁.inv := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((fiberFunctor F I₁.Y).obj (xI I₁)))
  let leftSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (xI I₁))
  let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
  let cgf₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)
  let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
  have hboundary :
      leftTarget ≫ FYg.map c₁.hom =
        cgf₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv := by
    -- Start from the already proved owner-side left boundary shell over the common refinement.
    simpa only [FYg, leftTarget, leftSource, c₁, cgf₁, cg₁] using
      local_cover_descent_data_functor_pullHom_left_boundary
        (F := F) f₁ g gf₁ hgf₁ (xI I₁)
  have hpost :
      leftTarget =
        cgf₁.hom ≫ ((fiberFunctor F V').map leftSource ≫ cg₁.inv) ≫ FYg.map c₁.inv := by
    -- Postcompose by the mapped inverse comparison so the final `c₁.hom ≫ c₁.inv` shell cancels
    -- in the literal downstream orientation.
    have hpost' :
        leftTarget =
          (cgf₁.hom ≫ (fiberFunctor F V').map leftSource ≫ cg₁.inv) ≫
            (FYg.mapIso c₁).inv := by
      exact (Iso.eq_comp_inv (FYg.mapIso c₁)).2 <| by
        simpa only [Category.assoc] using hboundary
    simpa only [Category.assoc] using hpost'
  -- Precompose by the `gf₁`-comparison inverse to expose the exact left prefix consumed later.
  exact (Iso.inv_comp_eq cgf₁).2 <| by
    simpa only [Category.assoc] using hpost

/-- Helper for Lemma 8.4.8: the raw left owner-side comparison shell can be canceled before the
local component isomorphism is whiskered across the common refinement leg. -/
private theorem source_descent_overlap_pullHom_left_comparison_cancel
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    {V' V : C} (g : V' ⟶ V)
    {I₁ : T.Arrow} (f₁ : V ⟶ I₁.Y) (gf₁ : V' ⟶ I₁.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((fiberFunctor F I₁.Y).obj (xI I₁)))
    let leftSource :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          (xI I₁))
    let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
    let cgf₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)
    let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
    (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫ FYg.map c₁.inv =
      cgf₁.inv ≫ leftTarget := by
  -- Route correction: use the literal postcomposed normalization first, then just reassociate the
  -- threefold prefix into the exact left-whiskered orientation.
  simpa only [Category.assoc] using
    (source_descent_overlap_left_boundary_postcompose_inv_normalized
      (F := F) T y xI (g := g) (f₁ := f₁) (gf₁ := gf₁) (hgf₁ := hgf₁)).symm

/-- Helper for Lemma 8.4.8: the `mapComp'` hom component is natural in the local comparison
isomorphism, already reassociated in the form used on the common refinement leg. -/
private theorem mapComp_hom_naturality_reassociated_over_common_refinement
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' V : C} (g : V' ⟶ V)
    {I₁ : T.Arrow} (f₁ : V ⟶ I₁.Y) (gf₁ : V' ⟶ I₁.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((fiberFunctor F I₁.Y).obj (xI I₁)))
    let leftY :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          (I₁.f ^*[localCanonicalPullbackChoice Y.p] y))
    leftTarget ≫
        FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          (eI' I₁).hom) =
      (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
        (eI' I₁).hom) ≫
        leftY := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((fiberFunctor F I₁.Y).obj (xI I₁)))
  let leftY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (I₁.f ^*[localCanonicalPullbackChoice Y.p] y))
  -- Package the `mapComp'` hom naturality square in the exact reassociated orientation needed
  -- after the left boundary shell has been normalized.
  simpa only [FYg, leftTarget, leftY, Category.assoc] using
    ((((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans).naturality
      ((eI' I₁).hom)).symm

/-- Helper for Lemma 8.4.8: the `mapComp'` inverse component is natural in the inverse local
comparison isomorphism, already reassociated in the form used on the common refinement leg. -/
private theorem mapComp_inv_naturality_reassociated_over_common_refinement
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' V : C} (g : V' ⟶ V)
    {I₂ : T.Arrow} (f₂ : V ⟶ I₂.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((fiberFunctor F I₂.Y).obj (xI I₂)))
    let rightY :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          (I₂.f ^*[localCanonicalPullbackChoice Y.p] y))
    FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          (eI' I₂).inv) ≫
        rightTarget =
      rightY ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          (eI' I₂).inv) := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((fiberFunctor F I₂.Y).obj (xI I₂)))
  let rightY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (I₂.f ^*[localCanonicalPullbackChoice Y.p] y))
  -- Package the inverse `mapComp'` naturality square in the exact orientation consumed by the
  -- right whiskered shell proof.
  simpa only [FYg, rightTarget, rightY, Category.assoc] using
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans).naturality
      ((eI' I₂).inv)

/-- Helper for Lemma 8.4.8: the raw right owner-side comparison shell can be canceled before the
inverse local component isomorphism is whiskered across the common refinement leg. -/
private theorem source_descent_overlap_pullHom_right_comparison_cancel
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    {V' V : C} (g : V' ⟶ V)
    {I₂ : T.Arrow} (f₂ : V ⟶ I₂.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((fiberFunctor F I₂.Y).obj (xI I₂)))
    let rightSource :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          (xI I₂))
    let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
    let cgf₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)
    let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂))
    FYg.map c₂.hom ≫ cg₂.hom ≫ (fiberFunctor F V').map rightSource =
      rightTarget ≫ cgf₂.hom := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((fiberFunctor F I₂.Y).obj (xI I₂)))
  let rightSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (xI I₂))
  let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
  let cgf₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)
  let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂))
  have hboundary :
      cg₂.inv ≫ FYg.map c₂.inv ≫ rightTarget =
        (fiberFunctor F V').map rightSource ≫ cgf₂.inv := by
    -- Reuse the already normalized right owner-side boundary shell over the common refinement.
    simpa only [FYg, rightTarget, rightSource, c₂, cgf₂, cg₂] using
      local_cover_descent_data_functor_pullHom_right_boundary
        (F := F) f₂ g gf₂ hgf₂ (xI I₂)
  have hcancel_left :
      FYg.map c₂.inv ≫ rightTarget =
        cg₂.hom ≫ ((fiberFunctor F V').map rightSource ≫ cgf₂.inv) := by
    -- Cancel the left `g`-comparison first so the remaining shell is literal.
    exact (Iso.inv_comp_eq cg₂).1 <| by
      simpa only [Category.assoc] using hboundary
  have hcancel_both :
      rightTarget =
        FYg.map c₂.hom ≫ cg₂.hom ≫ (fiberFunctor F V').map rightSource ≫ cgf₂.inv := by
    -- Then cancel the mapped `f₂`-comparison to expose the target-side shell.
    exact (Iso.inv_comp_eq (FYg.mapIso c₂)).1 <| by
      simpa only [Category.assoc] using hcancel_left
  have hpost :
      rightTarget ≫ cgf₂.hom =
        FYg.map c₂.hom ≫ cg₂.hom ≫ (fiberFunctor F V').map rightSource := by
    -- Postcompose by the `gf₂`-comparison to remove the final inverse shell.
    have hcancel_both' :
        rightTarget =
          (FYg.map c₂.hom ≫ cg₂.hom ≫ (fiberFunctor F V').map rightSource) ≫ cgf₂.inv := by
      simpa only [Category.assoc] using hcancel_both
    exact (Iso.eq_comp_inv cgf₂).1 hcancel_both'
  simpa only [Category.assoc] using hpost.symm

/-- Helper for Lemma 8.4.8: after the left comparison shell is transported to the common
refinement leg, the raw prefix becomes the pulled-back local isomorphism on `gf₁`. -/
private theorem source_descent_overlap_pullHom_left_local_iso_whiskered
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' V : C} (g : V' ⟶ V)
    {I₁ : T.Arrow} (f₁ : V ⟶ I₁.Y) (gf₁ : V' ⟶ I₁.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((fiberFunctor F I₁.Y).obj (xI I₁)))
    let leftY :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          (I₁.f ^*[localCanonicalPullbackChoice Y.p] y))
    let leftSource :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          (xI I₁))
    let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
    let cgf₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)
    let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
    (fiberFunctor F V').map leftSource ≫
        cg₁.inv ≫ FYg.map c₁.inv ≫
        FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          (eI' I₁).hom) =
      cgf₁.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          (eI' I₁).hom) ≫
        leftY := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((fiberFunctor F I₁.Y).obj (xI I₁)))
  let leftY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (I₁.f ^*[localCanonicalPullbackChoice Y.p] y))
  let leftSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (xI I₁))
  let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
  let cgf₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)
  let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
  have hprefix :
      (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫ FYg.map c₁.inv =
        cgf₁.inv ≫ leftTarget := by
    -- Normalize the owner-side left comparison shell to the literal common-refinement prefix.
    simpa only [FYg, leftTarget, leftSource, c₁, cgf₁, cg₁, Category.assoc] using
      source_descent_overlap_pullHom_left_comparison_cancel
        (F := F) T y xI (g := g) (f₁ := f₁) (gf₁ := gf₁) (hgf₁ := hgf₁)
  have hnat :
      leftTarget ≫
          FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) =
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          (eI' I₁).hom) ≫
          leftY := by
    -- The pulled-back local comparison isomorphism commutes with the `mapComp'` hom square.
    simpa only [FYg, leftTarget, leftY, Category.assoc] using
      mapComp_hom_naturality_reassociated_over_common_refinement
        (F := F) T y xI eI' (g := g) (f₁ := f₁) (gf₁ := gf₁) (hgf₁ := hgf₁)
  have hnat' :
      cgf₁.inv ≫
          (leftTarget ≫
            FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom)) =
        cgf₁.inv ≫
          ((((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
            leftY) := by
    -- Freeze the outer comparison inverse while replacing the inner `mapComp'` square.
    simpa only [Category.assoc] using
      congrArg (fun k ↦ cgf₁.inv ≫ k) hnat
  have hstep₁ :
      ((fiberFunctor F V').map leftSource ≫ cg₁.inv ≫ FYg.map c₁.inv) ≫
          FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) =
        (cgf₁.inv ≫ leftTarget) ≫
          FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) := by
    -- Freeze the final mapped local component while replacing the normalized left boundary.
    exact congrArg
      (fun k ↦ k ≫
        FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          (eI' I₁).hom))
      hprefix
  have hstep₂ :
      (cgf₁.inv ≫ leftTarget) ≫
          FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) =
        cgf₁.inv ≫
          (leftTarget ≫
            FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom)) := by
    simp only [Category.assoc]
  have hstep₃ :
      cgf₁.inv ≫
          ((((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
            leftY) =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY := by
    simp only [Category.assoc]
  -- Replace the left boundary shell first, then whisker the local isomorphism across the
  -- already-packaged naturality square.
  have hstart :
      (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫ FYg.map c₁.inv ≫
          FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) =
        ((fiberFunctor F V').map leftSource ≫ cg₁.inv ≫ FYg.map c₁.inv) ≫
          FYg.map (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) := by
    simp only [Category.assoc]
  exact hstart.trans (hstep₁.trans (hstep₂.trans (hnat'.trans hstep₃)))

/-- Helper for Lemma 8.4.8: the middle target-shell factor is exactly the target descent datum
pullback law on the common refinement leg. -/
private theorem source_descent_overlap_pullHom_middle_target_descent_whiskered
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let Dy :=
      (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
    let leftY :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          (I₁.f ^*[localCanonicalPullbackChoice Y.p] y))
    let rightY :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          (I₂.f ^*[localCanonicalPullbackChoice Y.p] y))
    leftY ≫ FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫ rightY =
      Dy.hom q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let leftY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (I₁.f ^*[localCanonicalPullbackChoice Y.p] y))
  let rightY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (I₂.f ^*[localCanonicalPullbackChoice Y.p] y))
  -- This is exactly the target descent datum pullback axiom, unfolded once.
  simpa only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, FYg, Dy, leftY, rightY] using
    Dy.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- Helper for Lemma 8.4.8: after the right comparison shell is transported to the common
refinement leg, the raw suffix becomes the pulled-back inverse local isomorphism on `gf₂`. -/
private theorem source_descent_overlap_pullHom_right_local_iso_whiskered
    (F : X ⟶ Y) {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' V : C} (g : V' ⟶ V)
    {I₂ : T.Arrow} (f₂ : V ⟶ I₂.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((fiberFunctor F I₂.Y).obj (xI I₂)))
    let rightY :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          (I₂.f ^*[localCanonicalPullbackChoice Y.p] y))
    let rightSource :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          (xI I₂))
    let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
    let cgf₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)
    let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂))
    FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          (eI' I₂).inv) ≫
        FYg.map c₂.hom ≫
        cg₂.hom ≫
        (fiberFunctor F V').map rightSource =
      rightY ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          (eI' I₂).inv) ≫
        cgf₂.hom := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((fiberFunctor F I₂.Y).obj (xI I₂)))
  let rightY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (I₂.f ^*[localCanonicalPullbackChoice Y.p] y))
  let rightSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (xI I₂))
  let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
  let cgf₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)
  let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂))
  have hprefix :
      FYg.map c₂.hom ≫ cg₂.hom ≫ (fiberFunctor F V').map rightSource =
        rightTarget ≫ cgf₂.hom := by
    -- Normalize the owner-side right comparison shell to the literal common-refinement suffix.
    simpa only [FYg, rightTarget, rightY, rightSource, c₂, cgf₂, cg₂, Category.assoc] using
      source_descent_overlap_pullHom_right_comparison_cancel
        (F := F) T y xI (g := g) (f₂ := f₂) (gf₂ := gf₂) (hgf₂ := hgf₂)
  have hnat :
      FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          rightTarget =
        rightY ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) := by
    -- The inverse local comparison isomorphism commutes with the inverse `mapComp'` square.
    simpa only [FYg, rightTarget, rightY, Category.assoc] using
      mapComp_inv_naturality_reassociated_over_common_refinement
        (F := F) T y xI eI' (g := g) (f₂ := f₂) (gf₂ := gf₂) (hgf₂ := hgf₂)
  have hnat' :
      (FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          rightTarget) ≫
          cgf₂.hom =
        (rightY ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv)) ≫
          cgf₂.hom := by
    -- Freeze the final `gf₂`-comparison while replacing the prefix by the naturality square.
    exact congrArg (fun k ↦ k ≫ cgf₂.hom) hnat
  have hstep₁ :
      FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource =
        FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          rightTarget ≫
          cgf₂.hom := by
    calc
      FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource =
        FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          (rightTarget ≫ cgf₂.hom) := by
            exact congrArg
              (fun k ↦
                FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
                  (eI' I₂).inv) ≫ k)
              hprefix
      _ =
        FYg.map (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          rightTarget ≫
          cgf₂.hom := by
            simp only [Category.assoc]
  -- Precompose the normalized right shell by the pulled-back inverse local isomorphism, then
  -- rewrite the resulting prefix by the packaged naturality square.
  exact hstep₁.trans <| by
    simpa only [Category.assoc] using hnat'

/-- Helper for Lemma 8.4.8: the reflected source overlaps should commute with further pullback
once the target shell is normalized to the common refinement leg. -/
private theorem source_descent_overlap_pullHom_middle_reflection_postcompose
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' V : C} (g : V' ⟶ V)
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    {q : V ⟶ U}
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let FXg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let d :=
      source_descent_overlap_hom_of_local_preimages
        (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂
    let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
    let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
      (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂))
    (fiberFunctor F V').map (FXg.map d) =
      cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d) ≫ cg₂.hom := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let d :=
    source_descent_overlap_hom_of_local_preimages
      (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂
  let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
  let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂))
  have hnat :
      (fiberFunctor F V').map (FXg.map d) ≫ cg₂.inv =
        cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d) := by
    -- Move the reflected source overlap across the `g`-comparison shell before normalizing the
    -- left and right boundaries.
    simpa only [FYg, FXg, d, cg₁, cg₂] using
      stack_morphism_pullbackComparison_inv_naturality_over_vertical
        (H := F) (f := g) (φ := d)
  -- Postcompose by the right comparison so the reflected middle factor is already in the literal
  -- syntax consumed by the whiskered left/right boundary lemmas.
  have hpost :
      (fiberFunctor F V').map (FXg.map d) =
        ((fiberFunctor F V').map (FXg.map d) ≫ cg₂.inv) ≫ cg₂.hom := by
    calc
      (fiberFunctor F V').map (FXg.map d) =
        (fiberFunctor F V').map (FXg.map d) ≫ 𝟙 _ := by
          symm
          exact Category.comp_id _
      _ =
        (fiberFunctor F V').map (FXg.map d) ≫ (cg₂.inv ≫ cg₂.hom) := by
          exact congrArg (fun k ↦ (fiberFunctor F V').map (FXg.map d) ≫ k) cg₂.inv_hom_id.symm
      _ =
        ((fiberFunctor F V').map (FXg.map d) ≫ cg₂.inv) ≫ cg₂.hom := by
          simp only [Category.assoc]
  have hpost' :
      ((fiberFunctor F V').map (FXg.map d) ≫ cg₂.inv) ≫ cg₂.hom =
        (cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d)) ≫ cg₂.hom := by
    exact congrArg (fun k ↦ k ≫ cg₂.hom) hnat
  exact hpost.trans <| by
    simpa only [Category.assoc] using hpost'

/-- Helper for Lemma 8.4.8: the reflected source overlaps should commute with further pullback
once the target shell is normalized to the common refinement leg. -/
private theorem source_descent_overlap_pullHom_map_flat
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (fiberFunctor F V').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (source_descent_overlap_hom_of_local_preimages
            (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂) =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
        ((((canonicalFiberPseudofunctor Y.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj y).hom q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)).hom := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let d :=
    source_descent_overlap_hom_of_local_preimages
      (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂
  let leftY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (I₁.f ^*[localCanonicalPullbackChoice Y.p] y))
  let rightY :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (I₂.f ^*[localCanonicalPullbackChoice Y.p] y))
  let leftSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (xI I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (xI I₂))
  let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
  let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
  let cgf₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)
  let cgf₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)
  let cg₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj (xI I₁))
  let cg₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) g
    (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj (xI I₂))
  have hunfolded :
      (fiberFunctor F V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom d g gf₁ gf₂ hgf₁ hgf₂) =
        (fiberFunctor F V').map leftSource ≫
          (fiberFunctor F V').map (FXg.map d) ≫
          (fiberFunctor F V').map rightSource := by
    -- Unfold the reflected source `pullHom` only once so the three visible source pieces can be
    -- normalized independently.
    rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    change
      (fiberFunctor F V').map (leftSource ≫ FXg.map d ≫ rightSource) =
        (fiberFunctor F V').map leftSource ≫
          (fiberFunctor F V').map (FXg.map d) ≫
          (fiberFunctor F V').map rightSource
    rw [functor_map_threefold_comp]
  have hreflect :
      (fiberFunctor F V').map (FXg.map d) =
        cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d) ≫ cg₂.hom := by
    -- Move the reflected source overlap across the `g`-comparison before the target shell is
    -- expanded.
    simpa only [FYg, FXg, d, cg₁, cg₂] using
      source_descent_overlap_pullHom_middle_reflection_postcompose
        (F := F) hff T y xI eI'
        (g := g) (f₁ := f₁) (f₂ := f₂) (q := q)
        (hf₁ := hf₁) (hf₂ := hf₂)
  have hsource :
      (fiberFunctor F V).map d =
        c₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
          Dy.hom q f₁ f₂ hf₁ hf₂ ≫
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
          c₂.hom := by
    -- Reuse the already packaged reflected overlap shell on the `V`-leg.
    simpa only [Dy, d, c₁, c₂] using
      source_descent_overlap_hom_map
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hmap :
      FYg.map ((fiberFunctor F V).map d) =
        FYg.map c₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom := by
    -- Expand the mapped reflected overlap into the visible fivefold target shell.
    calc
      FYg.map ((fiberFunctor F V).map d) =
        FYg.map
          (c₁.inv ≫
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
            Dy.hom q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
            c₂.hom) := by
              exact congrArg FYg.map hsource
      _ =
        FYg.map c₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom := by
              repeat rw [Functor.map_comp]
  have hleft :
      (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫ FYg.map c₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY := by
    -- Normalize the left boundary and whisker the left local isomorphism to the common
    -- refinement leg.
    simpa only [FYg, leftY, leftSource, c₁, cgf₁, cg₁] using
      source_descent_overlap_pullHom_left_local_iso_whiskered
        (F := F) T y xI eI'
        (g := g) (f₁ := f₁) (gf₁ := gf₁) (hgf₁ := hgf₁)
  have hmid :
      leftY ≫ FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫ rightY =
        Dy.hom q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
    -- The middle target factor is exactly the target descent pullback axiom on the common
    -- refinement leg.
    simpa only [FYg, Dy, leftY, rightY] using
      source_descent_overlap_pullHom_middle_target_descent_whiskered
        (T := T) y
        (g := g) (q := q) (q' := q') (hq := hq)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
        (gf₁ := gf₁) (gf₂ := gf₂) (hgf₁ := hgf₁) (hgf₂ := hgf₂)
  have hright :
      FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource =
        rightY ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom := by
    -- Normalize the right boundary and whisker the inverse local isomorphism to the common
    -- refinement leg.
    simpa only [FYg, rightY, rightSource, c₂, cgf₂, cg₂] using
      source_descent_overlap_pullHom_right_local_iso_whiskered
        (F := F) T y xI eI'
        (g := g) (f₂ := f₂) (gf₂ := gf₂) (hgf₂ := hgf₂)
  have hstart :
      (fiberFunctor F V').map leftSource ≫
          (fiberFunctor F V').map (FXg.map d) ≫
          (fiberFunctor F V').map rightSource =
        (fiberFunctor F V').map leftSource ≫
          cg₁.inv ≫ FYg.map c₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
    -- Route correction: first rewrite the middle reflected source shell through the `g`
    -- comparison, then expand only the mapped reflected overlap into its fivefold target shell.
    have hreflect' := congrArg
      (fun k ↦ (fiberFunctor F V').map leftSource ≫ k ≫ (fiberFunctor F V').map rightSource)
      hreflect
    have hmap' := congrArg
      (fun k ↦
        (fiberFunctor F V').map leftSource ≫ cg₁.inv ≫ k ≫ cg₂.hom ≫
          (fiberFunctor F V').map rightSource)
      hmap
    calc
      (fiberFunctor F V').map leftSource ≫
          (fiberFunctor F V').map (FXg.map d) ≫
          (fiberFunctor F V').map rightSource =
        (fiberFunctor F V').map leftSource ≫
          (cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d) ≫ cg₂.hom) ≫
          (fiberFunctor F V').map rightSource := by
            exact hreflect'
      _ =
        (fiberFunctor F V').map leftSource ≫
          cg₁.inv ≫ FYg.map ((fiberFunctor F V).map d) ≫ cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
            repeat rw [Category.assoc]
      _ =
        (fiberFunctor F V').map leftSource ≫
          cg₁.inv ≫
            (FYg.map c₁.inv ≫
              FYg.map
                (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
                  (eI' I₁).hom) ≫
              FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
              FYg.map
                (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
                  (eI' I₂).inv) ≫
              FYg.map c₂.hom) ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
            exact hmap'
      _ =
        (fiberFunctor F V').map leftSource ≫
          cg₁.inv ≫ FYg.map c₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
            repeat rw [Category.assoc]
  have hleft' :
      (fiberFunctor F V').map leftSource ≫
          cg₁.inv ≫ FYg.map c₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
    -- Replace the normalized left prefix while freezing the remaining middle and right factors.
    have hleft'' := congrArg
      (fun k ↦
        k ≫ FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource)
      hleft
    calc
      (fiberFunctor F V').map leftSource ≫
          cg₁.inv ≫ FYg.map c₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource =
        ((fiberFunctor F V').map leftSource ≫
            cg₁.inv ≫ FYg.map c₁.inv ≫
            FYg.map
              (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
                (eI' I₁).hom)) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
            repeat rw [Category.assoc]
      _ =
        (cgf₁.inv ≫
            (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
            leftY) ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
            exact hleft''
      _ =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource := by
            repeat rw [Category.assoc]
  have hright' :
      cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              (eI' I₂).inv) ≫
          FYg.map c₂.hom ≫
          cg₂.hom ≫
          (fiberFunctor F V').map rightSource =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          rightY ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom := by
    -- Replace the normalized right suffix while freezing the left prefix and middle target term.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦
          cgf₁.inv ≫
            (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
              (eI' I₁).hom) ≫
            leftY ≫
            FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
            k)
        hright
  have hmid' :
      cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          rightY ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          Dy.hom q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom := by
    -- Collapse the middle common-refinement target shell by the target descent pullback axiom.
    have hmid'' := congrArg
      (fun k ↦
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          k ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom)
      hmid
    calc
      cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          leftY ≫
          FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫
          rightY ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          (leftY ≫ FYg.map (Dy.hom q f₁ f₂ hf₁ hf₂) ≫ rightY) ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom := by
            repeat rw [Category.assoc]
      _ =
        cgf₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            (eI' I₁).hom) ≫
          Dy.hom q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            (eI' I₂).inv) ≫
          cgf₂.hom := by
            exact hmid''
  exact hunfolded.trans (hstart.trans (hleft'.trans (hright'.trans hmid')))

/-- Helper for Lemma 8.4.8: the reflected source overlaps should commute with further pullback
once the target shell is normalized to the common refinement leg. -/
private theorem source_descent_datum_of_local_preimages_pullHom_hom
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (source_descent_overlap_hom_of_local_preimages
          (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      source_descent_overlap_hom_of_local_preimages
        (F := F) hff T y xI eI' q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let hffV' : (fiberFunctor F V').FullyFaithful :=
    Classical.choice (fiber_functor_fullyFaithful_of_fullyFaithful (F := F) hff V')
  -- Reflect the pullback-compatibility law through the fully faithful fiber functor over `V'`.
  apply hffV'.map_injective
  have hleft :
      (fiberFunctor F V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (source_descent_overlap_hom_of_local_preimages
              (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂) =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)).hom := by
    -- Route correction: package the entire pulled-back source shell first, so the proof closes
    -- by direct comparison with the common-refinement target shell.
    simpa only [Category.assoc] using
      source_descent_overlap_pullHom_map_flat
        (F := F) hff T y xI eI'
        (g := g) (q := q) (q' := q') (hq := hq)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
        (gf₁ := gf₁) (gf₂ := gf₂) (hgf₁ := hgf₁) (hgf₂ := hgf₂)
  have hright :
      (fiberFunctor F V').map
          (source_descent_overlap_hom_of_local_preimages
            (F := F) hff T y xI eI' q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₁ (xI I₁)).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
          ((((canonicalFiberPseudofunctor Y.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).obj y).hom q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map (eI' I₂).inv) ≫
          (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) gf₂ (xI I₂)).hom := by
    -- The reflected overlap on the common refinement has the identical target shell.
    simpa only [Category.assoc] using
      source_descent_overlap_hom_map_common_refinement
        (F := F) hff T y xI eI'
        (q' := q') (I₁ := I₁) (I₂ := I₂)
        (gf₁ := gf₁) (gf₂ := gf₂)
        (hgf₁q := by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (hgf₂q := by rw [← hq, ← hgf₂, Category.assoc, hf₂])
  exact hleft.trans hright.symm

/-- Helper for Lemma 8.4.8: the chosen local lifts determine source descent data on the fixed
cover once their overlap morphisms are reflected from the target. -/
private noncomputable abbrev source_descent_datum_of_local_preimages
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y) :
    ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)) :=
  { obj := xI
    hom := fun {V} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦
      source_descent_overlap_hom_of_local_preimages
        (F := F) hff T y xI eI'
        (V := V) (q := q) (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
    pullHom_hom := fun {V' V} g q q' hq {I₁ I₂} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
      source_descent_datum_of_local_preimages_pullHom_hom
        (F := F) hff T y xI eI' (V' := V') (V := V) (g := g) (q := q) (q' := q')
        (hq := hq) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
        (hf₁ := hf₁) (hf₂ := hf₂) (gf₁ := gf₁) (gf₂ := gf₂)
        (hgf₁ := hgf₁) (hgf₂ := hgf₂)
    hom_self := fun {V} q {I} g hg ↦
      source_descent_datum_of_local_preimages_hom_self
        (F := F) hff T y xI eI' (V := V) (q := q) (I := I) (g := g) (hg := hg)
    hom_comp := fun {V} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
      source_descent_datum_of_local_preimages_hom_comp
        (F := F) hff T y xI eI' (V := V) (q := q)
        (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
        (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
        (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃) }

/-- Helper for Lemma 8.4.8: after fixed-cover transport, the reflected source overlap is exactly
the simple shell built from the chosen local component isomorphisms. -/
private theorem source_descent_datum_of_local_preimages_image_hom
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((local_cover_descent_data_functor (F := F) T).obj
        (source_descent_datum_of_local_preimages (F := F) hff T y xI eI')).hom
        q f₁ f₂ hf₁ hf₂ =
      (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
        ((((canonicalFiberPseudofunctor Y.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv) := by
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let d :=
    source_descent_overlap_hom_of_local_preimages
      (F := F) hff T y xI eI' q f₁ f₂ hf₁ hf₂
  let c₁ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₁ (xI I₁)
  let c₂ := FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) f₂ (xI I₂)
  let α₁ :=
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom)
  let β₂ :=
    (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).inv)
  have hmap :
      (fiberFunctor F V).map d =
        c₁.inv ≫ α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom := by
    -- Rewrite the mapped reflected overlap to the target-side comparison shell.
    simpa only [d, Dy, c₁, c₂, α₁, β₂, Category.assoc] using
      source_descent_overlap_hom_map
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hcancel_right :
      α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom ≫ c₂.inv =
        α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ := by
    -- The right comparison pair cancels in the same fully reassociated target shell.
    have hcancel :
        α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom ≫ c₂.inv =
          α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ 𝟙 _ := by
      exact congrArg
        (fun k ↦ α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ k)
        c₂.hom_inv_id
    simpa only [Category.assoc, Category.comp_id] using hcancel
  -- Unfold the transported source overlap once, rewrite its image, and cancel the outer
  -- comparison-conjugation shells.
  have hstart :
      ((local_cover_descent_data_functor (F := F) T).obj
          (source_descent_datum_of_local_preimages (F := F) hff T y xI eI')).hom
          q f₁ f₂ hf₁ hf₂ =
        c₁.hom ≫ (fiberFunctor F V).map d ≫ c₂.inv := by
    rfl
  have hrewrite :
      c₁.hom ≫ (fiberFunctor F V).map d ≫ c₂.inv =
        c₁.hom ≫ (c₁.inv ≫ α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom) ≫ c₂.inv := by
    exact congrArg (fun k ↦ c₁.hom ≫ k ≫ c₂.inv) hmap
  have hassoc :
      c₁.hom ≫ (c₁.inv ≫ α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom) ≫ c₂.inv =
        c₁.hom ≫ c₁.inv ≫ α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom ≫ c₂.inv := by
    simp only [Category.assoc]
  have hcancel_left :
      c₁.hom ≫ c₁.inv ≫ α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom ≫ c₂.inv =
        α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom ≫ c₂.inv := by
    simpa only [Category.assoc] using
      Iso.hom_inv_id_assoc c₁
        (α₁ ≫ Dy.hom q f₁ f₂ hf₁ hf₂ ≫ β₂ ≫ c₂.hom ≫ c₂.inv)
  -- Unfold the transported source overlap once, rewrite its image, and cancel the outer
  -- comparison-conjugation shells.
  exact hstart.trans (hrewrite.trans (hassoc.trans (hcancel_left.trans hcancel_right)))

/-- Helper for Lemma 8.4.8: the chosen local component isomorphisms package into an isomorphism
from the transported source descent datum to the canonical target descent datum of `y`. -/
private theorem source_descent_datum_of_local_preimages_image_comm
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
      ((((canonicalFiberPseudofunctor Y.p).toDescentData
          (fun I : T.Arrow ↦ I.f)).obj y).hom q f₁ f₂ hf₁ hf₂) =
      ((local_cover_descent_data_functor (F := F) T).obj
          (source_descent_datum_of_local_preimages (F := F) hff T y xI eI')).hom
          q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map (eI' I₂).hom) := by
  let Dy :=
    (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y)
  let F₂ := ((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor
  let core :=
    (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map (eI' I₁).hom) ≫
      Dy.hom q f₁ f₂ hf₁ hf₂
  have hstrong :
      ((local_cover_descent_data_functor (F := F) T).obj
          (source_descent_datum_of_local_preimages (F := F) hff T y xI eI')).hom
          q f₁ f₂ hf₁ hf₂ =
        core ≫ F₂.map (eI' I₂).inv := by
    -- Rewrite the image overlap into the reusable `core ≫ map(inv)` form.
    simpa only [Dy, F₂, core, Category.assoc] using
      source_descent_datum_of_local_preimages_image_hom
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hpost :
      ((local_cover_descent_data_functor (F := F) T).obj
          (source_descent_datum_of_local_preimages (F := F) hff T y xI eI')).hom
          q f₁ f₂ hf₁ hf₂ ≫
        F₂.map (eI' I₂).hom =
      (core ≫ F₂.map (eI' I₂).inv) ≫ F₂.map (eI' I₂).hom := by
    -- Postcompose the strong shell identity by the final mapped component.
    exact congrArg (fun k ↦ k ≫ F₂.map (eI' I₂).hom) hstrong
  have htail : F₂.map (eI' I₂).inv ≫ F₂.map (eI' I₂).hom = 𝟙 _ := by
    -- The mapped inverse/hom pair cancels by functoriality.
    calc
      F₂.map (eI' I₂).inv ≫ F₂.map (eI' I₂).hom =
        F₂.map ((eI' I₂).inv ≫ (eI' I₂).hom) := by
          rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
          exact congrArg F₂.map (eI' I₂).inv_hom_id
      _ = 𝟙 _ := by
          rw [F₂.map_id]
  have hcancel :
      (core ≫ F₂.map (eI' I₂).inv) ≫ F₂.map (eI' I₂).hom = core := by
    -- Reassociate once so the mapped inverse/hom pair is adjacent.
    calc
      (core ≫ F₂.map (eI' I₂).inv) ≫ F₂.map (eI' I₂).hom =
        core ≫ (F₂.map (eI' I₂).inv ≫ F₂.map (eI' I₂).hom) := by
          simp only [Category.assoc]
      _ = core ≫ 𝟙 _ := by
          exact congrArg (fun k ↦ core ≫ k) htail
      _ = core := by
          rw [Category.comp_id]
  -- The strong shell identity becomes the commuting square once the final mapped component is
  -- canceled.
  exact (hpost.trans hcancel).symm

/-- Helper for Lemma 8.4.8: the transported source descent datum is canonically isomorphic to the
canonical target descent datum of `y`. -/
private noncomputable abbrev source_descent_datum_of_local_preimages_image_iso
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C} (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y) :
    (local_cover_descent_data_functor (F := F) T).obj
        (source_descent_datum_of_local_preimages (F := F) hff T y xI eI') ≅
      (((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj y) :=
  -- Package the chosen local component isomorphisms into a descent-data isomorphism.
  Pseudofunctor.DescentData.isoMk
    (fun I ↦ eI' I)
    (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
      source_descent_datum_of_local_preimages_image_comm
        (F := F) hff T y xI eI'
        (q := q) (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂))

/-- Helper for Lemma 8.4.8: local preimages over a fixed cover should descend to a single global
preimage in the source fiber. -/
private theorem local_preimages_descend_to_global_preimage
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    {U : C}
    (T : J.Cover U)
    (y : Y.p.Fiber U)
    (xI : ∀ I : T.Arrow, X.p.Fiber I.Y)
    (eI : ∀ I : T.Arrow,
      Nonempty (((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y)) :
    ∃ x : X.p.Fiber U, Nonempty (((fiberFunctor F U).obj x) ≅ y) := by
  classical
  let eI' : ∀ I : T.Arrow,
      ((fiberFunctor F I.Y).obj (xI I)) ≅
        I.f ^*[localCanonicalPullbackChoice Y.p] y :=
    fun I ↦ Classical.choice (eI I)
  let FX := ((canonicalFiberPseudofunctor X.p).toDescentData (fun I : T.Arrow ↦ I.f))
  let FY := ((canonicalFiberPseudofunctor Y.p).toDescentData (fun I : T.Arrow ↦ I.f))
  let DX := source_descent_datum_of_local_preimages (F := F) hff T y xI eI'
  have hFX : FX.IsEquivalence := canonical_descent_functor_isEquivalence X T
  let _ : FX.IsEquivalence := hFX
  let _ : FX.EssSurj := by infer_instance
  -- Descend the reflected source datum to an actual source-fiber object over `U`.
  obtain ⟨x, ⟨hxDesc⟩⟩ := Functor.EssSurj.mem_essImage (F := FX) DX
  have hFY : FY.IsEquivalence := canonical_descent_functor_isEquivalence Y T
  let _ : FY.IsEquivalence := hFY
  let hffFY : FY.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful FY
  let descIso :
      FY.obj ((fiberFunctor F U).obj x) ≅ FY.obj y :=
    ((local_cover_descent_data_functor_toDescentData_iso (F := F) T).app x).symm ≪≫
      (local_cover_descent_data_functor (F := F) T).mapIso hxDesc ≪≫
      source_descent_datum_of_local_preimages_image_iso
        (F := F) hff T y xI eI'
  -- Pull the descent-data comparison back through full faithfulness of the canonical descent
  -- functor on `Y`.
  exact ⟨x, ⟨hffFY.preimageIso descIso⟩⟩

/-- Helper for Lemma 8.4.8: local essential-image data should globalize to essential surjectivity
on each fiber by descending a local section of `X ×_Y Y ⟶ Y`. -/
private theorem fiberFunctor_essSurj_of_locallyEssentiallySurjective
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful)
    (hFess : LocallyEssentiallySurjectiveOnObjects J F) :
    ∀ U : C, (fiberFunctor F U).EssSurj := by
  intro U
  refine ⟨?_⟩
  intro y
  -- Unpack the given local essential-image datum into an explicit cover and local source
  -- preimages, so the remaining globalization step is isolated in one descent lemma.
  rcases hFess U y with ⟨T, hT⟩
  choose xI eI using hT
  obtain ⟨x, hx⟩ :=
    local_preimages_descend_to_global_preimage
      (F := F) hff T y xI eI
  exact ⟨x, hx⟩

/-- Lemma 8.4.8: for a fully faithful morphism of stacks over `(C, J)`, being an equivalence over
the base is equivalent to local essential surjectivity on objects in every fiber. -/
theorem isEquivalenceOverBase_iff_locallyEssentiallySurjectiveOnObjects_of_fullyFaithful
    (F : X ⟶ Y)
    (hff : Nonempty (toBasedFunctor F).FullyFaithful) :
    IsEquivalenceOverBase F ↔
      LocallyEssentiallySurjectiveOnObjects J F := by
  constructor
  · intro hF U y
    refine ⟨⊤, ?_⟩
    intro I
    let FI := fiberFunctor F I.Y
    have hFI : FI.IsEquivalence := by
      -- Restrict the given over-base equivalence to the fiber over the cover leg.
      exact
        BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
          (toBasedFunctor F) hF I.Y
    let _ : FI.IsEquivalence := hFI
    let _ : FI.EssSurj := by infer_instance
    obtain ⟨x, hx⟩ := Functor.EssSurj.mem_essImage
      (F := FI)
      (I.f ^*[localCanonicalPullbackChoice Y.p] y)
    rcases hx with ⟨e⟩
    exact ⟨x, ⟨e⟩⟩
  · intro hFess
    have hFiberFullyFaithful :
        ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful :=
      fiber_functor_fullyFaithful_of_fullyFaithful (F := F) hff
    have hFiberEssSurj :
        ∀ U : C, (fiberFunctor F U).EssSurj :=
      fiberFunctor_essSurj_of_locallyEssentiallySurjective
        (F := F) hff hFess
    have hFiberIsEquivalence :
        ∀ U : C, (fiberFunctor F U).IsEquivalence := by
      intro U
      rcases hFiberFullyFaithful U with ⟨hFFU⟩
      -- Combine the already-known fiberwise full faithfulness with the globalization of local
      -- essential surjectivity.
      exact
        (Functor.isEquivalence_iff_full_faithful_essSurj (fiberFunctor F U)).2
          ⟨(fun a b ↦ hFFU.map_bijective a b), hFiberEssSurj U⟩
    exact
      isEquivalenceOverBase_of_fiberwise_isEquivalence
        (F := F) hFiberIsEquivalence

end CategoryTheory
