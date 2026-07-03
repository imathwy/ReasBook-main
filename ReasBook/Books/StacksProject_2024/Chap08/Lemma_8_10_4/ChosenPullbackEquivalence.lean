import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap04.Definition_4_35_1
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap08.Lemma_8_2_3

noncomputable section

universe u v

namespace CategoryTheory

namespace FibredCategoryOver

variable {C : Type u} [Category.{v} C]

open Functor

/-- Helper for Lemma 8.10.4: the underlying arrow of a morphism in `Over U` composes with the
target map as expected. -/
private theorem over_hom_left_comp_hom
    {U : C} {f g : Over U} (τ : f ⟶ g) :
    τ.left ≫ g.hom = f.hom :=
  Over.w τ

/-- Helper for Lemma 8.10.4: the chosen pullback arrow in the canonical pullback system is a lift
over its defining base morphism. -/
private theorem canonical_pullback_map_isHomLift
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p]
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    X.p.IsHomLift f ((canonicalPullbackChoice X.p).map f x) := by
  -- The canonical pullback arrow is strongly cartesian, so it is in particular a lift of `f`.
  let _ : X.p.IsStronglyCartesian f ((canonicalPullbackChoice X.p).map f x) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian f x
  infer_instance

/-- Helper for Lemma 8.10.4: for a slice morphism `τ : f ⟶ g`, there is a unique transition map
between the chosen pullbacks of `x` along `f.hom` and `g.hom`. -/
private theorem chosen_pullback_transition_existsUnique
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] {U : C} (x : X.p.Fiber U)
    {f g : Over U} (τ : f ⟶ g) :
    ∃! χ : (f.hom ^*[canonicalPullbackChoice X.p] x).1 ⟶
        (g.hom ^*[canonicalPullbackChoice X.p] x).1,
      X.p.IsHomLift τ.left χ ∧
        χ ≫ (canonicalPullbackChoice X.p).map g.hom x =
          (canonicalPullbackChoice X.p).map f.hom x := by
  -- The chosen pullback arrow of `g.hom` is strongly cartesian, so it controls all lifts of
  -- `τ.left ≫ g.hom = f.hom`.
  let hstrongG : X.p.IsStronglyCartesian g.hom ((canonicalPullbackChoice X.p).map g.hom x) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian g.hom x
  let hstrongF : X.p.IsStronglyCartesian f.hom ((canonicalPullbackChoice X.p).map f.hom x) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian f.hom x
  let hLiftF : X.p.IsHomLift f.hom ((canonicalPullbackChoice X.p).map f.hom x) :=
    hstrongF.toIsHomLift
  refine ⟨?_, ?_, ?_⟩
  · exact
      @Functor.IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _ g.hom
        ((canonicalPullbackChoice X.p).map g.hom x) hstrongG _ _ τ.left f.hom
        (over_hom_left_comp_hom τ).symm ((canonicalPullbackChoice X.p).map f.hom x) hLiftF
  · constructor
    · exact
        @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _ g.hom
          ((canonicalPullbackChoice X.p).map g.hom x) hstrongG _ _ τ.left f.hom
          (over_hom_left_comp_hom τ).symm ((canonicalPullbackChoice X.p).map f.hom x) hLiftF
    · exact
        @Functor.IsStronglyCartesian.fac _ _ _ _ X.p _ _ _ _ g.hom
          ((canonicalPullbackChoice X.p).map g.hom x) hstrongG _ _ τ.left f.hom
          (over_hom_left_comp_hom τ).symm ((canonicalPullbackChoice X.p).map f.hom x) hLiftF
  · intro ψ hψ
    exact
      @Functor.IsStronglyCartesian.map_uniq _ _ _ _ X.p _ _ _ _ g.hom
        ((canonicalPullbackChoice X.p).map g.hom x) hstrongG _ _ τ.left f.hom
        (over_hom_left_comp_hom τ).symm ((canonicalPullbackChoice X.p).map f.hom x) hLiftF
        ψ hψ.1 hψ.2

/-- Helper for Lemma 8.10.4: the unique transition map between chosen pullbacks of `x` along a
slice morphism. -/
private noncomputable def chosen_pullback_transition
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] {U : C} (x : X.p.Fiber U)
    {f g : Over U} (τ : f ⟶ g) :
    (f.hom ^*[canonicalPullbackChoice X.p] x).1 ⟶
      (g.hom ^*[canonicalPullbackChoice X.p] x).1 :=
  Classical.choose (chosen_pullback_transition_existsUnique X x τ)

/-- Helper for Lemma 8.10.4: the chosen pullback transition map postcomposes to the expected
chosen pullback arrow. -/
@[reassoc]
private theorem chosen_pullback_transition_fac
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] {U : C} (x : X.p.Fiber U)
    {f g : Over U} (τ : f ⟶ g) :
    chosen_pullback_transition X x τ ≫ (canonicalPullbackChoice X.p).map g.hom x =
      (canonicalPullbackChoice X.p).map f.hom x := by
  -- The defining universal-property witness gives the factorization immediately.
  exact (Classical.choose_spec (chosen_pullback_transition_existsUnique X x τ)).1.2

/-- Helper for Lemma 8.10.4: the chosen pullback transition map is a lift of the underlying slice
arrow. -/
private theorem chosen_pullback_transition_isHomLift
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] {U : C} (x : X.p.Fiber U)
    {f g : Over U} (τ : f ⟶ g) :
    X.p.IsHomLift τ.left (chosen_pullback_transition X x τ) := by
  -- The chosen witness already carries the required lift structure.
  exact (Classical.choose_spec (chosen_pullback_transition_existsUnique X x τ)).1.1

/-- Helper for Lemma 8.10.4: the chosen pullback transition map is the identity over identity
slice morphisms. -/
private theorem chosen_pullback_transition_id
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] {U : C} (x : X.p.Fiber U)
    (f : Over U) :
    chosen_pullback_transition X x (𝟙 f) = 𝟙 ((f.hom ^*[canonicalPullbackChoice X.p] x).1) := by
  -- Uniqueness for the identity triangle forces the chosen transition to be the identity.
  rcases chosen_pullback_transition_existsUnique X x (𝟙 f) with ⟨χ, hχ, hχuniq⟩
  have hChosen : chosen_pullback_transition X x (𝟙 f) = χ := by
    simpa [chosen_pullback_transition] using
      hχuniq
        (Classical.choose (chosen_pullback_transition_existsUnique X x (𝟙 f)))
        (Classical.choose_spec (chosen_pullback_transition_existsUnique X x (𝟙 f))).1
  have hId : 𝟙 ((f.hom ^*[canonicalPullbackChoice X.p] x).1) = χ := by
    apply hχuniq
    constructor
    · change X.p.IsHomLift (𝟙 f.left) (𝟙 ((f.hom ^*[canonicalPullbackChoice X.p] x).1))
      exact IsHomLift.id (f.hom ^*[canonicalPullbackChoice X.p] x).2
    · simp
  exact hChosen.trans hId.symm

/-- Helper for Lemma 8.10.4: the chosen pullback transition maps compose along slice morphisms. -/
private theorem chosen_pullback_transition_comp
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] {U : C} (x : X.p.Fiber U)
    {f g h : Over U} (τ : f ⟶ g) (θ : g ⟶ h) :
    chosen_pullback_transition X x (τ ≫ θ) =
      chosen_pullback_transition X x τ ≫ chosen_pullback_transition X x θ := by
  -- The composite has the same universal property as the chosen transition for `τ ≫ θ`.
  rcases chosen_pullback_transition_existsUnique X x (τ ≫ θ) with ⟨χ, hχ, hχuniq⟩
  have hChosen : chosen_pullback_transition X x (τ ≫ θ) = χ := by
    simpa [chosen_pullback_transition] using
      hχuniq
        (Classical.choose (chosen_pullback_transition_existsUnique X x (τ ≫ θ)))
        (Classical.choose_spec (chosen_pullback_transition_existsUnique X x (τ ≫ θ))).1
  have hComp :
      chosen_pullback_transition X x τ ≫ chosen_pullback_transition X x θ = χ := by
    apply hχuniq
    constructor
    · change X.p.IsHomLift (τ.left ≫ θ.left)
        (chosen_pullback_transition X x τ ≫ chosen_pullback_transition X x θ)
      letI : X.p.IsHomLift τ.left (chosen_pullback_transition X x τ) :=
        chosen_pullback_transition_isHomLift X x τ
      letI : X.p.IsHomLift θ.left (chosen_pullback_transition X x θ) :=
        chosen_pullback_transition_isHomLift X x θ
      infer_instance
    · calc
        (chosen_pullback_transition X x τ ≫ chosen_pullback_transition X x θ) ≫
            (canonicalPullbackChoice X.p).map h.hom x
            = chosen_pullback_transition X x τ ≫
                (chosen_pullback_transition X x θ ≫
                  (canonicalPullbackChoice X.p).map h.hom x) := by
                    simp [Category.assoc]
        _ = chosen_pullback_transition X x τ ≫
              (canonicalPullbackChoice X.p).map g.hom x := by
                rw [chosen_pullback_transition_fac X x θ]
        _ = (canonicalPullbackChoice X.p).map f.hom x := by
              exact chosen_pullback_transition_fac X x τ
  exact hChosen.trans hComp.symm

/-- Helper for Lemma 8.10.4: the chosen cartesian pullback of `x` along an arrow into `X.p.obj x`
defines the expected quasi-inverse on slice categories. -/
private noncomputable def chosen_pullback_over_functor
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] (x : X.S) :
    Over (X.p.obj x) ⥤ Over x where
  obj f :=
    let xFiber : X.p.Fiber (X.p.obj x) := ⟨x, rfl⟩
    Over.mk ((canonicalPullbackChoice X.p).map f.hom xFiber)
  map {f g} τ := by
    let xFiber : X.p.Fiber (X.p.obj x) := ⟨x, rfl⟩
    refine Over.homMk (chosen_pullback_transition X xFiber τ) ?_
    -- The universal-property transition map lands in the over-category because it reconstructs the
    -- chosen pullback arrow of `f.hom` after postcomposition.
    exact chosen_pullback_transition_fac X xFiber τ
  map_id f := by
    apply Over.OverMorphism.ext
    simpa using chosen_pullback_transition_id X ⟨x, rfl⟩ f
  map_comp {f g h} τ θ := by
    apply Over.OverMorphism.ext
    simpa using chosen_pullback_transition_comp X ⟨x, rfl⟩ τ θ

/-- Helper for Lemma 8.10.4: downstairs the chosen cartesian pullback arrow lies over the
original base arrow, giving the counit isomorphism. -/
private noncomputable def chosen_pullback_over_functor_counit_iso
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] (x : X.S) :
    chosen_pullback_over_functor X x ⋙ Over.post X.p ≅ 𝟭 (Over (X.p.obj x)) :=
  NatIso.ofComponents
    (fun f ↦ by
      let xFiber : X.p.Fiber (X.p.obj x) := ⟨x, rfl⟩
      let pulled := (canonicalPullbackChoice X.p).map f.hom xFiber
      have hpulled : X.p.IsHomLift f.hom pulled := by
        simpa [pulled] using canonical_pullback_map_isHomLift X f.hom xFiber
      have hleft : X.p.obj ((Over.mk pulled).left) = f.left := by
        simpa [pulled] using (f.hom ^*[canonicalPullbackChoice X.p] xFiber).2
      refine Over.isoMk (eqToIso hleft) ?_
      -- The pullback map of `x` over `f.hom` is a lift of that arrow, so the localized base
      -- object is identified with `f`.
      simpa [Category.assoc] using
        congrArg (eqToHom hleft ≫ ·) (IsHomLift.fac X.p f.hom pulled))
    (by
      intro f g τ
      let xFiber : X.p.Fiber (X.p.obj x) := ⟨x, rfl⟩
      let pulled_f := (canonicalPullbackChoice X.p).map f.hom xFiber
      let pulled_g := (canonicalPullbackChoice X.p).map g.hom xFiber
      have hpulled_f : X.p.IsHomLift f.hom pulled_f := by
        simpa [pulled_f] using canonical_pullback_map_isHomLift X f.hom xFiber
      have hpulled_g : X.p.IsHomLift g.hom pulled_g := by
        simpa [pulled_g] using canonical_pullback_map_isHomLift X g.hom xFiber
      have hleft_f : X.p.obj ((Over.mk pulled_f).left) = f.left := by
        simpa [pulled_f] using (f.hom ^*[canonicalPullbackChoice X.p] xFiber).2
      have hleft_g : X.p.obj ((Over.mk pulled_g).left) = g.left := by
        simpa [pulled_g] using (g.hom ^*[canonicalPullbackChoice X.p] xFiber).2
      apply Over.OverMorphism.ext
      change X.p.map (chosen_pullback_transition X xFiber τ) ≫ eqToHom hleft_g =
        eqToHom hleft_f ≫ τ.left
      letI : X.p.IsHomLift τ.left (chosen_pullback_transition X xFiber τ) :=
        chosen_pullback_transition_isHomLift X xFiber τ
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ eqToHom hleft_g)
          (IsHomLift.fac' X.p τ.left (chosen_pullback_transition X xFiber τ)))

/-- Helper for Lemma 8.10.4: both `φ : y ⟶ x` and the chosen pullback of `x` along `X.p.map φ`
are cartesian lifts of the same base arrow, so uniqueness of cartesian lifts gives the unit
isomorphism. -/
private noncomputable def chosen_pullback_over_functor_unit_iso
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] (x : X.S) :
    Over.post X.p ⋙ chosen_pullback_over_functor X x ≅ 𝟭 (Over x) :=
  NatIso.ofComponents
    (fun φ ↦ by
      let xFiber : X.p.Fiber (X.p.obj x) := ⟨x, rfl⟩
      let pulled := (canonicalPullbackChoice X.p).map (X.p.map φ.hom) xFiber
      have hpulled : X.p.IsHomLift (X.p.map φ.hom) pulled := by
        simpa [pulled] using canonical_pullback_map_isHomLift X (X.p.map φ.hom) xFiber
      have hstrong_phi : X.p.IsStronglyCartesian (X.p.map φ.hom) φ.hom := by
        exact IsFibredInGroupoids.isStronglyCartesian_map (p := X.p) φ.hom
      have hstrong_pulled : X.p.IsStronglyCartesian (X.p.map φ.hom) pulled := by
        simpa [pulled] using
          (canonicalPullbackChoice X.p).isStronglyCartesian (X.p.map φ.hom) xFiber
      letI : X.p.IsHomLift (X.p.map φ.hom) pulled := hpulled
      letI : X.p.IsStronglyCartesian (X.p.map φ.hom) φ.hom := hstrong_phi
      letI : X.p.IsStronglyCartesian (X.p.map φ.hom) pulled := hstrong_pulled
      have hcart_phi : X.p.IsCartesian (X.p.map φ.hom) φ.hom := inferInstance
      have hcart_pulled : X.p.IsCartesian (X.p.map φ.hom) pulled := inferInstance
      let e :=
        @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _
          X.p _ _ _ _ (X.p.map φ.hom) pulled hcart_pulled _ φ.hom hcart_phi
      refine Over.isoMk e.symm ?_
      -- Route correction: use the canonical `domainUniqueUpToIso` comparison rather than a
      -- hand-built inverse between the two cartesian lifts.
      change e.inv ≫ φ.hom = pulled
      simp [e, pulled]
    )
    (by
      intro φ ψ τ
      let xFiber : X.p.Fiber (X.p.obj x) := ⟨x, rfl⟩
      let pulled_φ := (canonicalPullbackChoice X.p).map (X.p.map φ.hom) xFiber
      let pulled_ψ := (canonicalPullbackChoice X.p).map (X.p.map ψ.hom) xFiber
      have hpulled_φ : X.p.IsHomLift (X.p.map φ.hom) pulled_φ := by
        simpa [pulled_φ] using canonical_pullback_map_isHomLift X (X.p.map φ.hom) xFiber
      have hpulled_ψ : X.p.IsHomLift (X.p.map ψ.hom) pulled_ψ := by
        simpa [pulled_ψ] using canonical_pullback_map_isHomLift X (X.p.map ψ.hom) xFiber
      have hstrong_φ : X.p.IsStronglyCartesian (X.p.map φ.hom) φ.hom := by
        exact IsFibredInGroupoids.isStronglyCartesian_map (p := X.p) φ.hom
      have hstrong_ψ : X.p.IsStronglyCartesian (X.p.map ψ.hom) ψ.hom := by
        exact IsFibredInGroupoids.isStronglyCartesian_map (p := X.p) ψ.hom
      have hstrong_pulled_φ : X.p.IsStronglyCartesian (X.p.map φ.hom) pulled_φ := by
        simpa [pulled_φ] using
          (canonicalPullbackChoice X.p).isStronglyCartesian (X.p.map φ.hom) xFiber
      have hstrong_pulled_ψ : X.p.IsStronglyCartesian (X.p.map ψ.hom) pulled_ψ := by
        simpa [pulled_ψ] using
          (canonicalPullbackChoice X.p).isStronglyCartesian (X.p.map ψ.hom) xFiber
      letI : X.p.IsHomLift (X.p.map φ.hom) pulled_φ := hpulled_φ
      letI : X.p.IsHomLift (X.p.map ψ.hom) pulled_ψ := hpulled_ψ
      letI : X.p.IsStronglyCartesian (X.p.map φ.hom) φ.hom := hstrong_φ
      letI : X.p.IsStronglyCartesian (X.p.map ψ.hom) ψ.hom := hstrong_ψ
      letI : X.p.IsStronglyCartesian (X.p.map φ.hom) pulled_φ := hstrong_pulled_φ
      letI : X.p.IsStronglyCartesian (X.p.map ψ.hom) pulled_ψ := hstrong_pulled_ψ
      have hcart_φ : X.p.IsCartesian (X.p.map φ.hom) φ.hom := inferInstance
      have hcart_ψ : X.p.IsCartesian (X.p.map ψ.hom) ψ.hom := inferInstance
      have hcart_pulled_φ : X.p.IsCartesian (X.p.map φ.hom) pulled_φ := inferInstance
      have hcart_pulled_ψ : X.p.IsCartesian (X.p.map ψ.hom) pulled_ψ := inferInstance
      let eφ :=
        @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _
          X.p _ _ _ _ (X.p.map φ.hom) pulled_φ hcart_pulled_φ _ φ.hom hcart_φ
      let eψ :=
        @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _
          X.p _ _ _ _ (X.p.map ψ.hom) pulled_ψ hcart_pulled_ψ _ ψ.hom hcart_ψ
      have heφ_inv_lift :
          X.p.IsHomLift (𝟙 (X.p.obj φ.left)) eφ.inv := by
        simpa [eφ] using
          (@Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _
            X.p _ _ _ _ (X.p.map φ.hom) pulled_φ hcart_pulled_φ _ φ.hom hcart_φ)
      have heψ_hom_lift :
          X.p.IsHomLift (𝟙 (X.p.obj ψ.left)) eψ.hom := by
        simpa [eψ] using
          (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _
            X.p _ _ _ _ (X.p.map ψ.hom) pulled_ψ hcart_pulled_ψ _ ψ.hom hcart_ψ)
      let τbase : (Over.post X.p).obj φ ⟶ (Over.post X.p).obj ψ := (Over.post X.p).map τ
      have htransition :
          chosen_pullback_transition X xFiber τbase =
            eφ.inv ≫ τ.left ≫ eψ.hom := by
        have hcandidate :
            X.p.IsHomLift τbase.left (eφ.inv ≫ τ.left ≫ eψ.hom) ∧
              (eφ.inv ≫ τ.left ≫ eψ.hom) ≫
                  (canonicalPullbackChoice X.p).map ((Over.post X.p).obj ψ).hom xFiber =
                (canonicalPullbackChoice X.p).map ((Over.post X.p).obj φ).hom xFiber := by
          constructor
          · have hleft_comp : X.p.IsHomLift (X.p.map τ.left) (eφ.inv ≫ τ.left) := by
              have hdom_φ : X.p.obj ((Over.mk pulled_φ).left) = X.p.obj φ.left := by
                simpa [pulled_φ] using (X.p.map φ.hom ^*[canonicalPullbackChoice X.p] xFiber).2
              have heφ_map : X.p.map eφ.inv = eqToHom hdom_φ := by
                letI : X.p.IsHomLift (𝟙 (X.p.obj φ.left)) eφ.inv := heφ_inv_lift
                simpa [hdom_φ] using IsHomLift.fac' X.p (𝟙 (X.p.obj φ.left)) eφ.inv
              refine IsHomLift.of_fac' X.p (X.p.map τ.left) (eφ.inv ≫ τ.left) hdom_φ rfl ?_
              calc
                X.p.map (eφ.inv ≫ τ.left)
                    = X.p.map eφ.inv ≫ X.p.map τ.left := by simp
                _ = eqToHom hdom_φ ≫ X.p.map τ.left ≫ eqToHom rfl.symm := by
                      rw [heφ_map]
                      simp
            have hcandidate_lift :
                X.p.IsHomLift (X.p.map τ.left) ((eφ.inv ≫ τ.left) ≫ eψ.hom) :=
              by
                have hdom_φ : X.p.obj ((Over.mk pulled_φ).left) = X.p.obj φ.left := by
                  simpa [pulled_φ] using
                    (X.p.map φ.hom ^*[canonicalPullbackChoice X.p] xFiber).2
                have hdom_ψ : X.p.obj ((Over.mk pulled_ψ).left) = X.p.obj ψ.left := by
                  simpa [pulled_ψ] using
                    (X.p.map ψ.hom ^*[canonicalPullbackChoice X.p] xFiber).2
                have hleft_map :
                    X.p.map (eφ.inv ≫ τ.left) = eqToHom hdom_φ ≫ X.p.map τ.left := by
                  letI : X.p.IsHomLift (X.p.map τ.left) (eφ.inv ≫ τ.left) := hleft_comp
                  simpa using IsHomLift.fac' X.p (X.p.map τ.left) (eφ.inv ≫ τ.left)
                have heψ_map : X.p.map eψ.hom = eqToHom hdom_ψ.symm := by
                  letI : X.p.IsHomLift (𝟙 (X.p.obj ψ.left)) eψ.hom := heψ_hom_lift
                  simpa [hdom_ψ] using IsHomLift.fac' X.p (𝟙 (X.p.obj ψ.left)) eψ.hom
                refine
                  IsHomLift.of_fac' X.p (X.p.map τ.left) ((eφ.inv ≫ τ.left) ≫ eψ.hom)
                    hdom_φ hdom_ψ ?_
                calc
                  X.p.map ((eφ.inv ≫ τ.left) ≫ eψ.hom)
                      = X.p.map (eφ.inv ≫ τ.left) ≫ X.p.map eψ.hom := by simp
                  _ = (eqToHom hdom_φ ≫ X.p.map τ.left) ≫ eqToHom hdom_ψ.symm := by
                        rw [hleft_map]
                        simpa [Category.assoc] using
                          congrArg (fun k ↦ (eqToHom hdom_φ ≫ X.p.map τ.left) ≫ k) heψ_map
                  _ = eqToHom hdom_φ ≫ X.p.map τ.left ≫ eqToHom hdom_ψ.symm := by
                        simp [Category.assoc]
            change X.p.IsHomLift (X.p.map τ.left) (eφ.inv ≫ τ.left ≫ eψ.hom)
            simpa [Category.assoc] using hcandidate_lift
          · have heφ_fac : eφ.inv ≫ φ.hom = pulled_φ := by
              simp [eφ, pulled_φ]
            have heψ_fac : eψ.hom ≫ pulled_ψ = ψ.hom := by
              simp [eψ, pulled_ψ]
            have hpostcompose :
                (eφ.inv ≫ τ.left ≫ eψ.hom) ≫ pulled_ψ = eφ.inv ≫ φ.hom := by
              have hstep₁ :
                  (eφ.inv ≫ τ.left ≫ eψ.hom) ≫ pulled_ψ =
                    eφ.inv ≫ (τ.left ≫ (eψ.hom ≫ pulled_ψ)) := by
                simp [Category.assoc]
              have hstep₂ :
                  eφ.inv ≫ (τ.left ≫ (eψ.hom ≫ pulled_ψ)) =
                    eφ.inv ≫ (τ.left ≫ ψ.hom) := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ eφ.inv ≫ (τ.left ≫ k)) heψ_fac
              have hstep₃ : eφ.inv ≫ (τ.left ≫ ψ.hom) = eφ.inv ≫ φ.hom := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ eφ.inv ≫ k) (Over.w τ)
              exact hstep₁.trans (hstep₂.trans hstep₃)
            exact hpostcompose.trans heφ_fac
        exact
          ((Classical.choose_spec
            (chosen_pullback_transition_existsUnique X xFiber τbase)).2
            (eφ.inv ≫ τ.left ≫ eψ.hom) hcandidate).symm
      apply Over.OverMorphism.ext
      change chosen_pullback_transition X xFiber τbase ≫ eψ.inv = eφ.inv ≫ τ.left
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eψ.inv) htransition)

/-- Helper for Lemma 8.10.4: the slice functor induced by a fibred-in-groupoids projection has a
chosen-pullback quasi-inverse. -/
theorem overPost_isEquivalence_of_isFibredInGroupoids_aux
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] (x : X.S) :
    (Over.post X.p : Over x ⥤ Over (X.p.obj x)).IsEquivalence := by
  -- The source-faithful route uses chosen cartesian pullbacks of `x` and uniqueness of lifts for
  -- the unit and counit comparisons.
  exact Functor.IsEquivalence.mk'
    (chosen_pullback_over_functor X x)
    (chosen_pullback_over_functor_unit_iso X x).symm
    (chosen_pullback_over_functor_counit_iso X x)

end FibredCategoryOver

end CategoryTheory
