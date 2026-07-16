import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Map

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: an isomorphism in a fiber has an isomorphism as its
underlying total morphism. -/
theorem stackificationLift_fiberHom_total_isIso
    {U : C} {x y : X.p.Fiber U} (d : x ⟶ y) [IsIso d] :
    IsIso d.1 := by
  let e := asIso d
  haveI : X.p.IsHomLift (𝟙 U) e.inv.1 := e.inv.2
  refine ⟨⟨e.inv.1, ?_, ?_⟩⟩
  · have hd : d ≫ e.inv = 𝟙 x := by
      simpa [e] using e.hom_inv_id
    exact congrArg (fun f : x ⟶ x => f.1) hd
  · have hd : e.inv ≫ d = 𝟙 y := by
      simpa [e] using e.inv_hom_id
    exact congrArg (fun f : y ⟶ y => f.1) hd

/-- Helper for Chap08 Lemma 8 8 3: the glued vertical map sends fiber isomorphisms to fiber
isomorphisms. -/
theorem stackificationLiftVerticalMap_isIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y₀ y₁ : S'.p.Fiber U} (d : y₀ ⟶ y₁) [IsIso d] :
    IsIso (stackificationLiftVerticalMap X G hG F d) := by
  let e := asIso d
  let invd : y₁ ⟶ y₀ := e.inv
  refine ⟨⟨stackificationLiftVerticalMap X G hG F invd, ?_, ?_⟩⟩
  · rw [← stackificationLiftVerticalMap_comp]
    have hd : d ≫ invd = 𝟙 y₀ := e.hom_inv_id
    rw [hd]
    exact stackificationLiftVerticalMap_id X G hG F y₀
  · rw [← stackificationLiftVerticalMap_comp]
    have hd : invd ≫ d = 𝟙 y₁ := e.inv_hom_id
    rw [hd]
    exact stackificationLiftVerticalMap_id X G hG F y₁

/-- Helper for Chap08 Lemma 8 8 3: if a total arrow of `S'` is strongly cartesian, then its
vertical factor through the chosen pullback is an isomorphism in the fiber. -/
theorem stackificationLiftArrowVerticalFactor_isIso_of_stronglyCartesian
    {T T' : S'.S} (φ : T ⟶ T')
    (hφ : S'.p.IsStronglyCartesian (S'.p.map φ) φ) :
    IsIso (stackificationLiftArrowVerticalFactor (S' := S') φ) := by
  let y' : S'.p.Fiber (S'.p.obj T') :=
    Functor.Fiber.mk (p := S'.p) (a := T') rfl
  let v := stackificationLiftArrowVerticalFactor (S' := S') φ
  let cart := (canonicalPullbackChoice S'.p).map (S'.p.map φ) y'
  have hcart : S'.p.IsStronglyCartesian (S'.p.map φ) cart :=
    (canonicalPullbackChoice S'.p).isStronglyCartesian (S'.p.map φ) y'
  have hcomp : S'.p.IsStronglyCartesian (𝟙 (S'.p.obj T) ≫ S'.p.map φ) (v.1 ≫ cart) := by
    have hvfac : v.1 ≫ cart = φ := by
      simpa [v, cart, y'] using stackificationLiftArrowVerticalFactor_fac (S' := S') φ
    simpa [hvfac] using hφ
  have hvstrong : S'.p.IsStronglyCartesian (𝟙 (S'.p.obj T)) v.1 := by
    letI : S'.p.IsHomLift (𝟙 (S'.p.obj T)) v.1 := v.2
    exact @Functor.IsStronglyCartesian.of_comp _ _ _ _ S'.p _ _ _ _ _ _
      (𝟙 (S'.p.obj T)) (S'.p.map φ) v.1 cart hcart hcomp v.2
  haveI : IsIso (𝟙 (S'.p.obj T)) := inferInstance
  haveI : IsIso v.1 := by
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso S'.p (𝟙 (S'.p.obj T)) v.1
  let e := asIso v.1
  haveI : S'.p.IsHomLift (𝟙 (S'.p.obj T)) e.inv := by
    simpa [e] using (inferInstance : S'.p.IsHomLift (𝟙 (S'.p.obj T)) (inv v.1))
  refine ⟨⟨⟨e.inv, inferInstance⟩, ?_, ?_⟩⟩
  · apply Functor.Fiber.hom_ext
    change v.1 ≫ e.inv = 𝟙 _
    simp [e]
  · apply Functor.Fiber.hom_ext
    change e.inv ≫ v.1 = 𝟙 _
    simp [e]

/-- Helper for Chap08 Lemma 8 8 3: the descended arrow formula sends strongly cartesian arrows
to strongly cartesian arrows. -/
theorem stackificationLiftBasedFunctorMap_isStronglyCartesian
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' : S'.S} (φ : T ⟶ T')
    (hφ : S'.p.IsStronglyCartesian (S'.p.map φ) φ) :
    X.p.IsStronglyCartesian (S'.p.map φ)
      (stackificationLiftBasedFunctorMap X G hG F φ) := by
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let y' : S'.p.Fiber (S'.p.obj T') :=
    Functor.Fiber.mk (p := S'.p) (a := T') rfl
  let pb : S'.p.Fiber (S'.p.obj T) :=
    stackificationLiftArrowPullbackTarget (S' := S') φ
  let v : y ⟶ pb :=
    stackificationLiftArrowVerticalFactor (S' := S') φ
  let a := (stackificationLiftVerticalMap X G hG F v).1
  let b := (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom.1
  let c := (canonicalPullbackChoice X.p).map (S'.p.map φ)
    (stackificationLiftObjectGlued X G hG F y')
  haveI : IsIso v := by
    simpa [v] using
      stackificationLiftArrowVerticalFactor_isIso_of_stronglyCartesian (S' := S') φ hφ
  haveI : IsIso (stackificationLiftVerticalMap X G hG F v) :=
    stackificationLiftVerticalMap_isIso X G hG F v
  haveI : IsIso a := by
    dsimp [a]
    exact stackificationLift_fiberHom_total_isIso
      (stackificationLiftVerticalMap X G hG F v)
  haveI : IsIso b := by
    dsimp [b]
    exact stackificationLift_fiberHom_total_isIso
      (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom
  have hablift : X.p.IsHomLift (𝟙 (S'.p.obj T)) (a ≫ b) := by
    have ha : X.p.IsHomLift (𝟙 (S'.p.obj T)) a := by
      dsimp [a]
      exact (stackificationLiftVerticalMap X G hG F v).2
    have hb : X.p.IsHomLift (𝟙 (S'.p.obj T)) b := by
      dsimp [b]
      exact (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom.2
    exact IsHomLift.comp_of_lift_id (p := X.p) (S'.p.obj T) a b
  have hprefix : X.p.IsStronglyCartesian (𝟙 (S'.p.obj T)) (a ≫ b) := by
    letI : X.p.IsHomLift (𝟙 (S'.p.obj T)) (a ≫ b) := hablift
    exact Functor.IsStronglyCartesian.of_isIso X.p (𝟙 (S'.p.obj T)) (a ≫ b)
  have hcart : X.p.IsStronglyCartesian (S'.p.map φ) c := by
    dsimp [c]
    exact (canonicalPullbackChoice X.p).isStronglyCartesian (S'.p.map φ)
      (stackificationLiftObjectGlued X G hG F y')
  have hcomp : X.p.IsStronglyCartesian (𝟙 (S'.p.obj T) ≫ S'.p.map φ)
      ((a ≫ b) ≫ c) := by
    letI : X.p.IsStronglyCartesian (𝟙 (S'.p.obj T)) (a ≫ b) := hprefix
    letI : X.p.IsStronglyCartesian (S'.p.map φ) c := hcart
    simpa using
      (show X.p.IsStronglyCartesian (𝟙 (S'.p.obj T) ≫ S'.p.map φ)
        ((a ≫ b) ≫ c) from inferInstance)
  simpa [stackificationLiftBasedFunctorMap, y, y', pb, v, a, b, c, Category.assoc] using hcomp

end

end CategoryTheory
