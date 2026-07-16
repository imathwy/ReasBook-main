import Mathlib
import stacks_proof.stacks_project.Chap08.Definition_8_4_1
import stacks_proof.stacks_project.Chap08.Lemma_8_4_2
import stacks_proof.stacks_project.Chap08.Lemma_8_12_1

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: the base arrow used to strictify the second component of an object
in a fiber of the categorical pullback projection. -/
def pullbackProjection_targetBaseMap
    (p : S ⥤ D) {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    u.obj U ⟶ p.obj X.1.snd :=
  eqToHom (congrArg u.obj X.2).symm ≫ X.1.iso.hom

/-- Helper for Lemma 8.12.2: strictify the second component of a pullback-fiber object to an
object in the target fiber over `u.obj U`. -/
noncomputable def pullbackProjection_targetFiberObj
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    p.Fiber (u.obj U) :=
  Functor.Fiber.mk
    (Functor.IsPreFibered.pullbackObj_proj (p := p) (a := X.1.snd) rfl
      (pullbackProjection_targetBaseMap u p X))

/-- Helper for Lemma 8.12.2: the chosen cartesian map from the strictified target-fiber object
back to the original second component of the pullback object. -/
noncomputable def pullbackProjection_targetFiberMap
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    (pullbackProjection_targetFiberObj u p X).1 ⟶ X.1.snd :=
  Functor.IsPreFibered.pullbackMap (p := p) (a := X.1.snd) rfl
    (pullbackProjection_targetBaseMap u p X)

/-- Helper for Lemma 8.12.2: the strictification map is cartesian over the structural base arrow
of the pullback object. -/
theorem pullbackProjection_targetFiberMap_isCartesian
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    p.IsCartesian (pullbackProjection_targetBaseMap u p X)
      (pullbackProjection_targetFiberMap u p X) := by
  -- This is the cartesian map chosen by the strictification object.
  exact Functor.IsPreFibered.pullbackMap.IsCartesian (p := p) (ha := rfl)
    (f := pullbackProjection_targetBaseMap u p X)

/-- Helper for Lemma 8.12.2: the base arrow used in target strictification is an isomorphism. -/
theorem pullbackProjection_targetBaseMap_isIso
    (p : S ⥤ D) {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    IsIso (pullbackProjection_targetBaseMap u p X) := by
  -- The base arrow is a transport isomorphism followed by the structural pullback isomorphism.
  dsimp [pullbackProjection_targetBaseMap]
  infer_instance

/-- Helper for Lemma 8.12.2: the chosen strictification map is an isomorphism. -/
theorem pullbackProjection_targetFiberMap_isIso
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    IsIso (pullbackProjection_targetFiberMap u p X) := by
  -- Cartesian morphisms over isomorphisms are isomorphisms; this is the object-level bridge for
  -- comparing pullback fibers with target fibers.
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p X)
        (pullbackProjection_targetFiberMap u p X) :=
    pullbackProjection_targetFiberMap_isCartesian u p X
  letI :
      p.IsStronglyCartesian (pullbackProjection_targetBaseMap u p X)
        (pullbackProjection_targetFiberMap u p X) :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p
      (pullbackProjection_targetBaseMap u p X)
      (pullbackProjection_targetFiberMap u p X)
  letI : IsIso (pullbackProjection_targetBaseMap u p X) :=
    pullbackProjection_targetBaseMap_isIso u p X
  exact
    Functor.IsStronglyCartesian.isIso_of_base_isIso p
      (pullbackProjection_targetBaseMap u p X)
      (pullbackProjection_targetFiberMap u p X)

/-- Helper for Lemma 8.12.2: the strict target-base arrow is natural for vertical morphisms in
the pullback-projection fiber. -/
theorem pullbackProjection_targetBaseMap_comp_snd
    (p : S ⥤ D) {U : C}
    {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    pullbackProjection_targetBaseMap u p X ≫ p.map φ.1.snd =
      pullbackProjection_targetBaseMap u p Y := by
  -- First read the verticality of `φ` as a transported identity statement on first components.
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) φ.1 := φ.2
  have hfst :
      φ.1.fst = eqToHom X.2 ≫ 𝟙 U ≫ eqToHom Y.2.symm := by
    simpa using
      (IsHomLift.fac' (CategoricalPullback.π₁ u p) (𝟙 U) φ.1)
  -- Then use the pullback morphism square to move the second component across the structural
  -- isomorphisms and cancel the transported first component.
  calc
    pullbackProjection_targetBaseMap u p X ≫ p.map φ.1.snd =
        eqToHom (congrArg u.obj X.2).symm ≫ X.1.iso.hom ≫ p.map φ.1.snd := by
          simp [pullbackProjection_targetBaseMap, Category.assoc]
    _ = eqToHom (congrArg u.obj X.2).symm ≫
          (X.1.iso.hom ≫ p.map φ.1.snd) := by
          simp
    _ = eqToHom (congrArg u.obj X.2).symm ≫
          (u.map φ.1.fst ≫ Y.1.iso.hom) := by
          exact congrArg (fun k ↦ eqToHom (congrArg u.obj X.2).symm ≫ k) φ.1.w.symm
    _ = eqToHom (congrArg u.obj X.2).symm ≫ u.map φ.1.fst ≫ Y.1.iso.hom := by
          simp
    _ = eqToHom (congrArg u.obj Y.2).symm ≫ Y.1.iso.hom := by
          rw [hfst]
          have hcancel :
              eqToHom (congrArg u.obj X.2).symm ≫
                  u.map (eqToHom X.2 ≫ 𝟙 U ≫ eqToHom Y.2.symm) =
                eqToHom (congrArg u.obj Y.2).symm := by
            simp [eqToHom_map]
          simpa using congrArg (fun k ↦ k ≫ Y.1.iso.hom) hcancel
    _ = pullbackProjection_targetBaseMap u p Y := by
          rfl

/-- Helper for Lemma 8.12.2: a vertical morphism in the pullback-projection fiber induces a
vertical morphism between the strictified target-fiber objects. -/
noncomputable def pullbackProjection_targetFiberHom
    (p : S ⥤ D) [p.IsFibered] {U : C}
    {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    pullbackProjection_targetFiberObj u p X ⟶ pullbackProjection_targetFiberObj u p Y := by
  -- The composite from the strictification of `X` to the second component of `Y` lies over the
  -- strict target-base map of `Y`, by the preceding naturality lemma.
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p X)
        (pullbackProjection_targetFiberMap u p X) :=
    pullbackProjection_targetFiberMap_isCartesian u p X
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p Y)
        (pullbackProjection_targetFiberMap u p Y) :=
    pullbackProjection_targetFiberMap_isCartesian u p Y
  letI :
      p.IsHomLift (pullbackProjection_targetBaseMap u p Y)
        (pullbackProjection_targetFiberMap u p X ≫ φ.1.snd) := by
    rw [← pullbackProjection_targetBaseMap_comp_snd (u := u) p φ]
    infer_instance
  letI :
      p.IsStronglyCartesian (pullbackProjection_targetBaseMap u p Y)
        (pullbackProjection_targetFiberMap u p Y) :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p
      (pullbackProjection_targetBaseMap u p Y)
      (pullbackProjection_targetFiberMap u p Y)
  exact
    ⟨Functor.IsStronglyCartesian.map p (pullbackProjection_targetBaseMap u p Y)
        (pullbackProjection_targetFiberMap u p Y)
        (g := 𝟙 (u.obj U)) (f' := pullbackProjection_targetBaseMap u p Y)
        (Category.id_comp _).symm (pullbackProjection_targetFiberMap u p X ≫ φ.1.snd),
      inferInstance⟩

/-- Helper for Lemma 8.12.2: the induced strict target-fiber morphism is characterized after
postcomposition with the chosen cartesian strictification map. -/
theorem pullbackProjection_targetFiberHom_fac
    (p : S ⥤ D) [p.IsFibered] {U : C}
    {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (pullbackProjection_targetFiberHom u p φ).1 ≫
        pullbackProjection_targetFiberMap u p Y =
      pullbackProjection_targetFiberMap u p X ≫ φ.1.snd := by
  -- This is exactly the factorization supplied by the strongly cartesian universal property.
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p X)
        (pullbackProjection_targetFiberMap u p X) :=
    pullbackProjection_targetFiberMap_isCartesian u p X
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p Y)
        (pullbackProjection_targetFiberMap u p Y) :=
    pullbackProjection_targetFiberMap_isCartesian u p Y
  letI :
      p.IsHomLift (pullbackProjection_targetBaseMap u p Y)
        (pullbackProjection_targetFiberMap u p X ≫ φ.1.snd) := by
    rw [← pullbackProjection_targetBaseMap_comp_snd (u := u) p φ]
    infer_instance
  letI :
      p.IsStronglyCartesian (pullbackProjection_targetBaseMap u p Y)
        (pullbackProjection_targetFiberMap u p Y) :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p
      (pullbackProjection_targetBaseMap u p Y)
      (pullbackProjection_targetFiberMap u p Y)
  simpa [pullbackProjection_targetFiberHom] using
    (Functor.IsStronglyCartesian.fac p (pullbackProjection_targetBaseMap u p Y)
      (pullbackProjection_targetFiberMap u p Y)
      (g := 𝟙 (u.obj U)) (f' := pullbackProjection_targetBaseMap u p Y)
      (Category.id_comp _).symm (pullbackProjection_targetFiberMap u p X ≫ φ.1.snd))

/-- Helper for Lemma 8.12.2: strictifying the target component preserves identity morphisms. -/
theorem pullbackProjection_targetFiberHom_id
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    pullbackProjection_targetFiberHom u p (𝟙 X) =
      𝟙 (pullbackProjection_targetFiberObj u p X) := by
  -- Both maps are vertical and have the same composite with the cartesian strictification map.
  apply Functor.Fiber.hom_ext
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p X)
        (pullbackProjection_targetFiberMap u p X) :=
    pullbackProjection_targetFiberMap_isCartesian u p X
  let α : pullbackProjection_targetFiberObj u p X ⟶ pullbackProjection_targetFiberObj u p X :=
    pullbackProjection_targetFiberHom u p (𝟙 X)
  let β : pullbackProjection_targetFiberObj u p X ⟶ pullbackProjection_targetFiberObj u p X :=
    𝟙 (pullbackProjection_targetFiberObj u p X)
  letI : p.IsHomLift (𝟙 (u.obj U)) α.1 := α.2
  letI : p.IsHomLift (𝟙 (u.obj U)) β.1 := by
    change p.IsHomLift (𝟙 (u.obj U)) (𝟙 (pullbackProjection_targetFiberObj u p X).1)
    exact IsHomLift.id (pullbackProjection_targetFiberObj u p X).2
  exact
    Functor.IsCartesian.ext p (pullbackProjection_targetBaseMap u p X)
      (pullbackProjection_targetFiberMap u p X) α.1 β.1 (by
        dsimp [α, β]
        rw [pullbackProjection_targetFiberHom_fac]
        change pullbackProjection_targetFiberMap u p X ≫ 𝟙 X.1.snd =
          𝟙 (pullbackProjection_targetFiberObj u p X).1 ≫
            pullbackProjection_targetFiberMap u p X
        simp)

/-- Helper for Lemma 8.12.2: strictifying the target component preserves composition of vertical
morphisms. -/
theorem pullbackProjection_targetFiberHom_comp
    (p : S ⥤ D) [p.IsFibered] {U : C}
    {X Y Z : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    pullbackProjection_targetFiberHom u p (φ ≫ ψ) =
      pullbackProjection_targetFiberHom u p φ ≫
        pullbackProjection_targetFiberHom u p ψ := by
  -- Cartesian uniqueness reduces composition preservation to the two factorization formulas.
  apply Functor.Fiber.hom_ext
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p Z)
        (pullbackProjection_targetFiberMap u p Z) :=
    pullbackProjection_targetFiberMap_isCartesian u p Z
  let α : pullbackProjection_targetFiberObj u p X ⟶ pullbackProjection_targetFiberObj u p Z :=
    pullbackProjection_targetFiberHom u p (φ ≫ ψ)
  let β : pullbackProjection_targetFiberObj u p X ⟶ pullbackProjection_targetFiberObj u p Z :=
    pullbackProjection_targetFiberHom u p φ ≫ pullbackProjection_targetFiberHom u p ψ
  letI : p.IsHomLift (𝟙 (u.obj U)) α.1 := α.2
  letI : p.IsHomLift (𝟙 (u.obj U)) β.1 := β.2
  exact
    Functor.IsCartesian.ext p (pullbackProjection_targetBaseMap u p Z)
      (pullbackProjection_targetFiberMap u p Z) α.1 β.1 (by
        dsimp [α, β]
        rw [pullbackProjection_targetFiberHom_fac]
        calc
          pullbackProjection_targetFiberMap u p X ≫ (φ ≫ ψ).1.snd =
              pullbackProjection_targetFiberMap u p X ≫ (φ.1.snd ≫ ψ.1.snd) := by
                rfl
          _ = (pullbackProjection_targetFiberMap u p X ≫ φ.1.snd) ≫ ψ.1.snd := by
                simp [Category.assoc]
          _ = ((pullbackProjection_targetFiberHom u p φ).1 ≫
                pullbackProjection_targetFiberMap u p Y) ≫ ψ.1.snd := by
                rw [pullbackProjection_targetFiberHom_fac]
          _ = (pullbackProjection_targetFiberHom u p φ).1 ≫
                (pullbackProjection_targetFiberMap u p Y ≫ ψ.1.snd) := by
                simp [Category.assoc]
          _ = (pullbackProjection_targetFiberHom u p φ).1 ≫
                ((pullbackProjection_targetFiberHom u p ψ).1 ≫
                  pullbackProjection_targetFiberMap u p Z) := by
                rw [pullbackProjection_targetFiberHom_fac]
          _ = (pullbackProjection_targetFiberHom u p φ ≫
                pullbackProjection_targetFiberHom u p ψ).1 ≫
                pullbackProjection_targetFiberMap u p Z := by
                exact (Category.assoc
                  (pullbackProjection_targetFiberHom u p φ).1
                  (pullbackProjection_targetFiberHom u p ψ).1
                  (pullbackProjection_targetFiberMap u p Z)).symm)

/-- Helper for Lemma 8.12.2: strictification of second components is functorial on each
pullback-projection fiber. -/
noncomputable def pullbackProjection_targetFiberFunctor
    (p : S ⥤ D) [p.IsFibered] (U : C) :
    (CategoricalPullback.π₁ u p).Fiber U ⥤ p.Fiber (u.obj U) where
  obj X := pullbackProjection_targetFiberObj u p X
  map φ := pullbackProjection_targetFiberHom u p φ
  map_id X := pullbackProjection_targetFiberHom_id u p X
  map_comp φ ψ := pullbackProjection_targetFiberHom_comp u p φ ψ

/-- Helper for Lemma 8.12.2: a strict target-fiber object determines an object in the fiber of
the categorical pullback projection. -/
noncomputable def pullbackProjection_ofTargetFiberObj
    (p : S ⥤ D) {U : C} (X : p.Fiber (u.obj U)) :
    (CategoricalPullback.π₁ u p).Fiber U :=
  ⟨{ fst := U
     snd := X.1
     iso := eqToIso X.2.symm }, rfl⟩

/-- Helper for Lemma 8.12.2: the compatibility equation for the pullback morphism induced by a
strict target-fiber morphism. -/
theorem pullbackProjection_ofTargetFiberHom_w
    (p : S ⥤ D) {U : C} {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    u.map (𝟙 U) ≫ (pullbackProjection_ofTargetFiberObj u p Y).1.iso.hom =
      (pullbackProjection_ofTargetFiberObj u p X).1.iso.hom ≫ p.map φ.1 := by
  -- The target-fiber morphism lies over the identity, so its hom-lift formula is exactly the
  -- compatibility needed for the categorical pullback morphism.
  letI : p.IsHomLift (𝟙 (u.obj U)) φ.1 := φ.2
  have hφ := IsHomLift.fac' p (𝟙 (u.obj U)) φ.1
  simp [pullbackProjection_ofTargetFiberObj, hφ]

/-- Helper for Lemma 8.12.2: the ambient categorical-pullback morphism induced by a strict
target-fiber morphism. -/
def pullbackProjection_ofTargetFiberAmbientHom
    (p : S ⥤ D) {U : C} {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (pullbackProjection_ofTargetFiberObj u p X).1 ⟶
      (pullbackProjection_ofTargetFiberObj u p Y).1 :=
  { fst := 𝟙 U
    snd := φ.1
    w := pullbackProjection_ofTargetFiberHom_w u p φ }

/-- Helper for Lemma 8.12.2: the pullback morphism induced from a strict target-fiber morphism
lies over the identity of `U`. -/
theorem pullbackProjection_ofTargetFiberAmbientHom_isHomLift
    (p : S ⥤ D) {U : C} {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U)
      (pullbackProjection_ofTargetFiberAmbientHom u p φ) := by
  -- The first projection of the ambient pullback morphism is definitionally the identity on `U`.
  change (CategoricalPullback.π₁ u p).IsHomLift
    ((CategoricalPullback.π₁ u p).map (pullbackProjection_ofTargetFiberAmbientHom u p φ))
      (pullbackProjection_ofTargetFiberAmbientHom u p φ)
  infer_instance

/-- Helper for Lemma 8.12.2: a strict target-fiber morphism induces a morphism in the
corresponding fiber of the categorical pullback projection. -/
def pullbackProjection_ofTargetFiberHom
    (p : S ⥤ D) {U : C} {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    pullbackProjection_ofTargetFiberObj u p X ⟶ pullbackProjection_ofTargetFiberObj u p Y :=
  ⟨pullbackProjection_ofTargetFiberAmbientHom u p φ,
    pullbackProjection_ofTargetFiberAmbientHom_isHomLift u p φ⟩

/-- Helper for Lemma 8.12.2: the target-to-pullback fiber morphism construction preserves
identity morphisms. -/
theorem pullbackProjection_ofTargetFiberHom_id
    (p : S ⥤ D) {U : C} (X : p.Fiber (u.obj U)) :
    pullbackProjection_ofTargetFiberHom u p (𝟙 X) =
      𝟙 (pullbackProjection_ofTargetFiberObj u p X) := by
  -- Compare in the ambient categorical pullback, where both components are identities.
  apply Functor.Fiber.hom_ext
  apply CategoricalPullback.hom_ext
  · rfl
  · rfl

/-- Helper for Lemma 8.12.2: the target-to-pullback fiber morphism construction preserves
composition. -/
theorem pullbackProjection_ofTargetFiberHom_comp
    (p : S ⥤ D) {U : C} {X Y Z : p.Fiber (u.obj U)} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    pullbackProjection_ofTargetFiberHom u p (φ ≫ ψ) =
      pullbackProjection_ofTargetFiberHom u p φ ≫ pullbackProjection_ofTargetFiberHom u p ψ := by
  -- Compare in the ambient categorical pullback, where composition is componentwise.
  apply Functor.Fiber.hom_ext
  apply CategoricalPullback.hom_ext
  · change 𝟙 U = 𝟙 U ≫ 𝟙 U
    simp
  · change (φ ≫ ψ).1 = φ.1 ≫ ψ.1
    rfl

/-- Helper for Lemma 8.12.2: the object-level lift from strict target fibers to pullback fibers,
bundled as a functor. -/
noncomputable def pullbackProjection_ofTargetFiberFunctor
    (p : S ⥤ D) (U : C) :
    p.Fiber (u.obj U) ⥤ (CategoricalPullback.π₁ u p).Fiber U where
  obj X := pullbackProjection_ofTargetFiberObj u p X
  map φ := pullbackProjection_ofTargetFiberHom u p φ
  map_id X := pullbackProjection_ofTargetFiberHom_id u p X
  map_comp φ ψ := pullbackProjection_ofTargetFiberHom_comp u p φ ψ

/-- Helper for Lemma 8.12.2: the strictification map satisfies the pullback square needed to
compare the lifted strict target object with the original pullback-fiber object. -/
theorem pullbackProjection_targetFiberComparison_w
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    u.map (eqToHom X.2.symm) ≫ X.1.iso.hom =
      (pullbackProjection_ofTargetFiberObj u p
          (pullbackProjection_targetFiberObj u p X)).1.iso.hom ≫
        p.map (pullbackProjection_targetFiberMap u p X) := by
  -- Both sides are the structural base arrow used to choose the strict target pullback.
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p X)
        (pullbackProjection_targetFiberMap u p X) :=
    pullbackProjection_targetFiberMap_isCartesian u p X
  have hfac :
      pullbackProjection_targetBaseMap u p X =
        eqToHom (IsHomLift.domain_eq p
            (pullbackProjection_targetBaseMap u p X)
            (pullbackProjection_targetFiberMap u p X)).symm ≫
          p.map (pullbackProjection_targetFiberMap u p X) ≫
          eqToHom (IsHomLift.codomain_eq p
            (pullbackProjection_targetBaseMap u p X)
            (pullbackProjection_targetFiberMap u p X) : p.obj X.1.snd =
              p.obj X.1.snd) := by
    simpa using
      (IsHomLift.fac p (pullbackProjection_targetBaseMap u p X)
        (pullbackProjection_targetFiberMap u p X))
  calc
    u.map (eqToHom X.2.symm) ≫ X.1.iso.hom =
        pullbackProjection_targetBaseMap u p X := by
          simp [pullbackProjection_targetBaseMap, eqToHom_map]
    _ =
        (pullbackProjection_ofTargetFiberObj u p
            (pullbackProjection_targetFiberObj u p X)).1.iso.hom ≫
          p.map (pullbackProjection_targetFiberMap u p X) := by
          rw [hfac]
          simp [pullbackProjection_ofTargetFiberObj, pullbackProjection_targetFiberObj,
            pullbackProjection_targetBaseMap]

/-- Helper for Lemma 8.12.2: the ambient pullback morphism from the lifted strict target object
back to the original pullback-fiber object. -/
noncomputable def pullbackProjection_targetFiberComparisonAmbientHom
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    (pullbackProjection_ofTargetFiberObj u p
        (pullbackProjection_targetFiberObj u p X)).1 ⟶ X.1 :=
  { fst := eqToHom X.2.symm
    snd := pullbackProjection_targetFiberMap u p X
    w := pullbackProjection_targetFiberComparison_w u p X }

/-- Helper for Lemma 8.12.2: the comparison ambient morphism lies over the identity of the
source fiber. -/
theorem pullbackProjection_targetFiberComparisonAmbientHom_isHomLift
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U)
      (pullbackProjection_targetFiberComparisonAmbientHom u p X) := by
  -- The first component is exactly the transported identity from the strict object over `U` to
  -- the original representative of the same fiber.
  exact
    IsHomLift.of_fac' (CategoricalPullback.π₁ u p) (𝟙 U)
      (pullbackProjection_targetFiberComparisonAmbientHom u p X) rfl X.2 (by
        simp [pullbackProjection_targetFiberComparisonAmbientHom])

/-- Helper for Lemma 8.12.2: the comparison from the lifted strict target object back to the
original pullback-fiber object. -/
noncomputable def pullbackProjection_targetFiberComparisonHom
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    pullbackProjection_ofTargetFiberObj u p
        (pullbackProjection_targetFiberObj u p X) ⟶ X :=
  ⟨pullbackProjection_targetFiberComparisonAmbientHom u p X,
    pullbackProjection_targetFiberComparisonAmbientHom_isHomLift u p X⟩

/-- Helper for Lemma 8.12.2: the comparison from the lifted strict target object to the original
pullback-fiber object is an isomorphism. -/
theorem pullbackProjection_targetFiberComparisonHom_isIso
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    IsIso (pullbackProjection_targetFiberComparisonHom u p X) := by
  -- The ambient pullback morphism has isomorphisms on both components, so it is an isomorphism;
  -- the inverse again lies over the identity because we are in a fiber.
  letI : IsIso (pullbackProjection_targetFiberMap u p X) :=
    pullbackProjection_targetFiberMap_isIso u p X
  letI : IsIso (pullbackProjection_targetFiberComparisonAmbientHom u p X).fst := by
    dsimp [pullbackProjection_targetFiberComparisonAmbientHom]
    infer_instance
  letI : IsIso (pullbackProjection_targetFiberComparisonAmbientHom u p X).snd := by
    dsimp [pullbackProjection_targetFiberComparisonAmbientHom]
    exact pullbackProjection_targetFiberMap_isIso u p X
  letI : IsIso (pullbackProjection_targetFiberComparisonAmbientHom u p X) := by
    exact
      (Limits.CategoricalPullback.isIso_iff u p
        (pullbackProjection_targetFiberComparisonAmbientHom u p X)).2
        ⟨inferInstance, inferInstance⟩
  letI :
      (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U)
        (asIso (pullbackProjection_targetFiberComparisonAmbientHom u p X)).hom := by
    change (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U)
      (pullbackProjection_targetFiberComparisonAmbientHom u p X)
    exact pullbackProjection_targetFiberComparisonAmbientHom_isHomLift u p X
  let invHom :
      X ⟶ pullbackProjection_ofTargetFiberObj u p
          (pullbackProjection_targetFiberObj u p X) :=
    ⟨inv (pullbackProjection_targetFiberComparisonAmbientHom u p X), by
      simpa using
        (IsHomLift.lift_id_inv (CategoricalPullback.π₁ u p) U
          (asIso (pullbackProjection_targetFiberComparisonAmbientHom u p X)))⟩
  refine ⟨⟨invHom, ?_, ?_⟩⟩
  · apply Functor.Fiber.hom_ext
    change pullbackProjection_targetFiberComparisonAmbientHom u p X ≫
        inv (pullbackProjection_targetFiberComparisonAmbientHom u p X) = 𝟙 _
    simp
  · apply Functor.Fiber.hom_ext
    change inv (pullbackProjection_targetFiberComparisonAmbientHom u p X) ≫
        pullbackProjection_targetFiberComparisonAmbientHom u p X = 𝟙 _
    simp

/-- Helper for Lemma 8.12.2: the comparison from the lifted strict target object to the original
pullback-fiber object, packaged as an isomorphism. -/
noncomputable def pullbackProjection_targetFiberComparisonIso
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    pullbackProjection_ofTargetFiberObj u p
        (pullbackProjection_targetFiberObj u p X) ≅ X :=
  let _ : IsIso (pullbackProjection_targetFiberComparisonHom u p X) :=
    pullbackProjection_targetFiberComparisonHom_isIso u p X
  asIso (pullbackProjection_targetFiberComparisonHom u p X)

/-- Helper for Lemma 8.12.2: the pullback-fiber comparison is natural for vertical morphisms. -/
theorem pullbackProjection_targetFiberComparisonHom_naturality
    (p : S ⥤ D) [p.IsFibered] {U : C}
    {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (pullbackProjection_ofTargetFiberFunctor u p U).map
        ((pullbackProjection_targetFiberFunctor u p U).map φ) ≫
      pullbackProjection_targetFiberComparisonHom u p Y =
    pullbackProjection_targetFiberComparisonHom u p X ≫ φ := by
  -- Compare the two ambient pullback morphisms componentwise.
  apply Functor.Fiber.hom_ext
  apply CategoricalPullback.hom_ext
  · letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) φ.1 := φ.2
    have hfst :
        φ.1.fst = eqToHom X.2 ≫ 𝟙 U ≫ eqToHom Y.2.symm := by
      simpa using
        (IsHomLift.fac' (CategoricalPullback.π₁ u p) (𝟙 U) φ.1)
    change 𝟙 U ≫ eqToHom Y.2.symm = eqToHom X.2.symm ≫ φ.1.fst
    rw [hfst]
    simp
  · simpa [pullbackProjection_ofTargetFiberFunctor, pullbackProjection_ofTargetFiberHom,
      pullbackProjection_ofTargetFiberAmbientHom, pullbackProjection_targetFiberFunctor,
      pullbackProjection_targetFiberComparisonHom,
      pullbackProjection_targetFiberComparisonAmbientHom] using
      (pullbackProjection_targetFiberHom_fac u p φ)

/-- Helper for Lemma 8.12.2: strictifying an already strict target-fiber object gives a morphism
back to it over the identity of the base. -/
theorem pullbackProjection_targetFiberMap_ofTargetFiberObj_isHomLift
    (p : S ⥤ D) [p.IsFibered] {U : C} (X : p.Fiber (u.obj U)) :
    p.IsHomLift (𝟙 (u.obj U))
      (pullbackProjection_targetFiberMap u p (pullbackProjection_ofTargetFiberObj u p X)) := by
  -- The cartesian strictification map lies over the transported identity, which is the identity in
  -- the fiber after using the source and target membership equalities.
  let Xpb := pullbackProjection_ofTargetFiberObj u p X
  letI :
      p.IsCartesian (pullbackProjection_targetBaseMap u p Xpb)
        (pullbackProjection_targetFiberMap u p Xpb) :=
    pullbackProjection_targetFiberMap_isCartesian u p Xpb
  have hfac :
      p.map (pullbackProjection_targetFiberMap u p Xpb) =
        eqToHom (IsHomLift.domain_eq p
            (pullbackProjection_targetBaseMap u p Xpb)
            (pullbackProjection_targetFiberMap u p Xpb)) ≫
          pullbackProjection_targetBaseMap u p Xpb ≫
          eqToHom (IsHomLift.codomain_eq p
            (pullbackProjection_targetBaseMap u p Xpb)
            (pullbackProjection_targetFiberMap u p Xpb)).symm := by
    simpa using
      (IsHomLift.fac' p (pullbackProjection_targetBaseMap u p Xpb)
        (pullbackProjection_targetFiberMap u p Xpb))
  exact
    IsHomLift.of_fac' p (𝟙 (u.obj U))
      (pullbackProjection_targetFiberMap u p Xpb)
      (pullbackProjection_targetFiberObj u p Xpb).2 X.2 (by
        rw [hfac]
        simp [Xpb, pullbackProjection_ofTargetFiberObj, pullbackProjection_targetFiberObj,
          pullbackProjection_targetBaseMap])

/-- Helper for Lemma 8.12.2: the target-fiber comparison from the strictification of a lifted
target object back to the original target object. -/
noncomputable def pullbackProjection_targetFiberCounitHom
    (p : S ⥤ D) [p.IsFibered] {U : C} (X : p.Fiber (u.obj U)) :
    pullbackProjection_targetFiberObj u p (pullbackProjection_ofTargetFiberObj u p X) ⟶ X :=
  ⟨pullbackProjection_targetFiberMap u p (pullbackProjection_ofTargetFiberObj u p X),
    pullbackProjection_targetFiberMap_ofTargetFiberObj_isHomLift u p X⟩

/-- Helper for Lemma 8.12.2: the target-fiber comparison morphism is an isomorphism. -/
theorem pullbackProjection_targetFiberCounitHom_isIso
    (p : S ⥤ D) [p.IsFibered] {U : C} (X : p.Fiber (u.obj U)) :
    IsIso (pullbackProjection_targetFiberCounitHom u p X) := by
  -- The underlying strictification map is an isomorphism over the identity, so its inverse is again
  -- a target-fiber morphism.
  let m :
      (pullbackProjection_targetFiberObj u p (pullbackProjection_ofTargetFiberObj u p X)).1 ⟶
        X.1 :=
    pullbackProjection_targetFiberMap u p (pullbackProjection_ofTargetFiberObj u p X)
  let hm : IsIso m := by
    dsimp [m]
    exact pullbackProjection_targetFiberMap_isIso u p (pullbackProjection_ofTargetFiberObj u p X)
  letI : IsIso m := hm
  letI :
      p.IsHomLift (𝟙 (u.obj U)) (asIso m).hom := by
    change p.IsHomLift (𝟙 (u.obj U)) m
    dsimp [m]
    exact pullbackProjection_targetFiberMap_ofTargetFiberObj_isHomLift u p X
  let invHom :
      X ⟶ pullbackProjection_targetFiberObj u p (pullbackProjection_ofTargetFiberObj u p X) :=
    ⟨@inv S _ _ _ m hm, by
      simpa using
        (IsHomLift.lift_id_inv p (u.obj U) (asIso m))⟩
  refine ⟨⟨invHom, ?_, ?_⟩⟩
  · apply Functor.Fiber.hom_ext
    simpa [Functor.Fiber.fiberInclusion, invHom, pullbackProjection_targetFiberCounitHom, m]
      using (IsIso.hom_inv_id m)
  · apply Functor.Fiber.hom_ext
    simpa [Functor.Fiber.fiberInclusion, invHom, pullbackProjection_targetFiberCounitHom, m]
      using (IsIso.inv_hom_id m)

/-- Helper for Lemma 8.12.2: strictifying and then lifting a target-fiber object is
isomorphic to the original target-fiber object. -/
noncomputable def pullbackProjection_targetFiberCounitIso
    (p : S ⥤ D) [p.IsFibered] {U : C} (X : p.Fiber (u.obj U)) :
    pullbackProjection_targetFiberObj u p (pullbackProjection_ofTargetFiberObj u p X) ≅ X :=
  let _ : IsIso (pullbackProjection_targetFiberCounitHom u p X) :=
    pullbackProjection_targetFiberCounitHom_isIso u p X
  asIso (pullbackProjection_targetFiberCounitHom u p X)

/-- Helper for Lemma 8.12.2: the target-fiber counit is natural for vertical morphisms. -/
theorem pullbackProjection_targetFiberCounitHom_naturality
    (p : S ⥤ D) [p.IsFibered] {U : C} {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (pullbackProjection_targetFiberFunctor u p U).map
        ((pullbackProjection_ofTargetFiberFunctor u p U).map φ) ≫
      pullbackProjection_targetFiberCounitHom u p Y =
    pullbackProjection_targetFiberCounitHom u p X ≫ φ := by
  -- The cartesian factorization formula for the strictification map gives the second component.
  apply Functor.Fiber.hom_ext
  simpa [pullbackProjection_targetFiberFunctor, pullbackProjection_ofTargetFiberFunctor,
      pullbackProjection_ofTargetFiberHom, pullbackProjection_ofTargetFiberAmbientHom,
      pullbackProjection_targetFiberCounitHom] using
    (pullbackProjection_targetFiberHom_fac u p (pullbackProjection_ofTargetFiberHom u p φ))

/-- Helper for Lemma 8.12.2: strictifying the target component is an equivalence on every
fiber of the pullback projection. -/
theorem pullbackProjection_targetFiberFunctor_isEquivalence
    (p : S ⥤ D) [p.IsFibered] (U : C) :
    (pullbackProjection_targetFiberFunctor u p U).IsEquivalence := by
  let F := pullbackProjection_targetFiberFunctor u p U
  let G := pullbackProjection_ofTargetFiberFunctor u p U
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · refine NatIso.ofComponents ?_ ?_
    · intro X
      exact (pullbackProjection_targetFiberComparisonIso u p X).symm
    · intro X Y f
      letI : IsIso (pullbackProjection_targetFiberComparisonHom u p Y) :=
        pullbackProjection_targetFiberComparisonHom_isIso u p Y
      letI : IsIso (pullbackProjection_targetFiberComparisonHom u p X) :=
        pullbackProjection_targetFiberComparisonHom_isIso u p X
      apply (cancel_mono (pullbackProjection_targetFiberComparisonHom u p Y)).1
      calc
        (f ≫ inv (pullbackProjection_targetFiberComparisonHom u p Y)) ≫
            pullbackProjection_targetFiberComparisonHom u p Y = f := by
              simp [Category.assoc]
        _ =
            (inv (pullbackProjection_targetFiberComparisonHom u p X) ≫
                (pullbackProjection_ofTargetFiberFunctor u p U).map
                  ((pullbackProjection_targetFiberFunctor u p U).map f)) ≫
              pullbackProjection_targetFiberComparisonHom u p Y := by
              have hnat := pullbackProjection_targetFiberComparisonHom_naturality u p f
              calc
                f = (inv (pullbackProjection_targetFiberComparisonHom u p X) ≫
                    pullbackProjection_targetFiberComparisonHom u p X) ≫ f := by
                    simp
                _ = inv (pullbackProjection_targetFiberComparisonHom u p X) ≫
                    (pullbackProjection_targetFiberComparisonHom u p X ≫ f) := by
                    simp
                _ = inv (pullbackProjection_targetFiberComparisonHom u p X) ≫
                    ((pullbackProjection_ofTargetFiberFunctor u p U).map
                        ((pullbackProjection_targetFiberFunctor u p U).map f) ≫
                      pullbackProjection_targetFiberComparisonHom u p Y) := by
                    exact
                      congrArg (fun k ↦
                        inv (pullbackProjection_targetFiberComparisonHom u p X) ≫ k) hnat.symm
                _ = (inv (pullbackProjection_targetFiberComparisonHom u p X) ≫
                    (pullbackProjection_ofTargetFiberFunctor u p U).map
                      ((pullbackProjection_targetFiberFunctor u p U).map f)) ≫
                    pullbackProjection_targetFiberComparisonHom u p Y := by
                    exact
                      (Category.assoc (inv (pullbackProjection_targetFiberComparisonHom u p X))
                        ((pullbackProjection_ofTargetFiberFunctor u p U).map
                          ((pullbackProjection_targetFiberFunctor u p U).map f))
                        (pullbackProjection_targetFiberComparisonHom u p Y)).symm
  · refine NatIso.ofComponents ?_ ?_
    · intro X
      exact pullbackProjection_targetFiberCounitIso u p X
    · intro X Y f
      simpa [F, G, pullbackProjection_targetFiberCounitIso] using
        pullbackProjection_targetFiberCounitHom_naturality u p f

end

end CategoryTheory
