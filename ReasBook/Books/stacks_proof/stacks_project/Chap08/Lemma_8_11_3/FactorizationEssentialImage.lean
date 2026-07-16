import stacks_proof.stacks_project.Chap08.Lemma_8_11_3.InheritedCoverProjection

open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver.{u₁, v₁, max u₁ v₁, v₁} J}

/-- Helper for Lemma 8.11.3: a source-fiber object with a comparison isomorphism to a target
fiber object gives an object of the canonical factorization over that target object. -/
theorem canonicalFactorization_fiber_nonempty_of_iso
    (F : Xₛ ⟶ Yₛ) {U : C} (x : Xₛ.p.Fiber U) (y : Yₛ.p.Fiber U)
    (e : (F.fiberFunctor U).obj x ≅ y) :
    Nonempty
      ((fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.Fiber y.1) := by
  let P : (fibredInGroupoidsFactorization (toBasedFunctor F)).obj :=
    { U := U
      obj := { fst := x, snd := y, iso := e } }
  exact ⟨⟨P, rfl⟩⟩

/-- Helper for Lemma 8.11.3: a strongly cartesian arrow identifies its domain fiber object with
the canonical pullback of its codomain. -/
theorem stronglyCartesianDomain_iso_canonicalPullback_nonempty
    {B : Type u₁} {E : Type u₂} [Category.{v₁} B] [Category.{v₂} E]
    (p : E ⥤ B) [p.IsFibered]
    {x y : E} (φ : x ⟶ y)
    [hφ : p.IsStronglyCartesian (p.map φ) φ] :
    Nonempty
      ((Functor.Fiber.mk (p := p) (show p.obj x = p.obj x from rfl)) ≅
        ((canonicalPullbackChoice p).pullbackFunctor (p.map φ)).obj
          (Functor.Fiber.mk (p := p) (show p.obj y = p.obj y from rfl))) := by
  let yFiber : p.Fiber (p.obj y) :=
    Functor.Fiber.mk (p := p) (show p.obj y = p.obj y from rfl)
  let canonicalY : p.Fiber (p.obj x) :=
    (p.map φ ^*[canonicalPullbackChoice p] yFiber)
  let pulledY : p.Fiber (p.obj x) :=
    Functor.Fiber.mk (p := p) (show p.obj x = p.obj x from rfl)
  let k : canonicalY.1 ⟶ y := (canonicalPullbackChoice p).map (p.map φ) yFiber
  have hk : p.IsStronglyCartesian (p.map φ) k := by
    -- The chosen canonical pullback arrow is strongly cartesian over the same base arrow.
    simpa [k] using (canonicalPullbackChoice p).isStronglyCartesian (p.map φ) yFiber
  letI : p.IsStronglyCartesian (p.map φ) k := hk
  letI : p.IsStronglyCartesian (p.map φ) φ := hφ
  let e : pulledY.1 ≅ canonicalY.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ p
      _ _ _ _ _ _ (p.map φ) (p.map φ) (Iso.refl (p.obj x))
      (show p.map φ = (Iso.refl (p.obj x)).hom ≫ p.map φ by simp)
      k φ hk hφ
  have hhom : p.IsHomLift (𝟙 (p.obj x)) e.hom := by
    -- The uniqueness comparison is vertical, so it is a morphism in the domain fiber.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ p
        _ _ _ _ _ _ (p.map φ) (p.map φ) (Iso.refl (p.obj x))
        (show p.map φ = (Iso.refl (p.obj x)).hom ≫ p.map φ by simp)
        k φ hk hφ)
  have hinv : p.IsHomLift (𝟙 (p.obj x)) e.inv := by
    -- The inverse comparison is vertical for the same reason.
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ p
        _ _ _ _ _ _ (p.map φ) (p.map φ) (Iso.refl (p.obj x))
        (show p.map φ = (Iso.refl (p.obj x)).hom ≫ p.map φ by simp)
        k φ hk hφ)
  refine ⟨?_⟩
  exact
    { hom := Functor.Fiber.homMk p (p.obj x) e.hom
      inv := Functor.Fiber.homMk p (p.obj x) e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 8.11.3: the domain of a total arrow in the target stack is isomorphic in
the base fiber to the chosen canonical pullback of its codomain. -/
theorem totalArrow_domain_iso_canonicalPullback_nonempty
    {y z : Yₛ.S} (i : z ⟶ y) :
    Nonempty
      ((Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj z = Yₛ.p.obj z from rfl)) ≅
        ((canonicalPullbackChoice Yₛ.p).pullbackFunctor (Yₛ.p.map i)).obj
          (Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))) := by
  have hi : Yₛ.p.IsStronglyCartesian (Yₛ.p.map i) i := by
    infer_instance
  letI : Yₛ.p.IsStronglyCartesian (Yₛ.p.map i) i := hi
  -- Apply the generic comparison lemma to the strongly cartesian target arrow.
  exact stronglyCartesianDomain_iso_canonicalPullback_nonempty (p := Yₛ.p) i

/-- Helper for Lemma 8.11.3: a factorization object over the domain of a target arrow supplies
the corresponding local essential-image datum over the projected base arrow. -/
theorem canonicalFactorization_fiber_localEssentialImageDatum
    (F : Xₛ ⟶ Yₛ) {y z : Yₛ.S} (i : z ⟶ y)
    (P :
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.Fiber z) :
    ∃ x : Xₛ.p.Fiber (Yₛ.p.obj z),
      Nonempty
        ((F.fiberFunctor (Yₛ.p.obj z)).obj x ≅
          ((canonicalPullbackChoice Yₛ.p).pullbackFunctor (Yₛ.p.map i)).obj
            (Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))) := by
  rcases P with ⟨P, hP⟩
  subst hP
  let xBase : Xₛ.p.Fiber (Yₛ.p.obj P.obj.snd.1) := P.obj.snd.2.symm ▸ P.obj.fst
  have eP :
      (F.fiberFunctor (Yₛ.p.obj P.obj.snd.1)).obj xBase ≅
        (Functor.Fiber.mk (p := Yₛ.p)
          (show Yₛ.p.obj P.obj.snd.1 = Yₛ.p.obj P.obj.snd.1 from rfl)) := by
    -- Normalize the explicit two-fibre-product object so its stored comparison isomorphism
    -- has exactly the required fiber spelling.
    cases P with
    | mk U Pobj =>
        cases Pobj with
        | mk fst snd iso =>
            rcases snd with ⟨snd, rfl⟩
            simpa [xBase] using iso
  refine ⟨xBase, ?_⟩
  obtain ⟨ey⟩ := totalArrow_domain_iso_canonicalPullback_nonempty (J := J) (Yₛ := Yₛ) i
  exact ⟨eP ≪≫ ey⟩

/-- Helper for Lemma 8.11.3: local essential-image data from a factorization object remains
valid after precomposing the target arrow by a base morphism. -/
theorem canonicalFactorization_fiber_localEssentialImageDatum_comp
    (F : Xₛ ⟶ Yₛ) {y z : Yₛ.S} (i : z ⟶ y)
    {V : C} (g : V ⟶ Yₛ.p.obj z)
    (P :
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor.Fiber z) :
    ∃ x : Xₛ.p.Fiber V,
      Nonempty
        ((F.fiberFunctor V).obj x ≅
          ((canonicalPullbackChoice Yₛ.p).pullbackFunctor (g ≫ Yₛ.p.map i)).obj
            (Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl))) := by
  obtain ⟨x, hx⟩ :=
    canonicalFactorization_fiber_localEssentialImageDatum
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F i P
  obtain ⟨e⟩ := hx
  let hcX := canonicalPullbackChoice Xₛ.p
  let hcY := canonicalPullbackChoice Yₛ.p
  let yFiber : Yₛ.p.Fiber (Yₛ.p.obj y) :=
    Functor.Fiber.mk (p := Yₛ.p) (show Yₛ.p.obj y = Yₛ.p.obj y from rfl)
  refine ⟨(hcX.pullbackFunctor g).obj x, ?_⟩
  -- Pull the comparison isomorphism back along `g`, then compare iterated pullbacks with the
  -- single pullback along the composite base arrow.
  refine ⟨?_⟩
  exact
    (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g x).symm ≪≫
      (hcY.pullbackFunctor g).mapIso e ≪≫
        (hcY.pullbackCompComponentIso (Yₛ.p.map i) g yFiber).symm

/-- Helper for Lemma 8.11.3: the source projection of a strict factorization through a functor
fibred in groupoids over the target total category is itself fibred in groupoids over the base. -/
theorem factorizationSource_isFibredInGroupoids
    {X' : BasedCategory.{v₁, max u₁ v₁} C}
    (F' : X' ⥤ᵇ Yₛ.toBasedCategory)
    [IsFibredInGroupoids F'.toFunctor] :
    IsFibredInGroupoids X'.p := by
  have hcomp : IsFibredInGroupoids (F'.toFunctor ⋙ Yₛ.p) := inferInstance
  -- The based-functor compatibility identifies the composite projection with `X'.p`.
  simpa [F'.w] using hcomp

/-- Helper for Lemma 8.11.3: the source projection of a strict factorization is a stack in
groupoids over the original site after transport along the source equivalence. -/
theorem factorizationSource_isStackInGroupoids
    {X' : BasedCategory.{v₁, max u₁ v₁} C}
    (a : Xₛ.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Yₛ.toBasedCategory)
    [IsFibredInGroupoids F'.toFunctor]
    (ha : a.IsEquivalenceOverBase) :
    IsStackInGroupoids J X'.p := by
  letI : IsFibredInGroupoids X'.p :=
    factorizationSource_isFibredInGroupoids (J := J) (Yₛ := Yₛ) F'
  have hsource : IsStackInGroupoids J Xₛ.p := inferInstance
  -- Transport the stack-in-groupoids structure across the fiberwise equivalence `a`.
  exact (isStackInGroupoids_iff_of_equivalence_over_base J Xₛ.p X'.p a ha).1 hsource

/-- Helper for Lemma 8.11.3: the arbitrary strict factorization source also carries the
underlying stack-on-site structure needed by raw inherited-stack arguments. -/
theorem factorizationSource_isStackOnSite
    {X' : BasedCategory.{v₁, max u₁ v₁} C}
    (a : Xₛ.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Yₛ.toBasedCategory)
    [IsFibredInGroupoids F'.toFunctor]
    (ha : a.IsEquivalenceOverBase) :
    IsStackOnSite J X'.p := by
  letI : IsFibredInGroupoids X'.p :=
    factorizationSource_isFibredInGroupoids (J := J) (Yₛ := Yₛ) F'
  letI : IsStackInGroupoids J X'.p :=
    factorizationSource_isStackInGroupoids (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) a F' ha
  -- Forget the groupoid part of the transported stack-in-groupoids structure.
  infer_instance

/- Route correction: raw instance search cannot discover the inherited-topology stack-on-site
structure here. Reuse the exported Lemma 8.10.5 wrapper and only normalize the local topology
spelling. -/
/-- Helper for Lemma 8.11.3: a fibred-in-groupoids stack morphism is stack-on-site for the
topology inherited from the target total category. -/
theorem inheritedTopology_stackOnSite_of_isFibredInGroupoids_forGerbeCriterion
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (StackInGroupoidsOver.Hom.G F)] :
    IsStackOnSite (inheritedTopology J Yₛ) (StackInGroupoidsOver.Hom.G F) := by
  -- Reuse the canonical inherited-topology stack theorem from Lemma 8.10.5.
  simpa [inheritedTopology] using
    (CategoryTheory.isStackOnSiteOverInheritedTopology_of_isFibredInGroupoids
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F)

/-- Helper for Lemma 8.11.3: a fibred-in-groupoids morphism of stacks is a stack in groupoids on
the topology inherited from the target total category. -/
theorem inheritedTopology_stackInGroupoids_of_isFibredInGroupoids
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (StackInGroupoidsOver.Hom.G F)] :
    IsStackInGroupoids (inheritedTopology J Yₛ) (StackInGroupoidsOver.Hom.G F) := by
  have hcomm : StackInGroupoidsOver.Hom.G F ⋙ Yₛ.p = Xₛ.p := by
    simpa [StackInGroupoidsOver.Hom.G] using
      StackInGroupoidsOver.Hom.comm F
  have hcomp : IsStackOnSite J (StackInGroupoidsOver.Hom.G F ⋙ Yₛ.p) := by
    rw [hcomm]
    infer_instance
  letI : IsStackOnSite J (StackInGroupoidsOver.Hom.G F ⋙ Yₛ.p) := hcomp
  letI : IsStackOnSite (inheritedTopology J Yₛ) (StackInGroupoidsOver.Hom.G F) :=
    inheritedTopology_stackOnSite_of_isFibredInGroupoids_forGerbeCriterion
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
  -- The groupoid part is exactly the ambient fibred-in-groupoids hypothesis.
  infer_instance

/-- Helper for Lemma 8.11.3: the stack-in-groupoids field for an arbitrary strict factorization
is inherited from the fact that the target projection is fibred in groupoids. -/
theorem factorizationProjection_isStackInGroupoidsOverInheritedTopology
    {X' : BasedCategory.{v₁, max u₁ v₁} C}
    (a : Xₛ.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Yₛ.toBasedCategory)
    [IsFibredInGroupoids F'.toFunctor]
    (ha : a.IsEquivalenceOverBase) :
    IsStackInGroupoids (inheritedTopology J Yₛ) F'.toFunctor := by
  letI : IsFibredInGroupoids X'.p :=
    factorizationSource_isFibredInGroupoids (J := J) (Yₛ := Yₛ) F'
  letI : IsStackInGroupoids J X'.p :=
    factorizationSource_isStackInGroupoids (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) a F' ha
  let X'ₛ : StackInGroupoidsOver J := StackInGroupoidsOver.ofProjection J X'.p
  let F'ₛ : X'ₛ ⟶ Yₛ := StackInGroupoidsOver.Hom.ofBasedFunctor F'
  letI : IsFibredInGroupoids (StackInGroupoidsOver.Hom.G F'ₛ) := by
    simpa [F'ₛ, StackInGroupoidsOver.Hom.G, StackInGroupoidsOver.Hom.ofBasedFunctor] using
      (inferInstance : IsFibredInGroupoids F'.toFunctor)
  -- Apply the inherited-topology theorem to the bundled morphism, then unfold the bundled
  -- functor back to the arbitrary strict factorization projection.
  simpa [F'ₛ, StackInGroupoidsOver.Hom.G, StackInGroupoidsOver.Hom.ofBasedFunctor] using
    inheritedTopology_stackInGroupoids_of_isFibredInGroupoids
      (J := J) (Xₛ := X'ₛ) (Yₛ := Yₛ) F'ₛ

end

end StackInGroupoidsOver.Hom

end CategoryTheory
