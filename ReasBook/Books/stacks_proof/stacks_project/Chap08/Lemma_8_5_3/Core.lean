import stacks_proof.stacks_project.Chap04.Definition_4_33_9
import stacks_proof.stacks_project.Chap04.Lemma_4_35_3
import stacks_proof.stacks_project.Chap04.Lemma_4_35_9

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open BasedFunctor Functor IsStronglyCartesian

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: the wide-subcategory inclusion exhibits the associated groupoid
projection as a based functor over `p`. -/
private theorem associated_groupoid_inclusion_w :
    wideSubcategoryInclusion (stronglyCartesianProperty p) ⋙ p =
      stronglyCartesianProjection p :=
  rfl

/-- Helper for Lemma 8.5.3: the inclusion of the strongly cartesian wide subcategory into the
ambient total category is a morphism over the base. -/
private noncomputable def associated_groupoid_inclusion_based :
    BasedCategory.ofFunctor (stronglyCartesianProjection p) ⥤ᵇ BasedCategory.ofFunctor p :=
  { toFunctor := wideSubcategoryInclusion (stronglyCartesianProperty p)
    w := associated_groupoid_inclusion_w (p := p) }

/-- Helper for Lemma 8.5.3: the canonical inclusion preserves strongly cartesian morphisms
because every morphism in the source already satisfies the defining property. -/
private theorem associated_groupoid_inclusion_preserves_strongly_cartesian
    [p.IsFibered] :
    (associated_groupoid_inclusion_based (p := p)).PreservesStronglyCartesian := by
  intro a b φ hφ
  -- Forgetting the wide-subcategory proof does not change the ambient strongly cartesian arrow.
  simpa [associated_groupoid_inclusion_based, stronglyCartesianProjection]
    using (show p.IsStronglyCartesian (p.map φ.1) φ.1 from φ.2)

/-- Helper for Lemma 8.5.3: the inclusion of the associated groupoid into the original fibred
category is a morphism of fibred categories over `C`. -/
noncomputable def associated_groupoid_inclusion
    [p.IsFibered] :
    FibredCategoryOver.ofFunctor (stronglyCartesianProjection p) ⟶ FibredCategoryOver.ofFunctor p :=
  FibredCategoryMor.ofBasedFunctor
    (associated_groupoid_inclusion_based (p := p))
    (associated_groupoid_inclusion_preserves_strongly_cartesian (p := p))

/-- Helper for Lemma 8.5.3: fibers of the associated groupoid projection are groupoids, so every
fiber morphism is automatically an isomorphism. -/
theorem associated_groupoid_fiber_hom_isIso
    [p.IsFibered] {U : C} {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    IsIso φ := by
  -- The Chapter 4 owner theorem already upgrades the associated projection to a fibred category
  -- in groupoids, so each fiber morphism is invertible.
  letI : IsFibredInGroupoids (stronglyCartesianProjection p) := inferInstance
  infer_instance

/-- Helper for Lemma 8.5.3: an object of an ambient fiber can be viewed in the corresponding
fiber of the associated groupoid, since the wide subcategory keeps all objects. -/
abbrev associated_groupoid_fiber_obj
    [p.IsFibered] {U : C} (x : p.Fiber U) :
    (stronglyCartesianProjection p).Fiber U :=
  Functor.Fiber.mk (a := ⟨x.1⟩) <| by
    simpa [stronglyCartesianProjection] using x.2

/-- Helper for Lemma 8.5.3: an isomorphism in an ambient fiber is already a morphism in the
associated-groupoid fiber, because vertical isomorphisms are strongly cartesian over identities. -/
noncomputable def associated_groupoid_fiber_hom_of_isIso
    [p.IsFibered] {U : C} {x y : p.Fiber U} (φ : x ⟶ y) [IsIso φ] :
    associated_groupoid_fiber_obj (p := p) x ⟶ associated_groupoid_fiber_obj (p := p) y := by
  -- Repackage the ambient vertical isomorphism as a wide-subcategory arrow.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : IsIso φ.1 := by
    simpa using
      (inferInstance : IsIso ((Functor.Fiber.fiberInclusion : p.Fiber U ⥤ S).map φ))
  have hmem : stronglyCartesianProperty p φ.1 := by
    letI : p.IsHomLift (p.map φ.1) φ.1 := Functor.IsHomLift.map (p := p) φ.1
    have hStrong' : p.IsStronglyCartesian (p.map φ.1) φ.1 :=
      IsStronglyCartesian.of_isIso p (p.map φ.1) φ.1
    simpa [stronglyCartesianProperty] using hStrong'
  let φ' :
      (associated_groupoid_fiber_obj (p := p) x).1 ⟶
        (associated_groupoid_fiber_obj (p := p) y).1 :=
    ⟨φ.1, hmem⟩
  letI : (stronglyCartesianProjection p).IsHomLift (𝟙 U) φ' := by
    have hfac :
        (stronglyCartesianProjection p).map φ' = eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm := by
      simpa [stronglyCartesianProjection] using
        (@IsHomLift.fac' _ _ _ _ p _ _ _ _ (𝟙 U) φ.1 φ.2)
    exact
      @IsHomLift.of_fac' _ _ _ _ (stronglyCartesianProjection p) _ _ _ _
        (𝟙 U) φ' x.2 y.2 hfac
  -- The resulting strongly-cartesian arrow is the desired morphism in the associated fiber.
  exact Functor.Fiber.homMk (stronglyCartesianProjection p) U φ'

/-- Helper for Lemma 8.5.3: each fiber functor of the associated-groupoid inclusion is faithful,
because it only forgets the wide-subcategory proof on morphisms. -/
theorem associated_groupoid_inclusion_fiberFunctor_faithful
    [p.IsFibered] (U : C) :
    (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).Faithful := by
  let hBased :
      (FibredCategoryMor.toBasedFunctor (associated_groupoid_inclusion (p := p))).Faithful := by
    -- The underlying wide-subcategory inclusion is already faithful on the total category.
    change (wideSubcategoryInclusion (stronglyCartesianProperty p)).Faithful
    infer_instance
  -- Apply the owner theorem that detects faithfulness fiberwise.
  exact
    (FibredCategoryMor.faithful_iff_fiberwise (F := associated_groupoid_inclusion (p := p))).1
      hBased U

/-- Helper for Lemma 8.5.3: forgetting a lifted ambient fiber isomorphism recovers the original
ambient fiber morphism. -/
theorem associated_groupoid_fiber_hom_of_isIso_forget
    [p.IsFibered] {U : C} {x y : p.Fiber U} (φ : x ⟶ y) [IsIso φ] :
    ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map
      (associated_groupoid_fiber_hom_of_isIso (p := p) φ)) = φ := by
  -- `associated_groupoid_fiber_hom_of_isIso` only adds the strongly-cartesian witness.
  apply Functor.Fiber.hom_ext
  rfl

end

end CategoryTheory
