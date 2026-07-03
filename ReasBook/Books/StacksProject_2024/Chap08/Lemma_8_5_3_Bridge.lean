import stacks_project.Chap04.Definition_4_33_9
import stacks_project.Chap04.Lemma_4_35_3
import stacks_project.Chap04.Lemma_4_35_9
import stacks_project.Chap08.Definition_8_5_1
import stacks_project.Chap08.Lemma_8_4_2

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open BasedFunctor Functor IsStronglyCartesian

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- Helper for Lemma 8.5.3: a hom-lift for the associated groupoid projection forgets to the
corresponding hom-lift for the ambient functor. -/
private theorem isHomLift_of_stronglyCartesianProjection
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p}
    {f : p.obj x.obj ⟶ p.obj y.obj} {φ : x ⟶ y}
    [(stronglyCartesianProjection p).IsHomLift f φ] :
    p.IsHomLift f φ.hom := by
  refine IsHomLift.of_fac p f φ.hom rfl rfl ?_
  simpa [stronglyCartesianProjection] using
    (IsHomLift.fac (stronglyCartesianProjection p) f φ)

/-- Helper for Lemma 8.5.3: an ambient hom-lift between strongly cartesian objects lifts back to
the associated groupoid projection. -/
private theorem isHomLift_stronglyCartesianProjection
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p}
    {f : p.obj x.obj ⟶ p.obj y.obj} {φ : x ⟶ y}
    [p.IsHomLift f φ.hom] :
    (stronglyCartesianProjection p).IsHomLift f φ := by
  refine IsHomLift.of_fac' (stronglyCartesianProjection p) f φ rfl rfl ?_
  simpa [stronglyCartesianProjection] using (IsHomLift.fac p f φ.hom).symm

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y : FibredCategoryOver C}

attribute [local instance] FibredCategoryOver.isFibred

/-- Helper for Lemma 8.5.3: a morphism of fibred categories carries a strongly cartesian lift
over `f` to a strongly cartesian lift over the same base arrow in the target. -/
private theorem fibred_morphism_map_stronglyCartesian_of_lift
    (F : X ⟶ Y) {a b : X.S} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f (F.toHom.map φ) := by
  letI : X.p.IsHomLift f φ := hφ.toIsHomLift
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    subst_hom_lift X.p f φ
    simpa using hφ
  letI : Y.p.IsHomLift f (F.toHom.map φ) := by
    infer_instance
  have hY :
      Y.p.IsStronglyCartesian (Y.p.map (F.toHom.map φ)) (F.toHom.map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  subst_hom_lift Y.p f (F.toHom.map φ)
  exact hY

/-- Helper for Lemma 8.5.3: a morphism of fibred categories admits the canonical comparison
isomorphism between pulling back after mapping and mapping after pulling back. -/
private theorem fibred_morphism_pullbackComparison_exists
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ∃ e :
      f ^*[canonicalPullbackChoice Y.p] ((F.toHom).fiberFunctor U).obj x ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x),
      e.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
        (canonicalPullbackChoice Y.p).map f (((F.toHom).fiberFunctor U).obj x) := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let φ :
      (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    F.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    hcY.map f (((F.toHom).fiberFunctor U).obj x)
  have hφ : Y.p.IsStronglyCartesian f φ :=
    fibred_morphism_map_stronglyCartesian_of_lift F f (hcX.map f x) (hcX.isStronglyCartesian f x)
  have hψ : Y.p.IsStronglyCartesian f ψ :=
    hcY.isStronglyCartesian f (((F.toHom).fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ≅
        (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 :=
    domainIsoOfBaseIso Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.hom := by
    change Y.p.IsHomLift (Iso.refl V).hom e.hom
    exact domainUniqueUpToIso_inv_isHomLift Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.inv := by
    change Y.p.IsHomLift (Iso.refl V).inv e.inv
    exact domainUniqueUpToIso_hom_isHomLift Y.p hf φ ψ
  let ehom :
      f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) ⟶
        ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) :=
    Functor.Fiber.homMk Y.p V e.hom
  let einv :
      ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) ⟶
        f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) :=
    Functor.Fiber.homMk Y.p V e.inv
  have hhom_inv : ehom ≫ einv = 𝟙 _ := by
    apply Functor.Fiber.hom_ext
    change e.hom ≫ e.inv = 𝟙 _
    exact e.hom_inv_id
  have hinv_hom : einv ≫ ehom = 𝟙 _ := by
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
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso Y.p hf φ ψ).hom ≫ φ = ψ
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac Y.p f φ hf ψ

/-- Helper for Lemma 8.5.3: a file-local replacement for the pullback-comparison isomorphism
from Lemma `8.2.3`, introduced here so this proof does not depend on that broken module. -/
noncomputable def fibred_morphism_pullbackComparison
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    f ^*[canonicalPullbackChoice Y.p] ((F.toHom).fiberFunctor U).obj x ≅
      ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x) :=
  Classical.choose (fibred_morphism_pullbackComparison_exists F f x)

/-- Helper for Lemma 8.5.3: the chosen local pullback-comparison isomorphism is characterized by
postcomposition with the chosen strongly cartesian pullback arrow. -/
theorem fibred_morphism_pullbackComparison_hom_postcompose
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (fibred_morphism_pullbackComparison F f x).hom.1 ≫
        F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
      (canonicalPullbackChoice Y.p).map f (((F.toHom).fiberFunctor U).obj x) := by
  change (Classical.choose (fibred_morphism_pullbackComparison_exists F f x)).hom.1 ≫
      F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
    (canonicalPullbackChoice Y.p).map f (((F.toHom).fiberFunctor U).obj x)
  exact Classical.choose_spec (fibred_morphism_pullbackComparison_exists F f x)

end

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/- Domain-style sampling for Lemma 8.5.3:
- primary domain: stacks over a site and the associated category fibred in groupoids cut out by
  strongly cartesian morphisms.
- inspected owner-level declarations:
  `stronglyCartesianProjection`,
  `stronglyCartesianProjection_isFibredInGroupoids`,
  `IsStackOnSite`,
  `IsStackInGroupoids`.
- best owner abstraction: the source-facing result should conclude in the Chapter 8 owner
  `IsStackInGroupoids J (stronglyCartesianProjection p)`, assembled from the Chapter 4 owner
  theorem giving the fibred-in-groupoids structure and the owner-level stack-on-site theorem on
  `stronglyCartesianProjection p`.
- primitive data: the original stack hypothesis `[IsStackOnSite J p]`.
- derived API: the owner-level theorem `stronglyCartesianProjection_isStackOnSite`, the
  fibred-in-groupoids instance on `stronglyCartesianProjection p`, and the final source-facing
  stack-in-groupoids theorem below.

Source/core/bridge triage:
- `source-facing`: `associatedGroupoidProjection_isStack`.
- `core/canonical`: `IsStackOnSite J _`, `IsStackInGroupoids J _`.
- `bridge/view`: `stronglyCartesianProjection` and the Chapter 4 owner theorem
  `stronglyCartesianProjection_isFibredInGroupoids`. -/

-- Proof sketch: Stacks Project, Lemma 8.5.3, identifies descent data in
-- `stronglyCartesianProjection p` with descent data in `p`, because the morphisms of the
-- associated category fibred in groupoids are precisely the strongly cartesian morphisms and these
-- contain all isomorphisms. Combined with Lemma `4.35.3`, this gives the canonical Chapter 8
-- conclusion that `stronglyCartesianProjection p` itself is a stack in groupoids over `(C, J)`.
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
  letI : IsFibredInGroupoids (stronglyCartesianProjection p) := inferInstance
  infer_instance

/-- Helper for Lemma 8.5.3: every overlap morphism in ordinary descent data is an isomorphism,
with inverse given by swapping the two cover legs. -/
private theorem ambient_cover_descent_hom_isIso
    [p.IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    IsIso (D.hom q f₁ f₂ hf₁ hf₂) := by
  -- The cocycle identity with indices swapped gives explicit two-sided inverses.
  refine ⟨⟨D.hom q f₂ f₁ hf₂ hf₁, ?_, ?_⟩⟩
  · calc
      D.hom q f₁ f₂ hf₁ hf₂ ≫ D.hom q f₂ f₁ hf₂ hf₁
          = D.hom q f₁ f₁ hf₁ hf₁ := by
              simpa using D.hom_comp q f₁ f₂ f₁ hf₁ hf₂ hf₁
      _ = 𝟙 _ := by
            simpa using D.hom_self q f₁ hf₁
  · calc
      D.hom q f₂ f₁ hf₂ hf₁ ≫ D.hom q f₁ f₂ hf₁ hf₂
          = D.hom q f₂ f₂ hf₂ hf₂ := by
              simpa using D.hom_comp q f₂ f₁ f₂ hf₂ hf₁ hf₂
      _ = 𝟙 _ := by
            simpa using D.hom_self q f₂ hf₂

/-- Helper for Lemma 8.5.3: descent-data morphisms for the associated groupoid projection are
isomorphisms because each component already lies in a groupoid fiber. -/
theorem associated_groupoid_descent_hom_isIso
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D E :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (η : D ⟶ E) :
    IsIso η := by
  -- Build the inverse componentwise in the groupoid fibers, then use extensionality.
  refine ⟨⟨
    { hom := fun I ↦ by
        letI : IsIso (η.hom I) :=
          associated_groupoid_fiber_hom_isIso (p := p) (φ := η.hom I)
        exact inv (η.hom I)
      comm := by
        intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
        let F₁ :=
          ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₁.op.toLoc).toFunctor
        let F₂ :=
          ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₂.op.toLoc).toFunctor
        letI : IsIso (η.hom I₁) :=
          associated_groupoid_fiber_hom_isIso (p := p) (φ := η.hom I₁)
        letI : IsIso (η.hom I₂) :=
          associated_groupoid_fiber_hom_isIso (p := p) (φ := η.hom I₂)
        letI : IsIso (F₁.map (η.hom I₁)) := by infer_instance
        letI : IsIso (F₂.map (η.hom I₂)) := by infer_instance
        apply (cancel_mono (F₂.map (η.hom I₂))).1
        have hpre :=
          congrArg (fun k ↦ F₁.map (inv (η.hom I₁)) ≫ k)
            (η.comm q f₁ f₂ hf₁ hf₂)
        simpa [F₁, F₂, Category.assoc] using hpre.symm },
    ?_, ?_⟩⟩
  · ext I
    letI : IsIso (η.hom I) :=
      associated_groupoid_fiber_hom_isIso (p := p) (φ := η.hom I)
    simp
  · ext I
    letI : IsIso (η.hom I) :=
      associated_groupoid_fiber_hom_isIso (p := p) (φ := η.hom I)
    simp

/-- Helper for Lemma 8.5.3: an object of an ambient fiber can be viewed in the corresponding
fiber of the associated groupoid, since the wide subcategory keeps all objects. -/
abbrev associated_groupoid_fiber_obj
    [p.IsFibered] {U : C} (x : p.Fiber U) :
    (stronglyCartesianProjection p).Fiber U :=
  Functor.Fiber.mk (a := ⟨x.1⟩) <| by
    simpa [stronglyCartesianProjection] using x.2

/-- Helper for Lemma 8.5.3: forgetting the strongly-cartesian proof on a lift preserves the same
strongly-cartesian base arrow in the ambient fibred category. -/
theorem associated_groupoid_inclusion_map_stronglyCartesian_of_lift
    [p.IsFibered] {a b : stronglyCartesianSubcategory p} {U V : C}
    (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : (stronglyCartesianProjection p).IsStronglyCartesian f φ) :
    p.IsStronglyCartesian f ((associated_groupoid_inclusion (p := p)).toHom.map φ) := by
  exact fibred_morphism_map_stronglyCartesian_of_lift
    (F := associated_groupoid_inclusion (p := p)) f φ hφ

end

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

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
    change (wideSubcategoryInclusion (stronglyCartesianProperty p)).Faithful
    infer_instance
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
