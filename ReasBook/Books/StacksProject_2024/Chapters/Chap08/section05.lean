import Mathlib
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_5_1 (from Chap08) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/- 
Domain-style sampling for Definition 8.5.1:
- primary domain: stacks over sites and categories fibred in groupoids.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Pseudofunctor.IsStack`,
  `IsStackOnSite`.
- best owner abstraction: the source-facing notion should remain the reusable property
  `IsStackInGroupoids J p`, but its parent owner should be the Chapter 8 stack condition
  `IsStackOnSite J p`; the extra source-facing primitive datum is then the Chapter 4 owner
  `IsFibredInGroupoids p`.
- primitive data: `IsStackOnSite J p` together with `IsFibredInGroupoids p`.
- derived API: the inherited `IsStackOnSite J p` owner, its `p.IsFibered` instance, and the
  Chapter 4 groupoid-fibration owner recovered from the extra field.

Source/core/bridge triage:
- `source-facing`: `IsStackInGroupoids J p`.
- `core/canonical`: `IsFibredInGroupoids p`, `IsStackOnSite J p`,
  `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`.
- `bridge/view`: no extra public bridge is needed, since `IsStackOnSite J p` is the parent
  owner of `IsStackInGroupoids J p`. -/

/-- Definition 8.5.1: a category over the site `(C, J)` is a stack in groupoids when its
projection functor is fibred in groupoids and, for every `U : C` and objects `x y` in the fiber
over `U`, the presheaf of isomorphisms `Isom(x, y)` on `C / U` is a sheaf and every descent datum
for a covering of `U` is effective. Equivalently, it is a category fibred in groupoids that is a
stack over `(C, J)` in the canonical site-theoretic sense of Definition `8.4.1`. -/
class IsStackInGroupoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsStackOnSite J p where
  toIsFibredInGroupoids : IsFibredInGroupoids p

attribute [instance] IsStackInGroupoids.toIsFibredInGroupoids

/-- A fibred-in-groupoids functor that is already a stack over `(C, J)` is a stack in groupoids. -/
instance (J : GrothendieckTopology C) [IsFibredInGroupoids p] [IsStackOnSite J p] :
    IsStackInGroupoids J p where
  toIsStackOnSite := inferInstance
  toIsFibredInGroupoids := inferInstance

end

end CategoryTheory

/-! ### Definition_8_5_1_Core (from Chap08) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Definition 8.5.1 core: a category over the site `(C, J)` is a stack in groupoids when it is
already a stack on the site and is fibred in groupoids. This small owner file isolates the
statement needed by Lemma 8.5.3 from the heavier wrapper module. -/
class IsStackInGroupoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsStackOnSite J p where
  toIsFibredInGroupoids : IsFibredInGroupoids p

attribute [instance] IsStackInGroupoids.toIsFibredInGroupoids

/-- A fibred-in-groupoids functor that is already a stack over `(C, J)` is a stack in groupoids. -/
instance (J : GrothendieckTopology C) [IsFibredInGroupoids p] [IsStackOnSite J p] :
    IsStackInGroupoids J p where
  toIsStackOnSite := inferInstance
  toIsFibredInGroupoids := inferInstance

end

end CategoryTheory

/-! ### Lemma_8_5_2 (from Chap08) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-
Domain-style sampling for Lemma 8.5.2:
- primary domain: stacks in groupoids over a site, viewed through the canonical parent owners
  `IsStackOnSite` and `IsFibredInGroupoids`.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `IsStackOnSite`,
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- best owner abstraction: `IsStackInGroupoids J p` remains the source-facing owner; this file is a
  bridge/view lemma unpacking that owner into the site-theoretic stack condition and the
  fiberwise groupoid condition.
- primitive data: the parent owner data `IsStackOnSite J p` and `IsFibredInGroupoids p`.
- derived API: the fiberwise groupoid condition, obtained canonically from the Chapter 4 owner
  theorem rather than by a parallel local reconstruction.

Source/core/bridge triage:
- `source-facing`: `IsStackInGroupoids J p`.
- `core/canonical`: `IsStackOnSite J p`, `IsFibredInGroupoids p`, and
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- `bridge/view`: `isStackInGroupoids_iff_isStackOnSite_and_fiber_groupoid`. -/

/-- Helper for Lemma 8.5.2: a stack in groupoids has groupoid fibers. -/
lemma fiber_groupoid_of_isStackInGroupoids
    (h : IsStackInGroupoids J p) : ∀ U : C, IsGroupoid (p.Fiber U) := by
  -- Read the fiberwise groupoid condition from the Chapter 4 characterization of
  -- `IsFibredInGroupoids`, applied to the inherited owner field.
  exact
    (isFibredInGroupoids_iff_isFibered_and_fiber_groupoid p).mp h.toIsFibredInGroupoids |>.2

/-- Helper for Lemma 8.5.2: a site-theoretic stack with groupoid fibers is fibred in groupoids. -/
lemma isFibredInGroupoids_of_isStackOnSite_and_fiber_groupoid
    (hstack : IsStackOnSite J p) (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    IsFibredInGroupoids p := by
  -- The stack-on-site owner already carries the needed `p.IsFibered` field.
  exact isFibredInGroupoids_of_isFibered_and_fiber_groupoid p hstack.toIsFibered hfiber

/-- Helper for Lemma 8.5.2: the stack condition together with groupoid fibers repackages into a
stack in groupoids. -/
lemma isStackInGroupoids_of_isStackOnSite_and_fiber_groupoid
    (hstack : IsStackOnSite J p) (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    IsStackInGroupoids J p := by
  -- Package the two canonical owner fields directly into the Chapter 8 structure.
  exact
    { toIsStackOnSite := hstack
      toIsFibredInGroupoids :=
        isFibredInGroupoids_of_isStackOnSite_and_fiber_groupoid
          (J := J) (p := p) hstack hfiber }

/-
Proof sketch: combine the canonical unpacking of `IsStackInGroupoids` with Lemma `4.35.2`,
which identifies fibred-in-groupoids functors with fibered functors whose fibers are groupoids.
-/
/-- Lemma 8.5.2: a category over a site is a stack in groupoids exactly when it is a stack and
all of its fiber categories are groupoids. -/
theorem isStackInGroupoids_iff_isStackOnSite_and_fiber_groupoid :
    IsStackInGroupoids J p ↔ IsStackOnSite J p ∧ ∀ U : C, IsGroupoid (p.Fiber U) := by
  constructor
  · intro h
    -- Unpack the source-facing owner into its stack component and its fiberwise groupoid data.
    exact
      ⟨h.toIsStackOnSite,
        fiber_groupoid_of_isStackInGroupoids (J := J) (p := p) h⟩
  · rintro ⟨hstack, hfiber⟩
    -- Repackage the two canonical components into the stack-in-groupoids owner.
    exact
      isStackInGroupoids_of_isStackOnSite_and_fiber_groupoid
        (J := J) (p := p) hstack hfiber

end

end CategoryTheory

/-! ### Lemma_8_5_3 (from Chap08) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: the imported PreimageWitness theorem gives the required coverwise
descent equivalence for the associated groupoid projection on each fixed cover. -/
private theorem strongly_cartesian_projection_coverwise_descent_equivalence
    [IsStackOnSite J p] {U : C} (cover : J.Cover U) :
    ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
      (fun I : cover.Arrow ↦ I.f)).IsEquivalence := by
  -- The fixed-cover source step is delegated to the canonical helper owner imported above.
  exact associated_groupoid_cover_toDescentData_isEquivalence (J := J) (p := p) cover

/-- Helper for Lemma 8.5.3: once the fixed-cover associated descent functors are equivalences for
every cover, the standard coverwise criterion upgrades the associated projection to a stack on the
site. -/
theorem stronglyCartesianProjection_isStackOnSite
    [IsStackOnSite J p] :
    IsStackOnSite J (stronglyCartesianProjection p) := by
  letI : IsFibredInGroupoids (stronglyCartesianProjection p) :=
    stronglyCartesianProjection_isFibredInGroupoids p
  -- Route correction: the fixed-cover comparison package now lives in `PreimageWitness`, so this
  -- file only applies the standard coverwise stack criterion to that imported theorem.
  refine
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      J (stronglyCartesianProjection p)).2 ?_
  intro U cover
  -- Reuse the dedicated fixed-cover helper so the wrapper theorem only runs the coverwise
  -- criterion from the source proof.
  exact strongly_cartesian_projection_coverwise_descent_equivalence
    (J := J) (p := p) cover

/-- Lemma 8.5.3: if `p : S ⥤ C` is a stack over the site `(C, J)`, then the associated category
fibred in groupoids `stronglyCartesianProjection p` is a stack in groupoids over `(C, J)`. -/
theorem associatedGroupoidProjection_isStack
    [IsStackOnSite J p] :
    IsStackInGroupoids J (stronglyCartesianProjection p) := by
  -- The final step only packages the site-level stack statement with the Chapter 4
  -- fibred-in-groupoids structure on the associated strongly-cartesian projection.
  exact
    { toIsStackOnSite :=
        stronglyCartesianProjection_isStackOnSite (J := J) (p := p)
      toIsFibredInGroupoids :=
        stronglyCartesianProjection_isFibredInGroupoids p }

end

end CategoryTheory

/-! ### Lemma_8_5_3_Bridge (from Chap08) -/
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

/-! ### Lemma_8_5_3_PullbackNaturality (from Chap08) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open BasedFunctor Functor IsStronglyCartesian

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: the chosen pullback functor carries vertical morphisms to vertical
morphisms in the fiber over the domain. -/
theorem canonical_pullbackFunctor_map_fac
    {T : Type*} [Category T] (q : T ⥤ C) [q.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : q.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice q).map f y =
      (canonicalPullbackChoice q).map f x ≫ φ.1 := by
  -- Compare the chosen pullback of `y` with the factorization induced by `φ`.
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : q.IsStronglyCartesian f ((canonicalPullbackChoice q).map f x) :=
    (canonicalPullbackChoice q).isStronglyCartesian f x
  letI : q.IsHomLift f ((canonicalPullbackChoice q).map f x) := hpull.toIsHomLift
  letI : q.IsHomLift f ((canonicalPullbackChoice q).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' q f ((canonicalPullbackChoice q).map f x) U φ.1
  letI : q.IsStronglyCartesian f ((canonicalPullbackChoice q).map f y) :=
    (canonicalPullbackChoice q).isStronglyCartesian f y
  change
      IsStronglyCartesian.map q f ((canonicalPullbackChoice q).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice q).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice q).map f y =
        (canonicalPullbackChoice q).map f x ≫ φ.1
  exact
    IsStronglyCartesian.fac q f ((canonicalPullbackChoice q).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice q).map f x ≫ φ.1)

/-- Helper for Lemma 8.5.3: composing two arrows in `C` and then passing to the locally discrete
opposite is the same as composing their `toLoc` images in the owner order used by `pullHom`. -/
theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to the locally discrete opposite.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.5.3: the hom component of the flexible pullback-composition comparison for
the canonical fiber pseudofunctor satisfies the same factorization identity as the chosen
pullback-composition comparison. -/
theorem canonicalFiberPseudofunctor_mapComp'_hom_app_fac
    {T : Type*} [Category T] (q : T ⥤ C) [q.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : q.Fiber D) :
    (((canonicalFiberPseudofunctor q).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice q).map g
          (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice q).map f x =
      (canonicalPullbackChoice q).map gf x := by
  -- Reduce the flexible comparison to the strict composite-leg comparison from the chosen
  -- pullback structure.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice q).pullbackCompComponentIso_fac f g x

/-- Helper for Lemma 8.5.3: the inverse component of the flexible pullback-composition comparison
for the canonical fiber pseudofunctor factors the composite pullback arrow through the iterated
chosen pullback arrows. -/
theorem canonicalFiberPseudofunctor_mapComp'_inv_app_fac
    {T : Type*} [Category T] (q : T ⥤ C) [q.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : q.Fiber D) :
    (((canonicalFiberPseudofunctor q).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice q).map gf x =
      (canonicalPullbackChoice q).map g
          (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice q).map f x := by
  -- Read the same comparison component in the inverse direction.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice q).pullbackCompComponentIso_inv_fac f g x

/-- Helper for Lemma 8.5.3: a functor maps a visible threefold composite to the corresponding
threefold composite of mapped arrows. -/
theorem functor_map_threefold_comp
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {W X Y Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  -- Split the threefold composite into the two binary functoriality steps.
  rw [Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 8.5.3: mapping the source pullback factorization identity through the
associated-groupoid inclusion preserves the same factorization in the ambient total category. -/
private theorem associated_groupoid_map_canonical_pullbackFunctor_map_fac
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    (associated_groupoid_inclusion (p := p)).toHom.map
        ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) ≫
      (associated_groupoid_inclusion (p := p)).toHom.map φ.1 =
    (associated_groupoid_inclusion (p := p)).toHom.map
          ((((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map
              φ).1) ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y) := by
  let ι := associated_groupoid_inclusion (p := p)
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hfac :
      ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) ≫ φ.1 =
        ((((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map
            φ).1) ≫
          (canonicalPullbackChoice (stronglyCartesianProjection p)).map f y := by
    exact
      (canonical_pullbackFunctor_map_fac
        (q := stronglyCartesianProjection p) (f := f) (x := x) (y := y) (φ := φ)).symm
  exact congrArg (fun k ↦ ι.toHom.map k) hfac

/-- Helper for Lemma 8.5.3: the hom-side pullback comparison for the inclusion is identified by
postcomposing with the chosen ambient strongly-cartesian pullback arrow. -/
theorem associated_groupoid_pullbackComparison_hom_postcompose
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    (x : (stronglyCartesianProjection p).Fiber U) :
    (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom.1 ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) =
      (canonicalPullbackChoice p).map f
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x) := by
  exact
    fibred_morphism_pullbackComparison_hom_postcompose
      (F := associated_groupoid_inclusion (p := p)) (f := f) (x := x)

/-- Helper for Lemma 8.5.3: after postcomposing both candidate inclusion-comparison composites
with the common ambient pullback arrow, the owner-level composites agree. -/
theorem associated_groupoid_pullbackComparison_hom_postcompose_eq
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ))).1 ≫
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).hom.1 ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y) =
      (((fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1) ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)) := by
  let ι := associated_groupoid_inclusion (p := p)
  let lhs :=
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫
      (fibred_morphism_pullbackComparison ι f y).hom.1 ≫
      ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫
      (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj x) ≫
      ((FibredCategoryMor.fiberFunctor ι U).map φ).1
  let mid₃ :=
    ((fibred_morphism_pullbackComparison ι f x).hom.1 ≫
        ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)) ≫
      ((FibredCategoryMor.fiberFunctor ι U).map φ).1
  let mid₄ :=
    (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
      ((FibredCategoryMor.fiberFunctor ι V).map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 ≫
      ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)
  let rhs :=
    ((fibred_morphism_pullbackComparison ι f x).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor ι V).map
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1) ≫
      ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)
  have h₁ : lhs = mid₁ := by
    exact
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫ k)
        (associated_groupoid_pullbackComparison_hom_postcompose (p := p) f y)
  have h₂ : mid₁ = mid₂ := by
    change
      ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫
          (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj y) =
        (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj x) ≫
          ((FibredCategoryMor.fiberFunctor ι U).map φ).1
    exact canonical_pullbackFunctor_map_fac (q := p) f ((FibredCategoryMor.fiberFunctor ι U).map φ)
  have h₃ : mid₂ = mid₃ := by
    exact
      (congrArg
        (fun k ↦ k ≫ ((FibredCategoryMor.fiberFunctor ι U).map φ).1)
        (associated_groupoid_pullbackComparison_hom_postcompose (p := p) f x)).symm
  have h₄ : mid₃ = mid₄ := by
    calc
      (((fibred_morphism_pullbackComparison ι f x).hom.1 ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)) ≫
        ((FibredCategoryMor.fiberFunctor ι U).map φ).1) =
          (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
            (ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) ≫
              ((FibredCategoryMor.fiberFunctor ι U).map φ).1) := by
            rw [Category.assoc]
      _ =
          (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
            (ι.toHom.map
                ((((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 ≫
              ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)) := by
            exact
              congrArg
                (fun k ↦ (fibred_morphism_pullbackComparison ι f x).hom.1 ≫ k)
                (associated_groupoid_map_canonical_pullbackFunctor_map_fac
                  (p := p) (f := f) (φ := φ))
      _ =
          (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
            ((FibredCategoryMor.fiberFunctor ι V).map
              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 ≫
            ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y) := by
            rfl
  have h₅ : mid₄ = rhs := by
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.5.3: the inclusion pullback-comparison isomorphism is fiberwise natural
with respect to vertical morphisms in the associated groupoid projection. -/
private theorem associated_groupoid_pullbackComparison_hom_naturality_over_vertical
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ))).1 ≫
      (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).hom.1 =
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 := by
  let ι := associated_groupoid_inclusion (p := p)
  let ex := fibred_morphism_pullbackComparison ι f x
  let ey := fibred_morphism_pullbackComparison ι f y
  let η :
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor ι U).obj x) ⟶
        ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor ι U).obj y) :=
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor ι U).map φ)
  let θ :
      (FibredCategoryMor.fiberFunctor ι V).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj x) ⟶
        (FibredCategoryMor.fiberFunctor ι V).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj y) :=
    (FibredCategoryMor.fiberFunctor ι V).map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)
  let hcA := canonicalPullbackChoice (stronglyCartesianProjection p)
  let φF :
      ((FibredCategoryMor.fiberFunctor ι V).obj (f ^*[hcA] y)).1 ⟶
        ((FibredCategoryMor.fiberFunctor ι U).obj y).1 :=
    ι.toHom.map (hcA.map f y)
  have hφF : p.IsStronglyCartesian f φF := by
    change p.IsStronglyCartesian f (ι.toHom.map (hcA.map f y))
    exact
      associated_groupoid_inclusion_map_stronglyCartesian_of_lift
        (p := p) f (hcA.map f y) (hcA.isStronglyCartesian f y)
  letI : p.IsStronglyCartesian f φF := hφF
  letI : p.IsHomLift (𝟙 V) η.1 := by
    exact η.2
  letI : p.IsHomLift (𝟙 V) θ.1 := by
    exact θ.2
  letI : p.IsHomLift (𝟙 V) ex.hom.1 := ex.hom.2
  letI : p.IsHomLift (𝟙 V) ey.hom.1 := ey.hom.2
  letI : p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _
      (𝟙 V) η.1 η.2 V ey.hom.1 ey.hom.2
  letI : p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _
      (𝟙 V) ex.hom.1 ex.hom.2 V θ.1 θ.2
  have hcomp :
      η.1 ≫ ey.hom.1 ≫ φF = (ex.hom.1 ≫ θ.1) ≫ φF := by
    simpa only [η, θ, φF, Category.assoc] using
      associated_groupoid_pullbackComparison_hom_postcompose_eq
        (p := p) (f := f) (φ := φ)
  have hηey : p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by infer_instance
  have hexθ : p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by infer_instance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f φF inferInstance _ _ (𝟙 V) (η.1 ≫ ey.hom.1) (ex.hom.1 ≫ θ.1) hηey hexθ <| by
        rw [Category.assoc]
        exact hcomp

/-- Helper for Lemma 8.5.3: the inclusion pullback-comparison isomorphism is fiberwise natural
with respect to vertical morphisms in the associated groupoid projection. -/
theorem associated_groupoid_pullbackComparison_naturality_over_vertical
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ)) ≫
      (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).hom =
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom ≫
          (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ) := by
  -- Project the owner-level equality back into the fiber.
  apply Functor.Fiber.hom_ext
  exact associated_groupoid_pullbackComparison_hom_naturality_over_vertical
    (p := p) f φ

/-- Helper for Lemma 8.5.3: the inverse inclusion pullback-comparison isomorphism rewrites the
right comparison inverse into the exact form needed by the fixed-cover transport shell. -/
theorem associated_groupoid_pullbackComparison_inv_naturality_over_vertical
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ) ≫
      (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).inv =
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).inv ≫
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ)) := by
  let ι := associated_groupoid_inclusion (p := p)
  let ex := fibred_morphism_pullbackComparison ι f x
  let ey := fibred_morphism_pullbackComparison ι f y
  let η :=
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor ι U).map φ)
  let θ :=
    (FibredCategoryMor.fiberFunctor ι V).map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)
  have hhom :
      η ≫ ey.hom = ex.hom ≫ θ := by
    simpa only [ex, ey, η, θ] using
      associated_groupoid_pullbackComparison_naturality_over_vertical
        (p := p) (f := f) (φ := φ)
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Precompose by `ex.inv` so the left comparison isomorphism cancels.
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor ι U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (FibredCategoryMor.fiberFunctor ι V).map
              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.5.3: the inverse inclusion pullback-comparison identifies the chosen
ambient pullback arrow with the image of the chosen pullback arrow in the associated groupoid. -/
theorem associated_groupoid_pullbackComparison_inv_postcompose_owner
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    (x : (stronglyCartesianProjection p).Fiber U) :
    (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).inv.1 ≫
        (canonicalPullbackChoice p).map f
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x) =
      (associated_groupoid_inclusion (p := p)).toHom.map
        ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
  let ι := associated_groupoid_inclusion (p := p)
  let e := fibred_morphism_pullbackComparison ι f x
  have h :=
    congrArg
      (fun k ↦ e.inv.1 ≫ k)
      (associated_groupoid_pullbackComparison_hom_postcompose (p := p) f x)
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 _ :=
    congrArg (fun k ↦ k.1) e.inv_hom_id
  have h' :
      e.inv.1 ≫
          (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj x) =
        e.inv.1 ≫ e.hom.1 ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
    exact h.symm
  have hassoc :
      e.inv.1 ≫ e.hom.1 ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) =
        (e.inv.1 ≫ e.hom.1) ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
    rw [← Category.assoc]
  have hfinal :
      (e.inv.1 ≫ e.hom.1) ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) =
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
      rw [hcancel, Category.id_comp]
      rfl
  exact h'.trans <| hassoc.trans hfinal

end

end CategoryTheory

/-! ### Lemma_8_5_4 (from Chap08) -/
universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open BasedFunctor

section

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]
variable (J : GrothendieckTopology C)

variable (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C)

/- Domain-style sampling for Lemma 8.5.4:
- primary domain: stacks in groupoids over a site, transported along equivalences in `Cat/C`.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `isStackOnSite_iff_of_equivalence_over_base`,
  `IsFibredInGroupoids`,
  `BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase`.
- best owner abstraction: the source-facing owner remains `IsStackInGroupoids J p`; the
  equivalence-over-base datum is only a bridge transporting the canonical owners
  `IsStackOnSite` and `IsFibredInGroupoids`.
- primitive data: the two projection functors and the over-base equivalence data.
- derived API: transport of `IsStackOnSite` and of the fiberwise groupoid condition, then
  reassembly through the existing owner instance
  `[IsFibredInGroupoids p] [IsStackOnSite J p] → IsStackInGroupoids J p`.

Source/core/bridge triage:
- `source-facing`: `isStackInGroupoids_iff_of_equivalence_over_base`.
- `core/canonical`: `IsStackInGroupoids`, `IsStackOnSite`, `IsFibredInGroupoids`, and
  `BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase`.
- `bridge/view`: transport of the owner predicates along an equivalence over the base. -/

-- Proof sketch: transport the owner `IsStackOnSite` across the equivalence over the base by
-- Lemma `8.4.4`. Then transport the groupoid structure on each fiber via the owner theorem
-- `BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase`, rebuild
-- `IsFibredInGroupoids` from the fiberwise groupoid condition, and conclude by the canonical
-- instance `[IsFibredInGroupoids p] [IsStackOnSite J p] → IsStackInGroupoids J p`.
/-- Lemma 8.5.4: if `S₁` and `S₂` are equivalent as categories over the site `(C, J)`, then
`S₁` is a stack in groupoids over `(C, J)` if and only if `S₂` is. -/
theorem isStackInGroupoids_iff_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    IsStackInGroupoids J p₁ ↔ IsStackInGroupoids J p₂ := by
  constructor
  · intro h
    letI : IsStackInGroupoids J p₁ := h
    letI : IsStackOnSite J p₂ :=
      (isStackOnSite_iff_of_equivalence_over_base J p₁ p₂ F hF).1 inferInstance
    letI : IsFibredInGroupoids p₂ :=
      isFibredInGroupoids_of_isFibered_and_fiber_groupoid p₂ inferInstance
        fun U ↦ by
          letI : IsGroupoid ((BasedCategory.ofFunctor p₁).p.Fiber U) := by
            simpa using (inferInstance : IsGroupoid (p₁.Fiber U))
          exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase F hF U
    exact inferInstance
  · intro h
    let e : EquivalenceOverBase F := Classical.choice hF.nonempty
    letI : IsStackInGroupoids J p₂ := h
    letI : IsStackOnSite J p₁ :=
      (isStackOnSite_iff_of_equivalence_over_base J p₁ p₂ F hF).2 inferInstance
    letI : IsFibredInGroupoids p₁ :=
      isFibredInGroupoids_of_isFibered_and_fiber_groupoid p₁ inferInstance
        fun U ↦ by
          letI : IsGroupoid ((BasedCategory.ofFunctor p₂).p.Fiber U) := by
            simpa using (inferInstance : IsGroupoid (p₂.Fiber U))
          exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase
            e.inverse e.inverse_isEquivalenceOverBase U
    exact inferInstance

end

end CategoryTheory

/-! ### Definition_8_5_5 (from Chap08) -/
universe u v

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- Definition 8.5.5 at the owner level: stacks in groupoids over `(C, J)` form the full
sub-`2`-category of `FibredInGroupoidsOver C` cut out by the stack-on-site condition on the
projection functor. Equivalently, they are stacks over `(C, J)` whose projection is already
fibred in groupoids. -/
abbrev stackInGroupoidsOverSubTwoCategory (J : GrothendieckTopology C) :
    SubTwoCategory (FibredInGroupoidsOver C) where
  obj := fun X ↦ IsStackOnSite J X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

/-- Definition 8.5.5: the objects of the `2`-category of stacks in groupoids over `(C, J)` are
the objects of the canonical owner sub-`2`-category `stackInGroupoidsOverSubTwoCategory J`. -/
abbrev StackInGroupoidsOver (J : GrothendieckTopology C) :=
  (stackInGroupoidsOverSubTwoCategory J).Obj

instance (J : GrothendieckTopology C) : Bicategory (StackInGroupoidsOver J) :=
  SubTwoCategory.bicategoryObj (stackInGroupoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Bicategory.Strict (StackInGroupoidsOver J) :=
  SubTwoCategory.strictObj (stackInGroupoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Category (StackInGroupoidsOver J) :=
  StrictBicategory.category (StackInGroupoidsOver J)

instance stackInGroupoidsOverHom₂IsMultiplicative
    (J : GrothendieckTopology C) (X Y : StackInGroupoidsOver J) :
    ((stackInGroupoidsOverSubTwoCategory J).hom₂ X Y).IsMultiplicative :=
  ((stackInGroupoidsOverSubTwoCategory J).hom X Y).hom_isMultiplicative

instance stackInGroupoidsOverHomInclusionFull
    (J : GrothendieckTopology C) (X Y : StackInGroupoidsOver J) :
    (((stackInGroupoidsOverSubTwoCategory J).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

instance stackInGroupoidsOverHomWideInclusionFull
    (J : GrothendieckTopology C) (X Y : StackInGroupoidsOver J) :
    (wideSubcategoryInclusion ((stackInGroupoidsOverSubTwoCategory J).hom₂ X Y)).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨η, trivial⟩, rfl⟩

namespace StackInGroupoidsOver

variable {J : GrothendieckTopology C}
variable {D : Type (max u v)} [Category.{v} D]

abbrev ofProjection (J : GrothendieckTopology C) (p : D ⥤ C) [IsStackInGroupoids J p] :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.ofFunctor p, by
    simpa [FibredInGroupoidsOver.p, FibredInGroupoidsOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

abbrev toFibredInGroupoidsOver (X : StackInGroupoidsOver J) : FibredInGroupoidsOver C :=
  X.obj

abbrev toFibredCategoryOver (X : StackInGroupoidsOver J) : FibredCategoryOver C :=
  X.toFibredInGroupoidsOver.toFibredCategoryOver

abbrev toStackOver (X : StackInGroupoidsOver J) : StackOver J :=
  ⟨X.toFibredCategoryOver, X.property⟩

abbrev toCategoryOver (X : StackInGroupoidsOver J) : CategoryOver C :=
  X.toFibredInGroupoidsOver.toCategoryOver

abbrev S (X : StackInGroupoidsOver J) :=
  X.toFibredInGroupoidsOver.S

abbrev p (X : StackInGroupoidsOver J) :=
  X.toFibredInGroupoidsOver.p

abbrev toBasedCategory (X : StackInGroupoidsOver J) : BasedCategory C :=
  X.toFibredInGroupoidsOver.toBasedCategory

instance : CoeOut (StackInGroupoidsOver J) (StackOver J) where
  coe X := X.toStackOver

instance : CoeOut (StackInGroupoidsOver J) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

instance : CoeOut (StackInGroupoidsOver J) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

instance : CoeOut (StackInGroupoidsOver J) (CategoryOver C) where
  coe X := X.toCategoryOver

instance : CoeOut (StackInGroupoidsOver J) (BasedCategory C) where
  coe X := X.toBasedCategory

instance (X : StackInGroupoidsOver J) : IsStackInGroupoids J X.p where
  toIsStackOnSite := X.property
  toIsFibredInGroupoids := inferInstance

instance (X : StackInGroupoidsOver J) : X.p.IsFibered :=
  inferInstance

instance (X : StackInGroupoidsOver J) : IsStackOnSite J X.p :=
  X.property

instance (X : StackInGroupoidsOver J) : HasFibers X.p :=
  HasFibers.canonical X.p

instance (X : StackInGroupoidsOver J) : IsFibredInGroupoids X.p :=
  inferInstance

/-- A stack in groupoids over `(C, J)` has projection functor a stack in groupoids. -/
-- Proof sketch: this is exactly the defining property carried by an object of the full
-- sub-`2`-category `stackInGroupoidsOverSubTwoCategory J`, together with the inherited
-- fibred-in-groupoids structure on its projection.
theorem isStackInGroupoids_p (X : StackInGroupoidsOver J) : IsStackInGroupoids J X.p := by
  -- The projection already carries both components of `IsStackInGroupoids`.
  exact inferInstance

end StackInGroupoidsOver

namespace FibredInGroupoidsMor

variable {J : GrothendieckTopology C}
variable {X : FibredInGroupoidsOver C}
variable {Y : StackInGroupoidsOver J}

abbrev toStackFibredCategoryMor
    (F : FibredInGroupoidsMor X Y) :
    FibredCategoryMor (X : FibredCategoryOver C) (Y : StackOver J) :=
  show FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C) from F

end FibredInGroupoidsMor

namespace StackInGroupoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/-- Regard an ambient morphism of the underlying categories fibred in groupoids over `C` as the
corresponding owner hom in the full sub-`2`-category `StackInGroupoidsOver J`. -/
abbrev ofAmbientHom
    (F : X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) :
    X ⟶ Y :=
  ⟨⟨F, trivial⟩⟩

/-- Regard an ambient morphism of the underlying fibred categories over `C` as the corresponding
owner hom in the full sub-`2`-category `StackInGroupoidsOver J`. -/
abbrev ofFibredCategoryHom
    (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) :
    X ⟶ Y :=
  ofAmbientHom <|
    FibredInGroupoidsMor.ofAmbientHom F

end StackInGroupoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

namespace StackInGroupoidsOver.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/- The ambient `1`-morphism of categories fibred in groupoids over `C` underlying an owner hom
of stacks in groupoids over `(C, J)`. -/
abbrev toFibredInGroupoidsMor (F : X ⟶ Y) :
    FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver :=
  F.toHom

instance : CoeOut (X ⟶ Y)
    (FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver) where
  coe F := toFibredInGroupoidsMor F

abbrev toFibredCategoryMor (F : X ⟶ Y) :
    FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C) :=
  toFibredInGroupoidsMor F

abbrev toBasedFunctor (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredInGroupoidsMor.toBasedFunctor (toFibredInGroupoidsMor F)

abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  (toBasedFunctor F).fiberFunctor U

abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  (toBasedFunctor F).toFunctor

abbrev comm (F : X ⟶ Y) : G F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

instance : CoeOut (X ⟶ Y)
    (FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C)) where
  coe F := toFibredCategoryMor F

instance : CoeOut (X ⟶ Y)
    (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  (toBasedFunctor F).IsEquivalenceOverBase

abbrev LocallyEssentiallySurjectiveOnObjects
    (F : X ⟶ Y) : Prop :=
  FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J (toFibredCategoryMor F)

/-- Regard an ambient based functor over `C` as the corresponding owner hom in the full
sub-`2`-category `StackInGroupoidsOver J`. -/
abbrev ofBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  StackInGroupoidsOver.ofAmbientHom (FibredInGroupoidsMor.ofBasedFunctor G)

/-- Convert an isomorphism between the ambient fibred-in-groupoids morphisms into an isomorphism
in the owner hom-category of stacks in groupoids over `(C, J)`. -/
noncomputable def ofAmbientHomIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  SubTwoCategory.Hom.isoMk e
    (show ((stackInGroupoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.hom) from trivial)
    (show ((stackInGroupoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.inv) from trivial)

/-- Compatibility alias for `ofAmbientHomIso`. -/
noncomputable def ofAmbientIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  ofAmbientHomIso e

end StackInGroupoidsOver.Hom

namespace WideSubcategory

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/-- Field-notation bridge to the ambient fibred-in-groupoids morphism underlying an owner hom of
stacks in groupoids over `(C, J)`. -/
abbrev toFibredInGroupoidsMor (F : X ⟶ Y) :
    FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver :=
  StackInGroupoidsOver.Hom.toFibredInGroupoidsMor F

/-- Field-notation bridge to the ambient fibred-category morphism underlying an owner hom of
stacks in groupoids over `(C, J)`. -/
abbrev toFibredCategoryMor (F : X ⟶ Y) :
    FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C) :=
  StackInGroupoidsOver.Hom.toFibredCategoryMor F

/-- Field-notation bridge to the underlying based functor of an owner hom of stacks in groupoids
over `(C, J)`. -/
abbrev toBasedFunctor (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  StackInGroupoidsOver.Hom.toBasedFunctor F

/-- Field-notation bridge to the induced functor on a fiber of an owner hom of stacks in
groupoids over `(C, J)`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  StackInGroupoidsOver.Hom.fiberFunctor F U

/-- Field-notation bridge to the underlying functor between total categories of an owner hom of
stacks in groupoids over `(C, J)`. -/
abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  StackInGroupoidsOver.Hom.G F

/-- Field-notation bridge to the compatibility of the underlying functor with the base
projections. -/
abbrev comm (F : X ⟶ Y) : F.G ⋙ Y.p = X.p :=
  StackInGroupoidsOver.Hom.comm F

/-- Field-notation bridge to the equivalence-over-base predicate on owner homs of stacks in
groupoids over `(C, J)`. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  StackInGroupoidsOver.Hom.IsEquivalenceOverBase F

/-- Field-notation bridge to the local essential-image predicate on owner homs of stacks in
groupoids over `(C, J)`. -/
abbrev LocallyEssentiallySurjectiveOnObjects
    (F : X ⟶ Y) : Prop :=
  StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects F

end WideSubcategory

end CategoryTheory

/-! ### Lemma_8_5_6 (from Chap08) -/
open CategoryTheory

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 8.5.6:
- primary domain: stacks in groupoids over a site and their bicategorical `2`-fibre products;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver`,
  `stackTwoFibreProduct_isStack`,
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- best owner abstraction: the pullback object is owned upstream by
  `FibredInGroupoidsOver.twoFibreProduct F G`; this file should add only the owner-level
  rebundling `StackInGroupoidsOver.twoFibreProduct F G`, with the comparison square stated in the
  stack bicategory and its legs reused directly from the ambient owner projections;
- primitive data: the fibred-in-groupoids `2`-fibre product and its canonical projections;
- derived API: the owner-level bundled view `StackInGroupoidsOver.twoFibreProduct` and the
  resulting based-functor square.

Source/core/bridge triage:
- `source-facing`: `StackInGroupoidsOver.twoFibreProductSquare` and
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInGroupoidsOver.twoFibreProduct F G`,
  `FibredInGroupoidsOver.twoFibreProductSquare F G`, and
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- `bridge/view`: the rebundled stack owner `StackInGroupoidsOver.twoFibreProduct F G`. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackInGroupoidsOver J}
variable (F : X ⟶ S) (G : Y ⟶ S)

namespace StackInGroupoidsOver

/-- The canonical `2`-fibre product of stacks in groupoids over `(C, J)`, obtained by bundling
the chapter-level owner `FibredInGroupoidsOver.twoFibreProduct` as an object of the full
sub-`2`-category `StackInGroupoidsOver J`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom, inferInstance⟩

/- The canonical `2`-commutative square in the bicategory of stacks in groupoids over `(C, J)`,
formed by restricting the chapter-level pullback owner of the stack morphisms `F` and `G`. -/
noncomputable abbrev twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  mkTwoFibreProductSquare F G
    (show IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p from
        inferInstance)

/- The canonical square `twoFibreProductSquare F G` is a bicategorical `2`-fibre product in
the bicategory of stacks in groupoids over `(C, J)`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  sorry

end StackInGroupoidsOver

/- Lemma 8.5.6 reuses the ambient explicit `2`-fibre-product theorem from Categories,
Lemma `4.32.3`, already formalized as `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`. -/
recall CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct

end

end CategoryTheory
