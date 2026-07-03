import Mathlib
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_35_1 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Functor.Fiber IsHomLift IsStronglyCartesian

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-
Domain-style sampling for Definition 4.35.1:
- primary domain: fibred categories and strongly cartesian morphisms.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsStronglyCartesian`,
  `Functor.Fiber`,
  `FibredCategoryOver`.
- best owner abstraction: the ambient chapter owner for categories over a fixed base is
  `FibredCategoryOver`, but there is no earlier owner for the source-facing extra condition
  "fibred in groupoids"; this file should therefore define only the minimal Prop-valued class on
  top of the canonical mathlib fibred-category owners.
- primitive data: fibredness of `p` together with the source-facing condition that every morphism
  of the total category is strongly cartesian over its image.
- derived API: every morphism in a standard fiber is an isomorphism, hence each standard fiber
  `p.Fiber U` is a groupoid.

Source/core/bridge triage:
- `source-facing`: `IsFibredInGroupoids p`.
- `core/canonical`: `Functor.IsFibered`, `Functor.IsStronglyCartesian`, `Functor.Fiber`.
- `bridge/view`: the instance deriving `IsGroupoid (p.Fiber U)` from the source-facing class. -/

/-- Definition 4.35.1: a functor `p : 𝒮 ⥤ 𝒞` is fibred in groupoids over `𝒞` if it is fibred
and every morphism of `𝒮` is strongly cartesian over its image in `𝒞`. In a fibered category,
cartesian and strongly cartesian arrows coincide, so this is the canonical mathlib-facing form of
the textbook condition. -/
class IsFibredInGroupoids (p : 𝒮 ⥤ 𝒞) : Prop extends p.IsFibered where
  /-- Every morphism in the total category is strongly cartesian over its image in the base. -/
  isStronglyCartesian_map {x y : 𝒮} (φ : x ⟶ y) : p.IsStronglyCartesian (p.map φ) φ

attribute [instance] IsFibredInGroupoids.isStronglyCartesian_map

/-- The primitive owner data for a functor fibred in groupoids reconstructs the source-facing
class. -/
instance (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    [∀ (x y : 𝒮) (φ : x ⟶ y), p.IsStronglyCartesian (p.map φ) φ] :
    IsFibredInGroupoids p where
  toIsFibered := inferInstance
  isStronglyCartesian_map _ := inferInstance

namespace IsFibredInGroupoids

variable {p : 𝒮 ⥤ 𝒞} [IsFibredInGroupoids p]
variable (U : 𝒞)

-- Proof sketch: the owner field `IsFibredInGroupoids.isStronglyCartesian_map` already makes the
-- underlying morphism strongly cartesian over `p.map φ.1`. Since `φ` lies in the fiber over `U`,
-- the defining hom-lift equation gives `p.map φ.1 = 𝟙 U`, so the base morphism is an
-- isomorphism. Then
-- `isIso_of_base_isIso` upgrades the underlying morphism, and the resulting inverse in `𝒮`
-- induces the inverse in the fiber.
private theorem fiber_hom_isIso {X Y : p.Fiber U} (φ : X ⟶ Y) : IsIso φ := by
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  haveI : IsIso (p.map φ.1) := by
    simpa [fac' p (𝟙 U) φ.1] using
      (show IsIso (eqToHom X.2 ≫ 𝟙 U ≫ eqToHom Y.2.symm) from inferInstance)
  letI : IsIso φ.1 := IsStronglyCartesian.isIso_of_base_isIso p (p.map φ.1) φ.1
  let e := asIso φ.1
  letI : p.IsHomLift (𝟙 U) e.inv := by
    simpa [e] using (inferInstance : p.IsHomLift (𝟙 U) (inv φ.1))
  refine ⟨⟨⟨e.inv, inferInstance⟩, ?_, ?_⟩⟩
  · apply hom_ext
    change φ.1 ≫ e.inv = 𝟙 X.1
    simp [e]
  · apply hom_ext
    change e.inv ≫ φ.1 = 𝟙 Y.1
    simp [e]

/-- Every fiber of a category fibred in groupoids is a groupoid. -/
instance fiber_isGroupoid : IsGroupoid (p.Fiber U) where
  all_isIso := fiber_hom_isIso U

/-- A morphism in a fiber of a category fibred in groupoids is an isomorphism. -/
theorem hom_isIso {X Y : p.Fiber U} (φ : X ⟶ Y) : IsIso φ := by
  infer_instance

end IsFibredInGroupoids

end CategoryTheory

/-! ### Lemma_4_35_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Functor.Fiber IsCartesian IsStronglyCartesian

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.35.2:
- primary domain: categories fibred in groupoids over a base functor.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Functor.IsFibered`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`,
  `Functor.Fiber`.
- best owner abstraction: `IsFibredInGroupoids` as the source-facing owner built directly on the
  canonical fibred-category API. This file should stay at the bridge/view layer between that owner
  and the fiberwise groupoid criterion, rather than introducing a second wrapper around the same
  `Functor.IsFibered` and `Functor.Fiber` data.
- primitive data: `p.IsFibered` together with the fiberwise groupoid condition
  `∀ U, IsGroupoid (p.Fiber U)`.
- derived API: the owner field `IsFibredInGroupoids.isStronglyCartesian_map`.

Source/core/bridge triage:
- `source-facing`: `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- `core/canonical`: `Functor.IsFibered`, `Functor.IsStronglyCartesian`, `Functor.Fiber`.
- `bridge/view`: `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`, upgrading
  `p.IsFibered` plus groupoid fibers to `IsFibredInGroupoids p`. -/

/-- Helper for Lemma 4.35.2: if every standard fiber of a fibered functor is a groupoid, then any
morphism in the total category is strongly cartesian. -/
private theorem isStronglyCartesian_of_fiber_groupoid
    {p : S ⥤ C} [p.IsFibered]
    (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) {x y : S} (φ : x ⟶ y) :
    p.IsStronglyCartesian (p.map φ) φ := by
  let U := p.obj x
  -- Choose a cartesian lift of the base map of `φ`; fiberedness upgrades it to a strongly
  -- cartesian lift over the same arrow in the base.
  obtain ⟨z, ψ, hψ⟩ := IsPreFibered.exists_isCartesian p rfl (p.map φ)
  letI : p.IsCartesian (p.map φ) ψ := hψ
  letI : p.IsStronglyCartesian (p.map φ) ψ :=
    IsFibered.isStronglyCartesian_of_isCartesian p (p.map φ) ψ
  letI : IsGroupoid (p.Fiber U) := hfiber U
  -- Compare `φ` with the chosen lift. This comparison is vertical, hence invertible in the fiber.
  let χ : x ⟶ z := IsCartesian.map p (p.map φ) ψ φ
  have hχ : χ ≫ ψ = φ := IsCartesian.fac p (p.map φ) ψ φ
  haveI : IsIso (homMk p U χ) := by infer_instance
  haveI : IsIso χ := by
    simpa using
      (inferInstance : IsIso (((fiberInclusion : p.Fiber U ⥤ S).map (homMk p U χ))))
  -- A vertical isomorphism is strongly cartesian over the identity, so composing with `ψ`
  -- transfers strong cartesianness to `φ`.
  letI : p.IsStronglyCartesian (𝟙 U) χ := of_isIso p (𝟙 U) χ
  simpa [hχ] using
    (inferInstance : p.IsStronglyCartesian (𝟙 U ≫ p.map φ) (χ ≫ ψ))

/-- A fibered functor whose standard fibers are groupoids is fibred in groupoids. -/
theorem isFibredInGroupoids_of_isFibered_and_fiber_groupoid
    (p : S ⥤ C) (hp : p.IsFibered) (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    IsFibredInGroupoids p := by
  letI : p.IsFibered := hp
  exact
    { toIsFibered := hp
      isStronglyCartesian_map φ := isStronglyCartesian_of_fiber_groupoid hfiber φ }

-- Proof sketch: one direction is built into `IsFibredInGroupoids`: fiberedness is inherited from
-- the class, and every fiber is a groupoid by `IsFibredInGroupoids.fiber_isGroupoid`. Conversely,
-- assume `p` is fibered and every fiber is a groupoid; for any `φ : y ⟶ x`, choose a cartesian
-- lift of `p.map φ` with codomain `x`, upgrade it to a strongly cartesian lift via the canonical
-- `IsFibered` owner API, compare `y` with that lift inside the relevant fiber, and use that
-- fiberwise morphisms are isomorphisms to conclude that `φ` itself is strongly cartesian.
/-- Lemma 4.35.2: a functor `p : S ⥤ C` is fibred in groupoids exactly when it is fibred and each
fiber category `p.Fiber U` is a groupoid. -/
theorem isFibredInGroupoids_iff_isFibered_and_fiber_groupoid
    (p : S ⥤ C) :
    IsFibredInGroupoids p ↔ p.IsFibered ∧ ∀ U : C, IsGroupoid (p.Fiber U) := by
  constructor
  · intro hp
    letI : IsFibredInGroupoids p := hp
    exact ⟨hp.toIsFibered, fun U ↦ IsFibredInGroupoids.fiber_isGroupoid U⟩
  · rintro ⟨hp, hfiber⟩
    exact isFibredInGroupoids_of_isFibered_and_fiber_groupoid p hp hfiber

/- Companion recall: once `p` is fibred in groupoids, the owner field
`IsFibredInGroupoids.isStronglyCartesian_map` states that every morphism of the total category is
strongly cartesian over its image in the base. -/
recall IsFibredInGroupoids.isStronglyCartesian_map

end CategoryTheory

/-! ### Lemma_4_35_3 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor IsStronglyCartesian

/-
Domain-style sampling for Lemma 4.35.3:
- primary domain: fibred categories, strongly cartesian morphisms, and the associated category
  fibred in groupoids;
- sampled owner-level declarations:
  `Functor.IsStronglyCartesian`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`,
  `CategoryTheory.WideSubcategory`,
  `CategoryTheory.IsFibredInGroupoids`.
- best owner abstraction: the core owner is `Functor.IsStronglyCartesian`; this file should stay at
  the bridge/view layer, building only the associated projection to `C` from the canonical
  `WideSubcategory` owner, without introducing a parallel owner for fibred-in-groupoids data.

Source/core/bridge triage:
- `source-facing`: `stronglyCartesianProjection_isFibredInGroupoids`;
- `core/canonical`: `Functor.IsStronglyCartesian`, `Functor.IsFibered`,
  `CategoryTheory.IsFibredInGroupoids`;
- `bridge/view`: `stronglyCartesianProjection`.

Primitive-vs-derived split:
- primitive data: the functor `p : S ⥤ C` and the owner-level predicate
  `p.IsStronglyCartesian (p.map φ) φ` on morphisms of `S`;
- derived API: the multiplicative wide subcategory cut out by that predicate, the restricted
  projection to `C`, and the induced fibred-in-groupoids structure when `p` is fibred.
-/

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- The morphism property on `S` consisting of the arrows that are strongly cartesian over their
image under `p`. -/
abbrev stronglyCartesianProperty (p : S ⥤ C) : MorphismProperty S :=
  fun {_ _} φ ↦ p.IsStronglyCartesian (p.map φ) φ

/-- The strongly cartesian morphisms over `p` form a multiplicative morphism property. -/
instance (p : S ⥤ C) :
    MorphismProperty.IsMultiplicative (stronglyCartesianProperty p) where
  id_mem x := by
    simpa [stronglyCartesianProperty] using
      (inferInstance : p.IsStronglyCartesian (𝟙 (p.obj x)) (𝟙 x))
  comp_mem φ ψ hφ hψ := by
    haveI : p.IsStronglyCartesian (p.map φ) φ := hφ
    haveI : p.IsStronglyCartesian (p.map ψ) ψ := hψ
    change p.IsStronglyCartesian (p.map (φ ≫ ψ)) (φ ≫ ψ)
    simpa using
      (inferInstance : p.IsStronglyCartesian (p.map φ ≫ p.map ψ) (φ ≫ ψ))

/-- The wide subcategory of `S` whose morphisms are exactly the strongly cartesian morphisms
over `p`. -/
abbrev stronglyCartesianSubcategory (p : S ⥤ C) :=
  WideSubcategory (stronglyCartesianProperty p)

/-- The restriction of `p` to its strongly cartesian wide subcategory. -/
abbrev stronglyCartesianProjection (p : S ⥤ C) :
    stronglyCartesianSubcategory p ⥤ C :=
  wideSubcategoryInclusion (stronglyCartesianProperty p) ⋙ p

private theorem isHomLift_of_stronglyCartesianProjection
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p}
    {f : p.obj x.obj ⟶ p.obj y.obj} {φ : x ⟶ y}
    [(stronglyCartesianProjection p).IsHomLift f φ] :
    p.IsHomLift f φ.hom := by
  refine IsHomLift.of_fac p f φ.hom rfl rfl ?_
  simpa [stronglyCartesianProjection] using
    (IsHomLift.fac (stronglyCartesianProjection p) f φ)

private theorem isHomLift_stronglyCartesianProjection
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p}
    {f : p.obj x.obj ⟶ p.obj y.obj} {φ : x ⟶ y}
    [p.IsHomLift f φ.hom] :
    (stronglyCartesianProjection p).IsHomLift f φ := by
  refine IsHomLift.of_fac (stronglyCartesianProjection p) f φ rfl rfl ?_
  simpa [stronglyCartesianProjection] using (IsHomLift.fac p f φ.hom)

-- Any morphism of the strongly cartesian wide subcategory remains strongly cartesian for the
-- restricted projection.
private theorem stronglyCartesianProjection_map_isStronglyCartesian
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p} (φ : x ⟶ y) :
    (stronglyCartesianProjection p).IsStronglyCartesian ((stronglyCartesianProjection p).map φ) φ := by
  constructor
  intro z g ψ hψ
  change p.obj z.obj ⟶ p.obj x.obj at g
  haveI : p.IsStronglyCartesian (p.map φ.hom) φ.hom :=
    φ.2
  letI : (stronglyCartesianProjection p).IsHomLift (g ≫ p.map φ.hom) ψ := by
    simpa [stronglyCartesianProjection, Functor.comp_map] using hψ
  letI : p.IsHomLift (g ≫ p.map φ.hom) ψ.hom :=
    isHomLift_of_stronglyCartesianProjection p
  obtain ⟨χ, hχlift, hχuniq⟩ :=
    IsStronglyCartesian.universal_property p (p.map φ.hom) φ.hom g
      (g ≫ p.map φ.hom) rfl ψ.hom
  letI : p.IsHomLift g χ :=
    hχlift.1
  have hχfac : χ ≫ φ.hom = ψ.hom :=
    hχlift.2
  have hψStrong : p.IsStronglyCartesian (g ≫ p.map φ.hom) ψ.hom := by
    haveI : p.IsStronglyCartesian (p.map ψ.hom) ψ.hom :=
      ψ.2
    have hψeq : g ≫ p.map φ.hom = p.map ψ.hom := IsHomLift.eq_of_isHomLift p _ ψ.hom
    simpa [hψeq] using (show p.IsStronglyCartesian (p.map ψ.hom) ψ.hom from inferInstance)
  have hχcomp : p.IsStronglyCartesian (g ≫ p.map φ.hom) (χ ≫ φ.hom) := by
    simpa [hχfac] using hψStrong
  letI : p.IsStronglyCartesian (g ≫ p.map φ.hom) (χ ≫ φ.hom) := hχcomp
  have hχStrong : p.IsStronglyCartesian g χ := by
    let hφStrong : p.IsStronglyCartesian (p.map φ.hom) φ.hom := φ.2
    exact
      @Functor.IsStronglyCartesian.of_comp
        _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hφStrong hχcomp hχlift.1
  -- Package the ambient lift `χ` into the wide subcategory once we know it is strongly cartesian.
  have hχ_mem : stronglyCartesianProperty p χ := by
    have hχeq : g = p.map χ := IsHomLift.eq_of_isHomLift p g χ
    simpa [stronglyCartesianProperty, hχeq] using hχStrong
  let χ' : z ⟶ x :=
    ⟨χ, hχ_mem⟩
  refine ⟨χ', ⟨?_, ?_⟩, ?_⟩
  · exact isHomLift_stronglyCartesianProjection p
  · apply WideSubcategory.hom_ext
    exact hχfac
  · intro τ hτ
    apply WideSubcategory.hom_ext
    letI : (stronglyCartesianProjection p).IsHomLift g τ := hτ.1
    letI : p.IsHomLift g τ.hom := isHomLift_of_stronglyCartesianProjection p
    exact hχuniq τ.hom ⟨inferInstance, congrArg (fun k ↦ k.hom) hτ.2⟩

-- Proof sketch: for existence of lifts, use that `p` is fibered and choose strongly cartesian
-- lifts, which already lie in the wide subcategory. For uniqueness, compare two composable lifts as
-- in Diagram `4.35.1.1`; since every morphism in the wide subcategory is strongly cartesian, the
-- comparison is an isomorphism, and isomorphisms remain strongly cartesian there.
/-- The strongly cartesian restriction of a fibred functor is fibred in groupoids. -/
instance (p : S ⥤ C) [p.IsFibered] :
    IsFibredInGroupoids (stronglyCartesianProjection p) := by
  refine
    { toIsFibered := Functor.IsFibered.of_exists_isStronglyCartesian ?_
      isStronglyCartesian_map := fun φ ↦
        stronglyCartesianProjection_map_isStronglyCartesian p φ }
  intro y R f
  change R ⟶ p.obj y.obj at f
  obtain ⟨x, φ, hφ⟩ := IsPreFibered.exists_isCartesian p rfl f
  letI : p.IsCartesian f φ := hφ
  letI : p.IsStronglyCartesian f φ :=
    IsFibered.isStronglyCartesian_of_isCartesian p f φ
  have hx : p.obj x = R := IsHomLift.domain_eq p f φ
  subst R
  have hfeq : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  -- The chosen ambient lift is already strongly cartesian, so it defines a morphism downstairs.
  have hφ'_mem : stronglyCartesianProperty p φ := by
    simpa [stronglyCartesianProperty, hfeq] using
      (show p.IsStronglyCartesian f φ from inferInstance)
  let φ' : (⟨x⟩ : stronglyCartesianSubcategory p) ⟶ y :=
    ⟨φ, hφ'_mem⟩
  change (stronglyCartesianProjection p).obj (⟨x⟩ : stronglyCartesianSubcategory p) ⟶
      (stronglyCartesianProjection p).obj y at f
  have hφ'eq : f = (stronglyCartesianProjection p).map φ' := by
    simpa [stronglyCartesianProjection, Functor.comp_map] using hfeq
  have hφ'_lift : (stronglyCartesianProjection p).IsHomLift f φ' := by
    refine IsHomLift.of_fac' (stronglyCartesianProjection p) f φ' rfl rfl ?_
    simpa using hφ'eq.symm
  letI : (stronglyCartesianProjection p).IsHomLift f φ' :=
    hφ'_lift
  have hφ' : (stronglyCartesianProjection p).IsStronglyCartesian f φ' := by
    simpa [hφ'eq] using stronglyCartesianProjection_map_isStronglyCartesian p φ'
  refine ⟨⟨x⟩, φ', ?_⟩
  exact hφ'

/-- Lemma 4.35.3: if `p : S ⥤ C` is fibred, then its restriction to the wide subcategory whose
morphisms are the strongly cartesian morphisms of `S` is fibred in groupoids. -/
theorem stronglyCartesianProjection_isFibredInGroupoids
    (p : S ⥤ C) [p.IsFibered] :
    IsFibredInGroupoids (stronglyCartesianProjection p) :=
  inferInstance

end CategoryTheory

/-! ### Example_4_35_4 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Functor IsHomLift Functor.Fiber
open CategoryTheory.SingleObj

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Monoid H]

/- Domain-style sampling for Example 4.35.4:
- primary domain: fibered categories attached to `MonoidHom.toFunctor` from a one-object
  groupoid to a one-object category;
- inspected owner-level declarations:
  `MonoidHom.toFunctor`,
  `Functor.IsFibered`,
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.Fiber`.
- best owner abstraction: the canonical owner is `p.toFunctor`, with fibredness expressed by
  `Functor.IsFibered` and the groupoid upgrade expressed by `IsFibredInGroupoids`.
- primitive data: the monoid homomorphism `p : G →* H`.
- derived API: the induced equivalence from the standard fiber of `p.toFunctor` to
  `SingleObj ↥(p.ker)`, together with the characterization of
  `IsFibredInGroupoids p.toFunctor` via surjectivity.

Source/core/bridge triage:
- `source-facing`: the two textbook clauses specialized to `p.toFunctor`.
- `core/canonical`: `Functor.IsFibered`, `IsFibredInGroupoids`, and `Functor.Fiber`.
- `bridge/view`: the canonical lift of `p.ker.subtype.toFunctor` into the standard fiber of
  `p.toFunctor`, the induced equivalence with `SingleObj ↥(p.ker)`, and the surjectivity
  criterion for the owner predicate. -/

/-- A vertical morphism in the fiber corresponds to an element of `ker p`. -/
-- Proof sketch: a morphism in `p.toFunctor.Fiber (SingleObj.star H)` lies over the identity of
-- the unique base object, so the defining equation `IsHomLift.fac'` forces its image under `p`
-- to be `1`.
private theorem fiberHom_mem_ker (p : G →* H) {x y : p.toFunctor.Fiber (star H)}
    (φ : x ⟶ y) : (φ.1 : G) ∈ p.ker := by
  letI : p.toFunctor.IsHomLift (𝟙 (star H)) φ.1 := φ.2
  change p φ.1 = 1
  simpa [toFunctor, mapHom, x.2, y.2] using
    (IsHomLift.fac' p.toFunctor (𝟙 (star H)) φ.1)

/-- For a homomorphism `p : G →* H` from a group to a monoid, the induced one-object-category
functor is fibered exactly when `p` is surjective. -/
-- Proof sketch: fibredness for `p.toFunctor` is the strongly-cartesian lift criterion from
-- `isFibered_iff_exists_isStronglyCartesian`. In a one-object source and base, such a lift is
-- exactly a preimage of the given element of `H`, so the criterion reduces to surjectivity.
theorem toFunctor_isFibered_iff_surjective (p : G →* H) :
    p.toFunctor.IsFibered ↔ Function.Surjective p := by
  constructor
  · intro hp h
    obtain ⟨⟨⟩, φ, hφ⟩ :=
      (isFibered_iff_exists_isStronglyCartesian p.toFunctor).1 hp
        (star G) (star H) h
    have hEq : h = p.toFunctor.map φ := by
      have hLift : p.toFunctor.IsHomLift h φ := hφ.toIsHomLift
      cases hLift
      rfl
    exact ⟨φ, by simpa using hEq.symm⟩
  · intro hp
    exact (isFibered_iff_exists_isStronglyCartesian p.toFunctor).2 fun x V f ↦ by
      cases x
      cases V
      obtain ⟨g, rfl⟩ := hp f
      let φ : star G ⟶ star G := g
      refine ⟨star G, φ, ?_⟩
      change p.toFunctor.IsStronglyCartesian (p.toFunctor.map φ) φ
      infer_instance

/- Internal bridge: the kernel inclusion `ker p ↪ G` induces a canonical functor from the
one-object groupoid `SingleObj ↥(p.ker)` into the standard fiber of `p.toFunctor` over the unique
object of `SingleObj H`. -/
private theorem kernelToFiberCompConst (p : G →* H) :
    (Subgroup.subtype p.ker).toFunctor ⋙ p.toFunctor =
      (const (SingleObj ↥(p.ker))).obj (star H) := by
  fapply CategoryTheory.Functor.ext
  · intro X
    cases X
    rfl
  · intro X Y g
    cases X
    cases Y
    simpa using p.mem_ker.mp g.2

private def kernelToFiberFunctor (p : G →* H) :
    SingleObj ↥(p.ker) ⥤ p.toFunctor.Fiber (star H) :=
  inducedFunctor (kernelToFiberCompConst p)

private instance kernelSubtype_toFunctor_faithful (p : G →* H) :
    (Subgroup.subtype p.ker).toFunctor.Faithful :=
  (toFunctor_faithful_iff_injective (Subgroup.subtype p.ker)).2 Subtype.val_injective

private instance kernelToFiberFunctor_faithful (p : G →* H) :
    (kernelToFiberFunctor p).Faithful :=
  Functor.Faithful.of_comp_eq <| by
    simpa [kernelToFiberFunctor] using inducedFunctor_comp (kernelToFiberCompConst p)

private instance kernelToFiberFunctor_full (p : G →* H) :
    (kernelToFiberFunctor p).Full where
  map_surjective := by
    intro X Y φ
    cases X
    cases Y
    refine ⟨⟨φ.1, fiberHom_mem_ker p φ⟩, ?_⟩
    apply hom_ext
    rfl

private instance kernelToFiberFunctor_essSurj (p : G →* H) :
    (kernelToFiberFunctor p).EssSurj := by
  apply essSurj_of_surj
  intro X
  cases X
  refine ⟨star ↥(p.ker), ?_⟩
  apply Subtype.ext
  rfl

private instance kernelToFiberFunctor_isEquivalence (p : G →* H) :
    (kernelToFiberFunctor p).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

private theorem fiber_isGroupoid (p : G →* H) :
    IsGroupoid (p.toFunctor.Fiber (star H)) := by
  let e := (kernelToFiberFunctor p).asEquivalence.symm
  exact isGroupoid_of_reflects_iso e.functor

/-- Example 4.35.4 (2): the fiber category of `p.toFunctor` over the unique object of
`SingleObj H` is the one-object groupoid attached to the kernel of `p`. -/
noncomputable def toFunctorFiberEquivalenceKer (p : G →* H) :
    p.toFunctor.Fiber (star H) ≌ SingleObj ↥(p.ker) :=
  (kernelToFiberFunctor p).asEquivalence.symm

/-- The equivalence from the fiber of `p.toFunctor` to the one-object category of `ker p`
has an equivalence of categories as its forward functor. -/
-- Proof sketch: this is the standard `IsEquivalence` instance carried by the functor part of
-- any categorical equivalence.
theorem toFunctorFiberEquivalenceKer_functor_isEquivalence (p : G →* H) :
    (toFunctorFiberEquivalenceKer p).functor.IsEquivalence := by
  -- The forward functor of any equivalence carries the standard `IsEquivalence` instance.
  simpa using
    (CategoryTheory.Equivalence.isEquivalence_functor (toFunctorFiberEquivalenceKer p))

/-- Example 4.35.4 (1): for a homomorphism `p : G →* H` from a group to a monoid, the induced
functor `SingleObj G ⥤ SingleObj H` is fibred in groupoids exactly when `p` is surjective. -/
-- Proof sketch: if `p` is surjective, every arrow of the base category lifts to an arrow in
-- `SingleObj G`, and Lemma `4.35.2` reduces fibredness in groupoids to fibredness together with
-- the fact that the unique fiber is a groupoid; the latter follows from the kernel equivalence
-- above.
-- Conversely, fibredness over the unique object forces every element of `H` to have a lift in
-- `G`.
theorem toFunctor_isFibredInGroupoids_iff_surjective (p : G →* H) :
    IsFibredInGroupoids p.toFunctor ↔ Function.Surjective p := by
  constructor
  · intro hp
    exact (toFunctor_isFibered_iff_surjective p).1 hp.toIsFibered
  · intro hp
    refine
      isFibredInGroupoids_of_isFibered_and_fiber_groupoid p.toFunctor
        ((toFunctor_isFibered_iff_surjective p).2 hp) ?_
    intro U
    cases U
    exact fiber_isGroupoid p

end MonoidHom

/-! ### Example_4_35_5 (from Chap04) -/
/- Domain-style sampling for Example 4.35.5:
- primary domain: fibred categories and fibred-in-groupoids counterexamples.
- inspected owner-level declarations:
  `Functor.IsHomLift`,
  `Functor.IsFibered`,
  `IsFibredInGroupoids`,
  `Functor.isFibered_iff_exists_isStronglyCartesian`,
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- best owner abstraction: the canonical owner is `Functor.IsFibered`, with the chapter's
  source-facing predicate `IsFibredInGroupoids` built on top of it.
- primitive data: the explicit small categories `Base`, `NoLift`, `TwoLift`, and their projection
  functors to `Base`.
- derived API: the lift/nonlift facts for `Base.Hom.f`, the fiberwise groupoid facts, and the
  counterexample conclusions `¬ projection.IsFibered` and `¬ IsFibredInGroupoids projection`.

Source/core/bridge triage:
- `source-facing`: the two counterexample projections in Example 4.35.5.
- `core/canonical`: `Functor.IsHomLift`, `Functor.IsCartesian`, `Functor.IsFibered`,
  `Functor.Fiber`.
- `bridge/view`: `Functor.isFibered_iff_exists_isStronglyCartesian` together with
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`. -/

namespace CategoryTheory
open Functor IsHomLift IsCartesian

namespace Example4355

/-- Objects of the base category used in Example 4.35.5. -/
inductive Base where
  | A | B | T
  deriving DecidableEq, Repr

namespace Base

/-- Morphisms of the base category used in Example 4.35.5. -/
inductive Hom : Base → Base → Type where
  | id : (X : Base) → Hom X X
  | f : Hom .A .B
  | g : Hom .B .T
  | h : Hom .A .T
  deriving DecidableEq, Repr

namespace Hom

/-- Composition law on the base category of Example 4.35.5. -/
def comp : {X Y Z : Base} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k
  | _, _, _, f, g => h

/-- Left identity for the base category composition. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the base category.
private theorem id_comp {X Y : Base} (k : Hom X Y) : comp (id X) k = k := by
  -- Enumerate the only well-typed morphism constructors in the finite base category.
  cases k <;> rfl

/-- Right identity for the base category composition. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the base category.
private theorem comp_id {X Y : Base} (k : Hom X Y) : comp k (id Y) = k := by
  -- Enumerate the only well-typed morphism constructors in the finite base category.
  cases k <;> rfl

/-- Associativity for the base category composition. -/
-- Proof sketch: case split on the only composable triples of non-identity arrows.
private theorem assoc {W X Y Z : Base} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := by
  -- The dependent types remove impossible triples, so a finite case split closes the proof.
  cases k <;> cases l <;> cases m <;> rfl

end Hom

/-- The explicit category structure on the base of Example 4.35.5. -/
instance : Category Base where
  Hom := Hom
  id := Hom.id
  comp := fun k l ↦ Hom.comp k l
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

end Base

/-- Objects of the source category where the arrow `f : A ⟶ B` has no lift. -/
inductive NoLift where
  | A' | B' | T'
  deriving DecidableEq, Repr

namespace NoLift

/-- Morphisms of the source category where the arrow `f : A ⟶ B` has no lift. -/
inductive Hom : NoLift → NoLift → Type where
  | id : (X : NoLift) → Hom X X
  | g : Hom .B' .T'
  | h : Hom .A' .T'
  deriving DecidableEq, Repr

namespace Hom

/-- Composition law on the source category with no lift of `f`. -/
def comp : {X Y Z : NoLift} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k

/-- Left identity for the source category with no lift of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
private theorem id_comp {X Y : NoLift} (k : Hom X Y) : comp (id X) k = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Right identity for the source category with no lift of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
private theorem comp_id {X Y : NoLift} (k : Hom X Y) : comp k (id Y) = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Associativity for the source category with no lift of `f`. -/
-- Proof sketch: all nontrivial composites factor through identities, so the finite case split is immediate.
private theorem assoc {W X Y Z : NoLift} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := by
  -- Every composable triple reduces to identities in this category.
  cases k <;> cases l <;> cases m <;> rfl

end Hom

/-- The category structure on the first source category of Example 4.35.5. -/
instance : Category NoLift where
  Hom := Hom
  id := Hom.id
  comp := fun k l ↦ Hom.comp k l
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The object map of the first source projection in Example 4.35.5. -/
private def objMap : NoLift → Base
  | .A' => .A
  | .B' => .B
  | .T' => .T

/-- The morphism map of the first source projection in Example 4.35.5. -/
private def homMap :
    {X Y : NoLift} → Hom X Y → (objMap X ⟶ objMap Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.g => Base.Hom.g
  | _, _, Hom.h => Base.Hom.h

/-- The first source projection preserves identities. -/
-- Proof sketch: check the three objects of the source category directly.
private theorem projection_map_id (X : NoLift) : homMap (𝟙 X) = 𝟙 (objMap X) := by
  -- The object map is explicit, so each identity is preserved by reflexivity.
  cases X <;> rfl

/-- The first source projection preserves composition. -/
-- Proof sketch: inspect the finitely many composable pairs of source morphisms.
private theorem projection_map_comp {X Y Z : NoLift} (k : Hom X Y) (l : Hom Y Z) :
    homMap (Hom.comp k l) = Base.Hom.comp (homMap k) (homMap l) := by
  -- The projection is defined by explicit images of the finitely many generators.
  cases k <;> cases l <;> rfl

/-- The projection from the first source category to the base category. -/
def projection : NoLift ⥤ Base where
  obj := objMap
  map := fun {_ _} k ↦ homMap k
  map_id := projection_map_id
  map_comp := by
    intro X Y Z k l
    -- Route correction: state preservation of composition using the explicit finite `comp`.
    simpa using projection_map_comp k l

/-- Helper for Example 4.35.5: every hom-set in a standard fiber of the first projection is a
singleton. -/
private abbrev fiber_hom_unique (U : Base) {X Y : projection.Fiber U} : Unique (X ⟶ Y) := by
  cases U with
  | A =>
      cases X with
      | mk X hX =>
          cases X with
          | A' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `A`, the only possible source morphism is the identity on `A'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom A' A' from φ.1) = Hom.id A' := by
                        cases (show Hom A' A' from φ.1) <;> rfl
                      simpa using hφ
                  | B' => cases hY
                  | T' => cases hY
          | B' => cases hX
          | T' => cases hX
  | B =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `B`, the only possible source morphism is the identity on `B'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom B' B' from φ.1) = Hom.id B' := by
                        cases (show Hom B' B' from φ.1) <;> rfl
                      simpa using hφ
                  | T' => cases hY
          | T' => cases hX
  | T =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' => cases hX
          | T' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' => cases hY
                  | T' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `T`, the only possible source morphism is the identity on `T'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom T' T' from φ.1) = Hom.id T' := by
                        cases (show Hom T' T' from φ.1) <;> rfl
                      simpa using hφ

/-- Example 4.35.5 (1): every standard fiber of the first projection is a groupoid. -/
-- Proof sketch: for each `U : Base`, the fiber `projection.Fiber U` has exactly one object by
-- inspection of `objMap`, and its only endomorphism is the identity.
instance fiber_isGroupoid (U : Base) :
    IsGroupoid (projection.Fiber U) := by
  -- The fiber is a thin category, so every morphism is automatically invertible.
  letI : Groupoid (projection.Fiber U) :=
    Groupoid.ofHomUnique (fun {X Y} ↦ fiber_hom_unique U (X := X) (Y := Y))
  infer_instance

/-- Example 4.35.5 (2): for the first projection, the arrow `f : A ⟶ B` has no lift from `A'` to
`B'`. -/
-- Proof sketch: inspect the morphisms in `Hom`; there is no arrow from `A'` to `B'`, so no
-- morphism can map to `f`.
theorem projection_not_isHomLift_f :
    ¬ ∃ φ : Hom A' B', projection.IsHomLift Base.Hom.f φ := by
  rintro ⟨φ, -⟩
  -- There is no constructor for a morphism `A' ⟶ B'` in `NoLift`.
  cases φ

private theorem homLift_f_domain_eq {X : NoLift} (φ : X ⟶ B')
    [projection.IsHomLift Base.Hom.f φ] : X = A' := by
  have hX : objMap X = Base.A := IsHomLift.domain_eq projection Base.Hom.f φ
  cases X with
  | A' => rfl
  | B' => simp [objMap] at hX
  | T' => simp [objMap] at hX

/-- The first projection in Example 4.35.5 is not fibred in groupoids. -/
-- Proof sketch: use the canonical strongly-cartesian lift criterion for fibredness. A lift of
-- `f : A ⟶ B` with codomain `B'` would have domain `A'`, contradicting
-- `projection_not_isHomLift_f`.
private theorem projection_not_isFibered :
    ¬ projection.IsFibered := by
  intro hp
  obtain ⟨X, φ, hφ⟩ :=
    (isFibered_iff_exists_isStronglyCartesian projection).1 hp B' Base.A Base.Hom.f
  letI : projection.IsStronglyCartesian Base.Hom.f φ := hφ
  have hX : X = A' := homLift_f_domain_eq φ
  subst hX
  exact projection_not_isHomLift_f ⟨φ, inferInstance⟩

theorem projection_not_isFibredInGroupoids :
    ¬ IsFibredInGroupoids projection := by
  rw [isFibredInGroupoids_iff_isFibered_and_fiber_groupoid]
  rintro ⟨hp, -⟩
  exact projection_not_isFibered hp

end NoLift

/-- Objects of the source category where the arrow `f : A ⟶ B` has two lifts. -/
inductive TwoLift where
  | A' | B' | T'
  deriving DecidableEq, Repr

namespace TwoLift

/-- Morphisms of the source category where the arrow `f : A ⟶ B` has two distinct lifts. -/
inductive Hom : TwoLift → TwoLift → Type where
  | id : (X : TwoLift) → Hom X X
  | f1 : Hom .A' .B'
  | f2 : Hom .A' .B'
  | g : Hom .B' .T'
  | h : Hom .A' .T'
  deriving DecidableEq, Repr

namespace Hom

/-- Composition law on the source category with two lifts of `f`. -/
def comp : {X Y Z : TwoLift} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k
  | _, _, _, f1, g => h
  | _, _, _, f2, g => h

/-- Left identity for the source category with two lifts of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
private theorem id_comp {X Y : TwoLift} (k : Hom X Y) : comp (id X) k = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Right identity for the source category with two lifts of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
private theorem comp_id {X Y : TwoLift} (k : Hom X Y) : comp k (id Y) = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Associativity for the source category with two lifts of `f`. -/
-- Proof sketch: check the only non-identity composites, namely `f1 ≫ g` and `f2 ≫ g`.
private theorem assoc {W X Y Z : TwoLift} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := by
  -- The dependent typing again removes impossible triples of generators.
  cases k <;> cases l <;> cases m <;> rfl

end Hom

/-- The category structure on the second source category of Example 4.35.5. -/
instance : Category TwoLift where
  Hom := Hom
  id := Hom.id
  comp := fun k l ↦ Hom.comp k l
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The object map of the second source projection in Example 4.35.5. -/
private def objMap : TwoLift → Base
  | .A' => .A
  | .B' => .B
  | .T' => .T

/-- The morphism map of the second source projection in Example 4.35.5. -/
private def homMap :
    {X Y : TwoLift} → Hom X Y → (objMap X ⟶ objMap Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.f1 => Base.Hom.f
  | _, _, Hom.f2 => Base.Hom.f
  | _, _, Hom.g => Base.Hom.g
  | _, _, Hom.h => Base.Hom.h

/-- The second source projection preserves identities. -/
-- Proof sketch: check the three objects of the source category directly.
private theorem projection_map_id (X : TwoLift) : homMap (𝟙 X) = 𝟙 (objMap X) := by
  -- The object map is explicit, so each identity is preserved by reflexivity.
  cases X <;> rfl

/-- The second source projection preserves composition. -/
-- Proof sketch: inspect the finitely many composable pairs of source morphisms and use that both lifts map to `f`.
private theorem projection_map_comp {X Y Z : TwoLift} (k : Hom X Y) (l : Hom Y Z) :
    homMap (Hom.comp k l) = Base.Hom.comp (homMap k) (homMap l) := by
  -- The only non-identity composites are `f1 ≫ g` and `f2 ≫ g`, both mapping to `h = f ≫ g`.
  cases k <;> cases l <;> rfl

/-- The projection from the second source category to the base category. -/
def projection : TwoLift ⥤ Base where
  obj := objMap
  map := fun {_ _} k ↦ homMap k
  map_id := projection_map_id
  map_comp := by
    intro X Y Z k l
    -- Route correction: state preservation of composition using the explicit finite `comp`.
    simpa using projection_map_comp k l

/-- Helper for Example 4.35.5: every hom-set in a standard fiber of the second projection is a
singleton. -/
private abbrev fiber_hom_unique (U : Base) {X Y : projection.Fiber U} : Unique (X ⟶ Y) := by
  cases U with
  | A =>
      cases X with
      | mk X hX =>
          cases X with
          | A' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- In the fiber over `A`, the lifts `f1` and `f2` disappear: only `id A'` remains.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom A' A' from φ.1) = Hom.id A' := by
                        cases (show Hom A' A' from φ.1) <;> rfl
                      simpa using hφ
                  | B' => cases hY
                  | T' => cases hY
          | B' => cases hX
          | T' => cases hX
  | B =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `B`, the only possible source morphism is `id B'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom B' B' from φ.1) = Hom.id B' := by
                        cases (show Hom B' B' from φ.1) <;> rfl
                      simpa using hφ
                  | T' => cases hY
          | T' => cases hX
  | T =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' => cases hX
          | T' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' => cases hY
                  | T' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `T`, the only possible source morphism is `id T'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom T' T' from φ.1) = Hom.id T' := by
                        cases (show Hom T' T' from φ.1) <;> rfl
                      simpa using hφ

/-- Example 4.35.5 (3): every standard fiber of the second projection is a groupoid. -/
-- Proof sketch: for each `U : Base`, the fiber `projection.Fiber U` again has exactly one object
-- by inspection of `objMap`, and its only endomorphism is the identity.
instance fiber_isGroupoid (U : Base) :
    IsGroupoid (projection.Fiber U) := by
  -- The fiber is a thin category, so every morphism is automatically invertible.
  letI : Groupoid (projection.Fiber U) :=
    Groupoid.ofHomUnique (fun {X Y} ↦ fiber_hom_unique U (X := X) (Y := Y))
  infer_instance

private theorem f1_ne_f2 : (Hom.f1 : A' ⟶ B') ≠ Hom.f2 := by
  intro h
  cases h

/-- Example 4.35.5 (4): for the second projection, the arrow `f : A ⟶ B` has two distinct lifts
from `A'` to `B'`. -/
-- Proof sketch: the arrows `f1` and `f2` are distinct morphisms `A' ⟶ B'`, and both map to
-- `Base.Hom.f` under `homMap`.
theorem projection_exists_two_distinct_isHomLift_f :
    ∃ φ₁ φ₂ : {φ : A' ⟶ B' // projection.IsHomLift Base.Hom.f φ}, φ₁ ≠ φ₂ := by
  have hf1 : projection.IsHomLift Base.Hom.f Hom.f1 := by
    -- The first explicit lift maps to `Base.Hom.f` by definition of `projection`.
    change projection.IsHomLift (projection.map Hom.f1) Hom.f1
    infer_instance
  have hf2 : projection.IsHomLift Base.Hom.f Hom.f2 := by
    -- The second explicit lift also maps to `Base.Hom.f`.
    change projection.IsHomLift (projection.map Hom.f2) Hom.f2
    infer_instance
  refine ⟨⟨Hom.f1, hf1⟩, ⟨Hom.f2, hf2⟩, ?_⟩
  intro h
  apply f1_ne_f2
  exact congrArg Subtype.val h

private theorem homLift_f_domain_eq {X : TwoLift} (φ : X ⟶ B')
    [projection.IsHomLift Base.Hom.f φ] : X = A' := by
  have hX : objMap X = Base.A := IsHomLift.domain_eq projection Base.Hom.f φ
  cases X with
  | A' => rfl
  | B' => simp [objMap] at hX
  | T' => simp [objMap] at hX

/-- The second projection in Example 4.35.5 is not fibred in groupoids. -/
-- Proof sketch: a functor fibred in groupoids is in particular fibered. Any cartesian lift of
-- `f : A ⟶ B` with codomain `B'` must be either `f1` or `f2`, and the other lift contradicts
-- cartesianness.
private theorem projection_not_isCartesian
    (φ ψ : A' ⟶ B') (hφψ : φ ≠ ψ) [projection.IsHomLift Base.Hom.f ψ] :
    ¬ projection.IsCartesian Base.Hom.f φ := by
  intro hφ
  letI : projection.IsCartesian Base.Hom.f φ := hφ
  have hχ :
      ∃! χ : A' ⟶ A', projection.IsHomLift (𝟙 Base.A) χ ∧ χ ≫ φ = ψ := by
    simpa using IsCartesian.universal_property
      (show Base.A ⟶ Base.B from Base.Hom.f) ψ
  obtain ⟨χ, hχ, -⟩ := hχ
  have hχ_id : χ = Hom.id A' := by
    refine match χ with
    | .id .A' => rfl
  apply hφψ
  simpa [hχ_id] using hχ.2

private theorem projection_not_isFibered :
    ¬ projection.IsFibered := by
  intro hp
  obtain ⟨X, φ, hφ⟩ :=
    (isFibered_iff_exists_isStronglyCartesian projection).1 hp B' Base.A Base.Hom.f
  have hX : X = A' := by
    letI : projection.IsStronglyCartesian Base.Hom.f φ := hφ
    exact homLift_f_domain_eq φ
  subst hX
  refine match φ, hφ with
  | .f1, hφ => by
      letI : projection.IsStronglyCartesian Base.Hom.f Hom.f1 := hφ
      haveI : projection.IsHomLift Base.Hom.f Hom.f2 := by
        change projection.IsHomLift (projection.map Hom.f2) Hom.f2
        infer_instance
      exact projection_not_isCartesian Hom.f1 Hom.f2
        f1_ne_f2 inferInstance
  | .f2, hφ => by
      letI : projection.IsStronglyCartesian Base.Hom.f Hom.f2 := hφ
      haveI : projection.IsHomLift Base.Hom.f Hom.f1 := by
        change projection.IsHomLift (projection.map Hom.f1) Hom.f1
        infer_instance
      exact projection_not_isCartesian Hom.f2 Hom.f1
        f1_ne_f2.symm inferInstance

theorem projection_not_isFibredInGroupoids :
    ¬ IsFibredInGroupoids projection := by
  rw [isFibredInGroupoids_iff_isFibered_and_fiber_groupoid]
  rintro ⟨hp, -⟩
  exact projection_not_isFibered hp

end TwoLift

end Example4355
end CategoryTheory
