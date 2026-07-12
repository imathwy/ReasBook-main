import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Subcategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : D ⥤ C) (G : C ⥤ D) (adj : F ⊣ G)

/- Domain-style sampling for Lemma 21.28.1:
- primary domain: adjunctions and the object properties cut out by unit/counit isomorphisms,
  together with the induced full-subcategory and fully-faithful bridge API;
- sampled owner declarations:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.IsStableUnderRetracts`,
  `Functor.FullyFaithful.nonempty_iff_map_bijective`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`;
- best owner abstraction:
  `source-facing`: the unit/counit-isomorphism properties attached to the adjunction `adj`;
  `core/canonical`: the owner predicates `unitIsomorphismProperty F G adj` and
    `counitIsomorphismProperty F G adj`;
  `bridge/view`: their full subcategories, the restricted functors, and the hom-bijection/full
    faithfulness consequences.

Primitive data are only the adjunction `adj : F ⊣ G`. The full subcategories, retract/triangle
closure, and full faithfulness of the restricted functors are derived API and should stay in the
owner/view split rather than being encoded as extra primitive wrapper data.
-/

/-- The object property on the target category consisting of those objects for which the adjunction
unit `K ⟶ GF(K)` is an isomorphism. -/
abbrev unitIsomorphismProperty : ObjectProperty D :=
  fun K ↦ IsIso (adj.unit.app K)

/-- The object property on the source category consisting of those objects for which the adjunction
counit `FG(K) ⟶ K` is an isomorphism. -/
abbrev counitIsomorphismProperty : ObjectProperty C :=
  fun K ↦ IsIso (adj.counit.app K)

/-- The full subcategory cut out by the unit-isomorphism condition `K ⟶ GF(K)`. -/
abbrev unitIsomorphismSubcategory :=
  (unitIsomorphismProperty F G adj).FullSubcategory

/-- The full subcategory cut out by the counit-isomorphism condition `FG(K) ⟶ K`. -/
abbrev counitIsomorphismSubcategory :=
  (counitIsomorphismProperty F G adj).FullSubcategory

private theorem counit_app_obj_isIso_of_unit_app_isIso
    (K : unitIsomorphismSubcategory F G adj) :
    IsIso (adj.counit.app (F.obj K.obj)) := by
  letI : IsIso (adj.unit.app K.obj) := K.property
  letI : IsIso (F.map (adj.unit.app K.obj)) := Functor.map_isIso F (adj.unit.app K.obj)
  exact
    isIso_of_hom_comp_eq_id
      (F.map (adj.unit.app K.obj))
      (adj.left_triangle_components K.obj)

private theorem unit_app_obj_isIso_of_counit_app_isIso
    (K : counitIsomorphismSubcategory F G adj) :
    IsIso (adj.unit.app (G.obj K.obj)) := by
  letI : IsIso (adj.counit.app K.obj) := K.property
  letI : IsIso (G.map (adj.counit.app K.obj)) := Functor.map_isIso G (adj.counit.app K.obj)
  exact
    isIso_of_comp_hom_eq_id
      (G.map (adj.counit.app K.obj))
      (adj.right_triangle_components K.obj)

/-- The left adjoint restricted to the source full subcategory lands in the counit-isomorphism
full subcategory. -/
private def restrictedLeftToCounitSubcategory :
    unitIsomorphismSubcategory F G adj ⥤ counitIsomorphismSubcategory F G adj where
  obj K := ⟨F.obj K.obj, counit_app_obj_isIso_of_unit_app_isIso F G adj K⟩
  map {X Y} f := by
    exact ⟨F.map f.hom⟩
  map_id X := by
    ext
    simpa using F.map_id X.obj
  map_comp f g := by
    ext
    simpa using F.map_comp f.hom g.hom

/-- The right adjoint restricted to the counit-isomorphism full subcategory lands in the
unit-isomorphism full subcategory. -/
private def restrictedRightToUnitSubcategory :
    counitIsomorphismSubcategory F G adj ⥤ unitIsomorphismSubcategory F G adj where
  obj K := ⟨G.obj K.obj, unit_app_obj_isIso_of_counit_app_isIso F G adj K⟩
  map {X Y} f := by
    exact ⟨G.map f.hom⟩
  map_id X := by
    ext
    simpa using G.map_id X.obj
  map_comp f g := by
    ext
    simpa using G.map_comp f.hom g.hom

private def restrictedLeftCompIso :
    (unitIsomorphismProperty F G adj).ι ⋙ F ≅
      restrictedLeftToCounitSubcategory F G adj ⋙ (counitIsomorphismProperty F G adj).ι :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (by
      intro X Y f
      simp [restrictedLeftToCounitSubcategory])

private def restrictedRightCompIso :
    (counitIsomorphismProperty F G adj).ι ⋙ G ≅
      restrictedRightToUnitSubcategory F G adj ⋙ (unitIsomorphismProperty F G adj).ι :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (by
      intro X Y f
      simp [restrictedRightToUnitSubcategory])

/-- The original adjunction restricts to the unit/counit full subcategories. -/
private noncomputable def restrictedAdjunction :
    restrictedLeftToCounitSubcategory F G adj ⊣ restrictedRightToUnitSubcategory F G adj :=
  adj.restrictFullyFaithful
    (unitIsomorphismProperty F G adj).fullyFaithfulι
    (counitIsomorphismProperty F G adj).fullyFaithfulι
    (restrictedLeftCompIso F G adj)
    (restrictedRightCompIso F G adj)

/-- The restriction of the left adjoint to the full subcategory on which the adjunction unit is an
isomorphism. -/
abbrev restrictedLeftAdjoint :
    unitIsomorphismSubcategory F G adj ⥤ C :=
  restrictedLeftToCounitSubcategory F G adj ⋙
    (counitIsomorphismProperty F G adj).ι

/-- The restriction of the right adjoint to the full subcategory on which the adjunction counit is
an isomorphism. -/
abbrev restrictedRightAdjoint :
    counitIsomorphismSubcategory F G adj ⥤ D :=
  restrictedRightToUnitSubcategory F G adj ⋙
    (unitIsomorphismProperty F G adj).ι

/-- The unit-isomorphism condition is invariant under isomorphism. -/
instance unitIsomorphismProperty_isClosedUnderIsomorphisms :
    (unitIsomorphismProperty F G adj).IsClosedUnderIsomorphisms := sorry

/-- The counit-isomorphism condition is invariant under isomorphism. -/
instance counitIsomorphismProperty_isClosedUnderIsomorphisms :
    (counitIsomorphismProperty F G adj).IsClosedUnderIsomorphisms := sorry

-- Proof sketch: the Stacks notion of “saturated” is retract-closure. If `K` is a retract of `L`
-- and the unit for `L` is an isomorphism, naturality of the adjunction unit shows that the unit
-- for `K` is a retract of an isomorphism, hence an isomorphism.
/-- Lemma 21.28.1 (1): in the abstract adjunction `F ⊣ G` underlying the ringed-topos situation,
the objects `K` for which the unit map `K ⟶ GF(K)` is an isomorphism form a saturated
subcategory, i.e. an object property stable under retracts. -/
@[stacks 0D7Q]
instance unitIsomorphismProperty_isStableUnderRetracts :
    (unitIsomorphismProperty F G adj).IsStableUnderRetracts := sorry

/-- The counit-isomorphism condition is saturated, i.e. stable under retracts. -/
instance counitIsomorphismProperty_isStableUnderRetracts :
    (counitIsomorphismProperty F G adj).IsStableUnderRetracts := sorry

/-- Lemma 21.28.1 (3), canonical owner form: the restriction of the left adjoint to the full
subcategory cut out by the unit-isomorphism condition is fully faithful. -/
@[stacks 0D7Q]
noncomputable instance restrictedLeftAdjoint_fullyFaithful :
    Functor.FullyFaithful (restrictedLeftAdjoint F G adj) := by
  let hι : Functor.FullyFaithful ((counitIsomorphismProperty F G adj).ι) :=
    (counitIsomorphismProperty F G adj).fullyFaithfulι
  letI (K : unitIsomorphismSubcategory F G adj) :
      IsIso ((restrictedAdjunction F G adj).unit.app K) := by
    letI :
        IsIso
          ((unitIsomorphismProperty F G adj).ι.map ((restrictedAdjunction F G adj).unit.app K)) := by
      have hmap :
          (unitIsomorphismProperty F G adj).ι.map ((restrictedAdjunction F G adj).unit.app K) =
            adj.unit.app K.obj := by
        change
          (unitIsomorphismProperty F G adj).ι.map
              ((adj.restrictFullyFaithful
                (unitIsomorphismProperty F G adj).fullyFaithfulι
                (counitIsomorphismProperty F G adj).fullyFaithfulι
                (restrictedLeftCompIso F G adj)
                (restrictedRightCompIso F G adj)).unit.app K) =
            adj.unit.app K.obj
        refine (adj.map_restrictFullyFaithful_unit_app
          (unitIsomorphismProperty F G adj).fullyFaithfulι
          (counitIsomorphismProperty F G adj).fullyFaithfulι
          (restrictedLeftCompIso F G adj)
          (restrictedRightCompIso F G adj)
          K).trans ?_
        erw [Functor.map_id]
        change adj.unit.app K.obj ≫ 𝟙 (G.obj (F.obj K.obj)) ≫
            𝟙 (G.obj ((restrictedLeftToCounitSubcategory F G adj).obj K).obj) =
          adj.unit.app K.obj
        simp [restrictedLeftToCounitSubcategory]
      rw [hmap]
      simpa using (K.property : IsIso (adj.unit.app K.obj))
    exact
      (unitIsomorphismProperty F G adj).fullyFaithfulι.isIso_of_isIso_map
        ((restrictedAdjunction F G adj).unit.app K)
  letI : IsIso (restrictedAdjunction F G adj).unit := NatIso.isIso_of_isIso_app _
  let hres : Functor.FullyFaithful (restrictedLeftToCounitSubcategory F G adj) := by
    simpa using (restrictedAdjunction F G adj).fullyFaithfulLOfIsIsoUnit
  simpa [restrictedLeftAdjoint] using hres.comp hι

-- Proof sketch: for objects `K` and `L` in the unit-isomorphism subcategory, the adjunction gives
-- `Hom(FK, FL) ≃ Hom(K, GFL)`. Since the unit `L ⟶ GFL` is an isomorphism, composition with it
-- identifies the right-hand side with `Hom(K, L)`, giving bijectivity on homs.
/-- Lemma 21.28.1 (3): in the abstract adjunction `F ⊣ G` underlying the ringed-topos situation,
the restriction of the left adjoint to the full subcategory of objects satisfying
`K ⟶ GF(K)` induces bijections on hom-sets. -/
@[stacks 0D7Q]
theorem restrictedLeftAdjoint_bijective_on_homs
    (K L : unitIsomorphismSubcategory F G adj) :
    Function.Bijective
      ((restrictedLeftAdjoint F G adj).map :
        (K ⟶ L) → (F.obj K.obj ⟶ F.obj L.obj)) := by
  let hff : Functor.FullyFaithful (restrictedLeftAdjoint F G adj) :=
    restrictedLeftAdjoint_fullyFaithful F G adj
  simpa [restrictedLeftAdjoint] using hff.map_bijective K L

/-- The restriction of the right adjoint to the counit-isomorphism subcategory is fully
faithful. -/
noncomputable instance restrictedRightAdjoint_fullyFaithful :
    Functor.FullyFaithful (restrictedRightAdjoint F G adj) := by
  let hι : Functor.FullyFaithful ((unitIsomorphismProperty F G adj).ι) :=
    (unitIsomorphismProperty F G adj).fullyFaithfulι
  letI (K : counitIsomorphismSubcategory F G adj) :
      IsIso ((restrictedAdjunction F G adj).counit.app K) := by
    letI :
        IsIso
          ((counitIsomorphismProperty F G adj).ι.map
            ((restrictedAdjunction F G adj).counit.app K)) := by
      have hmap :
          (counitIsomorphismProperty F G adj).ι.map
              ((restrictedAdjunction F G adj).counit.app K) =
            adj.counit.app K.obj := by
        change
          (counitIsomorphismProperty F G adj).ι.map
              ((adj.restrictFullyFaithful
                (unitIsomorphismProperty F G adj).fullyFaithfulι
                (counitIsomorphismProperty F G adj).fullyFaithfulι
                (restrictedLeftCompIso F G adj)
                (restrictedRightCompIso F G adj)).counit.app K) =
            adj.counit.app K.obj
        refine (adj.map_restrictFullyFaithful_counit_app
          (unitIsomorphismProperty F G adj).fullyFaithfulι
          (counitIsomorphismProperty F G adj).fullyFaithfulι
          (restrictedLeftCompIso F G adj)
          (restrictedRightCompIso F G adj)
          K).trans ?_
        erw [Functor.map_id]
        change 𝟙 (F.obj ((restrictedRightToUnitSubcategory F G adj).obj K).obj) ≫
            𝟙 (F.obj (G.obj K.obj)) ≫ adj.counit.app K.obj =
          adj.counit.app K.obj
        simp [restrictedRightToUnitSubcategory]
      rw [hmap]
      simpa using (K.property : IsIso (adj.counit.app K.obj))
    exact
      (counitIsomorphismProperty F G adj).fullyFaithfulι.isIso_of_isIso_map
        ((restrictedAdjunction F G adj).counit.app K)
  letI : IsIso (restrictedAdjunction F G adj).counit := NatIso.isIso_of_isIso_app _
  let hres : Functor.FullyFaithful (restrictedRightToUnitSubcategory F G adj) := by
    simpa using (restrictedAdjunction F G adj).fullyFaithfulROfIsIsoCounit
  simpa [restrictedRightAdjoint] using hres.comp hι

-- Proof sketch: for objects `K` and `L` in the counit-isomorphism subcategory, the adjunction
-- gives `Hom(GK, GL) ≃ Hom(FGK, L)`. Since the counit `FGK ⟶ K` is an isomorphism, composition
-- with it identifies the right-hand side with `Hom(K, L)`, giving bijectivity on homs.
/-- The restriction of the right adjoint to the counit-isomorphism subcategory is bijective on
hom-sets. -/
theorem restrictedRightAdjoint_bijective_on_homs
    (K L : counitIsomorphismSubcategory F G adj) :
    Function.Bijective
      ((restrictedRightAdjoint F G adj).map :
        (K ⟶ L) → (G.obj K.obj ⟶ G.obj L.obj)) := by
  let hff : Functor.FullyFaithful (restrictedRightAdjoint F G adj) :=
    restrictedRightAdjoint_fullyFaithful F G adj
  simpa [restrictedRightAdjoint] using hff.map_bijective K L

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
variable [Pretriangulated C] [Pretriangulated D]
variable (F : D ⥤ C) (G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
variable (adj : F ⊣ G) [adj.IsTriangulated]

-- Proof sketch: `F` and `G` are exact functors of triangulated categories, so the unit natural
-- transformation is compatible with distinguished triangles and shifts. Applying the
-- two-out-of-three formalism to the unit maps shows that the unit-isomorphism condition is
-- triangulated; the associated full subcategory is therefore strictly full.
/-- Lemma 21.28.1 (2): in the abstract triangulated adjunction `F ⊣ G` underlying the
ringed-topos situation, the objects `K` for which the unit map `K ⟶ GF(K)` is an isomorphism
form a triangulated strictly full subcategory of the target category. -/
@[stacks 0D7Q]
instance unitIsomorphismProperty_isTriangulated :
    (unitIsomorphismProperty F G adj).IsTriangulated := sorry

/-- The counit-isomorphism condition defines a triangulated object property. -/
instance counitIsomorphismProperty_isTriangulated :
    (counitIsomorphismProperty F G adj).IsTriangulated := sorry

end

end CategoryTheory
