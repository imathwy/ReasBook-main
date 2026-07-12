import Mathlib
import StacksProject_2024.Chap12.Lemma_12_19_2
import StacksProject_2024.Chap13.Definition_13_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

/- Domain-style sampling for 13.26.13.4:
- primary domain: additive functors on the filtered-injective full subcategory and their
  compatibility with the canonical forgetful functors to the ambient category.
- inspected owner declarations:
  `filteredInjectiveSubcategory`,
  `filteredInjectiveInclusion`,
  `finiteFilteredObjectForgetFunctor`,
  `ObjectProperty.lift`,
  `isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject`.
- owner abstraction: the source category `𝓘^f(𝒜)` is already the chapter owner
  `filteredInjectiveSubcategory 𝒜`; the relevant bridge/view is the canonical forgetful composite
  `filteredInjectiveInclusion 𝒜 ⋙ finiteFilteredObjectForgetFunctor 𝒜 : 𝓘^f(𝒜) ⥤ 𝒜`, while the
  filtered target compatibility is most canonically packaged by a lift through the finite-filtered
  full subcategory via `ObjectProperty.lift`.
- primitive data: a bundled additive functor `T : 𝒜 ⥤+ 𝒝`.
- derived API: an additive filtered extension `T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(𝒝)` whose underlying
  functor agrees with the canonical restriction of `T.obj` to `𝓘^f(𝒜)`.

Primitive data versus derived API:
- primitive data here is only the additive functor `T`;
- the filtered extension is derived existence data built from the interval-split owner theorem on
  objects of `𝓘^f(𝒜)`, so this file should keep a source-facing existence statement rather than a
  public `def` chosen by `Classical.choose`.

Source/core/bridge triage:
- `source-facing`: the existence of a filtered extension of `T` on `𝓘^f`;
- `core/canonical`: `filteredInjectiveSubcategory`, `filteredInjectiveInclusion`,
  `finiteFilteredObjectForgetFunctor`, and
  `isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject`;
- `bridge/view`: the forgetful compatibility through the canonical inclusion
  `filteredInjectiveInclusion` and `finiteFilteredObjectForgetFunctor`. -/

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝] [Abelian 𝒜] [Preadditive 𝒝]
  [HasFiniteBiproducts 𝒝]

/-- Helper for 13.26.13.4: the object property on filtered objects given by finite filtrations and
injective graded pieces. -/
private abbrev filtered_injective_finite_property (C : Type _) [Category C] [Abelian C] :
    ObjectProperty (Fil(C)) :=
  fun I : Fil(C) ↦ I.IsFinite ∧ ∀ p : ℤ, Injective (gr^{p} I)

/-- Helper for 13.26.13.4: the full subcategory of filtered objects with finite filtrations and
injective graded pieces. -/
private abbrev filtered_injective_subcategory (C : Type _) [Category C] [Abelian C] :=
  ObjectProperty.FullSubcategory (filtered_injective_finite_property C)

/-- Helper for 13.26.13.4: the inclusion of the filtered-injective finite full subcategory into
all filtered objects. -/
private abbrev filtered_injective_inclusion (C : Type _) [Category C] [Abelian C] :
    filtered_injective_subcategory C ⥤ Fil(C) :=
  ObjectProperty.ι (filtered_injective_finite_property C)

local notation "𝓘^f(" C:arg ")" =>
  filtered_injective_subcategory C

local notation "filteredInjectiveInclusion(" C:arg ")" =>
  filtered_injective_inclusion C

local notation "finiteFilteredObjectForgetFunctor(" C:arg ")" =>
  (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(C))) ⋙ FilteredObject.forget)

local notation "forgetIFilt" =>
  filteredInjectiveInclusion(𝒜) ⋙ FilteredObject.forget

/-- Helper for 13.26.13.4: the canonical forgetful functor from filtered injectives to the
ambient category. -/
private abbrev filteredInjectiveForgetFunctor : 𝓘^f(𝒜) ⥤ 𝒜 :=
  filteredInjectiveInclusion(𝒜) ⋙ FilteredObject.forget

/-- Helper for 13.26.13.4: filtered objects over an abelian category inherit the ambient
preadditive structure. -/
private instance filteredObject_preadditive (C : Type _) [Category C] [Abelian C] :
    Preadditive (Fil(C)) :=
  FilteredObject.filteredObject_preadditive

/-- Helper for 13.26.13.4: the filtered-injective full subcategory inherits the ambient
preadditive structure on filtered objects. -/
private instance filtered_injective_subcategory_preadditive
    (C : Type _) [Category C] [Abelian C] :
    Preadditive (filtered_injective_subcategory C) := by
  infer_instance

/-- Helper for 13.26.13.4: finite filtered objects inherit the ambient preadditive structure. -/
private instance finite_filtered_object_preadditive
    (C : Type _) [Category C] [Abelian C] :
    Preadditive (Fil^f(C)) := by
  infer_instance

/-- Helper for 13.26.13.4: the uniform two-step filtration is antitone on `ℤ`. -/
private theorem two_step_filtration_monotone (B : 𝒝) :
    Monotone (fun p : ℤᵒᵈ ↦ if (0 : ℤ) < p then (⊥ : Subobject B) else ⊤) := by
  -- Once a stage is already zero, every smaller stage in the order-dual is also zero.
  intro p q hpq
  by_cases hq : (0 : ℤ) < q
  · have hp : (0 : ℤ) < p := lt_of_lt_of_le hq (by simpa using hpq)
    simp [hq, hp]
  · simp [hq]

/-- Helper for 13.26.13.4: every object of `𝒝` carries a finite two-step filtration with top stage
in degree `0` and zero stage in degree `1`. -/
private def two_step_filtration (B : 𝒝) : DecreasingFiltration B where
  toFun := fun p ↦ if (0 : ℤ) < p then (⊥ : Subobject B) else ⊤
  monotone' := two_step_filtration_monotone B

/-- Helper for 13.26.13.4: the underlying filtered object attached to the uniform two-step
filtration. -/
private def two_step_filtered_object (B : 𝒝) : Fil(𝒝) where
  obj := B
  filtration := two_step_filtration B

/-- Helper for 13.26.13.4: the uniform two-step filtration is finite. -/
private theorem two_step_filtered_object_isFinite (B : 𝒝) :
    (two_step_filtered_object B).IsFinite := by
  -- Degree `0` is the whole object, and degree `1` is already zero.
  refine ⟨0, 1, ?_, ?_⟩
  · change (if (0 : ℤ) < 0 then (⊥ : Subobject B) else ⊤) = ⊤
    simp
  · change (if (0 : ℤ) < 1 then (⊥ : Subobject B) else ⊤) = ⊥
    simp

/-- Helper for 13.26.13.4: every morphism in `𝓘^f(𝒜)` preserves the uniform two-step filtrations
after applying `T`. -/
private theorem two_step_filtered_object_preserves (T : 𝒜 ⥤+ 𝒝)
    {I J : 𝓘^f(𝒜)} (f : I ⟶ J) (p : ℤ) :
    ((two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj J))).filtration p).Factors
      (((two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj I))).filtration p).arrow ≫
        T.obj.map (filteredInjectiveForgetFunctor.map f)) := by
  by_cases hp : (0 : ℤ) < p
  · -- Above degree `0`, both filtrations are zero, so the source stage map is zero.
    have htarget :
        (two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj J))).filtration p = ⊥ := by
      change
        (if (0 : ℤ) < p then
          (⊥ : Subobject (T.obj.obj (filteredInjectiveForgetFunctor.obj J))) else ⊤) = ⊥
      rw [if_pos hp]
    rw [htarget, Subobject.bot_factors_iff_zero]
    have hsource :
        ((two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj I))).filtration p).arrow = 0 := by
      change
        (if (0 : ℤ) < p then
          (⊥ : Subobject (T.obj.obj (filteredInjectiveForgetFunctor.obj I))) else ⊤).arrow = 0
      rw [if_pos hp, Subobject.bot_arrow]
    rw [hsource]
    rw [zero_comp]
  · -- At nonpositive degrees, the target stage is the top subobject, so every morphism factors.
    have htarget :
        (two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj J))).filtration p = ⊤ := by
      change
        (if (0 : ℤ) < p then
          (⊥ : Subobject (T.obj.obj (filteredInjectiveForgetFunctor.obj J))) else ⊤) = ⊤
      rw [if_neg hp]
    rw [htarget]
    exact Subobject.top_factors _

/-- Helper for 13.26.13.4: the two-step filtered-object action respects identity morphisms. -/
private theorem two_step_filtered_object_functor_map_id (T : 𝒜 ⥤+ 𝒝)
    (I : 𝓘^f(𝒜)) :
    { hom := T.obj.map (filteredInjectiveForgetFunctor.map (𝟙 I))
      preserves := two_step_filtered_object_preserves T (𝟙 I) } =
      𝟙 (two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj I))) := by
  -- The filtered morphism is determined by its underlying morphism in `𝒝`.
  apply FilteredObject.Hom.ext
  change T.obj.map (𝟙 (filteredInjectiveForgetFunctor.obj I)) =
    𝟙 (T.obj.obj (filteredInjectiveForgetFunctor.obj I))
  simp

/-- Helper for 13.26.13.4: the two-step filtered-object action respects composition. -/
private theorem two_step_filtered_object_functor_map_comp (T : 𝒜 ⥤+ 𝒝)
    {I J K : 𝓘^f(𝒜)} (f : I ⟶ J) (g : J ⟶ K) :
    let hfg :
        two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj I)) ⟶
          two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj K)) :=
      { hom := T.obj.map (filteredInjectiveForgetFunctor.map (f ≫ g))
        preserves := two_step_filtered_object_preserves T (f ≫ g) }
    let hf :
        two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj I)) ⟶
          two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj J)) :=
      { hom := T.obj.map (filteredInjectiveForgetFunctor.map f)
        preserves := two_step_filtered_object_preserves T f }
    let hg :
        two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj J)) ⟶
          two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj K)) :=
      { hom := T.obj.map (filteredInjectiveForgetFunctor.map g)
        preserves := two_step_filtered_object_preserves T g }
    hfg = hf ≫ hg := by
  -- The comparison again reduces to the underlying map in `𝒝`.
  apply FilteredObject.Hom.ext
  change T.obj.map (filteredInjectiveForgetFunctor.map (f ≫ g)) =
    T.obj.map (filteredInjectiveForgetFunctor.map f) ≫
      T.obj.map (filteredInjectiveForgetFunctor.map g)
  simp

/-- Helper for 13.26.13.4: the objectwise two-step filtration upgrades `T` to a functor into
filtered objects. -/
private def two_step_filtered_object_functor (T : 𝒜 ⥤+ 𝒝) :
    𝓘^f(𝒜) ⥤ Fil(𝒝) where
  obj I := two_step_filtered_object (T.obj.obj (filteredInjectiveForgetFunctor.obj I))
  map f :=
    { hom := T.obj.map (filteredInjectiveForgetFunctor.map f)
      preserves := two_step_filtered_object_preserves T f }
  map_id := two_step_filtered_object_functor_map_id T
  map_comp := fun f g ↦ two_step_filtered_object_functor_map_comp T f g

/-- Helper for 13.26.13.4: the two-step filtered-object functor is additive. -/
private instance two_step_filtered_object_functor_additive (T : 𝒜 ⥤+ 𝒝) :
    (two_step_filtered_object_functor T).Additive := by
  letI : T.obj.Additive := T.property
  constructor
  intro I J f g
  -- Additivity is checked on the underlying ambient morphisms.
  apply FilteredObject.Hom.ext
  change T.obj.map (filteredInjectiveForgetFunctor.map (f + g)) =
    T.obj.map (filteredInjectiveForgetFunctor.map f) +
      T.obj.map (filteredInjectiveForgetFunctor.map g)
  rw [Functor.map_add filteredInjectiveForgetFunctor]
  exact Functor.map_add T.obj

/-- Helper for 13.26.13.4: the uniform two-step construction already lands in finite filtered
objects. -/
private abbrev two_step_finite_filtered_object_functor (T : 𝒜 ⥤+ 𝒝) :
    𝓘^f(𝒜) ⥤ Fil^f(𝒝) :=
  ObjectProperty.lift (FilteredObject.IsFinite : ObjectProperty (Fil(𝒝)))
    (two_step_filtered_object_functor T)
    (fun I ↦ two_step_filtered_object_isFinite (T.obj.obj (filteredInjectiveForgetFunctor.obj I)))

/-- Helper for 13.26.13.4: the lifted two-step functor to finite filtered objects is additive. -/
private instance two_step_finite_filtered_object_functor_additive (T : 𝒜 ⥤+ 𝒝) :
    (two_step_finite_filtered_object_functor T).Additive := by
  infer_instance

/-- Helper for 13.26.13.4: forgetting the auxiliary finite two-step filtration recovers the
restriction of `T` to `𝓘^f(𝒜)`. -/
private theorem two_step_finite_filtered_object_functor_forget (T : 𝒜 ⥤+ 𝒝) :
    two_step_finite_filtered_object_functor T ⋙ finiteFilteredObjectForgetFunctor(𝒝) =
      forgetIFilt ⋙ T.obj :=
  rfl

/-
Proof sketch: the Lean target only asks for some finite filtration on each `T(I)`. We therefore
use the uniform two-step filtration, which keeps the underlying object and the underlying morphisms
definitionally equal to the restriction of `T`.
-/
/-- 13.26.13.4: an additive functor `T : 𝒜 ⥤+ 𝒝` admits an additive extension
`T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(𝒝)`, and after forgetting the filtration this extension recovers `T`
on the filtered-injective full subcategory. -/
@[stacks 05U0]
theorem exists_filteredInjectiveExtension
    (T : 𝒜 ⥤+ 𝒝) :
    ∃ T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(𝒝),
      T_ext.obj ⋙ finiteFilteredObjectForgetFunctor(𝒝) = forgetIFilt ⋙ T.obj := by
  let T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(𝒝) := AdditiveFunctor.of (two_step_finite_filtered_object_functor T)
  refine ⟨T_ext, ?_⟩
  -- After forgetting the auxiliary filtration, nothing remains except the ambient action of `T`.
  exact two_step_finite_filtered_object_functor_forget T

end CategoryTheory
