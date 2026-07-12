import Mathlib
import StacksProject_2024.Chap12.Lemma_12_19_2
import StacksProject_2024.Chap13.Definition_13_13_1
import StacksProject_2024.Chap13.Lemma_13_10_6

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory ZeroObject

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [HasZeroObject 𝒜] [HasZeroObject ℬ]

/- Domain-style sampling for 13.26.13.1:
- primary domain: filtered objects, the finite filtered full subcategory, and the canonical
  bounded-below homotopy lift of an additive functor;
- inspected owner declarations:
  `FilteredObject`,
  `finiteFilteredObjectCat`,
  `(FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))).ι`,
  `mapBoundedBelowHomotopyCategory`;
- best owner abstractions: the chapter full-subcategory owner `finiteFilteredObjectCat 𝒜` with
  notation `Fil^f(𝒜)`, together with the canonical homotopy lift
  `mapBoundedBelowHomotopyCategory` for the `K⁺`-level functor;
- primitive data in this file: a left exact functor `T : 𝒜 ⥤ₗ ℬ` and the induced stagewise image
  filtration whose `p`-th stage is the image of `T(F^{p} A ⟶ A)`, used internally to build the
  finite filtered functor;
- derived API: the induced functor on `Fil^f(𝒜)` and the final `K⁺` statement as a direct use of
  the canonical bounded-below homotopy lift.

Source/core/bridge triage:
- `source-facing`: the action of `T` on `Fil^f`;
- `core/canonical`: `FilteredObject`, `finiteFilteredObjectCat`, and
  `mapBoundedBelowHomotopyCategory`;
- `bridge/view`: the internal stagewise action on ambient filtered objects used to build the
  restriction to the finite full subcategory.

The `K⁺` construction is therefore not given a second owner name here: once
`mapFiniteFilteredObjectCat T` is built, the bounded-below homotopy functor is the canonical
`mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)`. -/

-- Proof sketch: if `p ≤ q`, then `F^q ⟶ A` factors through `F^p ⟶ A`; applying a left exact
-- functor preserves the monomorphisms defining these subobjects, so the mapped stages define a
-- monotone map `ℤᵒᵈ → Subobject (T.obj A)`.
private theorem mapFiltrationMonotone (T : 𝒜 ⥤ₗ ℬ)
    {A : 𝒜} (F : DecreasingFiltration A) :
    Monotone (fun p : ℤᵒᵈ ↦ Subobject.mk (T.obj.map (F.obj p).arrow)) := by
  intro p q hpq
  -- Map the canonical inclusion `F^p ↪ F^q` to compare the two mapped stages.
  refine Subobject.mk_le_mk_of_comm
    (T.obj.map (Subobject.ofLE (F.obj p) (F.obj q) (F.monotone hpq))) ?_
  rw [← T.obj.map_comp, Subobject.ofLE_arrow]

private def mapFiltration (T : 𝒜 ⥤ₗ ℬ) {A : 𝒜} (F : DecreasingFiltration A) :
    DecreasingFiltration (T.obj.obj A) where
  toFun := fun p ↦ Subobject.mk (T.obj.map (F.obj p).arrow)
  monotone' := mapFiltrationMonotone T F

private def mapFilteredObject (T : 𝒜 ⥤ₗ ℬ) (A : Fil(𝒜)) :
    Fil(ℬ) where
  obj := T.obj.obj A.obj
  filtration := mapFiltration T A.filtration

-- Proof sketch: a filtered morphism sends `F^p A` into `F^p B`; applying `T` to the resulting
-- commutative square of monomorphisms gives the required factorization through the mapped target
-- stage.
private theorem mapFilteredObject_preserves (T : 𝒜 ⥤ₗ ℬ)
    {A B : Fil(𝒜)} (f : A ⟶ B) (p : ℤ) :
    ((mapFilteredObject T B).filtration p).Factors
      (((mapFilteredObject T A).filtration p).arrow ≫ T.obj.map f.hom) := by
  let u := (B.filtration p).factorThru ((A.filtration p).arrow ≫ f.hom) (f.preserves p)
  let e := Subobject.underlyingIso (T.obj.map (A.filtration p).arrow)
  -- Rewrite the target stage as an explicit mapped subobject and give the mapped witness.
  change (Subobject.mk (T.obj.map (B.filtration p).arrow)).Factors
    ((Subobject.mk (T.obj.map (A.filtration p).arrow)).arrow ≫ T.obj.map f.hom)
  rw [Subobject.mk_factors_iff]
  refine ⟨e.hom ≫ T.obj.map u, ?_⟩
  -- Apply `T` to the original stagewise factorization and transport along the chosen representative.
  have hu :
      T.obj.map u ≫ T.obj.map (B.filtration p).arrow =
        T.obj.map (A.filtration p).arrow ≫ T.obj.map f.hom := by
    dsimp [u]
    rw [← T.obj.map_comp, Subobject.factorThru_arrow, T.obj.map_comp]
  calc
    (e.hom ≫ T.obj.map u) ≫ T.obj.map (B.filtration p).arrow
        = e.hom ≫ (T.obj.map u ≫ T.obj.map (B.filtration p).arrow) := by
            simp [Category.assoc]
    _ = e.hom ≫ (T.obj.map (A.filtration p).arrow ≫ T.obj.map f.hom) := by rw [hu]
    _ = (e.hom ≫ T.obj.map (A.filtration p).arrow) ≫ T.obj.map f.hom := by
          simp [Category.assoc]
    _ = (Subobject.mk (T.obj.map (A.filtration p).arrow)).arrow ≫ T.obj.map f.hom := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk]

/-- Helper for 13.26.13.1: a mapped top filtration stage remains the top subobject. -/
private theorem mapped_stage_eq_top_of_eq_top (T : 𝒜 ⥤ₗ ℬ)
    {A : 𝒜} (F : DecreasingFiltration A) {p : ℤ} (h : F.obj p = ⊤) :
    Subobject.mk (T.obj.map (F.obj p).arrow) = ⊤ := by
  -- After rewriting to the top stage, the inclusion arrow is an isomorphism and stays so under `T`.
  rw [h]
  exact Subobject.mk_eq_top_of_isIso (T.obj.map (⊤ : Subobject A).arrow)

/-- Helper for 13.26.13.1: a mapped zero filtration stage remains the zero subobject. -/
private theorem mapped_stage_eq_bot_of_eq_bot (T : 𝒜 ⥤ₗ ℬ)
    {A : 𝒜} (F : DecreasingFiltration A) {p : ℤ} (h : F.obj p = ⊥) :
    Subobject.mk (T.obj.map (F.obj p).arrow) = ⊥ := by
  letI : HasZeroMorphisms 𝒜 := HasZeroObject.zeroMorphismsOfZeroObject (C := 𝒜)
  letI : HasZeroMorphisms ℬ := HasZeroObject.zeroMorphismsOfZeroObject (C := ℬ)
  -- After rewriting to the bottom stage, the arrow is zero and remains zero after applying `T`.
  rw [h]
  rw [Subobject.mk_eq_bot_iff_zero]
  simp [Subobject.bot_arrow]

private def mapFilteredObjectFunctor (T : 𝒜 ⥤ₗ ℬ) :
    Fil(𝒜) ⥤ Fil(ℬ) where
  obj A := mapFilteredObject T A
  map f :=
    { hom := T.obj.map f.hom
      preserves := mapFilteredObject_preserves T f }
  map_id A := by
    apply FilteredObject.Hom.ext
    change T.obj.map (𝟙 A.obj) = 𝟙 (T.obj.obj A.obj)
    exact T.obj.map_id A.obj
  map_comp f g := by
    apply FilteredObject.Hom.ext
    change T.obj.map (f.hom ≫ g.hom) = T.obj.map f.hom ≫ T.obj.map g.hom
    exact T.obj.map_comp f.hom g.hom

-- Proof sketch: if `F^a A = ⊤` and `F^b A = ⊥`, then after applying `T` to the corresponding
-- monomorphisms the stages at `a` and `b` remain the top and bottom subobjects of `T(A)`.
/-- A left exact functor sends finite filtrations to finite filtrations. -/
private theorem mapFilteredObject_isFinite (T : 𝒜 ⥤ₗ ℬ)
    {A : Fil(𝒜)} (hA : A.IsFinite) :
    (mapFilteredObject T A).IsFinite := by
  rcases hA with ⟨n, m, hn, hm⟩
  -- Reuse the same endpoint indices and transport the top and bottom stage equalities through `T`.
  refine ⟨n, m, ?_, ?_⟩
  · simpa [mapFilteredObject, mapFiltration] using
      mapped_stage_eq_top_of_eq_top T A.filtration hn
  · simpa [mapFilteredObject, mapFiltration] using
      mapped_stage_eq_bot_of_eq_bot T A.filtration hm

/-- The induced functor on the full subcategory `Fil^f(𝒜)` of finite filtered objects. -/
abbrev mapFiniteFilteredObjectCat (T : 𝒜 ⥤ₗ ℬ) :
    Fil^f(𝒜) ⥤ Fil^f(ℬ) :=
  ObjectProperty.lift (FilteredObject.IsFinite : ObjectProperty (Fil(ℬ)))
    (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
      mapFilteredObjectFunctor T)
    (fun A ↦ mapFilteredObject_isFinite T A.property)

section Additive

variable [Preadditive 𝒜] [Preadditive ℬ] [HasBinaryBiproducts 𝒜]

private instance mapFilteredObjectFunctor_additive (T : 𝒜 ⥤ₗ ℬ) :
    (mapFilteredObjectFunctor T).Additive := by
  letI : T.obj.Additive := ((AdditiveFunctor.ofLeftExact 𝒜 ℬ).obj T).property
  constructor
  intro A B f g
  apply FilteredObject.Hom.ext
  change T.obj.map (f.hom + g.hom) = T.obj.map f.hom + T.obj.map g.hom
  exact Functor.map_add T.obj

/-- The induced functor on finite filtered objects is additive. -/
instance mapFiniteFilteredObjectCat_additive
    (T : 𝒜 ⥤ₗ ℬ) :
    (mapFiniteFilteredObjectCat T).Additive := by
  letI : Preadditive (Fil(𝒜)) := FilteredObject.filteredObject_preadditive
  letI : Preadditive (Fil(ℬ)) := FilteredObject.filteredObject_preadditive
  infer_instance

end Additive

section

variable [Preadditive 𝒜] [Preadditive ℬ]
  [HasBinaryBiproducts 𝒜]
  [HasBinaryBiproducts (Fil^f(𝒜))]
  [HasBinaryBiproducts (Fil^f(ℬ))]
variable (T : 𝒜 ⥤ₗ ℬ)

/- 13.26.13.1: once the left exact functor `T` has been restricted to
`mapFiniteFilteredObjectCat T : Fil^f(𝒜) ⥤ Fil^f(ℬ)`, the induced functor
`K^+(Fil^f(𝒜)) ⥤ K^+(Fil^f(ℬ))` is exactly the canonical bounded-below homotopy lift. Its
public surface only needs the source biproduct hypothesis that makes the induced functor additive
and the filtered-category biproduct hypotheses required by the owner
`mapBoundedBelowHomotopyCategory`; the zero-object structure on `Fil^f` is already owned upstream
by `Definition_13_13_1`. -/
#check
  (mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T) :
    K⁺(Fil^f(𝒜)) ⥤ K⁺(Fil^f(ℬ)))

end

end CategoryTheory
