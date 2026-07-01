import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap12.Lemma_12_19_2
import stacks_project.Chap13.Definition_13_13_1
import stacks_project.Chap13.Lemma_13_10_6
import stacks_project.Chap13.Lemma_13_13_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [Abelian (finiteFilteredObjectCat 𝒜)] [Abelian (finiteFilteredObjectCat ℬ)]
  [Abelian (GradedObject ℤ 𝒜)] [Abelian (GradedObject ℤ ℬ)]
  [HasDerivedCategory (GradedObject ℤ 𝒜)]
  [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))]

/- Domain-style sampling for 13.26.13.2:
- primary domain: bounded-below filtered derived categories and right derived functors along the
  localization from bounded-below filtered homotopy categories.
- sampled owner declarations:
  `DF⁺(𝒜)`,
  `mapBoundedBelowFilteredHomotopyToDerivedBelow`,
  `FQis⁺(𝒜)`,
  `Functor.totalRightDerived`.
- best owner abstraction: the chapter owner `DF⁺(𝒜)`, together with the generic
  `Functor.HasRightDerivedFunctor` and `Functor.totalRightDerived` API applied to the bounded-
  below filtered localization bridge from Lemma `13.13.9`.
- primitive data: the bounded-below homotopy lift
  `mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)` and the source
  localization functor `mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜`.
- derived API: the total right derived functor on the localization and its canonical unit.

Source/core/bridge triage:
- `source-facing`: the filtered right derived functor `RT : DF⁺(\mathcal A) ⥤ DF⁺(\mathcal B)`;
- `core/canonical`: `DF⁺(𝒜)`, `mapBoundedBelowFilteredHomotopyToDerivedBelow`, `FQis⁺(𝒜)`,
  and `Functor.totalRightDerived`;
- `bridge/view`: the specialization of `Functor.totalRightDerived` to the bounded-below filtered
  homotopy functor induced by `T`.

This item is source-facing, but its owner layer is the generic derived-functor API on the chapter
localization model of `DF⁺`; it should therefore expose `RT` by direct specialization of
`Functor.totalRightDerived`, not by a parallel wrapper around a different `DF⁺` model. -/

variable (T : 𝒜 ⥤ₗ ℬ)

local instance : PreservesFiniteLimits T.obj :=
  T.property

local instance : PreservesBinaryBiproducts T.obj :=
  preservesBinaryBiproducts_of_preservesBinaryProducts T.obj

local instance : T.obj.Additive :=
  Functor.additive_of_preservesBinaryBiproducts T.obj

omit [Abelian 𝒜] [Abelian ℬ] [Abelian (finiteFilteredObjectCat 𝒜)]
  [Abelian (finiteFilteredObjectCat ℬ)] [Abelian (GradedObject ℤ 𝒜)]
  [Abelian (GradedObject ℤ ℬ)] [HasDerivedCategory (GradedObject ℤ 𝒜)]
  [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))] in
/-- Helper for 13.26.13.2: applying a left exact functor to each stage of a finite filtration
again gives a monotone family of subobjects. -/
private theorem mapped_filtration_monotone
    {A : 𝒜} (F : DecreasingFiltration A) :
    Monotone (fun p : ℤᵒᵈ ↦ Subobject.mk (T.obj.map (F.obj p).arrow)) := by
  intro p q hpq
  refine Subobject.mk_le_mk_of_comm
    (T.obj.map (Subobject.ofLE (F.obj p) (F.obj q) (F.monotone hpq))) ?_
  have h :=
    congrArg (fun k ↦ T.obj.map k) (Subobject.ofLE_arrow (F.monotone hpq))
  change T.obj.map ((F.obj p).ofLE (F.obj q) (F.monotone hpq) ≫ (F.obj q).arrow) =
      T.obj.map (F.obj p).arrow at h
  rw [Functor.map_comp] at h
  exact h

/-- Helper for 13.26.13.2: the stagewise image filtration obtained from a left exact functor. -/
private def mapped_filtration {A : 𝒜} (F : DecreasingFiltration A) :
    DecreasingFiltration (T.obj.obj A) where
  toFun := fun p ↦ Subobject.mk (T.obj.map (F.obj p).arrow)
  monotone' := mapped_filtration_monotone (T := T) F

/-- Helper for 13.26.13.2: the filtered object obtained by applying `T` to a finite filtered
object stagewise. -/
private def mapped_filtered_object (A : Fil(𝒜)) : Fil(ℬ) where
  obj := T.obj.obj A.obj
  filtration := mapped_filtration (T := T) A.filtration

omit [Abelian 𝒜] [Abelian ℬ] [Abelian (finiteFilteredObjectCat 𝒜)]
  [Abelian (finiteFilteredObjectCat ℬ)] [Abelian (GradedObject ℤ 𝒜)]
  [Abelian (GradedObject ℤ ℬ)] [HasDerivedCategory (GradedObject ℤ 𝒜)]
  [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))] in
/-- Helper for 13.26.13.2: a filtration-preserving morphism stays filtration-preserving after
applying the left exact functor. -/
private theorem mapped_filtered_object_preserves
    {A B : Fil(𝒜)} (f : A ⟶ B) (p : ℤ) :
    ((mapped_filtered_object (T := T) B).filtration p).Factors
      (((mapped_filtered_object (T := T) A).filtration p).arrow ≫ T.obj.map f.hom) := by
  let u := (B.filtration p).factorThru ((A.filtration p).arrow ≫ f.hom) (f.preserves p)
  let e := Subobject.underlyingIso (T.obj.map (A.filtration p).arrow)
  change (Subobject.mk (T.obj.map (B.filtration p).arrow)).Factors
    ((Subobject.mk (T.obj.map (A.filtration p).arrow)).arrow ≫ T.obj.map f.hom)
  rw [Subobject.mk_factors_iff]
  refine ⟨e.hom ≫ T.obj.map u, ?_⟩
  have hu :
      T.obj.map u ≫ T.obj.map (B.filtration p).arrow =
        T.obj.map (A.filtration p).arrow ≫ T.obj.map f.hom := by
    have h :=
      congrArg (fun k ↦ T.obj.map k)
        (Subobject.factorThru_arrow (B.filtration p)
          ((A.filtration p).arrow ≫ f.hom) (f.preserves p))
    change T.obj.map
        ((B.filtration p).factorThru ((A.filtration p).arrow ≫ f.hom) (f.preserves p) ≫
          (B.filtration p).arrow) =
        T.obj.map ((A.filtration p).arrow ≫ f.hom) at h
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  calc
    (e.hom ≫ T.obj.map u) ≫ T.obj.map (B.filtration p).arrow
        = e.hom ≫ (T.obj.map u ≫ T.obj.map (B.filtration p).arrow) := by
            simp [Category.assoc]
    _ = e.hom ≫ (T.obj.map (A.filtration p).arrow ≫ T.obj.map f.hom) := by rw [hu]
    _ = (e.hom ≫ T.obj.map (A.filtration p).arrow) ≫ T.obj.map f.hom := by
          simp [Category.assoc]
    _ = (Subobject.mk (T.obj.map (A.filtration p).arrow)).arrow ≫ T.obj.map f.hom := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk]

omit [Abelian 𝒜] [Abelian ℬ] [Abelian (finiteFilteredObjectCat 𝒜)]
  [Abelian (finiteFilteredObjectCat ℬ)] [Abelian (GradedObject ℤ 𝒜)]
  [Abelian (GradedObject ℤ ℬ)] [HasDerivedCategory (GradedObject ℤ 𝒜)]
  [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))] in
/-- Helper for 13.26.13.2: a top filtration stage stays top after applying `T`. -/
private theorem mapped_top_stage_eq_top
    {A : 𝒜} (F : DecreasingFiltration A) {p : ℤ} (h : F.obj p = ⊤) :
    Subobject.mk (T.obj.map (F.obj p).arrow) = ⊤ := by
  rw [h]
  exact Subobject.mk_eq_top_of_isIso (T.obj.map (⊤ : Subobject A).arrow)

omit [Abelian (finiteFilteredObjectCat 𝒜)] [Abelian (finiteFilteredObjectCat ℬ)]
  [Abelian (GradedObject ℤ 𝒜)] [Abelian (GradedObject ℤ ℬ)]
  [HasDerivedCategory (GradedObject ℤ 𝒜)] [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))] in
/-- Helper for 13.26.13.2: a zero filtration stage stays zero after applying `T`. -/
private theorem mapped_bot_stage_eq_bot
    {A : 𝒜} (F : DecreasingFiltration A) {p : ℤ} (h : F.obj p = ⊥) :
    Subobject.mk (T.obj.map (F.obj p).arrow) = ⊥ := by
  rw [h]
  rw [Subobject.mk_eq_bot_iff_zero]
  simp [Subobject.bot_arrow]

/-- Helper for 13.26.13.2: the stagewise action of `T` defines a functor on filtered objects. -/
private def mapped_filtered_object_functor :
    Fil(𝒜) ⥤ Fil(ℬ) where
  obj A := mapped_filtered_object (T := T) A
  map f :=
    { hom := T.obj.map f.hom
      preserves := mapped_filtered_object_preserves (T := T) f }
  map_id A := by
    apply FilteredObject.Hom.ext
    change T.obj.map (𝟙 A.obj) = 𝟙 (T.obj.obj A.obj)
    exact T.obj.map_id A.obj
  map_comp f g := by
    apply FilteredObject.Hom.ext
    change T.obj.map (f.hom ≫ g.hom) = T.obj.map f.hom ≫ T.obj.map g.hom
    exact T.obj.map_comp f.hom g.hom

omit [Abelian (finiteFilteredObjectCat 𝒜)] [Abelian (finiteFilteredObjectCat ℬ)]
  [Abelian (GradedObject ℤ 𝒜)] [Abelian (GradedObject ℤ ℬ)]
  [HasDerivedCategory (GradedObject ℤ 𝒜)] [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))] in
/-- Helper for 13.26.13.2: finite filtrations remain finite after applying `T`. -/
private theorem mapped_filtered_object_isFinite
    {A : Fil(𝒜)} (hA : A.IsFinite) :
    (mapped_filtered_object (T := T) A).IsFinite := by
  rcases hA with ⟨n, m, hn, hm⟩
  refine ⟨n, m, ?_, ?_⟩
  · simpa [mapped_filtered_object, mapped_filtration] using
      mapped_top_stage_eq_top (T := T) A.filtration hn
  · simpa [mapped_filtered_object, mapped_filtration] using
      mapped_bot_stage_eq_bot (T := T) A.filtration hm

/-- Helper for 13.26.13.2: the left exact functor `T` restricts to finite filtered objects. -/
abbrev leftExactMapFiniteFilteredObjectCat :
    Fil^f(𝒜) ⥤ Fil^f(ℬ) :=
  ObjectProperty.lift (FilteredObject.IsFinite : ObjectProperty (Fil(ℬ)))
    (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
      mapped_filtered_object_functor (T := T))
    (fun A ↦ mapped_filtered_object_isFinite (T := T) A.property)

/-- Helper for 13.26.13.2: the induced functor on filtered objects is additive. -/
private instance mapped_filtered_object_functor_additive :
    (mapped_filtered_object_functor (T := T)).Additive := by
  constructor
  intro A B f g
  apply FilteredObject.Hom.ext
  change T.obj.map (f.hom + g.hom) = T.obj.map f.hom + T.obj.map g.hom
  exact Functor.map_add T.obj

/-- Helper for 13.26.13.2: the restriction of `T` to finite filtered objects is additive. -/
instance leftExactMapFiniteFilteredObjectCat_additive :
    (leftExactMapFiniteFilteredObjectCat (T := T)).Additive := by
  letI : Preadditive (Fil(𝒜)) := FilteredObject.filteredObject_preadditive
  letI : Preadditive (Fil(ℬ)) := FilteredObject.filteredObject_preadditive
  infer_instance

local notation "Tplus" => mapBoundedBelowHomotopyCategory (leftExactMapFiniteFilteredObjectCat T)
local notation "QFiltA" => mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜
local notation "QFiltB" => mapBoundedBelowFilteredHomotopyToDerivedBelow ℬ

local notation "W" => FQis⁺(𝒜)

variable
  [Functor.HasRightDerivedFunctor
    (mapBoundedBelowHomotopyCategory (leftExactMapFiniteFilteredObjectCat T) ⋙
      mapBoundedBelowFilteredHomotopyToDerivedBelow ℬ)
    (FQis⁺(𝒜))]

private instance qFiltA_isLocalization : Functor.IsLocalization QFiltA W :=
  mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization

/- Canonical owner recall: once the filtered homotopy functor into `DF⁺(\mathcal B)` has a right
derived functor along the source localization
`mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜`, the filtered right
derived functor is the generic owner `Functor.totalRightDerived`. -/
recall Functor.totalRightDerived

/- In the bounded-below filtered situation, this owner is the direct specialization
`Functor.totalRightDerived (Tplus ⋙ QFiltB) QFiltA W : DF⁺(𝒜) ⥤ DF⁺(ℬ)`. -/
#check Functor.totalRightDerived (Tplus ⋙ QFiltB) QFiltA W

/- The right-derived structure of that canonical functor is carried by the generic owner unit
`Functor.totalRightDerivedUnit`. -/
recall Functor.totalRightDerivedUnit

/- Its canonical unit is the specialization
`Functor.totalRightDerivedUnit (Tplus ⋙ QFiltB) QFiltA W :
  Tplus ⋙ QFiltB ⟶ QFiltA ⋙ Functor.totalRightDerived (Tplus ⋙ QFiltB) QFiltA W`. -/
#check Functor.totalRightDerivedUnit (Tplus ⋙ QFiltB) QFiltA W

/- 13.26.13.2 is the bounded-below filtered specialization of the canonical owners
`Functor.totalRightDerived` and `Functor.totalRightDerivedUnit` above. -/

/-- 13.26.13.2: the bounded-below filtered right derived functor associated to `T`. -/
abbrev filteredBoundedBelowRightDerivedFunctor :=
  -- This is exactly the canonical owner specialized to the bounded-below filtered localization.
  Functor.totalRightDerived (Tplus ⋙ QFiltB) QFiltA W

end

end CategoryTheory
