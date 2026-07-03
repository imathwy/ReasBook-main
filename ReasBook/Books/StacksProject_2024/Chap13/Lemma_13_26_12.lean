import Mathlib
import StacksProject_2024.Chap13.Lemma_13_10_6
import StacksProject_2024.Chap13.Lemma_13_13_3
import StacksProject_2024.Chap13.Lemma_13_13_9
import StacksProject_2024.Chap13.Lemma_13_26_5
import StacksProject_2024.Chap13.Proposition_13_23_1
import StacksProject_2024.Chap13.Situation_13_15_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open FilteredObject
open DerivedCategory.TStructure
open scoped CategoryTheory ZeroObject

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.26.12`.
- primary domain: bounded-below filtered derived categories, filtered injective finite filtered
  objects, and the graded-piece / forgetful comparison functors into `D⁺(𝒜)`;
- sampled owner declarations:
  `IsFilteredInjective`,
  `mapBoundedBelowHomotopyCategory`,
  `mapHomotopyCategoryToDerived`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `finiteFilteredObjectAssociatedGradedFunctor`;
- best owner abstraction: the filtered-injective source category is the full subcategory cut out by
  the chapter owner `IsFilteredInjective`, while the bounded-below homotopy and derived lifts are
  already owned upstream by `mapBoundedBelowHomotopyCategory` and
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`;
- primitive data: the full subcategory `filteredInjectiveSubcategory 𝒜` and the canonical
  associated-graded / forgetful functors on `Fil^f(𝒜)`;
- derived API: the source-facing comparison functor
  `K^+(filteredInjectiveSubcategory 𝒜) ⥤ DF⁺(𝒜)` and its graded-piece / forgetful compatibilities.

Source/core/bridge triage:
- `source-facing`: the comparison functor of Lemma `13.26.12` and its two compatibilities;
- `core/canonical`: `IsFilteredInjective`, `filteredInjectiveSubcategory`,
  `filteredInjectiveInclusion`, `mapBoundedBelowHomotopyCategory`,
  `mapHomotopyCategoryToDerived`, `mapBoundedBelowHomotopyCategoryToDerivedBelow`, and
  `finiteFilteredObjectAssociatedGradedFunctor`;
- `bridge/view`: the full subcategory `filteredInjectiveSubcategory 𝒜` and the induced functors on
  bounded-below homotopy categories. -/

section GradedPieceFunctor

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

variable [Abelian (finiteFilteredObjectCat 𝒜)]

private instance finiteFilteredObjectGradedPieceFunctor_additive (p : ℤ) :
    ((finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙
      GradedObject.eval p : finiteFilteredObjectCat 𝒜 ⥤ 𝒜)).Additive := by
  infer_instance

end GradedPieceFunctor

section FilteredInjectiveSubcategoryInstances

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "IFiltProp" => (IsFilteredInjective : ObjectProperty FilF)

private instance filteredInjective_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms IFiltProp where
  of_iso e hI := by
    refine ⟨fun p ↦ ?_⟩
    let G : FilF ⥤ 𝒜 := finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙ GradedObject.eval p
    simpa [G] using Injective.of_iso (Functor.mapIso G e) (hI.injective p)

private instance filteredInjective_containsZero :
    ObjectProperty.ContainsZero IFiltProp where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    refine ⟨fun p ↦ ?_⟩
    let G : FilF ⥤ 𝒜 := finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙ GradedObject.eval p
    letI : G.Additive := by
      infer_instance
    simpa [G] using (Functor.map_isZero G (isZero_zero FilF)).injective

private instance filteredInjective_isClosedUnderBinaryProducts :
    ObjectProperty.IsClosedUnderBinaryProducts IFiltProp := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine ⟨fun p ↦ ?_⟩
  let G : FilF ⥤ 𝒜 := finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙ GradedObject.eval p
  letI : G.Additive := by
    infer_instance
  letI : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  letI : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProducts_of_preservesBinaryBiproducts G
  let X₁ : 𝒜 := G.obj (F.obj ⟨WalkingPair.left⟩)
  let X₂ : 𝒜 := G.obj (F.obj ⟨WalkingPair.right⟩)
  letI : Injective X₁ := by
    simpa [X₁, G] using (hF ⟨WalkingPair.left⟩).injective p
  letI : Injective X₂ := by
    simpa [X₂, G] using (hF ⟨WalkingPair.right⟩).injective p
  let e₁ : G.obj (limit F) ≅ limit (F ⋙ G) :=
    (isLimitOfPreserves G (limit.isLimit F)).conePointUniqueUpToIso (limit.isLimit (F ⋙ G))
  let e₂ : limit (F ⋙ G) ≅ X₁ ⨯ X₂ :=
    HasLimit.isoOfNatIso (diagramIsoPair (F ⋙ G))
  simpa [X₁, X₂, G] using
    Injective.of_iso (e₁.trans e₂).symm (inferInstance : Injective (X₁ ⨯ X₂))

private instance filteredInjectiveSubcategory_hasZeroObject :
    HasZeroObject (𝓘^f(𝒜)) := by
  infer_instance

private instance filteredInjectiveSubcategory_hasBinaryProducts :
    HasBinaryProducts (𝓘^f(𝒜)) := by
  infer_instance

private instance filteredInjectiveSubcategory_hasBinaryBiproducts :
    HasBinaryBiproducts (𝓘^f(𝒜)) :=
  HasBinaryBiproducts.of_hasBinaryProducts

end FilteredInjectiveSubcategoryInstances

section Core

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFiltPlus" => K⁺(FilF)
local notation "ιIFilt" => (filteredInjectiveInclusion 𝒜 : 𝓘^f(𝒜) ⥤ FilF)

private instance filteredInjectiveInclusion_additive :
    (filteredInjectiveInclusion 𝒜 : 𝓘^f(𝒜) ⥤ FilF).Additive := by
  infer_instance

/-
The canonical functor `K^+(\mathcal I^f) ⥤ DF^+(\mathcal A)` obtained by forgetting that a
bounded-below complex of filtered injectives lives in the filtered-injective subcategory and then
localizing at bounded filtered quasi-isomorphisms.
-/
variable (𝒜) in
abbrev filteredInjectiveHomotopyToFilteredDerived :
    K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜) :=
  mapBoundedBelowHomotopyCategory (ιIFilt : 𝓘^f(𝒜) ⥤ FilF) ⋙
    (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜 : K⁺(FilF) ⥤ DF⁺(𝒜))

/-- The comparison functor of Lemma `13.26.12` commutes with shifts. -/
noncomputable instance filteredInjectiveHomotopyToFilteredDerived_commShift :
    (filteredInjectiveHomotopyToFilteredDerived 𝒜).CommShift ℤ := by
  sorry

/-- The comparison functor of Lemma `13.26.12` is exact. -/
instance filteredInjectiveHomotopyToFilteredDerived_isTriangulated :
    (filteredInjectiveHomotopyToFilteredDerived 𝒜).IsTriangulated := by
  sorry

-- Proof sketch: essential surjectivity is supplied by Lemma `13.26.9`, which produces bounded-
-- below filtered injective resolutions, and full faithfulness is supplied by Lemma `13.26.11`,
-- which identifies morphisms into bounded-below filtered injective complexes before and after
-- localization.
/-- Lemma 13.26.12: the canonical functor `K^+(\mathcal I^f) ⥤ DF^+(\mathcal A)` from
bounded-below complexes of filtered injective objects to the bounded-below filtered derived
category is an equivalence of triangulated categories. -/
theorem filteredInjectiveHomotopyToFilteredDerived_isEquivalence [EnoughInjectives 𝒜] :
    Functor.IsEquivalence
      (filteredInjectiveHomotopyToFilteredDerived 𝒜 :
        K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜)) := sorry

end Core

section DerivedBridge

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "DFilt" => DF(𝒜)
local notation "DFiltPlus" => DF⁺(𝒜)
local notation "DPlus" => D⁺(𝒜)

local instance :
    (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜).IsLocalization (FQis⁺(𝒜)) :=
  mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization

/-
The bounded-below derived functor induced by the `p`-th graded-piece functor on `Fil^f(𝒜)`.
-/
variable (𝒜) in
abbrev filteredBoundedHomotopyToDerivedByGradedPiece (p : ℤ) :
    K⁺(FilF) ⥤ DPlus :=
  mapBoundedBelowHomotopyCategory
      ((finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙
        GradedObject.eval p : FilF ⥤ 𝒜)) ⋙
    mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)

/-
The bounded-below derived functor induced by forgetting the filtration on `Fil^f(𝒜)`.
-/
variable (𝒜) in
abbrev filteredBoundedHomotopyToDerivedByForget :
    K⁺(FilF) ⥤ DPlus :=
  mapBoundedBelowHomotopyCategory
      (finiteFilteredObjectForgetFunctor 𝒜 : FilF ⥤ 𝒜) ⋙
    mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)

-- Proof sketch: the `p`-th graded-piece functor on bounded filtered homotopy categories sends a
-- bounded filtered quasi-isomorphism to a quasi-isomorphism in `K^+(\mathcal A)`, hence the
-- induced functor to `D^+(\mathcal A)` factors through the bounded filtered localization.
/-- The bounded-below derived functor of `gr^p` inverts bounded filtered quasi-isomorphisms. -/
theorem filteredBoundedGradedPieceToDerived_inverts_quasiIsomorphisms (p : ℤ) :
    (FQis⁺(𝒜)).IsInvertedBy
      (filteredBoundedHomotopyToDerivedByGradedPiece 𝒜 p) := sorry

/-- The owner functor `gr^{p}` sends bounded-below filtered derived objects to bounded-below
derived objects. -/
theorem filteredDerivedGradedPieceFunctor_obj_mem_boundedBelowDerivedCategory
    (p : ℤ) (X : DFiltPlus) :
    (t.plus : ObjectProperty (D(𝒜)))
      (((filteredDerivedPlusProperty 𝒜).ι ⋙ (gr^{p} : DFilt ⥤ D(𝒜))).obj X) := sorry

/-
The bounded-below `p`-th graded-piece functor is the restriction of the Chapter `13` owner
`gr^{p}` to `DF^+(\mathcal A)`.
-/
variable (𝒜) in
abbrev filteredBoundedDerivedGradedPieceFunctor (p : ℤ) :
    DFiltPlus ⥤ DPlus :=
  ObjectProperty.lift
    (t.plus : ObjectProperty (D(𝒜)))
    ((filteredDerivedPlusProperty 𝒜).ι ⋙ (gr^{p} : DFilt ⥤ D(𝒜)))
    (fun X ↦ filteredDerivedGradedPieceFunctor_obj_mem_boundedBelowDerivedCategory p X)

-- Proof sketch: the forgetful functor from filtered complexes to ordinary complexes sends bounded
-- filtered quasi-isomorphisms to quasi-isomorphisms in the ordinary derived category, so the
-- bounded-below derived functor factors through the bounded filtered localization.
/-- The bounded-below derived functor of `\text{forget }F` inverts bounded filtered
quasi-isomorphisms. -/
theorem filteredBoundedForgetToDerived_inverts_quasiIsomorphisms :
    (FQis⁺(𝒜)).IsInvertedBy
      (filteredBoundedHomotopyToDerivedByForget 𝒜) := sorry

/-- The owner functor `filteredDerivedForgetFunctor` sends bounded-below filtered derived objects
to bounded-below derived objects. -/
theorem filteredDerivedForgetFunctor_obj_mem_boundedBelowDerivedCategory
    (X : DFiltPlus) :
    (t.plus : ObjectProperty (D(𝒜)))
      (((filteredDerivedPlusProperty 𝒜).ι ⋙ filteredDerivedForgetFunctor).obj X) := sorry

/-
The bounded-below forgetful functor is the restriction of the Chapter `13` owner
`filteredDerivedForgetFunctor` to `DF^+(\mathcal A)`.
-/
variable (𝒜) in
abbrev filteredBoundedDerivedForgetFunctor :
    DFiltPlus ⥤ DPlus :=
  ObjectProperty.lift
    (t.plus : ObjectProperty (D(𝒜)))
    ((filteredDerivedPlusProperty 𝒜).ι ⋙ filteredDerivedForgetFunctor)
    (fun X ↦ filteredDerivedForgetFunctor_obj_mem_boundedBelowDerivedCategory X)

end DerivedBridge

section FilteredInjectiveObjectLevel

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" => finiteFilteredObjectCat 𝒜

-- Proof sketch: an object of `𝓘^f` is filtered injective by definition, so its `p`-th graded
-- piece is injective in `𝒜`.
/-- The graded pieces of a filtered injective object are injective. -/
theorem filteredInjectiveGradedPiece_injective (I : 𝓘^f(𝒜)) (p : ℤ) :
    Injective (gr^{p} I.obj.obj) :=
  I.property.injective p

-- Proof sketch: a finite filtered injective object splits as a finite extension of its graded
-- pieces, so its underlying object is injective in the ambient abelian category.
/-- Forgetting the filtration on a filtered injective object yields an injective object. -/
theorem filteredInjectiveForget_injective (I : 𝓘^f(𝒜)) :
    Injective I.obj.obj := sorry

end FilteredInjectiveObjectLevel

section FilteredInjectiveHomotopy

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "ιIFilt" => (filteredInjectiveInclusion 𝒜 : 𝓘^f(𝒜) ⥤ FilF)

variable (𝒜)

private abbrev filteredInjectiveGradedPieceFunctor (p : ℤ) : 𝓘^f(𝒜) ⥤ 𝒜 :=
  ιIFilt ⋙ finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙ GradedObject.eval p

-- Proof sketch: additivity is inherited from the graded-piece construction on finite filtered
-- objects, since the source functor is just the inclusion of a full subcategory.
private instance filteredInjectiveGradedPieceFunctor_additive (p : ℤ) :
    ((filteredInjectiveGradedPieceFunctor 𝒜 p : 𝓘^f(𝒜) ⥤ 𝒜)).Additive := by
  infer_instance

private abbrev filteredInjectiveGradedPieceHomotopyMap (p : ℤ) :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺(𝒜) :=
  mapBoundedBelowHomotopyCategory
    (filteredInjectiveGradedPieceFunctor 𝒜 p : 𝓘^f(𝒜) ⥤ 𝒜)

private abbrev filteredInjectiveForgetHomotopyMap :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺(𝒜) :=
  mapBoundedBelowHomotopyCategory
    (ιIFilt ⋙ finiteFilteredObjectForgetFunctor 𝒜)

-- Proof sketch: apply the previous objectwise injectivity statement degreewise to the bounded-
-- below complex obtained by taking the `p`-th graded piece termwise.
/-- Taking graded pieces degreewise sends a bounded-below complex of filtered injectives to a
bounded-below complex of injectives. -/
private theorem filteredInjectiveGradedPieceHomotopy_obj_mem_injectiveProperty
    (p : ℤ) (X : K⁺(𝓘^f(𝒜))) :
    boundedBelowInjectiveHomotopyProperty 𝒜
      ((filteredInjectiveGradedPieceHomotopyMap 𝒜 p).obj X) := sorry

/-
The functor `K^+(\mathcal I^f) ⟶ K^+(\mathcal I)` obtained by taking the `p`-th graded piece
termwise.
-/
abbrev filteredInjectiveGradedPieceHomotopyFunctor (p : ℤ) :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺ᵢ(𝒜) :=
  ObjectProperty.lift (boundedBelowInjectiveHomotopyProperty 𝒜)
    (filteredInjectiveGradedPieceHomotopyMap 𝒜 p)
    (fun X ↦ filteredInjectiveGradedPieceHomotopy_obj_mem_injectiveProperty 𝒜 p X)

-- Proof sketch: apply the previous objectwise injectivity statement degreewise to the bounded-
-- below complex obtained by forgetting the filtration termwise.
/-- Forgetting the filtration degreewise sends a bounded-below complex of filtered injectives to a
bounded-below complex of injectives. -/
private theorem filteredInjectiveForgetHomotopy_obj_mem_injectiveProperty
    (X : K⁺(𝓘^f(𝒜))) :
    boundedBelowInjectiveHomotopyProperty 𝒜
      ((filteredInjectiveForgetHomotopyMap 𝒜).obj X) := sorry

/-
The functor `K^+(\mathcal I^f) ⟶ K^+(\mathcal I)` obtained by forgetting the filtration
termwise.
-/
abbrev filteredInjectiveForgetHomotopyFunctor :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺ᵢ(𝒜) :=
  ObjectProperty.lift (boundedBelowInjectiveHomotopyProperty 𝒜)
    (filteredInjectiveForgetHomotopyMap 𝒜)
    (fun X ↦ filteredInjectiveForgetHomotopy_obj_mem_injectiveProperty 𝒜 X)

end FilteredInjectiveHomotopy

section Compatibility

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "IToD" =>
  (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
    (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))

-- Proof sketch: all four functors are induced from the corresponding termwise functors on
-- bounded-below filtered injective complexes, and localization preserves the obvious equality of
-- the two composites there.
/-- The canonical functor `K^+(\mathcal I^f) ⟶ DF^+(\mathcal A)` commutes with taking the `p`-th
graded piece. -/
theorem filteredInjectiveHomotopyToFilteredDerived_gr_comm (p : ℤ) :
    filteredInjectiveHomotopyToFilteredDerived 𝒜 ⋙
        filteredBoundedDerivedGradedPieceFunctor 𝒜 p =
      filteredInjectiveGradedPieceHomotopyFunctor 𝒜 p ⋙
        IToD := sorry

-- Proof sketch: both composites are induced from the same termwise forgetful functor on bounded-
-- below complexes of filtered injectives, so they agree after passing to the bounded filtered and
-- ordinary derived localizations.
/-- The canonical functor `K^+(\mathcal I^f) ⟶ DF^+(\mathcal A)` commutes with forgetting the
filtration. -/
theorem filteredInjectiveHomotopyToFilteredDerived_forget_comm :
    filteredInjectiveHomotopyToFilteredDerived 𝒜 ⋙
        filteredBoundedDerivedForgetFunctor 𝒜 =
      filteredInjectiveForgetHomotopyFunctor 𝒜 ⋙
        IToD := sorry

end Compatibility

end CategoryTheory
