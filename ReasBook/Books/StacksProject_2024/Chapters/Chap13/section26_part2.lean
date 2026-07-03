import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_26_12 (from Chap13) -/
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

/-! ### Remark_13_26_13 (from Chap13) -/
universe w v u

/-
Domain-style sampling:
- primary domain: object properties and full subcategories of abelian categories with enough
  injectives;
- sampled owner-side declarations:
  `ObjectProperty.ofObj`,
  `ObjectProperty.ofObj_le_iff`,
  `ObjectProperty.Small`,
  `ObjectProperty.IsWeakSerreClass`,
  `exists_small_abelian_fullSubcategory_containing`,
  `EnoughInjectives`;
- best owner abstraction: an `ObjectProperty 𝒜` whose full subcategory is the ambient owner of the
  desired small abelian subcategory;
- primitive data: a small object property `E : ObjectProperty 𝒜`, together with the target owner
  data `E ≤ P`, `ObjectProperty.Small P`, and `ObjectProperty.IsWeakSerreClass P`;
- derived API: the source-facing family-membership bridge `∀ i, P (A i)`, induced from
  `ObjectProperty.ofObj_le_iff`, together with the abelian structure on `P.FullSubcategory` and
  the additional conclusion
  `EnoughInjectives P.FullSubcategory`.

Layer triage:
- `source-facing`: the existence of a small abelian full subcategory with enough injectives
  containing the family `A`;
- `core/canonical`: `ObjectProperty.Small`, `ObjectProperty.IsWeakSerreClass`, and the owner-level
  existence theorem for a small object property `E`;
- `bridge/view`: the equivalence between owner-side containment `ObjectProperty.ofObj A ≤ P` and
  the source-facing pointwise condition `∀ i, P (A i)` via `ObjectProperty.ofObj_le_iff`.
-/

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
variable {I : Type w}

-- Proof sketch: first use `exists_small_abelian_fullSubcategory_containing` on `E` to obtain a
-- small weak-LinearRepresentations_Serre_1977 object property containing `E`; then refine that witness so that its full
-- subcategory also has enough injectives.
/-- Owner refinement of Remark 13.26.13: any small object property in an abelian category with
enough injectives is contained in a small weak-LinearRepresentations_Serre_1977 object property whose full subcategory also
has enough injectives. -/
theorem exists_small_abelian_fullSubcategory_with_enough_injectives_containing
    (E : ObjectProperty 𝒜) [ObjectProperty.Small.{w} E] :
    ∃ P : ObjectProperty 𝒜,
      E ≤ P ∧
        ObjectProperty.Small.{w} P ∧
        P.IsWeakSerreClass ∧
        EnoughInjectives P.FullSubcategory := sorry

-- Proof sketch: specialize the owner theorem above to the small object property
-- `ofObj A`.
/-- Remark 13.26.13: in a possibly large abelian category with enough injectives, every
set-indexed family of objects is contained in a small full subcategory that is abelian and has
enough injectives. -/
theorem exists_small_abelian_subcategory_with_enough_injectives_containing
    (A : I → 𝒜) :
    ∃ P : ObjectProperty 𝒜,
      (∀ i, P (A i)) ∧
        ObjectProperty.Small.{w} P ∧
        P.IsWeakSerreClass ∧
        EnoughInjectives P.FullSubcategory := by
  simpa [ObjectProperty.ofObj_le_iff] using
    exists_small_abelian_fullSubcategory_with_enough_injectives_containing
      (ObjectProperty.ofObj A)

end

end CategoryTheory

/-! ### Lemma_13_26_14 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section SpectralSequences

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [LocallySmall ℬ] [WellPowered ℬ] [HasWidePullbacks ℬ] [HasCoproducts ℬ]
  [InitialMonoClass ℬ] [HasDerivedCategory.{w} ℬ]

open FilteredComplex

/- Domain-style sampling:
- primary domain: filtered complexes in `ℬ`, their associated cohomological spectral sequences,
  and the right-derived cohomology of the graded pieces and the underlying complex of a bounded-
  below filtered complex in `𝒜`;
- sampled owner declarations:
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.cohomologyFiltrationIsFinite`,
  `FilteredComplex.convergesToCohomology`,
  `SpectralSequence.Hom`,
  `rightDerivedValueMap`;
- best owner abstraction:
  `source-facing`: Lemma `13.26.14`, i.e. existence of the filtered right-derived spectral
    sequence with its `E₁`-page, boundedness, convergence, finite abutment filtrations,
    functoriality, and choice-independence for pages `r ≥ 1`;
  `core/canonical`: `FilteredComplex`, `IsAssociatedToFilteredComplex`,
    `FilteredComplex.pageOneIso`, `FilteredComplex.cohomologyFiltrationIsFinite`,
    `FilteredComplex.convergesToCohomology`, `SpectralSequence.Hom`, `rightDerivedValue`, and
    `rightDerivedValueMap`;
  `bridge/view`: the source-facing `E₁`-page and abutment isomorphisms expressed against
    `DerivedCategory.homologyFunctor`.
- primitive data: a filtered-complex model `M` in `ℬ`, its associated spectral sequence `E`, and
  the page-one and abutment comparison isomorphisms;
- derived API: boundedness, finite abutment filtrations, convergence, the morphisms induced by a
  map `K ⟶ L`, and the choice-independence isomorphisms on pages `r ≥ 1`;
  the finite-filtration witness on `M` is auxiliary proof data internal to the construction.

The public surface should therefore keep a single existence theorem on the canonical filtered-
complex/spectral-sequence owners, with direct `pageOneIso` and `targetIso` bridge data and the
canonical Chapter `12` boundedness/convergence package recorded on the same returned owners, plus
separate companion theorems for functoriality and choice-independence. The former local split into
a page-one existence theorem and a second abutment theorem weakened the source semantics and hid
the owner-level page-one surface. -/

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "Qh" => HomotopyCategory.quotient 𝒜 (up ℤ)
local notation "H" => DerivedCategory.homologyFunctor ℬ

variable (T : 𝒜 ⥤ ℬ) [T.Additive]

local notation "KtoD" => mapHomotopyCategoryToDerived T

local instance gradedPiece_hasPointwiseRightDerivedFunctorAt
    (K : FilteredComplex 𝒜)
    (hgr : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    (p : ℤ) :
    Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)) :=
  hgr p

local instance underlying_hasPointwiseRightDerivedFunctorAt
    (K : FilteredComplex 𝒜)
    (hKder : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj K.underlying)) :
    Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj K.underlying) :=
  hKder

private theorem zero_le_of_one_le {r : ℤ} (hr : 1 ≤ r) : 0 ≤ r :=
  le_trans (by decide : (0 : ℤ) ≤ 1) hr

-- Proof sketch: choose a filtered quasi-isomorphism `K^• ⟶ I^•` to a bounded-below filtered
-- complex of filtered injectives, apply `T` termwise, and take the associated spectral sequence
-- of the resulting filtered complex in `ℬ`. Chapter `12` then supplies the owner-level page-one,
-- boundedness, finite-filtration, and convergence package, while the derived-functor comparison
-- identifies the page-one terms with `R^{p + q}T(gr^p(K^•))` and the abutment with `R^*T(K^•)`.
/-- Lemma 13.26.14: for a left exact functor `T : \mathcal A ⥤ \mathcal B` and a bounded-below
filtered complex `K^•` with finite filtrations, there exists an associated cohomological spectral
sequence whose `E_1`-page is `R^{p + q}T(\mathrm{gr}^p(K^•))`, which is bounded, converges to
`R^*T(K^•)`, and induces finite filtrations on the abutment objects; the returned
`pageOneIso`/`abutmentIso` data make the source-facing comparisons explicit on the theorem surface,
while the boundedness, finite abutment filtration, and convergence package is recorded through the
canonical Chapter `12` owners rather than by returning extra construction witnesses. -/
theorem exists_filteredRightDerivedSpectralSequence
    [PreservesFiniteLimits T]
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations)
    (hKplus : CochainComplex.plus 𝒜 K.underlying)
    (hgr : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    (hKder : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj K.underlying)) :
    ∃ (M : FilteredComplex ℬ)
      (E : CohomologicalSpectralSequence ℬ 0) (_ : IsAssociatedToFilteredComplex M E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          (H (p + q)).obj
            (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K))))
      (abutmentIso : ∀ n : ℤ,
        M.underlying.homology n ≅
          (H n).obj
            (rightDerivedValue Qis KtoD ((Qh).obj K.underlying))),
      CohomologicalSpectralSequence.IsBounded E ∧
        M.cohomologyFiltrationIsFinite ∧
        M.convergesToCohomology E := sorry

-- Proof sketch: choose filtered injective models for `K` and `L`, use Lemma `13.26.11` to lift
-- a morphism `K ⟶ L` to a map between the chosen filtered injective models in the filtered
-- homotopy category, apply `T` termwise, and pass to the associated spectral-sequence morphism.
/-- The spectral sequence of Lemma `13.26.14` is functorial in the filtered complex `K^•`. -/
theorem exists_filteredRightDerivedSpectralSequenceMap
    [PreservesFiniteLimits T]
    {K L : FilteredComplex 𝒜}
    (hgrK : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    (hgrL : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} L)))
    (α : K ⟶ L)
    {M : FilteredComplex ℬ} {E : CohomologicalSpectralSequence ℬ 0}
    (hE : IsAssociatedToFilteredComplex M E)
    (pageOneIsoK : ∀ p q : ℤ,
      (E.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K))))
    {M' : FilteredComplex ℬ} {E' : CohomologicalSpectralSequence ℬ 0}
    (hE' : IsAssociatedToFilteredComplex M' E')
    (pageOneIsoL : ∀ p q : ℤ,
      (E'.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} L)))) :
    ∃ φ : E ⟶ E',
      ∀ p q : ℤ,
        CommSq
          ((φ.hom 1).f (p, q))
          (pageOneIsoK p q).hom
          (pageOneIsoL p q).hom
          ((H (p + q)).map
            (rightDerivedValueMap Qis KtoD ((Qh).map (gradedPieceMap α p)))) := sorry

-- Proof sketch: apply the functoriality theorem to the identity map on `K`, once in each
-- direction between two choices. The resulting page-one comparison is the identity under the
-- common `E₁`-identifications, and from page `1` onward the induced morphisms are isomorphisms.
/-- For `r ≥ 1`, the pages and differentials of the spectral sequence of Lemma `13.26.14` do not
depend on the choice of filtered injective model. -/
theorem exists_filteredRightDerivedSpectralSequenceIso_of_sameSource
    [PreservesFiniteLimits T]
    (K : FilteredComplex 𝒜)
    (hgr : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    {M : FilteredComplex ℬ} {E : CohomologicalSpectralSequence ℬ 0}
    (hE : IsAssociatedToFilteredComplex M E)
    (pageOneIso : ∀ p q : ℤ,
      (E.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K))))
    {M' : FilteredComplex ℬ} {E' : CohomologicalSpectralSequence ℬ 0}
    (hE' : IsAssociatedToFilteredComplex M' E')
    (pageOneIso' : ∀ p q : ℤ,
      (E'.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K)))) :
    ∃ φ : E ⟶ E',
      (∀ p q : ℤ,
        CommSq
          ((φ.hom 1).f (p, q))
          (pageOneIso p q).hom
          (pageOneIso' p q).hom
          (𝟙 _)) ∧
      ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ),
        IsIso ((φ.hom r (zero_le_of_one_le hr)).f (p, q)) := sorry

end SpectralSequences

end CategoryTheory
