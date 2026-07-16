import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CategoryTheory.Localization
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
  [HasCountableProducts 𝒜] [EnoughInjectives 𝒜]

local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
local notation "Q" => DerivedCategory.Q

/-
Domain-style sampling for Lemma 13.34.3:
- primary domain: sequential inverse systems in the bounded-below derived category and their
  Milnor triangles in the ambient derived category;
- inspected owner declarations:
  * `CategoryTheory.IsDerivedLimit`
  * `CategoryTheory.CochainComplex.InjectiveResolution`
  * `CategoryTheory.SequentialInverseSystem.isKInjective_limit_of_termwiseSplitEpi`
  * `CategoryTheory.boundedBelowInjectiveHomotopyToDerived_isEquivalence`
- best owner abstraction:
  * the source-facing owner is the tower
    `K : SequentialInverseSystem (D⁺(𝒜))`;
  * the core owner is the ambient derived-limit predicate `IsDerivedLimit` on the image tower
    in `D(𝒜)`;
  * the bounded-below hypothesis is bridge data carried by the canonical inclusion
    `plusι : D⁺(𝒜) ⥤ D(𝒜)`, not a second owner for homotopy limits;
- primitive data:
  * a sequential inverse system `K : SequentialInverseSystem (D⁺(𝒜))`;
  * countable products in `𝒜`;
  * enough injectives in `𝒜`;
- derived API:
  * a product witness for the specific family underlying `K ⋙ plusι`;
  * existence of an object of `D(𝒜)` satisfying `IsDerivedLimit (K ⋙ plusι)`;
  * the stronger exact-countable-products owner from Lemma 13.34.2 is only background domain
    style here, not the public conclusion of this file.

Source/core/bridge triage:
- `source-facing`: existence of the homotopy inverse limit of a sequential system in `D⁺(𝒜)`;
- `core/canonical`: `IsDerivedLimit` in `D(𝒜)`;
- `bridge/view`: the inclusion `plusι : D⁺(𝒜) ⥤ D(𝒜)` and bounded-below injective models of the
  stages.
-/

namespace SequentialInverseSystem

/-- Helper for Lemma 13.34.3: once the product of a sequential inverse system exists, completing
its Milnor difference map gives a derived limit object. -/
theorem exists_derivedLimit_of_hasProduct
    {D : Type*} [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
    (Ksys : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily Ksys)] :
    ∃ L : D, IsDerivedLimit Ksys L := by
  -- Complete the canonical difference map to the Milnor triangle.
  obtain ⟨L, ι, δ, hT⟩ := distinguished_cocone_triangle₁ (derivedLimitDifferenceMap Ksys)
  exact ⟨L, ⟨inferInstance, ⟨ι, δ, hT⟩⟩⟩

/-
Helper for Lemma 13.34.3: a chosen cochain-level preimage of a bounded-below derived object
has vanishing homology in sufficiently negative degrees.
-/
omit [HasCountableProducts 𝒜] [EnoughInjectives 𝒜] in
theorem objPreimage_eventually_isZero_homology
    (X : D⁺(𝒜)) :
    ∃ a : ℤ, ∀ i < a, IsZero ((Q.objPreimage X.obj).homology i) := by
  -- Route correction: instead of passing through a global homotopy resolution functor, use the
  -- ambient derived object `X.obj`, choose a cochain-level preimage, and transfer the low-degree
  -- cohomology vanishing of `X` back to the preimage complex.
  obtain ⟨a, ha⟩ := (derivedCategory_t_plus_iff (K := X.obj)).1 X.property
  refine ⟨a, ?_⟩
  intro i hi
  have hXi : IsZero ((H^i).obj X.obj) := ha i hi
  have hQpreimage : IsZero ((H^i).obj (Q.obj (Q.objPreimage X.obj))) := by
    let e : (H^i).obj (Q.obj (Q.objPreimage X.obj)) ≅ (H^i).obj X.obj :=
      (H^i).mapIso (Q.objObjPreimageIso X.obj)
    exact (e.isZero_iff).2 hXi
  exact (((homologyFunctorFactors 𝒜 i).app (Q.objPreimage X.obj)).isZero_iff).1 hQpreimage

/-
Helper for Lemma 13.34.3: every bounded-below derived object admits an injective-resolution
model on a chosen cochain-level preimage.
-/
omit [HasCountableProducts 𝒜] in
theorem nonempty_objPreimage_injectiveResolution
    (X : D⁺(𝒜)) :
    Nonempty (CochainComplex.InjectiveResolution (Q.objPreimage X.obj)) := by
  -- The preimage complex is bounded below on cohomology, so Lemma 13.18.3 supplies an injective
  -- resolution.
  exact nonempty_injectiveResolution_of_eventually_isZero_homology
    (K := Q.objPreimage X.obj)
    (objPreimage_eventually_isZero_homology (𝒜 := 𝒜) X)

/-- Helper for Lemma 13.34.3: a chosen injective-resolution model of a bounded-below derived
object, obtained from a fixed cochain-level preimage. -/
noncomputable def objPreimage_injectiveResolution
    (X : D⁺(𝒜)) :
    CochainComplex.InjectiveResolution (Q.objPreimage X.obj) :=
  Classical.choice (nonempty_objPreimage_injectiveResolution (𝒜 := 𝒜) X)

/-- Helper for Lemma 13.34.3: the chosen injective-resolution model represents the original
bounded-below derived object in the ambient derived category. -/
noncomputable def objPreimage_injectiveResolution_iso
    (X : D⁺(𝒜)) :
    Q.obj (objPreimage_injectiveResolution (𝒜 := 𝒜) X : CochainComplex 𝒜 ℤ) ≅ X.obj := by
  let α : Q.objPreimage X.obj ⟶
      (objPreimage_injectiveResolution (𝒜 := 𝒜) X : CochainComplex 𝒜 ℤ) :=
    (objPreimage_injectiveResolution (𝒜 := 𝒜) X).ι
  have hα : IsIso (Q.map α) := by
    rw [isIso_Q_map_iff_quasiIso]
    infer_instance
  -- The injective resolution is quasi-isomorphic to the chosen preimage, which already represents
  -- `X` in the derived category.
  exact (asIso (Q.map α)).symm ≪≫ Q.objObjPreimageIso X.obj

/-- Helper for Lemma 13.34.3: a countable family of K-injective representatives realizes the
product of the corresponding derived objects. -/
noncomputable def termwise_product_represents_product
    (X : ℕ → DerivedCategory 𝒜) (K : ℕ → CochainComplex 𝒜 ℤ)
    [∀ i, (K i).IsKInjective]
    (eK : ∀ i, Q.obj (K i) ≅ X i) :
    IsLimit
      (Fan.mk (Q.obj (∏ᶜ K)) fun i ↦ Q.map (Pi.π K i) ≫ (eK i).hom) := by
  let e : Discrete.functor (fun i ↦ Q.obj (K i)) ≅ Discrete.functor X :=
    Discrete.natIso fun i : Discrete ℕ ↦ eK i.as
  let _ : PreservesLimit (Discrete.functor K) Q :=
    derivedCategory_Q_preserves_product_of_kInjective K
  simpa using
    (IsLimit.postcomposeHomEquiv e (Fan.mk (Q.obj (∏ᶜ K)) fun i ↦ Q.map (Pi.π K i))).symm
      (isLimitOfHasProductOfPreservesLimit Q K)

/-
Helper for Lemma 13.34.3: stagewise K-injective models produce the countable product of the
ambient family in `D(\mathcal A)`.
-/
omit [EnoughInjectives 𝒜] in
theorem hasProduct_of_stagewise_kInjective_models
    (X : ℕ → D(𝒜))
    (K : ℕ → CochainComplex 𝒜 ℤ)
    [∀ n : ℕ, (K n).IsKInjective]
    (eK : ∀ n : ℕ, DerivedCategory.Q.obj (K n) ≅ X n) :
    HasProduct X := by
  refine HasLimit.mk ⟨
    Fan.mk (DerivedCategory.Q.obj (∏ᶜ K))
      (fun n ↦ DerivedCategory.Q.map (Pi.π K n) ≫ (eK n).hom),
    ?_⟩
  -- Lemma 13.34.2 identifies the termwise product of the injective representatives with the
  -- product of the ambient derived objects.
  simpa using termwise_product_represents_product (X := X) K eK

-- Proof sketch: choose bounded-below representatives of the stages using localization,
-- replace those representatives by bounded-below injective resolutions, use Lemma 13.34.2 to
-- obtain the ambient product, and then complete the Milnor difference map to a distinguished
-- triangle.
/-- Lemma 13.34.3: in an abelian category with countable products and enough injectives, every
sequential inverse system in `D^+(\mathcal A)` admits a homotopy inverse limit in the ambient
derived category `D(\mathcal A)`, i.e. the object usually denoted `R lim K_n` exists. -/
theorem exists_derivedLimit
    (K : SequentialInverseSystem (D⁺(𝒜))) :
    ∃ Kholim : D(𝒜), IsDerivedLimit (K ⋙ plusι) Kholim := by
  let complexes : ℕ → CochainComplex 𝒜 ℤ := fun n ↦
    objPreimage_injectiveResolution (𝒜 := 𝒜) (K.obj (Opposite.op n))
  let eComplex : ∀ n : ℕ, Q.obj (complexes n) ≅ inverseSystemFamily (K ⋙ plusι) n := fun n ↦
    objPreimage_injectiveResolution_iso (𝒜 := 𝒜) (K.obj (Opposite.op n))
  let _ : ∀ n : ℕ, (complexes n).IsKInjective := fun n ↦ inferInstance
  let hP : HasProduct (inverseSystemFamily (K ⋙ plusι)) :=
    hasProduct_of_stagewise_kInjective_models
      (𝒜 := 𝒜) (inverseSystemFamily (K ⋙ plusι)) complexes eComplex
  let _ : HasProduct (inverseSystemFamily (K ⋙ plusι)) := hP
  -- With the countable product in hand, the Milnor triangle packages the derived limit.
  exact exists_derivedLimit_of_hasProduct (Ksys := K ⋙ plusι)

end SequentialInverseSystem

end

end CategoryTheory
