import Mathlib
import stacks_project.Chap13.Definition_13_11_3
import stacks_project.Chap13.Definition_13_34_1
import stacks_project.Chap13.Lemma_13_11_6
import stacks_project.Chap13.Lemma_13_23_4
import stacks_project.Chap13.Lemma_13_31_5

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

/-- Helper for Lemma 13.34.3: for a bounded-below injective complex, passing through
`D^+(\mathcal A)` and then including into `D(\mathcal A)` agrees definitionally with viewing the
same cochain complex directly in the ambient derived category. -/
noncomputable abbrev injective_plus_to_ambient_derived_iso (J : K⁺ᵢ(𝒜)) :
    DerivedCategory.Q.obj J.toInjectivePlus ≅
      (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).obj
        (((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
          (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))).obj J) :=
  Iso.refl _

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

omit [EnoughInjectives 𝒜] in
/-- Helper for Lemma 13.34.3: stagewise bounded-below injective models produce the countable
product of the ambient family in `D(\mathcal A)`. -/
theorem hasProduct_of_stagewise_boundedBelowInjective_models
    (K : SequentialInverseSystem (D⁺(𝒜)))
    (I : ℕ → K⁺ᵢ(𝒜))
    (eI : ∀ n : ℕ,
      (((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
        (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))).obj (I n) ≅
          K.obj (Opposite.op n))) :
    HasProduct (inverseSystemFamily (K ⋙ plusι)) := by
  let complexes : ℕ → CochainComplex 𝒜 ℤ := fun n ↦ (I n).toInjectivePlus
  let eAmbient : ∀ n : ℕ, DerivedCategory.Q.obj (complexes n) ≅ inverseSystemFamily (K ⋙ plusι) n :=
    fun n ↦
      injective_plus_to_ambient_derived_iso (𝒜 := 𝒜) (I n) ≪≫
        (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).mapIso (eI n)
  let _ : ∀ n : ℕ, (complexes n).IsKInjective :=
    fun n ↦ CochainComplex.PlusWithTermsIn.instIsKInjective ((I n).toInjectivePlus)
  refine HasLimit.mk ⟨
    Fan.mk (DerivedCategory.Q.obj (∏ᶜ complexes))
      (fun n ↦ DerivedCategory.Q.map (Pi.π complexes n) ≫ (eAmbient n).hom),
    ?_⟩
  -- Lemma 13.34.2 identifies the termwise product of the injective representatives with the
  -- product of the ambient derived objects.
  simpa [complexes, eAmbient, inverseSystemFamily] using
    (termwise_product_represents_product
      (X := inverseSystemFamily (K ⋙ plusι)) complexes eAmbient)

-- Proof sketch: choose bounded-below representatives of the stages using localization,
-- resolve those representatives by a homotopy resolution functor into bounded-below injective
-- complexes, use Lemma 13.34.2 to obtain the ambient product, and then complete the Milnor
-- difference map to a distinguished triangle.
/-- Lemma 13.34.3: in an abelian category with countable products and enough injectives, every
sequential inverse system in `D^+(\mathcal A)` admits a homotopy inverse limit in the ambient
derived category `D(\mathcal A)`, i.e. the object usually denoted `R lim K_n` exists. -/
theorem exists_derivedLimit
    (K : SequentialInverseSystem (D⁺(𝒜))) :
    ∃ Kholim : D(𝒜), IsDerivedLimit (K ⋙ plusι) Kholim := by
  let Qplus : K⁺(𝒜) ⥤ D⁺(𝒜) := mapBoundedBelowHomotopyToDerivedBelow
  let _ : Functor.IsLocalization Qplus (Qis⁺(𝒜)) :=
    mapBoundedBelowHomotopyToDerivedBelow_isLocalization (𝒜 := 𝒜)
  let _ : Qplus.EssSurj := Localization.essSurj Qplus (Qis⁺(𝒜))
  obtain ⟨J⟩ : Nonempty (HomotopyResolutionFunctor 𝒜) :=
    exists_homotopyResolutionFunctor (𝒜 := 𝒜)
  let preimage : ℕ → K⁺(𝒜) := fun n ↦ Qplus.objPreimage (K.obj (Opposite.op n))
  let I : ℕ → K⁺ᵢ(𝒜) := fun n ↦ J.toFunctor.obj (preimage n)
  let eI : ∀ n : ℕ,
      (((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
        Qplus).obj (I n) ≅ K.obj (Opposite.op n)) := by
    intro n
    let α : preimage n ⟶ (I n).obj := J.ι.app (preimage n)
    have hα : Qis⁺(𝒜) α := J.quasiIso_app (preimage n)
    haveI : IsIso (Qplus.map α) := by
      simpa using (Localization.inverts Qplus (Qis⁺(𝒜)) α hα)
    -- The chosen injective model is quasi-isomorphic to the selected bounded-below preimage.
    exact (asIso (Qplus.map α)).symm ≪≫ Qplus.objObjPreimageIso (K.obj (Opposite.op n))
  let hP : HasProduct (inverseSystemFamily (K ⋙ plusι)) :=
    hasProduct_of_stagewise_boundedBelowInjective_models (𝒜 := 𝒜) K I eI
  let _ : HasProduct (inverseSystemFamily (K ⋙ plusι)) := hP
  -- With the countable product in hand, the Milnor triangle packages the derived limit.
  exact exists_derivedLimit_of_hasProduct (Ksys := K ⋙ plusι)

end SequentialInverseSystem

end

end CategoryTheory
