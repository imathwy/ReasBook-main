import StacksProject_2024.Chap19.Remark_19_13_11
import StacksProject_2024.Chap21.Definition_21_17_13_Core
import StacksProject_2024.Chap21.Lemma_21_19_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [LocallySmall (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [IsGrothendieckAbelian.{w} (ringedSiteModuleCategory J 𝒪)]
variable [HasDerivedCategory (ringedSiteModuleCategory J 𝒪)]

variable [WellPowered (ringedSiteModuleCategory J 𝒪)]
variable [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
variable [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [InitialMonoClass (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

local notation "single₀" => DerivedCategory.singleFunctor Mod (0 : ℤ)
local notation "QMod" => (DerivedCategory.Q : Cpx ⥤ DerivedCategory Mod)
local notation "DerivedExtCohSSData" => DerivedExtCohomologySpectralSequenceData
local notation "DerivedExtStupidSSData" =>
  DerivedExtStupidFiltrationSpectralSequenceData

/- Domain-style sampling for Example 21.32.1:
- primary domain: derived `Ext` spectral sequences in a Grothendieck abelian category, specialized
  to the ringed-site module category `ringedSiteModuleCategory J 𝒪`;
- inspected owner declarations:
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `ringedSiteModuleCategory`,
  `derivedExtGroup`,
  `CohomologicalSpectralSequence`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction:
  `source-facing`: the two ringed-site existence statements matching Example 21.32.1;
  `core/canonical`: the canonical `derivedExtGroup` owner in the derived category together with
    `FilteredComplex`, `IsAssociatedToFilteredComplex`, `CohomologicalSpectralSequence`, and
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the degree-zero realization of `ℱ` as `((single₀).obj ℱ)` together with the
    Chapter `19` abbreviations `derivedCohomologyAsDerivedObject`,
    `cochainTermAsDerivedObject`, and `addCommGrpFilteredComplexCohomologyObject` that package
    the page and abutment identifications carried by the owner data.

The public surface therefore keeps the two source-facing existence theorems directly in terms of
the canonical Chapter `19` spectral-sequence owners together with the convergence consequence
coming from their boundedness fields, instead of introducing a local wrapper structure or
re-stating every page and abutment field by hand. -/

omit [LocallySmall (ringedSiteModuleCategory J 𝒪)]
  [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
  [IsGrothendieckAbelian.{w} (ringedSiteModuleCategory J 𝒪)]
  [WellPowered (ringedSiteModuleCategory J 𝒪)]
  [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
  [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
  [InitialMonoClass (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Example 21.32.1: a bounded-above cochain complex defines a bounded-above derived
object after applying the quotient functor `QMod`. -/
private theorem qObjMinusPropertyOfCochainComplexIsBoundedAbove
    (K : Cpx) (hK : cochainComplexIsBoundedAbove K) :
    derivedCategoryMinusProperty ((QMod).obj K) := by
  -- Proof comment: unpack the source bounded-above hypothesis into a concrete degree bound.
  rcases hK with ⟨n, hn⟩
  -- Proof comment: strict vanishing above `n` upgrades to the `IsLE n` witness used by
  -- `DerivedCategory.isLE_Q_obj_iff`.
  letI : K.IsStrictlyLE n := hn
  have hLE : K.IsLE n := inferInstance
  -- Proof comment: transport the bounded-above witness across the quotient functor.
  refine ⟨n, ?_⟩
  simpa using (DerivedCategory.isLE_Q_obj_iff K n).2 hLE

omit [LocallySmall (ringedSiteModuleCategory J 𝒪)]
  [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
  [IsGrothendieckAbelian.{w} (ringedSiteModuleCategory J 𝒪)]
  [WellPowered (ringedSiteModuleCategory J 𝒪)]
  [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
  [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
  [InitialMonoClass (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Example 21.32.1: the degree-zero derived object `ℱ[0]` is bounded below. -/
private theorem singleZeroDerivedObjectPlusProperty
    (ℱ : Mod) :
    derivedCategoryPlusProperty ((single₀).obj ℱ) := by
  -- Proof comment: `ℱ[0]` is concentrated in degree `0`, so `0` is a valid lower bound.
  exact ⟨0, inferInstance⟩

omit [LocallySmall (ringedSiteModuleCategory J 𝒪)]
  [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
  [IsGrothendieckAbelian.{w} (ringedSiteModuleCategory J 𝒪)]
  [WellPowered (ringedSiteModuleCategory J 𝒪)]
  [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
  [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
  [InitialMonoClass (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Example 21.32.1: a chosen Chapter `19` cohomology spectral-sequence owner
converges once the boundedness of `K` and `ℱ[0]` is supplied. -/
private theorem chosenCohomologyOwnerConverges
    (K : Cpx) (ℱ : Mod)
    (S : DerivedExtCohSSData ((QMod).obj K) ((single₀).obj ℱ))
    (hK : cochainComplexIsBoundedAbove K) :
    S.filteredComplex.convergesToCohomology S.spectralSequence := by
  -- Proof comment: package the source and target boundedness hypotheses in the exact Chapter `19`
  -- format expected by the owner field `converges_of_boundedness`.
  have hMinus : derivedCategoryMinusProperty ((QMod).obj K) :=
    qObjMinusPropertyOfCochainComplexIsBoundedAbove J 𝒪 K hK
  have hPlus : derivedCategoryPlusProperty ((single₀).obj ℱ) :=
    singleZeroDerivedObjectPlusProperty J 𝒪 ℱ
  -- Proof comment: the owner already records convergence from these two boundedness inputs.
  exact S.converges_of_boundedness hMinus hPlus

omit [LocallySmall (ringedSiteModuleCategory J 𝒪)]
  [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
  [IsGrothendieckAbelian.{w} (ringedSiteModuleCategory J 𝒪)]
  [WellPowered (ringedSiteModuleCategory J 𝒪)]
  [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
  [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
  [InitialMonoClass (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Example 21.32.1: a chosen Chapter `19` stupid-filtration spectral-sequence owner
converges once the boundedness of `K` and `ℱ[0]` is supplied. -/
private theorem chosenStupidOwnerConverges
    (K : Cpx) (ℱ : Mod)
    (S : DerivedExtStupidSSData K ((single₀).obj ℱ))
    (hK : cochainComplexIsBoundedAbove K) :
    S.filteredComplex.convergesToCohomology S.spectralSequence := by
  -- Proof comment: only the degree-zero bounded-below witness for `ℱ[0]` is needed here because
  -- the owner already takes the cochain-level bounded-above hypothesis directly.
  have hPlus : derivedCategoryPlusProperty ((single₀).obj ℱ) :=
    singleZeroDerivedObjectPlusProperty J 𝒪 ℱ
  -- Proof comment: invoke the packaged convergence field of the chosen owner.
  exact S.converges_of_boundedness hK hPlus

-- Proof sketch: specialize the Chapter `19` owner
-- `DerivedExtCohomologySpectralSequenceData` to `M = K^•` and `K = ℱ[0]`, then use the
-- bounded-above hypothesis on `K^•` and the canonical bounded-below witness for `ℱ[0]` to obtain
-- convergence from the chosen owner's `converges_of_boundedness` field.
omit [LocallySmall (ringedSiteModuleCategory J 𝒪)]
  [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
  [WellPowered (ringedSiteModuleCategory J 𝒪)]
  [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
  [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
  [InitialMonoClass (ringedSiteModuleCategory J 𝒪)] in
/-- Example 21.32.1: (1) for a bounded-above complex `K^•` of `𝒪`-modules on a ringed site and an
`𝒪`-module `ℱ`, the cohomology `Ext` spectral sequence exists with the Chapter `19` owner data
and converges. -/
theorem ringedSiteExtCohomologySpectralSequenceExists
    (K : Cpx) (ℱ : Mod) (hK : cochainComplexIsBoundedAbove K) :
    ∃ S : DerivedExtCohSSData ((QMod).obj K) ((single₀).obj ℱ),
      S.filteredComplex.convergesToCohomology S.spectralSequence := by
  classical
  -- Proof comment: choose the canonical Chapter `19` owner for the pair `((QMod).obj K, ℱ[0])`.
  let S : DerivedExtCohSSData ((QMod).obj K) ((single₀).obj ℱ) :=
    Classical.choice
      (CategoryTheory.derivedExt_cohomology_spectralSequence_exists
        ((QMod).obj K) ((single₀).obj ℱ))
  -- Proof comment: convergence is a separate boundedness consequence recorded by the owner.
  have hconv : S.filteredComplex.convergesToCohomology S.spectralSequence :=
    chosenCohomologyOwnerConverges J 𝒪 K ℱ S hK
  exact ⟨S, hconv⟩

-- Proof sketch: specialize the Chapter `19` owner
-- `DerivedExtStupidFiltrationSpectralSequenceData` to source complex `K^•` and target `ℱ[0]`,
-- then apply its boundedness-to-convergence field using the same bounded-above and degree-zero
-- bounded-below witnesses.
omit [LocallySmall (ringedSiteModuleCategory J 𝒪)]
  [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
  [WellPowered (ringedSiteModuleCategory J 𝒪)]
  [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
  [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
  [InitialMonoClass (ringedSiteModuleCategory J 𝒪)] in
/-- Example 21.32.1: (2) for a bounded-above complex `K^•` of `𝒪`-modules on a ringed site and an
`𝒪`-module `ℱ`, the stupid-filtration `Ext` spectral sequence exists with the Chapter `19` owner
data and converges. -/
theorem ringedSiteExtStupidFiltrationSpectralSequenceExists
    (K : Cpx) (ℱ : Mod) (hK : cochainComplexIsBoundedAbove K) :
    ∃ S : DerivedExtStupidSSData K ((single₀).obj ℱ),
      S.filteredComplex.convergesToCohomology S.spectralSequence := by
  classical
  -- Proof comment: choose the canonical Chapter `19` owner for the stupid-filtration spectral
  -- sequence attached to `K^•` and `ℱ[0]`.
  let S : DerivedExtStupidSSData K ((single₀).obj ℱ) :=
    Classical.choice
      (CategoryTheory.derivedExt_stupidFiltration_spectralSequence_exists
        K ((single₀).obj ℱ))
  -- Route correction: reuse the owner-level convergence field instead of unfolding the chosen
  -- filtered complex or spectral-sequence data.
  have hconv : S.filteredComplex.convergesToCohomology S.spectralSequence :=
    chosenStupidOwnerConverges J 𝒪 K ℱ S hK
  exact ⟨S, hconv⟩

omit [LocallySmall (ringedSiteModuleCategory J 𝒪)]
  [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
  [WellPowered (ringedSiteModuleCategory J 𝒪)]
  [HasWidePullbacks (ringedSiteModuleCategory J 𝒪)]
  [HasCoproducts (ringedSiteModuleCategory J 𝒪)]
  [InitialMonoClass (ringedSiteModuleCategory J 𝒪)] in
/-- Combined existence statement for the two spectral sequences in Example 21.32.1. -/
theorem ringedSiteExtSpectralSequencesExist
    (K : Cpx) (ℱ : Mod) (hK : cochainComplexIsBoundedAbove K) :
    (∃ S : DerivedExtCohSSData ((QMod).obj K) ((single₀).obj ℱ),
      S.filteredComplex.convergesToCohomology S.spectralSequence) ∧
      ∃ S : DerivedExtStupidSSData K ((single₀).obj ℱ),
        S.filteredComplex.convergesToCohomology S.spectralSequence := by
  -- Proof comment: combine the two already-constructed source-facing spectral sequences.
  refine ⟨?_, ?_⟩
  · exact ringedSiteExtCohomologySpectralSequenceExists J 𝒪 K ℱ hK
  · exact ringedSiteExtStupidFiltrationSpectralSequenceExists J 𝒪 K ℱ hK

end

end SheafOfModules.RingedSite
