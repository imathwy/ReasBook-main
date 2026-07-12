import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap19.Remark_19_13_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open DerivedCategory
open scoped DerivedExt
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

/-- Local alias for the category of `R`-modules in the ambient universe. -/
private abbrev moduleCatOver (_R : Type u) [Ring _R] := ModuleCat.{u} _R

local notation "single₀" => singleFunctor (moduleCatOver R) (0 : ℤ)

/- Domain-style sampling for `15.68.0.1`.
- primary domain: the derived-`Ext` cohomology spectral sequence for a bounded-below derived
  object of `ModuleCat.{u} R`;
- sampled owner/canonical declarations in the same domain:
  `DerivedExtCohomologySpectralSequenceData`,
  `derivedExtCohomologySpectralSequence_exists`,
  `derivedExtGroup`,
  `Ext^i(X, Y)`,
  `H^j`;
- best owner abstraction: the Chapter `19` owner
  `DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj`, whose primitive fields are
  exactly the `E₂` spectral sequence, its page-two identification, its chosen abutment objects,
  the abutment comparison, and the boundedness consequence under `D⁻/D⁺` hypotheses;
- primitive data for the source-facing statement below: the owner package
  `DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj`;
- derived API: the owner fields `S.pageTwoIso` and `S.abutmentIso`, together with the boundedness
  consequence for `M[0]` and `K ∈ D⁺(R)`;
- source/core/bridge triage:
  `source-facing`: the existence of the `Ext` cohomology spectral sequence for `M` and `K`;
  `core/canonical`: `DerivedExtCohomologySpectralSequenceData`;
  `bridge/view`: the specialized page-two, abutment, and boundedness companions below, written in
    the Chapter `13` `Ext^i` and `H^j` notation rather than the raw `derivedExtGroup` field
    surface.
-/

theorem ext_cohomology_spectral_sequence_bounded
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R)))
    (S : DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj) :
    CohomologicalSpectralSequence.IsBounded S.spectralSequence := by
  have hM : DerivedCategoryIsBoundedAbove ((single₀).obj M) :=
    ⟨0, fun i hi ↦
      isZero_of_isLE ((single₀).obj M) 0 i hi⟩
  have hK : DerivedCategoryIsBoundedBelow K.obj :=
    (derivedCategory_t_plus_iff K.obj).1 K.property
  exact S.bounded_of_boundedness hM hK

section ExtCohomologySpectralSequence

variable [LocallySmall.{u} (moduleCatOver R)] [WellPowered.{u} (moduleCatOver R)]
  [CategoryTheory.Limits.HasWidePullbacks (moduleCatOver R)]
  [CategoryTheory.Limits.HasCoproducts (moduleCatOver R)]
  [CategoryTheory.Limits.InitialMonoClass (moduleCatOver R)]
  [IsGrothendieckAbelian (moduleCatOver R)]

/-- Helper for 15.68.0.1: specialize the Chapter `19` existence theorem directly on the local
`ModR`/`D⁺(ModR)` surface used by the source-facing statement. -/
theorem derivedExtCohomologySpectralSequence_exists_module_surface
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R))) :
    Nonempty
      (DerivedExtCohomologySpectralSequenceData
        ((single₀).obj M)
        K.obj) := by
  -- The Chapter `19` owner theorem applies directly to the specialized module-category inputs.
  exact
    derivedExtCohomologySpectralSequence_exists
      (𝒜 := moduleCatOver R)
      ((single₀).obj M)
      K.obj

/-- Helper for 15.68.0.1: the `E₂`-page term
`\operatorname{Ext}^i_R(M, H^j(K))`, expressed through the Chapter `19` owner surface. -/
abbrev derivedExtCohomologyPageTwo
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R))) (i j : ℤ) : AddCommGrpCat :=
  derivedExtGroup
    ((single₀).obj M)
    ((single₀).obj ((DerivedCategory.homologyFunctor (moduleCatOver R) j).obj K.obj))
    i

/-- Helper for 15.68.0.1: the abutment term
`\operatorname{Ext}^{n}_R(M, K)`, expressed through the Chapter `19` owner surface. -/
abbrev derivedExtCohomologyAbutment
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R))) (n : ℤ) : AddCommGrpCat :=
  derivedExtGroup ((single₀).obj M) K.obj n

/-- Helper for 15.68.0.1: a chosen abutment family for the Ext cohomology spectral sequence,
identified termwise with `\operatorname{Ext}^{*}_R(M, K)`. -/
def AbutsToDerivedExtCohomology
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R))) : Prop :=
  ∃ A : ℤ → AddCommGrpCat,
    ∀ n : ℤ,
      Nonempty (A n ≅ derivedExtCohomologyAbutment M K n)

/-- Helper for 15.68.0.1: a bounded `E₂`-cohomological spectral sequence whose second page is
`\operatorname{Ext}^i_R(M, H^j(K))` and whose chosen abutment objects identify with
`\operatorname{Ext}^{i + j}_R(M, K)`. -/
def IsDerivedExtCohomologySpectralSequence
    (E : E₂CohomologicalSpectralSequence AddCommGrpCat)
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R))) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ i j : ℤ,
      Nonempty ((E.page 2).X (i, j) ≅ derivedExtCohomologyPageTwo M K i j)) ∧
    AbutsToDerivedExtCohomology M K

omit [LocallySmall.{u} (moduleCatOver R)] [WellPowered.{u} (moduleCatOver R)]
  [CategoryTheory.Limits.HasWidePullbacks (moduleCatOver R)]
  [CategoryTheory.Limits.HasCoproducts (moduleCatOver R)]
  [CategoryTheory.Limits.InitialMonoClass (moduleCatOver R)]
  [IsGrothendieckAbelian (moduleCatOver R)] in
/-- Helper for 15.68.0.1: a Chapter `19` owner package provides the chosen abutment objects for
the source-facing Ext spectral sequence statement. -/
theorem abuts_to_derived_ext_cohomology_of_data
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R)))
    (S : DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj) :
    AbutsToDerivedExtCohomology M K := by
  -- Reuse the owner package's chosen abutment family and its termwise comparison isomorphisms.
  refine ⟨S.abutment, ?_⟩
  intro n
  exact ⟨S.abutmentIso n⟩

omit [LocallySmall.{u} (moduleCatOver R)] [WellPowered.{u} (moduleCatOver R)]
  [CategoryTheory.Limits.HasWidePullbacks (moduleCatOver R)]
  [CategoryTheory.Limits.HasCoproducts (moduleCatOver R)]
  [CategoryTheory.Limits.InitialMonoClass (moduleCatOver R)]
  [IsGrothendieckAbelian (moduleCatOver R)] in
/-- Helper for 15.68.0.1: a Chapter `19` owner package already satisfies the boundedness,
page-two, and abutment clauses of the source-facing Ext spectral sequence predicate. -/
theorem is_derived_ext_cohomology_spectral_sequence_of_data
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R)))
    (S : DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj) :
    IsDerivedExtCohomologySpectralSequence S.spectralSequence M K := by
  constructor
  · -- The boundedness clause is exactly the local boundedness packaging lemma proved above.
    exact ext_cohomology_spectral_sequence_bounded M K S
  constructor
  · -- The page-two comparison is one of the primitive fields of the owner package.
    intro i j
    exact ⟨S.pageTwoIso i j⟩
  · -- The abutment clause is packaged separately to keep the main theorem flat.
    exact abuts_to_derived_ext_cohomology_of_data M K S

-- Proof sketch: choose the Chapter `19` owner package for `M[0]` and `K`, then expose only the
-- three source-facing components needed here: boundedness, the `E₂` page identification, and the
-- abutment identification.
/-- 15.68.0.1: for an `R`-module `M` and a bounded-below derived `R`-complex `K ∈ D^+(R)`, there
exists a bounded cohomological spectral sequence whose second page is
`\operatorname{Ext}^i_R(M, H^j(K))` and whose abutment identifies with
`\operatorname{Ext}^{i + j}_R(M, K)`. -/
theorem exists_ext_cohomology_spectral_sequence
    (M : moduleCatOver R) (K : D⁺((moduleCatOver R))) :
    ∃ E : E₂CohomologicalSpectralSequence AddCommGrpCat,
      IsDerivedExtCohomologySpectralSequence E M K := by
  -- Extract the Chapter `19` owner package on the source-facing `ModR`/`D⁺(ModR)` inputs.
  obtain ⟨S⟩ := derivedExtCohomologySpectralSequence_exists_module_surface M K
  -- The chosen owner package already carries the boundedness, page-two, and abutment data.
  exact ⟨S.spectralSequence, is_derived_ext_cohomology_spectral_sequence_of_data M K S⟩

end ExtCohomologySpectralSequence

end

end CategoryTheory
