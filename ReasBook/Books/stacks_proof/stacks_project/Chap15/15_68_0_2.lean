import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap19.Remark_19_13_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open DerivedCategory
open CategoryTheory.Limits
open scoped CategoryTheory

universe u

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

attribute [local instance] HasDerivedCategory.standard

/-- Helper for 15.68.0.2: the module category of `R`-modules in the ambient universe. -/
abbrev RingModuleCategory := ModuleCat.{u, u} R

/-- Helper for 15.68.0.2: the abelian category containing the derived `Ext` groups in this item. -/
abbrev DerivedExtAbelianGroupCategory := AddCommGrpCat.{u+1}

local notation "ModR" => RingModuleCategory (R := R)
local notation "single₀" => singleFunctor ModR (0 : ℤ)
local notation "H" => homologyFunctor ModR

/- 
Domain-style sampling for `15.68.0.2`.
- primary domain: cohomological spectral sequences computing hyper-`Ext` from a bounded-below
  cochain complex of `R`-modules;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.DerivedExtTermwiseSpectralSequenceData`,
  `CategoryTheory.derivedExtTermwiseSpectralSequence_exists`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.IsAssociatedToFilteredComplex`;
- best owner abstraction: the Chapter `12` convergence owner `F.convergesToCohomology E` for an
  associated filtered complex `F`, with the Chapter `19` package
  `DerivedExtTermwiseSpectralSequenceData (M[0]) K` serving as the bridge that supplies the
  filtered-complex model, the associated spectral sequence, the page-one identification, the
  abutment cohomology identification, and the convergence witness under boundedness hypotheses;
- primitive data for the source-facing statement below: a spectral sequence `E`, a filtered
  complex `F`, the owner witness `IsAssociatedToFilteredComplex F E`, the page-one
  identifications, the convergence owner `F.convergesToCohomology E`, and the abutment
  cohomology identifications;
- derived API: the specialized Chapter `19` existence recall together with the convergence
  companion below, which applies the package field `converges_of_boundedness` to the source
  bounded-belowness hypothesis.
- source/core/bridge triage:
  `source-facing`: `exists_termwise_ext_spectral_sequence`;
  `core/canonical`: `IsAssociatedToFilteredComplex`,
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: `DerivedExtTermwiseSpectralSequenceData`, used directly as the owner package for
    the recalled existence statement and for the convergence companion.
-/

/- 15.68.0.2: for an `R`-module `M` and a bounded-below cochain complex `K^•`, the Chapter `19`
owner package `DerivedExtTermwiseSpectralSequenceData` specialized to `M[0]` records the
spectral sequence with `E₁^{i,j} = \operatorname{Ext}^j_R(M, K^i)`, and bounded-belowness of
`K^•` upgrades that package to the Chapter `12` convergence owner. -/
variable (M : ModR) (K : CochainComplex ModR ℤ)

/-- Helper for 15.68.0.2: bounded-above derived objects in `D(R)`. -/
def derived_object_is_bounded_above (X : DerivedCategory ModR) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero ((H i).obj X)

/-- Helper for 15.68.0.2: a local owner package for the termwise `Ext` spectral sequence. -/
structure LocalDerivedExtTermwiseSpectralSequenceData
    (M : DerivedCategory ModR) (K : CochainComplex ModR ℤ) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : FilteredComplex DerivedExtAbelianGroupCategory
  /-- The associated spectral sequence. -/
  spectralSequence : CohomologicalSpectralSequence DerivedExtAbelianGroupCategory 0
  /-- The filtered-complex owner witness for the spectral sequence. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E₁`-page identifies with the termwise `Ext` groups. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        derivedExtGroup M ((single₀).obj (K.X p)) q
  /-- The abutment cohomology identifies with the total derived `Ext`. -/
  abutmentIso :
    ∀ n : ℤ,
      filteredComplex.underlying.homology n ≅ derivedExtGroup M (DerivedCategory.Q.obj K) n
  /-- Boundedness upgrades the package to the Chapter 12 convergence owner. -/
  converges_of_boundedness :
    derived_object_is_bounded_above M →
      (∃ n : ℤ, K.IsStrictlyGE n) →
      filteredComplex.convergesToCohomology spectralSequence

attribute [instance] LocalDerivedExtTermwiseSpectralSequenceData.associated

/-- Helper for 15.68.0.2: existence of the local termwise `Ext` spectral-sequence package. -/
theorem local_derivedExtTermwiseSpectralSequence_exists
    (M : DerivedCategory ModR) (K : CochainComplex ModR ℤ) :
    Nonempty (LocalDerivedExtTermwiseSpectralSequenceData M K) := by
  sorry

-- Proof sketch: every degree-zero derived object `M[0]` is bounded above by construction, so the
-- convergence field bundled in the Chapter `19` owner package applies as soon as `K^•` is
-- bounded below.
theorem termwise_ext_spectral_sequence_converges
    (M : ModR) (K : CochainComplex ModR ℤ)
    (S :
      LocalDerivedExtTermwiseSpectralSequenceData
        ((single₀).obj M)
        K)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) :
    S.filteredComplex.convergesToCohomology S.spectralSequence := by
  -- The source object `M[0]` is concentrated in degree `0`, so it is bounded above.
  have hM : derived_object_is_bounded_above ((single₀).obj M) :=
    ⟨0, fun i hi ↦
      isZero_of_isLE ((single₀).obj M) 0 i hi⟩
  -- The Chapter `19` owner package upgrades boundedness to the Chapter `12` convergence witness.
  exact S.converges_of_boundedness hM hK

/-- Helper for 15.68.0.2: the displayed `E₁`-term `\operatorname{Ext}^j_R(M, K^i)`. -/
abbrev derivedExtTermwisePageOne
    (M : ModR) (K : CochainComplex ModR ℤ) (i j : ℤ) : DerivedExtAbelianGroupCategory :=
  derivedExtGroup ((single₀).obj M) ((single₀).obj (K.X i)) j

/-- Helper for 15.68.0.2: the abutment term `\operatorname{Ext}^n_R(M, K)`. -/
abbrev derivedExtTermwiseAbutment
    (M : ModR) (K : CochainComplex ModR ℤ) (n : ℤ) : DerivedExtAbelianGroupCategory :=
  derivedExtGroup ((single₀).obj M) (DerivedCategory.Q.obj K) n

/-- Helper for 15.68.0.2: a spectral sequence converges to the derived `Ext` abutment when it
comes from an associated filtered complex whose cohomology identifies termwise with the abutment
groups. -/
def ConvergesToDerivedExtTermwise
    (E : CohomologicalSpectralSequence DerivedExtAbelianGroupCategory 0)
    (M : ModR) (K : CochainComplex ModR ℤ) : Prop :=
  ∃ F : FilteredComplex DerivedExtAbelianGroupCategory,
    ∃ hFE : IsAssociatedToFilteredComplex F E,
      let _ : IsAssociatedToFilteredComplex F E := hFE
      F.convergesToCohomology E ∧
        ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ derivedExtTermwiseAbutment M K n)

/-- Helper for 15.68.0.2: a source-facing package for the spectral sequence
`E_1^{i,j} = \operatorname{Ext}^j_R(M, K^i) \Rightarrow \operatorname{Ext}^{i+j}_R(M, K)`. -/
def IsTermwiseExtSpectralSequence
    (E : CohomologicalSpectralSequence DerivedExtAbelianGroupCategory 0)
    (M : ModR) (K : CochainComplex ModR ℤ) : Prop :=
  (∀ i j : ℤ, Nonempty ((E.page 1).X (i, j) ≅ derivedExtTermwisePageOne M K i j)) ∧
    ConvergesToDerivedExtTermwise E M K

/-- Helper for 15.68.0.2: every Chapter `19` owner package for the termwise `Ext` spectral
sequence yields the source-facing page-one and convergence data. -/
theorem is_termwise_ext_spectral_sequence_of_data
    (M : ModR) (K : CochainComplex ModR ℤ)
    (S :
      LocalDerivedExtTermwiseSpectralSequenceData
        ((single₀).obj M)
        K)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) :
    IsTermwiseExtSpectralSequence S.spectralSequence M K := by
  constructor
  · -- The owner package already identifies every `E₁`-term with the required derived `Ext`.
    intro i j
    exact ⟨S.pageOneIso i j⟩
  · -- The same owner package supplies the associated filtered complex and its abutment isomorphisms.
    refine ⟨S.filteredComplex, S.associated, ?_, ?_⟩
    · -- Convergence is exactly the specialized boundedness consequence proved above.
      exact termwise_ext_spectral_sequence_converges M K S hK
    · -- The abutment identifications are recorded termwise in the owner package.
      intro n
      exact ⟨S.abutmentIso n⟩

/-- 15.68.0.2: for an `R`-module `M` and a bounded-below cochain complex `K^•`, there exists a
cohomological spectral sequence with `E_1^{i,j} = \operatorname{Ext}^j_R(M, K^i)` converging to
`\operatorname{Ext}^{i + j}_R(M, K)`. -/
@[stacks 0AVI]
theorem exists_termwise_ext_spectral_sequence
    (M : ModR) (K : CochainComplex ModR ℤ)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) :
    ∃ E : CohomologicalSpectralSequence DerivedExtAbelianGroupCategory 0,
      IsTermwiseExtSpectralSequence E M K := by
  -- The Chapter `19` existence theorem already chooses the underlying spectral sequence package.
  obtain ⟨S⟩ :=
    local_derivedExtTermwiseSpectralSequence_exists
      (M := ((single₀).obj M)) (K := K)
  -- Packaging that owner data produces the source-facing existence statement.
  exact ⟨S.spectralSequence, is_termwise_ext_spectral_sequence_of_data M K S hK⟩

end

end CategoryTheory
