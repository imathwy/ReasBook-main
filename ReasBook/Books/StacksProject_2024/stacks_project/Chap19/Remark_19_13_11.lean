import StacksProject_2024.stacks_project.Chap12.Definition_12_24_5
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_2
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap19.Remark_19_13_8

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [LocallySmall A] [WellPowered A]
  [HasWidePullbacks A] [HasCoproducts A] [InitialMonoClass A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory A]

local notation "AbFilteredComplex" => FilteredComplex AddCommGrpCat
local notation "single0" => DerivedCategory.singleFunctor A (0 : ℤ)

/- Domain-style sampling for Remark 19.13.11:
- primary domain: the two Chapter `19` source-facing `Ext` spectral sequences for a
  Grothendieck abelian category, namely the cohomology spectral sequence for an object of
  `D(A)` and the stupid-filtration spectral sequence for a cochain complex;
- canonical owners reused here:
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`,
  `derivedExtGroup`,
  `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`;
- source/core/bridge triage:
  `source-facing`: the two public structure owners and their existence theorems;
  `core/canonical`: the Chapter `12` filtered-complex and cohomological-spectral-sequence
    owners, together with the Chapter `19` owner `derivedExtGroup`;
  `bridge/view`: the degree-zero realizations `H^j(M)[0]` and `M^j[0]`.

This file intentionally keeps only the public API needed downstream. The concrete construction
proofs remain theorem-level proof debt rather than forcing additional local wrapper data. -/

/-- The bounded-below condition on a derived object, i.e. membership in `D^+(A)`. -/
def derivedCategoryPlusProperty (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, K.IsGE n

/-- The bounded-above condition on a derived object, i.e. membership in `D^-(A)`. -/
def derivedCategoryMinusProperty (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, K.IsLE n

/-- A cochain complex is bounded above when it is zero in all sufficiently high degrees. -/
def cochainComplexIsBoundedAbove (M : CochainComplex A ℤ) : Prop :=
  ∃ n : ℤ, M.IsStrictlyLE n

/-- The cohomology object `H^n(F^•)` of the underlying complex of an `AddCommGrpCat`-valued
filtered complex. -/
abbrev addCommGrpFilteredComplexCohomologyObject
    (F : AbFilteredComplex) (n : ℤ) : AddCommGrpCat :=
  (FilteredComplex.underlying F).homology n

/-- The derived object corresponding to the cohomology object `H^j(M)` placed in degree `0`. -/
abbrev derivedCohomologyAsDerivedObject
    (M : DerivedCategory A) (j : ℤ) : DerivedCategory A :=
  (single0).obj ((DerivedCategory.homologyFunctor A j).obj M)

/-- The derived object corresponding to the term `M^j` of a cochain complex, placed in degree
`0`. -/
abbrev cochainTermAsDerivedObject
    (M : CochainComplex A ℤ) (j : ℤ) : DerivedCategory A :=
  (single0).obj (M.X j)

/-- A chosen renumbered spectral sequence computing `Ext^*(M, K)` from the cohomology objects
`H^{-j}(M)` of `M`. The owner objects are an `AddCommGrpCat`-valued filtered complex and its
associated cohomological spectral sequence. -/
structure DerivedExtCohomologySpectralSequenceData
    (M K : DerivedCategory A) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E'_2`-page identifies with `Ext^i(H^{-j}(M), K)`. -/
  pageTwoIso :
    ∀ i j : ℤ,
      (spectralSequence.page 2).X (i, j) ≅
        derivedExtGroup (derivedCohomologyAsDerivedObject M (-j)) K i
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      addCommGrpFilteredComplexCohomologyObject filteredComplex n ≅
        derivedExtGroup M K n
  /-- If `M ∈ D^-(A)` and `K ∈ D^+(A)`, then the renumbered spectral sequence converges to the
  cohomology of the underlying filtered complex in the Chapter `12` sense, hence to
  `Ext^*(M, K)` via `abutmentIso`. -/
  converges_of_boundedness :
    derivedCategoryMinusProperty M →
      derivedCategoryPlusProperty K →
      filteredComplex.convergesToCohomology spectralSequence

/-- A chosen spectral sequence obtained from the filtration `F^p M^• = σ_{\ge p} M^•` on a
cochain complex `M^•`. The owner objects are an `AddCommGrpCat`-valued filtered complex and its
associated cohomological spectral sequence. -/
structure DerivedExtStupidFiltrationSpectralSequenceData
    (M : CochainComplex A ℤ) (K : DerivedCategory A) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E_1`-page identifies with `Ext^q(M^{-p}, K)`. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        derivedExtGroup (cochainTermAsDerivedObject M (-p)) K q
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, K)` for the
  derived object represented by `M^•`. -/
  abutmentIso :
    ∀ n : ℤ,
      addCommGrpFilteredComplexCohomologyObject filteredComplex n ≅
        derivedExtGroup (DerivedCategory.Q.obj M) K n
  /-- If `M^•` is bounded above and `K ∈ D^+(A)`, then the spectral sequence converges to the
  cohomology of the underlying filtered complex in the Chapter `12` sense, hence to
  `Ext^*(M, K)` via `abutmentIso`. -/
  converges_of_boundedness :
    cochainComplexIsBoundedAbove M →
      derivedCategoryPlusProperty K →
      filteredComplex.convergesToCohomology spectralSequence

attribute [instance] DerivedExtCohomologySpectralSequenceData.associated
attribute [instance] DerivedExtStupidFiltrationSpectralSequenceData.associated

/-- Remark 19.13.11: for objects `M, K` of the derived category of a Grothendieck abelian
category, there is a renumbered spectral sequence with `E'_2{}^{\, i, j} = Ext^i(H^{-j}(M), K)`;
if `M ∈ D^-(A)` and `K ∈ D^+(A)`, then this spectral sequence is bounded and converges to
`Ext^{i + j}(M, K)`. In this file, the chosen spectral sequence is packaged as
`DerivedExtCohomologySpectralSequenceData M K`. -/
theorem derivedExt_cohomology_spectralSequence_exists
    (M K : DerivedCategory A) :
    Nonempty (DerivedExtCohomologySpectralSequenceData M K) := by
  sorry

/-- The stupid-filtration spectral sequence associated to a cochain complex `M^•` has
`E_1^{p,q} = Ext^q(M^{-p}, K)` and converges to `Ext^{p + q}(M, K)` when `M^•` is bounded above
and `K ∈ D^+(A)`. -/
theorem derivedExt_stupidFiltration_spectralSequence_exists
    (M : CochainComplex A ℤ) (K : DerivedCategory A) :
    Nonempty (DerivedExtStupidFiltrationSpectralSequenceData M K) := by
  sorry

end CategoryTheory
