import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap19.Remark_19_13_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [LocallySmall A] [WellPowered A]
  [HasWidePullbacks A] [HasCoproducts A] [InitialMonoClass A] [IsGrothendieckAbelian.{w} A]

/-- The `AddCommGrpCat`-valued filtered complexes used to package the spectral sequences in this
item. -/
abbrev AbFilteredComplex :=
  CochainComplex (FilteredObject AddCommGrpCat) ℤ

/-- The standard derived-category model attached to a Grothendieck abelian category in this item.
-/
local instance grothendieckAbelian_hasDerivedCategoryForRemark_19_13_11 :
    HasDerivedCategory A :=
  HasDerivedCategory.standard A

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

/-- The convergence package used in this file: the spectral sequence is associated to a filtered
complex and is bounded, so it converges to the cohomology of the underlying complex. -/
def filteredComplexAssociatedSpectralSequenceConverges
    (F : AbFilteredComplex)
    (E : CohomologicalSpectralSequence AddCommGrpCat 0) : Prop :=
  IsAssociatedToFilteredComplex F E ∧ CohomologicalSpectralSequence.IsBounded E

/-- The derived object corresponding to the cohomology object `H^j(M)` placed in degree `0`. -/
abbrev derivedCohomologyAsDerivedObject
    (M : DerivedCategory A) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj ((DerivedCategory.homologyFunctor A j).obj M)

/-- The derived object corresponding to the term `M^j` of a cochain complex, placed in degree `0`.
-/
abbrev cochainTermAsDerivedObject
    (M : CochainComplex A ℤ) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj (M.X j)

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
  /-- If `M ∈ D^-(A)` and `K ∈ D^+(A)`, then the renumbered spectral sequence is bounded and
  converges to `Ext^*(M, K)`. -/
  converges_of_boundedness :
    derivedCategoryMinusProperty M →
      derivedCategoryPlusProperty K →
      filteredComplexAssociatedSpectralSequenceConverges filteredComplex spectralSequence

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
  /-- If `M^•` is bounded above and `K ∈ D^+(A)`, then the spectral sequence is bounded and
  converges to `Ext^*(M, K)`. -/
  converges_of_boundedness :
    cochainComplexIsBoundedAbove M →
      derivedCategoryPlusProperty K →
      filteredComplexAssociatedSpectralSequenceConverges filteredComplex spectralSequence

-- Proof sketch: choose a complex representing `M`, filter it by the canonical truncations
-- `τ_{\le -p}`, apply Remark 19.13.8 to the resulting filtered Hom complex, and then renumber
-- the indices by `p = -j` and `q = i + 2j`. The resulting spectral sequence depends only on the
-- derived object `M`, not on the chosen representative, because quasi-isomorphic representatives
-- have canonically identified cohomology objects and give isomorphic filtered-Hom constructions.
/-- Remark 19.13.11: for objects `M, K` of the derived category of a Grothendieck abelian
category, there is a renumbered spectral sequence with `E'_2{}^{\, i, j} = Ext^i(H^{-j}(M), K)`;
if `M ∈ D^-(A)` and `K ∈ D^+(A)`, then this spectral sequence is bounded and converges to
`Ext^{i + j}(M, K)`. In this file, the chosen spectral sequence is packaged as
`DerivedExtCohomologySpectralSequenceData M K`. -/
theorem derivedExt_cohomology_spectralSequence_exists
    (M K : DerivedCategory A) :
    Nonempty (DerivedExtCohomologySpectralSequenceData M K) := sorry

-- Proof sketch: filter the chosen cochain complex `M^•` by the stupid truncations
-- `σ_{\ge p} M^•`, apply Remark 19.13.8 to the resulting filtered Hom complex, and identify the
-- graded pieces of the filtration with the single-term complexes `M^{-p}[p]`. If `M^•` is
-- bounded above and `K ∈ D^+(A)`, the same boundedness argument gives convergence to
-- `Ext^*(DerivedCategory.Q.obj M, K)`.
/-- The stupid-filtration spectral sequence associated to a cochain complex `M^•` has
`E_1^{p,q} = Ext^q(M^{-p}, K)` and converges to `Ext^{p + q}(M, K)` when `M^•` is bounded above
and `K ∈ D^+(A)`. -/
theorem derivedExt_stupidFiltration_spectralSequence_exists
    (M : CochainComplex A ℤ) (K : DerivedCategory A) :
    Nonempty (DerivedExtStupidFiltrationSpectralSequenceData M K) := sorry

end CategoryTheory
