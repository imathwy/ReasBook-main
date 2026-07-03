import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_7
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap19.Remark_19_13_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe t w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory.{t} 𝒜]

local notation "D" => DerivedCategory 𝒜
local notation "single0" => DerivedCategory.singleFunctor 𝒜 (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor 𝒜

/-- The bounded-below condition on an object of `D(\mathcal A)`. -/
def DerivedCategoryIsBoundedBelow (K : D) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n →
    IsZero ((H i).obj K)

/-- The bounded-above condition on an object of `D(\mathcal A)`. -/
def DerivedCategoryIsBoundedAbove (K : D) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, n < i →
    IsZero ((H i).obj K)

/-- A renumbered cohomological spectral sequence computing `Ext^*(M, K)` from the cohomology
objects `H^j(K)` of an object `K` in the derived category. -/
structure DerivedExtCohomologySpectralSequenceData (M K : D) where
  /-- The spectral sequence starting on the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequence AddCommGrpCat
  /-- The `E₂`-page is identified with the groups `Ext^i(M, H^j(K))`, where `H^j(K)` is viewed as
  an object of the derived category concentrated in degree `0`. -/
  pageTwoIso :
    ∀ i j : ℤ,
      (spectralSequence.page 2).X (i, j) ≅
        derivedExtGroup M ((single0).obj ((H j).obj K)) i
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℤ → AddCommGrpCat
  /-- The abutment identifies with the groups `Ext^n(M, K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      abutment n ≅ derivedExtGroup M K n
  /-- If `M ∈ D^-(𝒜)` and `K ∈ D^+(𝒜)`, then the spectral sequence is bounded. -/
  bounded_of_boundedness :
    DerivedCategoryIsBoundedAbove M →
      DerivedCategoryIsBoundedBelow K →
      CohomologicalSpectralSequence.IsBounded spectralSequence

/-- A cohomological spectral sequence computing `Ext^*(M, Q.obj K)` from the terms `K^p` of a
bounded-below cochain complex `K^•`, using the stupid filtration `σ_{\ge p}`. -/
structure DerivedExtTermwiseSpectralSequenceData (M : D) (K : CochainComplex 𝒜 ℤ) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : FilteredComplex AddCommGrpCat
  /-- The spectral sequence starting on the `E₁`-page. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E₁`-page is identified with the groups `Ext^q(M, K^p)`, with `K^p` placed in degree
  `0` of the derived category. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        derivedExtGroup M ((single0).obj (K.X p)) q
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, Q.obj K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      filteredComplex.underlying.homology n ≅ derivedExtGroup M (DerivedCategory.Q.obj K) n
  /-- If `M ∈ D^-(𝒜)` and `K^•` is bounded below, then the associated spectral sequence
  converges to the cohomology of the underlying filtered complex in the Chapter `12` sense. -/
  converges_of_boundedness :
    DerivedCategoryIsBoundedAbove M →
      (∃ n : ℤ, K.IsStrictlyGE n) →
      filteredComplex.convergesToCohomology spectralSequence

attribute [instance] DerivedExtTermwiseSpectralSequenceData.associated

-- Proof sketch: apply Remark `19.13.8` to a representative `K^•` of `K` filtered by
-- `F^p K^• := τ_{\le -p}K^•`, identify the graded pieces with the cohomology objects `H^{-p}(K)`,
-- and then renumber indices by `p = -j` and `q = i + 2j`. The resulting `E₂`-spectral sequence
-- depends only on the derived object `K`, which is the independence-of-representative statement.
/-- Remark 19.13.9: for objects `M, K` of `D(\mathcal A)`, there is a cohomological spectral
sequence starting on the `E₂`-page with
`(E'_2)^{i,j} = \operatorname{Ext}^i(M, H^j(K))`, and this package depends only on the derived
object `K`, not on a chosen representative complex. If `M ∈ D^-(\mathcal A)` and
`K ∈ D^+(\mathcal A)`, the package also records boundedness, so it abuts to
`\operatorname{Ext}^{i + j}(M, K)`. -/
theorem derivedExtCohomologySpectralSequence_exists
    (M K : D) :
    Nonempty (DerivedExtCohomologySpectralSequenceData M K) := sorry

-- Proof sketch: filter a bounded-below representative `K^•` by the stupid filtration
-- `F^p K^• := σ_{\ge p}K^•`, apply the filtered-complex Ext spectral sequence from
-- Remark `19.13.8`, identify the graded pieces with the single-term complexes on the objects
-- `K^p`, and use the bounded-above hypothesis on `M` together with bounded-belowness of `K^•`
-- to obtain boundedness.
/-- Using the stupid filtration `σ_{\ge p}` on a bounded-below representative `K^•` yields a
cohomological spectral sequence with `E_1^{p,q} = \operatorname{Ext}^q(M, K^p)` abutting to
`\operatorname{Ext}^{p + q}(M, Q.obj K)`. The chosen package records the filtered-complex model,
its associated spectral sequence, and the Chapter `12` convergence witness under the boundedness
hypotheses. -/
theorem derivedExtTermwiseSpectralSequence_exists
    (M : D) (K : CochainComplex 𝒜 ℤ) :
    Nonempty (DerivedExtTermwiseSpectralSequenceData M K) := sorry

end CategoryTheory
