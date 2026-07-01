import Mathlib
import stacks_project.Chap12.Definition_12_20_2
import stacks_project.Chap12.Lemma_12_24_2
import stacks_project.Chap12.Definition_12_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

section

variable [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]
variable (K : FilteredComplex 𝒜)

local notation "HFil" n => inducedCohomologyFiltration K n

private abbrev filtrationStage (n p : ℤ) : Subobject ((K.X n).obj) :=
  (K.X n).filtration.obj p

private abbrev cyclesSubobject (n : ℤ) : Subobject ((K.X n).obj) :=
  kernelSubobject ((K.d n (n + 1)).hom)

private abbrev boundariesSubobject (n : ℤ) : Subobject ((K.X n).obj) :=
  imageSubobject ((K.d (n - 1) n).hom)

/- Domain-style sampling for Lemma `12.24.10`.
- primary domain: weak convergence and abutment for the spectral sequence associated to a filtered
  cochain complex in an abelian category;
- sampled core/canonical declarations:
  `FilteredComplex.inducedCohomologyFiltration`,
  `DecreasingFiltration.IsSeparated`,
  `DecreasingFiltration.IsExhaustive`,
  `SpectralSequence.infinityPage`;
- best owner abstraction: the induced filtration `inducedCohomologyFiltration K n` on
  `H^n(K^•)` together with the canonical limit term
  `E.toPageOneSpectralSequence.infinityPage (p, n - p)`;
- primitive data: the filtered complex `K`, the stage subobjects of `K^{n-1}`, `K^n`, and
  `K^{n+1}`, and an associated spectral sequence `E`;
- derived API: the source-facing pagewise equalities `(12.24.6.2)` and `(12.24.6.1)`, the
  graded-piece / `E_∞` comparison, and the intersection/union criterion for the induced
  cohomology filtration;
- source/core/bridge triage:
  `source-facing`: `weaklyConvergesToCohomology`, `abutsToCohomology`,
    `weakConvergenceCriterion`, `cohomologyFiltrationCriterion`;
  `core/canonical`: `inducedCohomologyFiltration` and `SpectralSequence.infinityPage`;
  `bridge/view`: the representative-level subobject equalities inside `K^n` that compare the
    source formulas to those owner objects.

Only the source-facing predicates and their two bridge criteria stay public here; the auxiliary
comparison and representative wrappers remain internal. -/

/-- The eventual boundary representative
`⋃_r (F^p K^n ∩ im(F^{p-r+1} K^{n-1} ⟶ K^n)) + F^{p+1} K^n`
appearing in equation `(12.24.6.2)`. -/
def eventualBoundaryStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨆ r : ℕ,
    (filtrationStage K n p ⊓
        imageSubobject
          ((filtrationStage K (n - 1) (p - r + 1)).arrow ≫ (K.d (n - 1) n).hom)) ⊔
      filtrationStage K n (p + 1)

/-- The eventual cycle representative
`⋂_r (F^p K^n ∩ (d^n)⁻¹(F^{p+r} K^{n+1})) + F^{p+1} K^n`
appearing in equation `(12.24.6.1)`. -/
def eventualCycleStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨅ r : ℕ,
    (filtrationStage K n p ⊓
        (Subobject.pullback ((K.d n (n + 1)).hom)).obj
          (filtrationStage K (n + 1) (p + r))) ⊔
      filtrationStage K n (p + 1)

/-- The cycle representative
`(\ker d^n ∩ F^p K^n) + F^{p+1} K^n` for the `p`-th graded piece of cohomology. -/
def cohomologyCycleStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (cyclesSubobject K n ⊓ filtrationStage K n p) ⊔ filtrationStage K n (p + 1)

/-- The boundary representative
`(\operatorname{im} d^{n-1} ∩ F^p K^n) + F^{p+1} K^n` for the `p`-th graded piece of
cohomology. -/
def cohomologyBoundaryStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (boundariesSubobject K n ⊓ filtrationStage K n p) ⊔ filtrationStage K n (p + 1)

/-- The equalities of `(12.24.6.2)` and `(12.24.6.1)` for every degree and every filtration
index. This is the concrete pagewise criterion appearing in Lemma `12.24.10 (1)`. -/
def weakConvergenceCriterion : Prop :=
  ∀ n p : ℤ,
    eventualBoundaryStep K n p = cohomologyBoundaryStep K n p ∧
      cohomologyCycleStep K n p = eventualCycleStep K n p

-- For a chosen associated spectral sequence `E`, weak convergence to cohomology is the
-- identification of each graded piece `gr^p H^n(K^•)` with the antidiagonal limit term
-- `E_∞^{p, n - p}`. This comparison remains internal; the public owner is
-- `weaklyConvergesToCohomology`.
private abbrev weakConvergenceComparison (E : CohomologicalSpectralSequence 𝒜 0) : Prop :=
  ∀ n p : ℤ,
    Nonempty
      ((HFil n).gradedPiece p ≅
        E.toPageOneSpectralSequence.infinityPage (p, n - p))

/-- Definition 12.24.9 (1): the associated spectral sequence of a filtered complex weakly
converges to `H^*(K^•)` when some associated cohomological spectral sequence has
`E_∞^{p, n - p} ≅ gr^p H^n(K^•)` in every bidegree. Lemma `12.24.10 (1)` supplies the equivalent
pagewise criterion `(12.24.6.2)` and `(12.24.6.1)`. -/
def weaklyConvergesToCohomology : Prop :=
  ∃ (E : CohomologicalSpectralSequence 𝒜 0) (_ : IsAssociatedToFilteredComplex K E),
    weakConvergenceComparison K E

-- The representative `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` of the `p`-th step of
-- the filtration induced on `H^n(K^•)` is only auxiliary here, so it remains internal.
private abbrev cohomologyFiltrationRepresentative (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (cyclesSubobject K n ⊓ filtrationStage K n p) ⊔ boundariesSubobject K n

/-- The concrete intersection/union criterion on the representatives
`\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` from Lemma `12.24.10 (2)`. -/
def cohomologyFiltrationCriterion : Prop :=
  ∀ n : ℤ,
    (⨅ p : ℤ, cohomologyFiltrationRepresentative K n p) =
        boundariesSubobject K n ∧
      (⨆ p : ℤ, cohomologyFiltrationRepresentative K n p) =
        cyclesSubobject K n

/-- Definition 12.24.9 (2): the associated spectral sequence of a filtered complex abuts to
`H^*(K^•)` if it weakly converges and the induced cohomology filtration is separated and
exhaustive in every degree. -/
def abutsToCohomology : Prop :=
  weaklyConvergesToCohomology K ∧
    ∀ n : ℤ,
      DecreasingFiltration.IsSeparated (HFil n) ∧
        DecreasingFiltration.IsExhaustive (HFil n)

-- Proof sketch: compare the intrinsic filtration on `H^n(K^•)` with its textbook representatives
-- `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` inside `K^n`, using the quotient description
-- from Definition `12.24.5`.
/-- The induced cohomology filtration is separated and exhaustive exactly when the representatives
`\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` have intersection `\operatorname{im}(d^{n-1})`
and union `\ker(d^n)` in every degree. -/
theorem cohomologyFiltrationCriterion_iff_separatedExhaustive
    :
    (∀ n : ℤ,
      DecreasingFiltration.IsSeparated (HFil n) ∧
        DecreasingFiltration.IsExhaustive (HFil n)) ↔
      cohomologyFiltrationCriterion K := by
  sorry

-- Proof sketch: weak convergence is source-facingly the identification
-- `\mathrm{gr}^p H^n(K^•) \cong E_\infty^{p,n-p}`, while equations `(12.24.6.2)` and
-- `(12.24.6.1)` are the pagewise criterion forcing that identification.
/-- Lemma 12.24.10 (1): for a filtered complex in an abelian category, the associated spectral
sequence weakly converges to the cohomology of the underlying complex exactly when the equalities
of `(12.24.6.2)` and `(12.24.6.1)` hold in every degree and filtration step. -/
theorem weaklyConvergesToCohomology_iff
    :
    weaklyConvergesToCohomology K ↔
      weakConvergenceCriterion K := by
  sorry

-- Proof sketch: abutment means weak convergence together with separatedness and exhaustiveness of
-- the induced filtration, and the previous bridge identifies those intrinsic properties with the
-- textbook intersection/union criterion on
-- `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})`.
/-- Lemma 12.24.10 (2): for a filtered complex in an abelian category, the associated spectral
sequence abuts to the cohomology of the underlying complex exactly when it weakly converges and
the representatives `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` have intersection
`\operatorname{im}(d^{n-1})` and union `\ker(d^n)` in every degree. -/
theorem abutsToCohomology_iff
    :
    abutsToCohomology K ↔
      weaklyConvergesToCohomology K ∧
        cohomologyFiltrationCriterion K := by
  rw [abutsToCohomology]
  exact and_congr_right fun _ ↦ cohomologyFiltrationCriterion_iff_separatedExhaustive K

end

end FilteredComplex
end CategoryTheory
