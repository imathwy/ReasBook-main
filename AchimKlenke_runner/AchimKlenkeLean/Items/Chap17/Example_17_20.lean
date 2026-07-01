import AchimKlenkeLean.Items.Chap09.Definition_9_10
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap17.Lemma_17_45
import AchimKlenkeLean.Items.Chap17.Theorem_17_8
import AchimKlenkeLean.Items.Chap03.Definition_3_9
import AchimKlenkeLean.Items.Chap26.Exercise_26_3_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Example 17.20 is `source-facing`: for an arbitrary initial population `x`, the branching
process `branchingProcess x Y` driven by an i.i.d. offspring array has one-step law
`p(x,y) = q_y^{*x}`. The primitive data is the recursive offspring-convolution family `q^{*x}`.
Its `core/canonical` one-step owner is the stochastic matrix
`branchingTransitionMatrix q : ℕ → ℕ → ℝ≥0∞` together with the associated discrete kernel
`branchingTransitionKernel q = discreteMatrixKernel (branchingTransitionMatrix q)`. The
real-valued singleton formula is only a `bridge/view` companion. At the process level, the
ambient Chapter 17 owner is `HasNaturalMarkovProperty μ Z`, while the one-ancestor Chapter 3
owner `IsGaltonWatsonProcess Z μ q` is a `bridge/view` specialization obtained by taking `x = 1`
and recovering the offspring array with `IsGaltonWatsonProcess.exists_offspring`. -/

/-- The `x`-fold offspring law obtained by convolving the one-particle offspring distribution `q`
`x` times. This is the distribution denoted `q^{*x}` in the textbook. -/
def branchingOffspringPMF (q : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | n + 1 =>
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l)

scoped notation:arg q "^{*" x "}" => branchingOffspringPMF q x

-- Proof sketch: unfold the recursive definition of `branchingOffspringPMF` at `0`.
/-- The zeroth offspring convolution is the Dirac mass at `0`. -/
theorem branchingOffspringPMF_zero (q : PMF ℕ) :
    branchingOffspringPMF q 0 = PMF.pure 0 := sorry

-- Proof sketch: unfold the recursive definition at `n + 1`; the next convolution adds one more
-- offspring variable with law `q`.
/-- The successor step of the offspring-convolution recursion. -/
theorem branchingOffspringPMF_succ (q : PMF ℕ) (n : ℕ) :
    branchingOffspringPMF q (n + 1) =
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l) := sorry

/-- The branching-process transition matrix `p(x,y) = q^{*x}_y` attached to the offspring
distribution `q`. This is the textbook matrix view of the recursive offspring law. -/
def branchingTransitionMatrix (q : PMF ℕ) : ℕ → ℕ → ℝ≥0∞ :=
  fun x y ↦ branchingOffspringPMF q x y

-- Proof sketch: each row of `branchingTransitionMatrix q` is the PMF `q^{*x}`, so its total mass
-- is `1`.
/-- The branching-process transition matrix is stochastic. -/
theorem branchingTransitionMatrix_isStochasticMatrix (q : PMF ℕ) :
    IsStochasticMatrix (branchingTransitionMatrix q) := sorry

/-- The one-step transition kernel of the branching process associated with the offspring law `q`,
expressed through the canonical discrete-matrix kernel owner. -/
def branchingTransitionKernel (q : PMF ℕ) : Kernel ℕ ℕ :=
  discreteMatrixKernel (branchingTransitionMatrix q)

-- Proof sketch: `branchingTransitionMatrix q` was defined from the row PMFs `q^{*x}`.
/-- Evaluating the branching transition matrix at `(x,y)` gives the `y`-mass of the `x`-fold
offspring convolution. -/
theorem branchingTransitionMatrix_apply (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionMatrix q x y = (q^{*x}) y := rfl

-- Proof sketch: unfold `branchingTransitionKernel`; `discreteMatrixKernel` stores exactly the row
-- measures determined by the point masses `q^{*x}_y`, which is the PMF measure
-- `(branchingOffspringPMF q x).toMeasure`.
/-- Evaluating the branching transition kernel at `x` gives the measure associated with the
`x`-fold offspring PMF. -/
theorem branchingTransitionKernel_apply (q : PMF ℕ) (x : ℕ) :
    branchingTransitionKernel q x = (q^{*x}).toMeasure := sorry

-- Proof sketch: evaluate `branchingTransitionKernel q x` via `branchingTransitionKernel_apply`
-- and then compute the singleton mass of the PMF `q^{*x}`.
/-- The singleton mass of the branching transition kernel is the corresponding stochastic-matrix
entry. -/
theorem branchingTransitionKernel_apply_singleton (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionKernel q x {y} = branchingTransitionMatrix q x y := sorry

/-- Example 17.20: the branching process started from an arbitrary population `x` and driven by
an i.i.d. offspring array with common law `q` has one-step conditional law given by the branching
kernel whose matrix entries are `p(x,y) = q^{*x}_y`. -/
theorem branchingProcess_one_step_conditionalProb_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    ⦃A : Set ℕ⦄ (hA : MeasurableSet A) (n : ℕ) :
    P⟦branchingProcess x Y (n + 1) ⁻¹' A | generatedFiltrationSpace (branchingProcess x Y) n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionKernel q (branchingProcess x Y n ω)).real A := sorry

-- Proof sketch: specialize
-- `branchingProcess_one_step_conditionalProb_eq_transitionKernel` to the singleton set `{y}`
-- and rewrite the singleton kernel mass with `branchingTransitionKernel_apply_singleton`.
/-- The singleton-state form of Example 17.20 is the textbook matrix formula
`P[Z_{n+1} = y | Z_n] = p(Z_n,y)` for the branching process started from `x`. -/
theorem branchingProcess_one_step_conditionalProb_eq_transitionMatrix
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n y : ℕ) :
    P⟦branchingProcess x Y (n + 1) ⁻¹' {y} |
        generatedFiltrationSpace (branchingProcess x Y) n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionMatrix q (branchingProcess x Y n ω) y).toReal := sorry

-- Proof sketch: the measurable-coordinate hypothesis gives the first owner field of
-- `HasNaturalMarkovProperty`, and the one-step kernel identity from
-- `branchingProcess_one_step_conditionalProb_eq_transitionKernel` iterates through the discrete
-- natural history on the countable state space `ℕ`.
/-- The branching process started from `x` has the natural Markov property on `ℕ` under its
offspring-array law. -/
theorem branchingProcess_hasNaturalMarkovProperty
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (h_meas : ∀ n, Measurable (branchingProcess x Y n)) :
    HasNaturalMarkovProperty (P : Measure Ω) (branchingProcess x Y) := sorry

-- Proof sketch: recover the offspring array from the Chapter 3 owner and identify `Z` with the
-- one-ancestor branching process `branchingProcess 1 offspring`; then apply the source-facing
-- branching-process theorem above.
/-- The Chapter 3 one-ancestor Galton--Watson owner specializes the source-facing branching
transition law of Example 17.20. -/
theorem galtonWatsonProcess_one_step_conditionalProb_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Z : ℕ → Ω → ℕ)
    (hZ : IsGaltonWatsonProcess Z (P : Measure Ω) q)
    ⦃A : Set ℕ⦄ (hA : MeasurableSet A) (n : ℕ) :
    P⟦Z (n + 1) ⁻¹' A | generatedFiltrationSpace Z n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionKernel q (Z n ω)).real A := sorry

-- Proof sketch: specialize the preceding bridge theorem to the singleton set `{y}` and rewrite
-- the singleton kernel mass with `branchingTransitionKernel_apply_singleton`.
/-- The Chapter 3 one-ancestor owner also yields the textbook singleton-matrix formula
`P[Z_{n+1} = y | Z_n] = p(Z_n,y)`. -/
theorem galtonWatsonProcess_one_step_conditionalProb_eq_transitionMatrix
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Z : ℕ → Ω → ℕ)
    (hZ : IsGaltonWatsonProcess Z (P : Measure Ω) q)
    (n y : ℕ) :
    P⟦Z (n + 1) ⁻¹' {y} | generatedFiltrationSpace Z n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionMatrix q (Z n ω) y).toReal := sorry

-- Proof sketch: apply `branchingProcess_hasNaturalMarkovProperty` to the recovered offspring
-- array and transport the result along the one-ancestor identification of `Z`.
/-- A measurable Galton--Watson process has the natural Markov property on `ℕ`. -/
theorem galtonWatsonProcess_hasNaturalMarkovProperty
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Z : ℕ → Ω → ℕ)
    (hZ : IsGaltonWatsonProcess Z (P : Measure Ω) q)
    (hZ_meas : ∀ n, Measurable (Z n)) :
    HasNaturalMarkovProperty (P : Measure Ω) Z := sorry

end ProbabilityTheory
