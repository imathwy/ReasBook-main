import Mathlib
import ProbabilityTheory_Klenke_2020.Chap10.Theorem_10_1
import ProbabilityTheory_Klenke_2020.Chap11.Theorem_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Finset

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable [m0]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ m0}

local macro:max "absMaxUpTo(" X:term ", " n:term ", " ω:term ")" : term =>
  `((range ($n + 1)).sup' nonempty_range_add_one fun k ↦ |($X k $ω)|)

/- Exercise 11.1.1 is a `source-facing` maximal-inequality corollary in the discrete-time
martingale domain. The owner abstraction for the maximal event is the canonical running maximum
already used by `MeasureTheory.maximal_ineq`, while the chapter-level bridge layer is
`doobLp_tail_bound` together with the canonical Doob decomposition and its predictable-part
monotonicity criterion from Theorem 10.1. This exercise therefore stays `source-facing`: it keeps
the textbook absolute-maximal tail inequality but relies on those owner declarations rather than a
parallel local wrapper. -/
recall MeasureTheory.maximal_ineq
recall doobLp_tail_bound
recall canonical_doobDecomposition
recall submartingale_ae_monotone_predictablePart

-- Proof sketch: if `X` is a submartingale, combine Doob's decomposition with Theorem 11.2 applied
-- to the martingale part and the predictable monotonicity estimates for the finite-variation part.
-- If `X` is a supermartingale, apply the same argument to `-X`, noting that the running maxima of
-- `|-X|` and `|X|` agree pointwise and that `|(-X) n| = |X n|`.
/-- Exercise 11.1.1: for a real-valued submartingale or supermartingale, the tail of the maximal
absolute process up to time `n` is bounded by `|X_0|` and `|X_n|` with constants `1 / 2` and `9`.
-/
theorem submartingale_or_supermartingale_absMaxUpTo_tail_bound {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ ∨ Supermartingale X ℱ μ) (n : ℕ) (c : NNReal) :
    c * μ {ω | (c : ℝ) ≤ absMaxUpTo(X, n, ω)} ≤
      ENNReal.ofReal (μ[fun ω ↦ |X 0 ω|] / 2 + 9 * μ[fun ω ↦ |X n ω|]) := sorry
