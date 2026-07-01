import AchimKlenkeLean.Items.Chap09.Example_9_4
import Mathlib.Probability.Martingale.BorelCantelli

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u}

/-- The local time of an integer-valued walk at `0`, counting visits before time `n`. -/
noncomputable def simpleRandomWalkLocalTimeAtZero (X : ℕ → Ω → ℤ) : ℕ → Ω → ℝ :=
  BorelCantelli.process (fun
    | 0 => ∅
    | n + 1 => {ω | X n ω = 0})

-- Proof sketch: unfold the event-counting owner process, split the cumulative sum over
-- `Finset.range (n + 1)` into `Finset.range n` and the last index `n`, and observe that the new
-- contribution is `1` exactly on the event `X n = 0`.
/-- The local time at `0` evolves by adding the indicator of the event that the walk is at `0` at
the previous time. -/
theorem simpleRandomWalkLocalTimeAtZero_succ (X : ℕ → Ω → ℤ) (n : ℕ) :
    simpleRandomWalkLocalTimeAtZero X (n + 1) =
      fun ω ↦ simpleRandomWalkLocalTimeAtZero X n ω +
        if X n ω = 0 then 1 else 0 := by
  ext ω
  unfold simpleRandomWalkLocalTimeAtZero
  simp only [BorelCantelli.process]
  rw [Finset.sum_range_succ, Pi.add_apply]
  congr
  change ({ω | X n ω = 0} : Set Ω).indicator (1 : Ω → ℝ) ω = if X n ω = 0 then 1 else 0
  by_cases h : X n ω = 0 <;> simp [h]

section SymmetricSimpleRandomWalk

variable [MeasurableSpace Ω]
variable {P : Measure Ω} {X : ℕ → Ω → ℤ}
variable (hX_zero : X 0 = 0)
variable (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
variable (hX_law : ∀ n,
  HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)

local notation "Xℝ" => fun n ω ↦ (X n ω : ℝ)
local notation "ℱX" =>
  Filtration.natural Xℝ (symmetricSimpleRandomWalk_real_stronglyMeasurable hX_zero hX_law)
local instance : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure

include hX_zero hX_indep hX_law

-- Proof sketch: identify `|X|` as a submartingale for the natural filtration of the walk, apply
-- the canonical formula for `predictablePart`, and compute the one-step conditional expectation of
-- `|(X_{i+1})| - |X_i|` using the symmetric `±1` increment law. The increment is `1` exactly when
-- `X_i = 0`, so the predictable part is the local-time process.
/-- For a symmetric simple random walk, the predictable part in Doob's decomposition of the
absolute-value process is exactly the local time at `0`. -/
theorem symmetricSimpleRandomWalk_abs_predictablePart_eq_localTimeAtZero
    : predictablePart (fun n ω ↦ |Xℝ n ω|) ℱX P = simpleRandomWalkLocalTimeAtZero X := sorry

-- Proof sketch: integrate the identity from
-- `symmetricSimpleRandomWalk_abs_predictablePart_eq_localTimeAtZero`, use the Doob decomposition
-- `|X| = martingalePart |X| + predictablePart |X|`, and note that the martingale part has mean
-- `0` at each time.
/-- For a symmetric simple random walk, the expectation of the absolute position equals the
expected local time at `0`. -/
theorem symmetricSimpleRandomWalk_integral_abs_eq_integral_localTimeAtZero
    (n : ℕ) : ∫ ω, |Xℝ n ω| ∂P = ∫ ω, simpleRandomWalkLocalTimeAtZero X n ω ∂P := sorry

-- Proof sketch: first identify the expectation of `|X_n|` with the expected local time at `0`.
-- Expand the local time as the finite sum of the indicators of the return events `{X_i = 0}`,
-- rewrite the integral of each indicator as `P (X_i = 0)`, use the standard symmetric random-walk
-- return probabilities `P[X_{2j} = 0] = (Nat.choose (2 * j) j : ℝ) / 4^j` and
-- `P[X_{2j+1} = 0] = 0`, and collect the even indices.
/-- Example 10.8: for a one-dimensional symmetric simple random walk, the expectation of the
absolute position at time `n` equals the expected local time at `0`, hence
`∑_{j=0}^{⌊(n-1)/2⌋} \binom{2j}{j} 4^{-j}`. -/
theorem symmetricSimpleRandomWalk_integral_abs_eq_centralBinomialSum
    (n : ℕ) :
    ∫ ω, |Xℝ n ω| ∂P =
      ∑ j ∈ Finset.range ((n + 1) / 2), (Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j := sorry

end SymmetricSimpleRandomWalk
