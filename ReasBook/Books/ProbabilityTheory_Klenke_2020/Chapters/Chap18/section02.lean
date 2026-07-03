import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_18_2_1 (from Items/Chap18) -/
open MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
variable [CompleteSpace E] [SecondCountableTopology E]

-- Proof sketch: apply Strassen's coupling characterization of the Lévy--Prokhorov distance and
-- then use Markov's inequality on the transport-cost random variable under a coupling realizing
-- the Wasserstein infimum. Rearranging the resulting estimate gives the squared form of the
-- textbook square-root bound.
/-- Exercise 18.2.1 (1): for probability measures on a Polish metric space, the
Lévy--Prokhorov distance is bounded above by the square root of the Wasserstein transport cost,
written here in the equivalent squared form over `ℝ≥0∞`. -/
theorem levyProkhorovDist_sq_le_wassersteinDistance
    (P Q : ProbabilityMeasure E) :
    ENNReal.ofReal (levyProkhorovDist (P : Measure E) (Q : Measure E)) ^ (2 : ℕ) ≤
      wassersteinDistance P Q := sorry

variable [BoundedSpace E]

-- Proof sketch: when `E` is bounded, use a coupling with Prohorov error close to
-- `levyProkhorovDist P Q`. The transport cost is controlled by `Metric.diam univ` on the matched
-- part of the coupling and by an additional `1` times the mismatch mass, giving the linear bound.
/-- Exercise 18.2.1 (2): if the metric space `E` has finite diameter, then the Wasserstein
distance is bounded above by `(diam(E) + 1)` times the Lévy--Prokhorov distance, with the
Wasserstein metric written as its defining coupling-cost infimum. -/
theorem wassersteinDistance_le_diam_add_one_mul_levyProkhorovDist
    (P Q : ProbabilityMeasure E) :
    wassersteinDistance P Q ≤
      ENNReal.ofReal
        ((Metric.diam (Set.univ : Set E) + 1) *
          levyProkhorovDist (P : Measure E) (Q : Measure E)) := sorry

end ProbabilityTheory

/-! ### Exercise_18_2_2 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [DiscreteMeasurableSpace (E × E)]
variable {Ω : Type v} [MeasurableSpace Ω]

variable {p : E → E → ℝ≥0∞}
variable {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z]

-- Proof sketch: view `Z` as the Markov chain on `E × E` with transition matrix
-- `independentCoalescentMatrix p`. The formulas from Example 18.6 show that the first and second
-- coordinate marginals of one step are both given by `p`; iterating the Markov property for `Z`
-- therefore identifies the coordinate laws at time `n` with `(discreteMatrixKernel p ^ n) x` and
-- `(discreteMatrixKernel p ^ n) y`, while the coordinate processes inherit the natural Markov
-- property from the bivariate chain.
/-- Exercise 18.2.2: if `Z` is the bivariate process from Example 18.6 with transition matrix
`independentCoalescentMatrix p`, then its coordinate process is a Markov coupling for `p`. In
other words, writing `X n ω = (Z n ω).1` and `Y n ω = (Z n ω).2`, the process `(X, Y)` is a
coupling with transition matrix `\bar p`. -/
theorem independentCoalescentChain_isMarkovCoupling :
    IsMarkovCoupling p P Z := sorry

end ProbabilityTheory

/-! ### Lemma_18_2 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: choose finitely many positive return times whose gcd is `statePeriod κ x`; the
-- Chapman-Kolmogorov semigroup law makes the positive return-time set at `x` closed under
-- addition, and the Frobenius coin-problem argument then shows that every sufficiently large
-- multiple of `statePeriod κ x` is a nonnegative combination of those return times and hence again
-- lies in `positiveTransitionStepSet κ x x`.
/-- Lemma 18.2: all sufficiently large multiples of the period `statePeriod κ x` are positive
self-return times of `x`, that is, they eventually belong to
`positiveTransitionStepSet κ x x`. By `mem_positiveTransitionStepSet_iff`, this is equivalent to
the positivity of the corresponding self-return probabilities. -/
theorem eventually_positive_self_return_probability_at_period_multiples
    (κ : Kernel E E) (x : E) :
    ∃ n_x : ℕ, ∀ ⦃n : ℕ⦄, n_x ≤ n →
      n * statePeriod κ x ∈ positiveTransitionStepSet κ x x :=
  sorry

end ProbabilityTheory

/-! ### Exercise_18_2_3 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']

/- Layering for Exercise 18.2.3:
- source-facing conclusion: for an aperiodic irreducible recurrent lattice random walk, the
  independent coalescent coupling succeeds from every starting pair;
- core/canonical owner: the increment law `ν : PMF (LatticePoint d)` with owner kernel
  `dirac_convolution_kernel ν.toMeasure`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law. -/

-- Proof sketch: let the two coordinates evolve independently until they meet, and consider their
-- difference process on `ℤ^d`. Translation invariance makes this difference a recurrent random
-- walk, so it hits `0` almost surely from every initial displacement. Once the independent
-- coalescent reaches the diagonal, `independentCoalescentMatrix` keeps the two coordinates
-- together forever, which is exactly the success criterion from Definition 18.5.
/-- Exercise 18.2.3 at the owner layer: if `X` is an aperiodic irreducible recurrent random walk
on `ℤ^d` with increment law `ν`, then every realization of the associated independent coalescent
chain is a successful Markov coupling. -/
theorem independentCoalescent_isSuccessfulMarkovCoupling_of_aperiodic_irreducible_recurrent_latticeRandomWalk
    {d : ℕ} (ν : PMF (LatticePoint d))
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    [IsMarkovProcessRealization
      (fun n ↦
        discreteMatrixKernel
          (independentCoalescentMatrix
            (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) ^ n)
      Pcouple Z]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    (hrec : IsRecurrentMarkovChain P X)
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure)) :
    IsSuccessfulMarkovCoupling
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) Pcouple Z := sorry

-- Proof sketch: if the walk is presented by a translation-invariant transition matrix `p`, then
-- the common increment law is encoded by the row at the origin, so the owner theorem above
-- applies to that intrinsic law.
/-- Bridge form of Exercise 18.2.3: if `X` is an aperiodic irreducible recurrent random walk on
`ℤ^d` with translation-invariant transition matrix `p`, then every realization of the associated
independent coalescent chain is a successful Markov coupling. -/
theorem
    translationInvariant_independentCoalescent_isSuccessfulMarkovCoupling_of_aperiodic_irreducible_recurrent_latticeRandomWalk
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (htranslation : IsTranslationInvariantStepMatrix p)
    (hrec : IsRecurrentMarkovChain P X)
    (haperiodic : IsAperiodic (discreteMatrixKernel p)) :
    IsSuccessfulMarkovCoupling p Pcouple Z := sorry

end ProbabilityTheory

/-! ### Exercise_18_2_4 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

local notation "AxisState" => ℤ × ℤ

private abbrev isHorizontalNeighbor (x y : AxisState) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2)

private abbrev isVerticalNeighbor (x y : AxisState) : Prop :=
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1)

private abbrev isAxisNeighbor (x y : AxisState) : Prop :=
  isHorizontalNeighbor x y ∨ isVerticalNeighbor x y

/-- The transition matrix of the walk on `ℤ²` whose vertical moves are blocked away from the
vertical axis: on the axis it is the symmetric nearest-neighbor walk, while off the axis it moves
horizontally by `±1` with probability `1 / 4` each and otherwise stays put with probability
`1 / 2`. -/
def vertical_axis_blocked_walk_transition_matrix : AxisState → AxisState → ℝ≥0∞
  | x, y =>
      if x.1 = 0 then
        if isAxisNeighbor x y then
          1 / 4
        else
          0
      else if isHorizontalNeighbor x y then
        1 / 4
      else if y = x then
        1 / 2
      else
        0

-- Proof sketch: this is just the defining case split for
-- `vertical_axis_blocked_walk_transition_matrix`.
/-- The axis-blocked walk transition matrix is given by the stated axis and off-axis cases. -/
theorem vertical_axis_blocked_walk_transition_matrix_apply (x y : AxisState) :
    vertical_axis_blocked_walk_transition_matrix x y =
      if x.1 = 0 then
        if (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
            (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
            (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
            (y.1 = x.1 ∧ y.2 = x.2 - 1) then
          1 / 4
        else
          0
      else if (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) then
        1 / 4
      else if y = x then
        1 / 2
      else
        0 := by
  simp [vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor,
    isHorizontalNeighbor, isVerticalNeighbor, or_assoc]

section RealizationResults

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : AxisState → ProbabilityMeasure Ω} {X : ℕ → Ω → AxisState}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) ^ n) P X]

-- Proof sketch: project the chain to its first coordinate. Away from the axis this coordinate is
-- a lazy nearest-neighbor walk on `ℤ` and it returns to `0` almost surely, while each visit to
-- the axis restarts a recurrent vertical excursion. The chain is therefore recurrent, but the
-- expected return time is infinite as in the two-dimensional simple random walk regime.
/-- Exercise 18.2.4 (1): every realization of the axis-blocked walk on `ℤ²` is null recurrent. -/
theorem vertical_axis_blocked_walk_isNullRecurrentMarkovChain :
    IsNullRecurrentMarkovChain P X := sorry

-- Proof sketch: the horizontal coordinate can always be moved one step toward `0`, along the
-- axis the walk can change the vertical coordinate by nearest-neighbor moves, and then the
-- horizontal coordinate can be moved away from the axis again. Concatenating such paths gives a
-- positive-probability route between any two states.
/-- Exercise 18.2.4 (2): every realization of the axis-blocked walk on `ℤ²` is irreducible. -/
theorem vertical_axis_blocked_walk_isIrreducibleMarkovChain :
    IsIrreducibleMarkovChain P X := sorry

end RealizationResults

-- Proof sketch: every off-axis state has a one-step self-loop of probability `1 / 2`, so its
-- period is `1`. Irreducibility then forces all states, including those on the vertical axis, to
-- have period `1`.
/-- Exercise 18.2.4 (3): the axis-blocked walk on `ℤ²` is aperiodic. -/
theorem vertical_axis_blocked_walk_isAperiodic :
    IsAperiodic (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) := sorry

section IndependentCoalescence

variable {Ω : Type v} [MeasurableSpace Ω]
variable {Pcouple : AxisState × AxisState → ProbabilityMeasure Ω}
variable {Z : ℕ → Ω → AxisState × AxisState}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦
    discreteMatrixKernel
      (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
  Pcouple Z]

-- Proof sketch: before coalescence the difference of the two coordinates evolves like the
-- difference of two independent copies of the axis-blocked walk. The null-recurrent structure lets
-- the pair separate repeatedly, so the diagonal is not trapped quickly enough for the tail
-- disagreement probabilities to tend to `0`. Exercise 18.2.2 already identifies the independent
-- coalescent realization as a Markov coupling, so this tail-condition failure is exactly the
-- negation of the canonical Chapter 18 owner `IsSuccessfulMarkovCoupling`.
/-- Exercise 18.2.4 (4): the independent coalescent chain built from the axis-blocked walk is not
a successful Markov coupling. -/
theorem independentCoalescentChain_not_isSuccessfulMarkovCoupling :
    ¬ IsSuccessfulMarkovCoupling vertical_axis_blocked_walk_transition_matrix Pcouple Z := sorry

-- Proof sketch: unpack `IsSuccessfulMarkovCoupling`; the failure comes from its tail-disagreement
-- field.
/-- For the axis-blocked walk, some initial pair has tail disagreement probabilities that do not
converge to `0`. -/
theorem independentCoalescentChain_tail_disagreement_not_tendsto_zero :
    ∃ x y : AxisState,
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          (Pcouple (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        Filter.atTop (nhds 0) := sorry

end IndependentCoalescence

end ProbabilityTheory
