import AchimKlenkeLean.Items.Chap05.Definition_5_25
import AchimKlenkeLean.Items.Chap08.Example_8_27
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap20.Definition_20_30
import AchimKlenkeLean.Items.Chap20.Example_20_10
import AchimKlenkeLean.Items.Chap20.Example_20_3
import AchimKlenkeLean.Items.Chap20.Theorem_20_35
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory
open ProbabilityTheory.Kernel

noncomputable section

universe u

namespace ProbabilityTheory

section Basic

variable {E : Type u}

/- Example 20.32 is a `bridge/view`: the source-facing stationary Markov entropy formula is
expressed for the canonical path-space shift system through the chapter owner
`kolmogorov_sinai_entropy`, while the explicit block-law calculations below remain auxiliary
bridge lemmas. -/

/-- The stationary Markov weight of a block `x : Fin (n + 1) → E`, namely the initial mass of
`x 0` under `π` times the product of the successive transition probabilities along the block. -/
def stationaryMarkovWordWeight (π : PMF E) (p : E → E → ℝ≥0∞) (n : ℕ)
    (x : Fin (n + 1) → E) : ℝ≥0∞ :=
  π (x 0) * ∏ k : Fin n, p (x k.castSucc) (x k.succ)

-- Proof sketch: for `n = 0` the product over `Fin 0` is empty, so it is `1`.
/-- For a block of length `1`, the stationary Markov word weight is just the initial mass under
`π`. -/
theorem stationaryMarkovWordWeight_zero (π : PMF E) (p : E → E → ℝ≥0∞)
    (x : Fin 1 → E) :
    stationaryMarkovWordWeight π p 0 x = π (x 0) := by
  simp [stationaryMarkovWordWeight]

/-- The one-step transition entropy of a stationary Markov chain, namely the average of
`-log p(x,y)` against the stationary edge weights `π x * p(x,y)`. -/
def stationaryMarkovTransitionEntropy (π : PMF E) (p : E → E → ℝ≥0∞) : EReal :=
  -∑' x : E, ∑' y : E, (((π x * p x y : ℝ≥0∞) : EReal) * ENNReal.log (p x y))

-- Proof sketch: unfold `stationaryMarkovTransitionEntropy`; this is exactly the defining edge
-- entropy series.
/-- The stationary Markov transition entropy is the stationary edge-entropy series. -/
theorem stationaryMarkovTransitionEntropy_def (π : PMF E) (p : E → E → ℝ≥0∞) :
    stationaryMarkovTransitionEntropy π p =
      -∑' x : E, ∑' y : E, (((π x * p x y : ℝ≥0∞) : EReal) * ENNReal.log (p x y)) :=
  rfl

end Basic

section MeasurableHelpers

variable {E : Type u} [MeasurableSpace E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

/-- The measurable map recording the first `n + 1` coordinates of a path in `E^ℕ`. -/
def stationaryMarkovBlockMap (n : ℕ) : Stream' E → Fin (n + 1) → E :=
  fun ω i ↦ ω i

theorem measurable_stationaryMarkovBlockMap (n : ℕ) :
    Measurable (stationaryMarkovBlockMap n : Stream' E → Fin (n + 1) → E) := by
  exact measurable_pi_lambda _ fun i ↦ (measurable_pi_apply (i : ℕ))

theorem measurable_tail : Measurable (Stream'.tail : Stream' E → Stream' E) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i + 1)

end MeasurableHelpers

section PathSpace

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

/-- The stationary Markov path law on `E^ℕ`, obtained from the initial law `π` and the transition
matrix `p` via the canonical Ionescu-Tulcea trajectory measure. -/
def stationaryMarkovPathMeasure (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) :
    Measure (ℕ → E) :=
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel _ hp
  trajMeasure π.toMeasure
    (fun n ↦ comap (discreteMatrixKernel p) (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop))

instance stationaryMarkovPathMeasure_isProbabilityMeasure
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) :
    IsProbabilityMeasure (stationaryMarkovPathMeasure π p hp) := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel _ hp
  unfold stationaryMarkovPathMeasure
  letI : IsProbabilityMeasure π.toMeasure := inferInstance
  infer_instance

/-- The `(n + 1)`-block law of the stationary Markov path measure, viewed as a canonical
probability mass function on `Fin (n + 1) → E`. -/
def stationaryMarkovBlockLaw (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (n : ℕ) : PMF (Fin (n + 1) → E) := by
  let f : (ℕ → E) → Fin (n + 1) → E := stationaryMarkovBlockMap n
  let μ : Measure (ℕ → E) := stationaryMarkovPathMeasure π p hp
  letI : IsProbabilityMeasure μ := stationaryMarkovPathMeasure_isProbabilityMeasure π p hp
  letI : IsProbabilityMeasure (μ.map f) :=
    Measure.isProbabilityMeasure_map (measurable_stationaryMarkovBlockMap n).aemeasurable
  exact (μ.map f).toPMF

-- Proof sketch: evaluate the cylinder probability of the canonical Markov trajectory law on a
-- singleton block `x`, and unwind the Ionescu-Tulcea construction to obtain the product
-- `π (x 0) * ∏ k, p (x k.castSucc) (x k.succ)`.
/-- The canonical `(n + 1)`-block law has the expected stationary Markov word weights. -/
theorem stationaryMarkovBlockLaw_apply_eq_wordWeight
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (n : ℕ) (x : Fin (n + 1) → E) :
    stationaryMarkovBlockLaw π p hp n x = stationaryMarkovWordWeight π p n x := sorry

-- Proof sketch: combine the canonical Shannon-series formula `entropy_def` with the explicit block
-- weights from `stationaryMarkovBlockLaw_apply_eq_wordWeight`.
/-- The entropy of the canonical stationary Markov `(n + 1)`-block law is the Shannon series of
its word weights. -/
theorem entropy_stationaryMarkovBlockLaw_eq_shannon_series
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (n : ℕ) :
    entropy (stationaryMarkovBlockLaw π p hp n) =
      -∑' x : Fin (n + 1) → E,
          ((stationaryMarkovWordWeight π p n x : EReal) *
            ENNReal.log (stationaryMarkovWordWeight π p n x)) := by
  simp [entropy_def, stationaryMarkovBlockLaw_apply_eq_wordWeight]

-- Proof sketch: `coordinate_process_traj_measure_is_stationary_of_invariant` gives stationarity
-- of the canonical coordinate process under the Markov trajectory law started from `π`, and
-- `canonical_process_stationary_iff_measurePreserving_tail` rewrites that stationarity as
-- invariance of the path law under `Stream'.tail`.
omit [Countable E] in
/-- The stationary Markov path law on `E^ℕ` is preserved by the one-sided shift. -/
theorem stationaryMarkovShift_measurePreserving
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) :
    MeasurePreserving Stream'.tail
      (stationaryMarkovPathMeasure π p hp) (stationaryMarkovPathMeasure π p hp) := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel _ hp
  let π' : ProbabilityMeasure E := ⟨π.toMeasure, inferInstance⟩
  refine
    (canonical_process_stationary_iff_measurePreserving_tail
      (stationaryMarkovPathMeasure π p hp)).mp ?_
  simpa [π', Function.eval, stationaryMarkovPathMeasure] using
    coordinate_process_traj_measure_is_stationary_of_invariant (discreteMatrixKernel p) π' hπ

-- Proof sketch: expand the entropy of the block law using
-- `entropy_stationaryMarkovBlockLaw_eq_shannon_series`, split the logarithm of the product
-- defining `stationaryMarkovWordWeight`, and use the stationarity identity
-- `Kernel.Invariant (discreteMatrixKernel p) π.toMeasure` to show that each transition level
-- contributes the same one-step edge entropy.
/-- The entropy of the stationary `(n + 1)`-block law is the entropy of the initial distribution
plus `n` copies of the stationary one-step transition entropy. -/
theorem stationaryMarkovBlockEntropy_eq_initialEntropy_add_nsmul_transitionEntropy
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) (n : ℕ) :
    entropy (stationaryMarkovBlockLaw π p hp n) =
      entropy π + n • stationaryMarkovTransitionEntropy π p := sorry

end PathSpace

section FiniteState

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Fintype E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

/-- The time-`0` coordinate partition on `E^ℕ`, available in the finite-state case where the label
space `E` is finite. -/
def stationaryMarkovCoordinatePartition : MeasurableFinpartition (Stream' E) :=
  MeasurableFinpartition.ofSimpleFunc
    { toFun := Function.eval 0
      measurableSet_fiber' := fun x ↦ measurable_pi_apply 0 (measurableSet_singleton x)
      finite_range' := Set.toFinite _ }

-- Proof sketch: unfold `MeasurableFinpartition.dynamicalEntropy`; the `n`-block partition of
-- the time-`0` coordinate partition records the first `n` coordinates of the path, so its
-- partition entropy is the entropy of the canonical block law `stationaryMarkovBlockLaw`. Then
-- apply `stationaryMarkovBlockEntropy_eq_initialEntropy_add_nsmul_transitionEntropy`.
/-- In the finite-state case, the dynamical entropy of the time-`0` coordinate partition equals
the stationary one-step transition entropy. -/
theorem stationaryMarkovCoordinatePartition_dynamicalEntropy_eq_transitionEntropy
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) :
    h(stationaryMarkovPathMeasure π p hp, Stream'.tail, measurable_tail;
      stationaryMarkovCoordinatePartition) =
      stationaryMarkovTransitionEntropy π p := sorry

-- Proof sketch: on `E^ℕ` with finite `E`, the backward iterates of the time-`0` coordinate
-- partition recover all cylinder sets, hence generate the product σ-algebra.
/-- The time-`0` coordinate partition is a generator for the one-sided shift in the finite-state
case. -/
theorem stationaryMarkovCoordinatePartition_is_generator :
    is_generator Stream'.tail
      (stationaryMarkovCoordinatePartition : MeasurableFinpartition (Stream' E)) := sorry

-- Proof sketch: apply `kolmogorov_sinai_of_generator` to the finite-state time-`0` coordinate
-- partition and then use
-- `stationaryMarkovCoordinatePartition_dynamicalEntropy_eq_transitionEntropy`.
/-- Finite-state companion to Example 20.32: the chapter generator theorem identifies the
Kolmogorov--Sinai entropy of the stationary Markov shift with the mean one-step transition
entropy. -/
theorem stationaryMarkovShiftEntropy_eq_transitionEntropy_of_fintype
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) :
    h(stationaryMarkovPathMeasure π p hp, Stream'.tail, measurable_tail) =
      stationaryMarkovTransitionEntropy π p := by
  let part : MeasurableFinpartition (Stream' E) := stationaryMarkovCoordinatePartition
  have hgen : is_generator Stream'.tail part := stationaryMarkovCoordinatePartition_is_generator
  rw [kolmogorov_sinai_of_generator
        (stationaryMarkovPathMeasure π p hp)
        (stationaryMarkovShift_measurePreserving π p hp hπ) part hgen]
  simpa [part] using
    stationaryMarkovCoordinatePartition_dynamicalEntropy_eq_transitionEntropy π p hp hπ

end FiniteState

section PathSpace

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

-- Proof sketch: the canonical path-space system is the one-sided shift `Stream'.tail` acting on
-- the stationary Markov trajectory law. The finite-state bridge through
-- `stationaryMarkovCoordinatePartition_dynamicalEntropy_eq_transitionEntropy` records the chapter
-- owner interpretation, and the same block-law entropy computation yields the countable-state
-- formula.
/-- Example 20.32: for a stationary countable-state Markov chain with transition matrix `p` and
stationary distribution `π`, the Kolmogorov--Sinai entropy of the canonical one-sided shift system
on the Markov path law equals the mean one-step transition entropy
`-∑' x, ∑' y, π x * p x y * log (p x y)`, i.e. formula `(20.9)`. -/
theorem stationaryMarkovShiftEntropy_eq_transitionEntropy
    (π : PMF E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) :
    h(stationaryMarkovPathMeasure π p hp, Stream'.tail, measurable_tail) =
      stationaryMarkovTransitionEntropy π p := sorry

end PathSpace

end ProbabilityTheory
