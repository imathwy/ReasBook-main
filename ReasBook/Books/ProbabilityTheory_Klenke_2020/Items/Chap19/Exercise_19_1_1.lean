import ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8
import ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_12
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

open Classical

attribute [local instance] Classical.propDecidable

variable {E : Type u} {Ω : Type v}

section EntranceTime

variable [MeasurableSpace Ω]

/-- The chain started from every state outside `A` hits `A` almost surely at the first entrance
time `τ_A = hittingAfter X A 1`. -/
def HitsSetAlmostSurely (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) : Prop :=
  ∀ x : E, x ∉ A → (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1

-- Proof sketch: unfold `HitsSetAlmostSurely`; this is exactly the pointwise almost-sure finiteness
-- of the first entrance time into `A` from every starting state outside `A`.
/-- Hitting `A` almost surely means that `τ_A` is finite with probability `1` from every state in
`E \ A`. -/
theorem hitsSetAlmostSurely_iff (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) :
    HitsSetAlmostSurely P X A ↔
      ∀ x : E, x ∉ A → (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1 :=
  Iff.rfl

end EntranceTime

section KilledGreenFunction

variable [MeasurableSpace Ω]

/- Layering for Exercise 19.1.1:
- `source-facing`: `killedVisitCount` and `killedGreenFunction`, the intrinsic visit-count and
  Green-function objects for the chain killed on first entrance into `A`.
- `core/canonical`: `hittingAfter`, `stoppedValue`, and the Chapter 17 Green-function framework
  around expected visit counts.
- `bridge/view`: the finite-state real matrices below, obtained from the owner kernel
  `discreteMatrixKernel p` and from `killedGreenFunction` by taking singleton masses and
  `ENNReal.toReal`. -/

/-- The pathwise visit count of the chain killed on entering `A`. If the initial state `x` already
lies in `A`, only the time-`0` visit survives; if `x ∉ A` and `y ∈ A`, the only possible visit is
the entrance hit at time `hittingAfter X A 1`; if `x, y ∉ A`, this counts visits to `y` strictly
before the first entrance into `A`. -/
def killedVisitCount (X : ℕ → Ω → E) (A : Set E) (x y : E) (ω : Ω) : ℝ≥0∞ :=
  if x ∈ A then
    if x = y then 1 else 0
  else if y ∈ A then
    if hittingAfter X A 1 ω < ⊤ ∧ stoppedValue X (hittingAfter X A 1) ω = y then 1 else 0
  else
    Measure.count {n : ℕ | (n : ℕ∞) < hittingAfter X A 1 ω ∧ X n ω = y}

/-- The intrinsic Green function of the chain killed on first entrance into `A`, defined as the
expected value of `killedVisitCount`. -/
def killedGreenFunction
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ≥0∞ :=
  ∫⁻ ω, killedVisitCount X A x y ω ∂(P x : Measure Ω)

-- Proof sketch: if `x ∈ A`, then `killedVisitCount` is definitionally the constant Kronecker-delta
-- pathwise count, so its expectation is the same delta value.
/-- If the chain starts inside `A`, the killed Green function is the Kronecker delta at the
starting point. -/
theorem killedGreenFunction_eq_kroneckerDelta_of_mem
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) {x y : E} (hx : x ∈ A) :
    killedGreenFunction P X A x y = if x = y then 1 else 0 := sorry

-- Proof sketch: for `x ∉ A` and `y ∈ A`, the definition of `killedVisitCount` reduces pointwise
-- to the indicator of the event that the first entrance into `A` occurs at `y`; integrating that
-- indicator gives the corresponding entrance distribution.
/-- If `x ∉ A` and `y ∈ A`, the killed Green function at `(x, y)` is the probability that the
first entrance into `A` occurs at `y`. -/
theorem killedGreenFunction_eq_firstEntranceMeasure
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E)
    {x y : E} (hx : x ∉ A) (hy : y ∈ A) :
    killedGreenFunction P X A x y =
      (P x : Measure Ω)
        {ω | hittingAfter X A 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X A 1) ω = y} := sorry

end KilledGreenFunction

section MatrixBridge

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Bridge/view: the finite-state real matrix obtained from the owner kernel
`discreteMatrixKernel p` by killing rows indexed by `A`. -/
def killedKernelMatrixView (p : E → E → ℝ≥0∞) (A : Set E) : Matrix E E ℝ :=
  fun x y ↦ if x ∈ A then 0 else (((discreteMatrixKernel p) x) ({y} : Set E)).toReal

/-- Bridge/view: the real matrix of the owner kernel `discreteMatrixKernel p` restricted to the
state space `E \ A`. -/
def restrictedKernelMatrixView (p : E → E → ℝ≥0∞) (A : Set E) :
    Matrix (↥(Aᶜ)) (↥(Aᶜ)) ℝ :=
  fun x y ↦ (((discreteMatrixKernel p) x) ({(y : E)} : Set E)).toReal

-- Proof sketch: evaluate the kernel `discreteMatrixKernel p` on the singleton `{y}`; on a
-- discrete state space this singleton mass is exactly `p x y`, and the extra `if` kills the rows
-- indexed by `A`.
/-- Evaluating `killedKernelMatrixView` recovers the row-killed transition formula in finite-state
real-matrix coordinates. -/
theorem killedKernelMatrixView_apply
    (p : E → E → ℝ≥0∞) (A : Set E) (x y : E) :
    killedKernelMatrixView p A x y = if x ∈ A then 0 else (p x y).toReal := sorry

-- Proof sketch: on `Aᶜ` there is no row-killing term, and the singleton mass of
-- `discreteMatrixKernel p` is exactly the original transition weight `p x y`.
/-- On the restricted state space `E \ A`, `restrictedKernelMatrixView` is the original transition
matrix written in real-valued coordinates. -/
theorem restrictedKernelMatrixView_apply
    (p : E → E → ℝ≥0∞) (A : Set E) (x y : ↥(Aᶜ)) :
    restrictedKernelMatrixView p A x y = (p x y).toReal := sorry

end MatrixBridge

section

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [Fintype E]
variable [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Bridge/view: the finite-state real matrix obtained from the intrinsic killed Green function by
taking `ENNReal.toReal` entrywise. -/
def killedGreenMatrixView (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) :
    Matrix E E ℝ :=
  fun x y ↦ (killedGreenFunction P X A x y).toReal

-- Proof sketch: use the almost-sure finiteness of the first entrance time into `A` to identify
-- the Neumann series of the killed kernel matrix with the intrinsic killed Green function; this
-- produces a two-sided inverse for `1 - killedKernelMatrixView p A`.
/-- Exercise 19.1.1 (1): if the chain started from every state outside `A` enters `A` almost
surely, then the finite-state bridge matrix `1 - \bar p` is invertible. -/
theorem one_sub_killedKernelMatrixView_isUnit
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) :
    IsUnit (1 - killedKernelMatrixView p A) := sorry

-- Proof sketch: identify `(1 - killedKernelMatrixView p A)⁻¹` with the intrinsic killed Green
-- function by comparing both with the expected killed visit counts.
/-- The inverse of the killed kernel matrix bridge is the matrix representation of the intrinsic
killed Green function. -/
theorem inv_one_sub_killedKernelMatrixView_eq_killedGreenMatrixView
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) :
    (1 - killedKernelMatrixView p A)⁻¹ = killedGreenMatrixView P X A := sorry

-- Proof sketch: after decomposing the state space as `A ⊔ (E \ A)`, the block on `A` is the
-- identity, so the restriction of the inverse to `Aᶜ` agrees with the inverse of the restricted
-- kernel matrix.
/-- Exercise 19.1.1 (2): on `E \ A`, the matrix representation of the intrinsic killed Green
function agrees with the inverse of `1 - \tilde p` for the restricted chain. -/
theorem killedGreenMatrixView_eq_restrictedKernelMatrixView_inv
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) (x y : ↥(Aᶜ)) :
    killedGreenMatrixView P X A x y = ((1 - restrictedKernelMatrixView p A)⁻¹) x y := sorry

-- Proof sketch: if `x ∈ A`, the intrinsic killed Green function is already the Kronecker delta
-- row, and `killedGreenMatrixView` is its real-valued finite-state presentation.
/-- Exercise 19.1.1 (3): if `x ∈ A`, then the row of the killed Green matrix bridge at `x` is the
Kronecker delta row. -/
theorem killedGreenMatrixView_eq_kroneckerDelta_of_mem
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) {x y : E} (hx : x ∈ A) :
    killedGreenMatrixView P X A x y = if x = y then 1 else 0 := sorry

-- Proof sketch: for `x ∉ A` and `y ∈ A`, the intrinsic killed Green function is the first
-- entrance distribution of `A` at `y`; `killedGreenMatrixView` is its real-valued matrix bridge.
/-- Exercise 19.1.1 (4): for `x ∈ E \ A` and `y ∈ A`, the boundary entry of the killed Green
matrix bridge is the probability that the chain first enters `A` at the point `y`. -/
theorem killedGreenMatrixView_eq_firstEntranceDistribution
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) {x y : E} (hx : x ∉ A) (hy : y ∈ A) :
    killedGreenMatrixView P X A x y =
      (P x : Measure Ω).real
        {ω | hittingAfter X A 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X A 1) ω = y} := sorry

end

end ProbabilityTheory
