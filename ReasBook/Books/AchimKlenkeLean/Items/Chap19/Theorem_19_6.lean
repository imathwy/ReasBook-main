import AchimKlenkeLean.Items.Chap08.Example_8_27
import AchimKlenkeLean.Items.Chap17.Theorem_17_8
import AchimKlenkeLean.Items.Chap19.Definition_19_5

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-
Layering for Theorem 19.6:
- `source-facing`: `F_A` and `S_A`, the textbook first-hit probability of the killed chain and the
  corresponding positive-probability reachability set.
- `core/canonical`: `hittingAfter` for the first time the trajectory enters `insert y A`,
  `stoppedValue` for the state reached at that time, `IsHarmonicOutside` for harmonicity on
  `E \ A`, and `discreteMatrixKernel p` for the transition kernel of the discrete chain.
- `bridge/view`: the internal event that the first hit of `insert y A` occurs at the state `y`.
  For `y ∉ A` this is exactly the usual event `τ_y < τ_A`, while for `y ∈ A` it is the
  boundary-inclusive first-hit event `X_{τ_A} = y`.
-/

/-- The event that the trajectory `X` first hits `insert y A` at the state `y`, where the first
hit may occur at time `0`. For `y ∉ A`, this is the usual event `τ_y < τ_A`; for `y ∈ A`, it is
the event that the first hit of `A` occurs at `y`. -/
private def firstHitAtStateEvent (X : ℕ → Ω → E) (A : Set E) (y : E) : Set Ω :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- The quantity `F_A x y` is the probability under `P x` that the first hit of `insert y A`
occurs at the state `y`, where the hit may occur at time `0`. Equivalently, for `y ∉ A` it is the
probability of the event `τ_y < τ_A`, while for `y ∈ A` it is the first-hit distribution of `A`
at the point `y`. -/
def F_A (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ :=
  (P x : Measure Ω).real (firstHitAtStateEvent X A y)

/-- The set `S_A x` consists of states that can be reached from `x` with positive probability
as the first point where the trajectory enters `insert y A`; in particular it contains the
boundary points of `A` that occur with positive first-hit probability. -/
def S_A (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x : E) : Set E :=
  {y | 0 < F_A P X A x y}

-- Proof sketch: unfold `S_A`; membership is defined exactly by strict positivity of `F_A`.
/-- Membership in `S_A x` is equivalent to strict positivity of the first-hit probability
`F_A x y`. -/
theorem mem_S_A_iff
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) :
    y ∈ S_A P X A x ↔ 0 < F_A P X A x y :=
  Iff.rfl

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
variable {A : Set E} {f : E → ℝ} {x₀ : E}

-- Proof sketch: pass from `hf` to the chain stopped on first entering `A`; iterating the stopped
-- transition operator expresses `f x₀` as an average of the values of `f` on states in
-- `S_A x₀`. If `f x₀` is already the greatest value attained on `S_A x₀`, every state with
-- positive first-hit probability from `x₀` must share the same value.
/-- Theorem 19.6 (1): (i) if a function harmonic on `E \ A` attains the supremum of its values on
`S_A(x₀)` at some `x₀ ∉ A`, then it is constant on `S_A(x₀)`. -/
theorem harmonicOn_compl_eq_on_S_A_of_isGreatest
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f) (hx₀ : x₀ ∉ A)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀)) :
    ∀ ⦃y : E⦄, y ∈ S_A P X A x₀ → f y = f x₀ := sorry

-- Proof sketch: the positivity assumption on `F_A` says that every `y ∉ A` belongs to
-- `S_A x₀`. Apply part (i) at the point where `f` attains its global supremum; since the global
-- supremum also bounds `f` on `S_A x₀`, the local maximum principle forces equality on all of
-- `E \ A`.
/-- Theorem 19.6 (2): (ii) if `F_A(x,y) > 0` for all `x, y ∈ E \ A` and `f` attains its global
supremum at some `x₀ ∉ A`, then `f` is constant on `E \ A`. -/
theorem harmonicOn_compl_eq_on_compl_of_F_A_pos_of_isGreatest
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hFA : ∀ ⦃x y : E⦄, x ∉ A → y ∉ A → 0 < F_A P X A x y)
    (hx₀ : x₀ ∉ A) (hmax : IsGreatest (Set.range f) (f x₀)) :
    ∀ ⦃y : E⦄, y ∉ A → f x₀ = f y := sorry

end

end ProbabilityTheory
