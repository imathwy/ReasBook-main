import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_21_67 (from Items/Chap21) -/
open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- A real-valued continuous-time process is bounded if one deterministic constant bounds all of
its sample values uniformly in time and sample point. -/
def IsBoundedProcess (X : NNReal → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : NNReal, ∀ ω : Ω, |X t ω| ≤ C

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {M : NNReal → Ω → ℝ} {τ : Ω → ENNReal}

local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : TimeFiltration}

/-- A sequence of stopping times approximates `τ` if it is almost surely increasing and converges
almost surely to `τ`. -/
def IsStoppingTimeApproximationUpTo
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τSeq : ℕ → Ω → ENNReal) (τ : Ω → ENNReal) : Prop :=
  IsStoppingTime ℱ τ ∧
    (∀ n : ℕ, IsStoppingTime ℱ (τSeq n)) ∧
    ∀ᵐ ω ∂μ,
      Monotone (fun n ↦ τSeq n ω) ∧
        Tendsto (fun n ↦ τSeq n ω) atTop (𝓝 (τ ω))

namespace IsLocalizingSequenceUpTo

/-- Every localizing sequence up to `τ` yields the underlying stopping-time approximation to `τ`.
-/
theorem stoppingTimeApproximationUpTo
    {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ} {τSeq : ℕ → Ω → ENNReal} :
    IsLocalizingSequenceUpTo ℱ μ τ M τSeq →
      IsStoppingTimeApproximationUpTo ℱ μ τSeq τ
  | ⟨hτ, hStopping, hlim, _⟩ => ⟨hτ, hStopping, hlim⟩

end IsLocalizingSequenceUpTo

-- Proof sketch: unfold `IsLocalMartingaleUpTo`; the only extra datum beyond the localizing
-- sequence is the assumed adaptedness of `M`, which is supplied by `hM_adapted`.
/-- Under the standing adaptedness assumption, being a local martingale up to `τ` is equivalent to
admitting an almost surely increasing sequence of stopping times converging to `τ` whose stopped
processes are martingales. -/
theorem isLocalMartingaleUpTo_iff_exists_stopped_martingale_sequence
    (hM_adapted : Adapted ℱ M) :
    IsLocalMartingaleUpTo ℱ μ τ M ↔
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
          ∀ n : ℕ, Martingale (stoppedProcess M (τSeq n)) ℱ μ := sorry

-- Proof sketch: `(iii) → (i)` is immediate from the previous characterization. For `(i) → (iii)`,
-- start from a localizing sequence giving martingale stopped processes and intersect it with the
-- first-exit times of `|M|` from the levels `n`; continuity makes these exit times tend to `∞`,
-- so the doubly stopped processes are bounded martingales while the sequence still increases
-- almost surely to `τ`.
/-- Remark 21.67: for a continuous adapted process `M`, being a local martingale up to the
stopping time `τ` is equivalent to admitting a sequence of stopping times increasing almost surely
to `τ` such that every stopped process `M^{τ_n}` is a bounded martingale. -/
theorem isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω) :
    IsLocalMartingaleUpTo ℱ μ τ M ↔
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
          (∀ n : ℕ, Martingale (stoppedProcess M (τSeq n)) ℱ μ) ∧
          ∀ n : ℕ, IsBoundedProcess (stoppedProcess M (τSeq n)) := sorry

end ProbabilityTheory
