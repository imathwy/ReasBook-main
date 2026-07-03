

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_10_14 (from Items/Chap10) -/
open MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "DiscreteFiltration" => Filtration ℕ mΩ

-- Proof sketch: the owner σ-algebra at time `n` is `(hτ.min_const n).measurableSpace`, and
-- `X^τ_n` is `stoppedValue X (τ ∧ n)`. Apply `measurable_stoppedValue` to the progressively
-- measurable discrete-time process obtained from `hX`.
/-- Remark 10.14: the stopped process `X^τ` is adapted to the stopped filtration `𝔽^τ`. -/
theorem stoppedProcess_adapted_stoppedFiltration {ℱ : DiscreteFiltration} {X : ℕ → Ω → ℝ}
    {τ : Ω → WithTop ℕ} (hX : Adapted ℱ X) (hτ : IsStoppingTime ℱ τ) :
    Adapted (stoppedFiltration ℱ hτ) (stoppedProcess X τ) := by
  intro n
  rw [stoppedFiltration_apply ℱ hτ n, stoppedProcess_eq_stoppedValue]
  simpa [min_comm] using
    measurable_stoppedValue (hX.stronglyAdapted.progMeasurable_of_discrete) (hτ.min_const n)
