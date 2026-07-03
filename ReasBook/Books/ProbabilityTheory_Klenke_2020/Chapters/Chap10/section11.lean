import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_11 (from Items/Chap10) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

/-
Theorem 10.11 mixes two owner abstractions from mathlib's martingale API:

- `core/canonical`: `Martingale.stoppedValue_ae_eq_condExp_of_le` in optional sampling and
  `Submartingale.expected_stoppedValue_mono` in optional stopping.
- `bridge/view`: item (3), which is exactly the owner optional-sampling theorem and is therefore
  recalled directly.
- `source-facing`: the supermartingale reformulations, the nonnegative almost-surely finite
  extensions, and the martingale characterization by bounded stopping times.

The file keeps only those genuinely source-facing companions beyond the exact owner statement.
-/
variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {σ τ : Ω → ℕ∞}

section BoundedSupermartingale

variable (hX : Supermartingale X ℱ μ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
variable (hστ : σ ≤ τ) {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N)

-- Proof sketch: apply the martingale optional sampling theorem to the martingale part of the Doob
-- decomposition of `X`, combine it with the monotonicity of the predictable part, and use the
-- monotonicity of conditional expectation.
/-- Theorem 10.11 (1): Part (i), if a supermartingale is sampled at bounded stopping times
`σ ≤ τ`, then the conditional expectation of the later stopped value is almost surely bounded above
by the earlier stopped value. -/
theorem supermartingale_condExp_stoppedValue_le_of_le_of_bounded
    :
    μ[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X σ := sorry

-- Proof sketch: apply the optional stopping theorem for submartingales to `-X`, using
-- `Supermartingale.neg` to turn the supermartingale into a submartingale and then simplify the
-- stopped values of the negated process.
/-- Theorem 10.11 (2): Part (i), if a supermartingale is sampled at bounded stopping times
`σ ≤ τ`, then the expected stopped value is decreasing:
`𝔼[X_τ] ≤ 𝔼[X_σ]`. -/
theorem supermartingale_expected_stoppedValue_mono_of_le_of_bounded
    :
    μ[stoppedValue X τ] ≤ μ[stoppedValue X σ] := sorry

end BoundedSupermartingale

/- Theorem 10.11 (3): Part (i), if `X` is a martingale and `σ ≤ τ` with `τ` bounded, then the
stopped value at `σ` is almost surely the conditional expectation of the stopped value at `τ`
with respect to `𝓕_σ`. This is exactly the canonical owner theorem
`Martingale.stoppedValue_ae_eq_condExp_of_le`. -/
recall Martingale.stoppedValue_ae_eq_condExp_of_le

section BoundedMartingale

variable (hX : Martingale X ℱ μ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
variable (hστ : σ ≤ τ) {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N)

-- Proof sketch: integrate the almost-sure identity from the martingale optional sampling theorem,
-- or equivalently apply the stopped-value expectation monotonicity to both `X` and `-X`.
/-- Theorem 10.11 (4): Part (i), if `X` is a martingale and `σ ≤ τ` with `τ` bounded, then the
expected stopped values at `σ` and `τ` agree. -/
theorem martingale_expected_stoppedValue_eq_of_le_of_bounded
    :
    μ[stoppedValue X τ] = μ[stoppedValue X σ] := sorry

end BoundedMartingale

section NonnegativeSupermartingale

variable (hX : Supermartingale X ℱ μ) (hX_nonneg : ∀ n ω, 0 ≤ X n ω)

-- Proof sketch: approximate `τ` from below by the bounded stopping times `fun ω ↦ min (τ ω) n`,
-- apply the bounded optional stopping inequality, use nonnegativity and Fatou's lemma to obtain
-- integrability of the stopped value, and then conclude the expectation bound.
/-- Theorem 10.11 (5): Part (ii), for a nonnegative supermartingale and an almost surely finite
stopping time `τ`, the stopped value at `τ` is integrable and its expectation is bounded above by
the initial expectation. -/
theorem supermartingale_expected_stoppedValue_le_initial_of_nonneg_of_ae_ne_top
    (hτ : IsStoppingTime ℱ τ)
    (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue X τ) μ ∧
      μ[stoppedValue X τ] ≤ μ[X 0] := sorry

-- Proof sketch: deduce that `σ` is almost surely finite from `σ ≤ τ`, apply the preceding bound
-- to `σ`, and use nonnegativity of the supermartingale.
/-- Theorem 10.11 (6): Part (ii), under the same nonnegativity and almost-sure finiteness
hypotheses, the stopped value at the earlier stopping time `σ` is integrable and its expectation
is also bounded by the initial expectation. -/
theorem supermartingale_expected_stoppedValue_left_le_initial_of_nonneg_of_ae_ne_top
    (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue X σ) μ ∧
      μ[stoppedValue X σ] ≤ μ[X 0] := sorry

-- Proof sketch: truncate `σ` and `τ` by deterministic bounds, apply the bounded optional
-- sampling inequality, use Fatou's lemma to retain integrability of the later stopped value, and
-- then pass to the limit in the conditional-expectation inequality.
/-- Theorem 10.11 (7): Part (ii), for a nonnegative supermartingale and almost surely finite
stopping times `σ ≤ τ`, the optional sampling inequality still holds without a deterministic bound
on `τ`; moreover the later stopped value remains integrable. -/
theorem supermartingale_condExp_stoppedValue_le_of_nonneg_of_ae_ne_top
    (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue X τ) μ ∧
      μ[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X σ := sorry

end NonnegativeSupermartingale

section Characterization

variable (hX_adapted : Adapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)

-- Proof sketch: the forward implication follows from the martingale case of optional stopping.
-- For the converse, test the stopping-time expectation identity on piecewise constant bounded
-- stopping times built from events in `𝓕_s` to recover the martingale conditional expectation
-- identity at deterministic times.
/-- Theorem 10.11 (8): Part (iii), an adapted integrable real-valued process is a martingale if
and only if every bounded stopping time preserves the initial expectation. -/
theorem martingale_iff_expected_stoppedValue_eq_initial_of_bounded_stopping_times
    :
    Martingale X ℱ μ ↔
      ∀ τ : Ω → ℕ∞, IsStoppingTime ℱ τ → (∃ N : ℕ, ∀ ω, τ ω ≤ N) →
        μ[stoppedValue X τ] = μ[X 0] := sorry

end Characterization
