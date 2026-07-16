import DifferentialForms_Cartan_1970.cartan.IV.section13.«0004_Proposition_2_I»
import DifferentialForms_Cartan_1970.cartan.IV.section13.«0003_Definition_IV_1_extra_3»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: convergence-domain statements for two-variable formal power series
* source-facing owners reused here: `formalSeriesConvergenceLocus` and
  `formalSeriesConvergenceDomain`
* core/canonical owner abstraction in this chapter: the convergence locus/domain from
  `0003_Definition_IV_1_extra_3`, whose primitive datum is weighted norm summability
* nearby owner-pattern samples checked before refining:
  `mem_formalSeriesConvergenceLocus_iff`,
  `mem_formalSeriesConvergenceDomain_iff`,
  `formalSeriesConvergenceLocus_of_bounded_coefficients`,
  `FormalMultilinearSeries.summable_norm_mul_pow`

This file stays at the source-facing theorem layer. The first two results only use the chapter
convergence-domain owners, while the last two additionally need the ring structure coming from the
actual series terms `a p q * z₁^p * z₂^q`.
-/

universe u

section ConvergenceDomain

variable {𝕜 : Type u} [SeminormedAddCommGroup 𝕜]

/-- Helper for Cartan section13 0005_Proposition_2_2: every point of the convergence domain
already belongs to the convergence locus. -/
lemma mem_formalSeriesConvergenceLocus_of_mem_domain
    (a : ℕ → ℕ → 𝕜) {r₁ r₂ : ℝ}
    (hr : (r₁, r₂) ∈ formalSeriesConvergenceDomain a) :
    (r₁, r₂) ∈ formalSeriesConvergenceLocus a := by
  -- Proposition 2.I supplies a larger point of the locus above `(r₁, r₂)`.
  rcases
      (mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus
        a r₁ r₂).1 hr with
    ⟨hr₁_pos, hr₂_pos, R₁, hr₁_lt, R₂, hr₂_lt, hR⟩
  -- Shrink back along the coordinatewise monotonicity of the locus.
  exact formalSeriesConvergenceLocus_mono a hR hr₁_pos.le (le_of_lt hr₁_lt) hr₂_pos.le
    (le_of_lt hr₂_lt)

/-- Proposition 2.2 (1): if `(r₁, r₂)` belongs to the domain of convergence, then the radii
defining the closed polydisc are nonnegative. -/
theorem nonneg_radii_of_mem_formal_series_convergence_domain
    (a : ℕ → ℕ → 𝕜) {r₁ r₂ : ℝ}
    (hr : (r₁, r₂) ∈ formalSeriesConvergenceDomain a) :
    0 ≤ r₁ ∧ 0 ≤ r₂ := by
  -- Move from domain membership to locus membership and read off the sign conditions.
  rcases
      (mem_formalSeriesConvergenceLocus_iff a (r₁, r₂)).1
        (mem_formalSeriesConvergenceLocus_of_mem_domain a hr) with
    ⟨hr₁_nonneg, hr₂_nonneg, -⟩
  exact ⟨hr₁_nonneg, hr₂_nonneg⟩

/-- Cartan section13 0005_Proposition_2_2: if `(r₁, r₂)` belongs to the domain of convergence,
then the normal majorant series `∑ ‖a p q‖ r₁^p r₂^q` is summable. -/
theorem summable_double_power_series_normal_majorant_of_mem_domain
    (a : ℕ → ℕ → 𝕜) {r₁ r₂ : ℝ}
    (hr : (r₁, r₂) ∈ formalSeriesConvergenceDomain a) :
    Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2) := by
  -- The summability component is exactly the third field of locus membership.
  rcases
      (mem_formalSeriesConvergenceLocus_iff a (r₁, r₂)).1
        (mem_formalSeriesConvergenceLocus_of_mem_domain a hr) with
    ⟨-, -, hsum⟩
  exact hsum

end ConvergenceDomain

section SeriesTerms

variable {𝕜 : Type u} [NormedRing 𝕜]

/-- Proposition 2.2 (3): if `(r₁, r₂)` belongs to the domain of convergence, then on the closed
polydisc `‖z₁‖ ≤ r₁`, `‖z₂‖ ≤ r₂` each term of the double power series is dominated by the
normal majorant term `‖a p q‖ r₁^p r₂^q`. -/
theorem norm_double_power_series_term_le_normal_majorant_of_mem_domain
    (a : ℕ → ℕ → 𝕜) {r₁ r₂ : ℝ}
    (hr : (r₁, r₂) ∈ formalSeriesConvergenceDomain a)
    (n : ℕ × ℕ) (z₁ z₂ : 𝕜) (hz₁ : ‖z₁‖ ≤ r₁) (hz₂ : ‖z₂‖ ≤ r₂) :
    ‖a n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2‖ ≤ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2 := by
  -- First extract the nonnegativity needed to compare real powers.
  rcases nonneg_radii_of_mem_formal_series_convergence_domain a hr with
    ⟨hr₁_nonneg, hr₂_nonneg⟩
  rcases n with ⟨n₁, n₂⟩
  -- Split off the zero-exponent cases so no `‖1‖ ≤ 1` estimate is needed.
  cases n₁ with
  | zero =>
      cases n₂ with
      | zero =>
          simp
      | succ m₂ =>
          have hnorm_pow₂ : ‖z₂ ^ (m₂ + 1)‖ ≤ r₂ ^ (m₂ + 1) := by
            calc
              ‖z₂ ^ (m₂ + 1)‖ ≤ ‖z₂‖ ^ (m₂ + 1) := norm_pow_le' _ (Nat.succ_pos _)
              _ ≤ r₂ ^ (m₂ + 1) := pow_le_pow_left₀ (norm_nonneg _) hz₂ _
          calc
            ‖a 0 (m₂ + 1) * z₁ ^ 0 * z₂ ^ (m₂ + 1)‖
              = ‖a 0 (m₂ + 1) * z₂ ^ (m₂ + 1)‖ := by simp
            _ ≤ ‖a 0 (m₂ + 1)‖ * ‖z₂ ^ (m₂ + 1)‖ := norm_mul_le _ _
            _ ≤ ‖a 0 (m₂ + 1)‖ * r₂ ^ (m₂ + 1) := by
                  exact mul_le_mul_of_nonneg_left hnorm_pow₂ (norm_nonneg _)
            _ = ‖a 0 (m₂ + 1)‖ * r₁ ^ 0 * r₂ ^ (m₂ + 1) := by simp
  | succ m₁ =>
      have hnorm_pow₁ : ‖z₁ ^ (m₁ + 1)‖ ≤ r₁ ^ (m₁ + 1) := by
        calc
          ‖z₁ ^ (m₁ + 1)‖ ≤ ‖z₁‖ ^ (m₁ + 1) := norm_pow_le' _ (Nat.succ_pos _)
          _ ≤ r₁ ^ (m₁ + 1) := pow_le_pow_left₀ (norm_nonneg _) hz₁ _
      cases n₂ with
      | zero =>
          calc
            ‖a (m₁ + 1) 0 * z₁ ^ (m₁ + 1) * z₂ ^ 0‖
              = ‖a (m₁ + 1) 0 * z₁ ^ (m₁ + 1)‖ := by simp
            _ ≤ ‖a (m₁ + 1) 0‖ * ‖z₁ ^ (m₁ + 1)‖ := norm_mul_le _ _
            _ ≤ ‖a (m₁ + 1) 0‖ * r₁ ^ (m₁ + 1) := by
                  exact mul_le_mul_of_nonneg_left hnorm_pow₁ (norm_nonneg _)
            _ = ‖a (m₁ + 1) 0‖ * r₁ ^ (m₁ + 1) * r₂ ^ 0 := by simp
      | succ m₂ =>
          have hnorm_pow₂ : ‖z₂ ^ (m₂ + 1)‖ ≤ r₂ ^ (m₂ + 1) := by
            calc
              ‖z₂ ^ (m₂ + 1)‖ ≤ ‖z₂‖ ^ (m₂ + 1) := norm_pow_le' _ (Nat.succ_pos _)
              _ ≤ r₂ ^ (m₂ + 1) := pow_le_pow_left₀ (norm_nonneg _) hz₂ _
          have hfirstFactor :
              ‖a (m₁ + 1) (m₂ + 1)‖ * ‖z₁ ^ (m₁ + 1)‖ ≤
                ‖a (m₁ + 1) (m₂ + 1)‖ * r₁ ^ (m₁ + 1) :=
            mul_le_mul_of_nonneg_left hnorm_pow₁ (norm_nonneg _)
          have hsecondFactor :
              (‖a (m₁ + 1) (m₂ + 1)‖ * r₁ ^ (m₁ + 1)) * ‖z₂ ^ (m₂ + 1)‖ ≤
                (‖a (m₁ + 1) (m₂ + 1)‖ * r₁ ^ (m₁ + 1)) * r₂ ^ (m₂ + 1) :=
            mul_le_mul_of_nonneg_left hnorm_pow₂
              (mul_nonneg (norm_nonneg _) (pow_nonneg hr₁_nonneg _))
          calc
            ‖a (m₁ + 1) (m₂ + 1) * z₁ ^ (m₁ + 1) * z₂ ^ (m₂ + 1)‖
              ≤ ‖a (m₁ + 1) (m₂ + 1)‖ * ‖z₁ ^ (m₁ + 1)‖ * ‖z₂ ^ (m₂ + 1)‖ := by
                  calc
                    ‖a (m₁ + 1) (m₂ + 1) * z₁ ^ (m₁ + 1) * z₂ ^ (m₂ + 1)‖
                      = ‖(a (m₁ + 1) (m₂ + 1) * z₁ ^ (m₁ + 1)) * z₂ ^ (m₂ + 1)‖ := by
                          rw [mul_assoc]
                    _ ≤ ‖a (m₁ + 1) (m₂ + 1) * z₁ ^ (m₁ + 1)‖ * ‖z₂ ^ (m₂ + 1)‖ :=
                        norm_mul_le _ _
                    _ ≤ (‖a (m₁ + 1) (m₂ + 1)‖ * ‖z₁ ^ (m₁ + 1)‖) * ‖z₂ ^ (m₂ + 1)‖ := by
                          gcongr
                          exact norm_mul_le _ _
                    _ = ‖a (m₁ + 1) (m₂ + 1)‖ * ‖z₁ ^ (m₁ + 1)‖ * ‖z₂ ^ (m₂ + 1)‖ := by
                          ring
            _ ≤ (‖a (m₁ + 1) (m₂ + 1)‖ * r₁ ^ (m₁ + 1)) * ‖z₂ ^ (m₂ + 1)‖ := by
                  simpa [mul_assoc] using
                    mul_le_mul_of_nonneg_right hfirstFactor (norm_nonneg _)
            _ ≤ (‖a (m₁ + 1) (m₂ + 1)‖ * r₁ ^ (m₁ + 1)) * r₂ ^ (m₂ + 1) := hsecondFactor
            _ = ‖a (m₁ + 1) (m₂ + 1)‖ * r₁ ^ (m₁ + 1) * r₂ ^ (m₂ + 1) := by ring

/-- Proposition 2.2 (4): if `(‖z₁‖, ‖z₂‖)` does not belong to the closure of `Γ`, then the
normal majorant series diverges at `(z₁, z₂)`. This is the source-facing normal-convergence
boundary statement; the stronger statement about the actual ring-valued series is false for a
general `NormedRing` with zero divisors. -/
theorem not_summable_double_power_series_of_norm_pair_not_mem_closure
    (a : ℕ → ℕ → 𝕜) {z₁ z₂ : 𝕜}
    (hz : (‖z₁‖, ‖z₂‖) ∉ closure (formalSeriesConvergenceLocus a)) :
    ¬ Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * ‖z₁‖ ^ n.1 * ‖z₂‖ ^ n.2) := by
  intro hsum
  -- Summability at the norm pair is exactly membership in the convergence locus.
  have hmem : (‖z₁‖, ‖z₂‖) ∈ formalSeriesConvergenceLocus a := by
    rw [mem_formalSeriesConvergenceLocus_iff]
    exact ⟨norm_nonneg _, norm_nonneg _, hsum⟩
  -- Any point of the locus lies in its closure, contradicting the hypothesis.
  exact hz (subset_closure hmem)

-- Proof sketch: the source-facing proposition is the conjunction of the summable normal majorant
-- on every closed polydisc coming from the convergence domain and the divergence of that majorant
-- once the norm pair leaves the closure of the convergence locus.
/-- Helper for Cartan section13 0005_Proposition_2_2: bundles the normal-majorant summability,
the termwise domination on closed polydiscs, and the boundary divergence statement into one
source-facing conjunction. -/
theorem formalSeriesNormalConvergenceAndBoundaryMajorantDivergence
    (a : ℕ → ℕ → 𝕜) :
    (∀ {r₁ r₂ : ℝ}, (r₁, r₂) ∈ formalSeriesConvergenceDomain a →
      0 ≤ r₁ ∧ 0 ≤ r₂ ∧
        Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2) ∧
          ∀ n : ℕ × ℕ, ∀ z₁ z₂ : 𝕜,
            ‖z₁‖ ≤ r₁ → ‖z₂‖ ≤ r₂ →
              ‖a n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2‖ ≤ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2) ∧
      ∀ {z₁ z₂ : 𝕜},
        (‖z₁‖, ‖z₂‖) ∉ closure (formalSeriesConvergenceLocus a) →
          ¬ Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * ‖z₁‖ ^ n.1 * ‖z₂‖ ^ n.2) := by
  constructor
  · intro r₁ r₂ hr
    -- The earlier clauses already provide the nonnegativity, summable majorant, and termwise bound.
    rcases nonneg_radii_of_mem_formal_series_convergence_domain a hr with
      ⟨hr₁_nonneg, hr₂_nonneg⟩
    refine ⟨hr₁_nonneg, hr₂_nonneg, ?_, ?_⟩
    · exact summable_double_power_series_normal_majorant_of_mem_domain a hr
    · intro n z₁ z₂ hz₁ hz₂
      exact norm_double_power_series_term_le_normal_majorant_of_mem_domain a hr n z₁ z₂ hz₁ hz₂
  · intro z₁ z₂ hz
    -- Outside the closure of `Γ`, the normal majorant cannot be summable.
    exact not_summable_double_power_series_of_norm_pair_not_mem_closure a hz

end SeriesTerms
