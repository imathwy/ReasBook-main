import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_7_2_1 (from Items/Chap07) -/
/- Exercise 7.2.1: Hölder's inequality for real-valued random variables on a probability space is
the canonical theorem `integral_mul_norm_le_Lp_mul_Lq`. For `ℝ`-valued functions, its norm-based
conclusion is exactly the textbook absolute-value inequality, and mathlib expresses the conjugacy
condition canonically as `p.HolderConjugate q`. -/
recall MeasureTheory.integral_mul_norm_le_Lp_mul_Lq

/- The textbook reciprocal assumption `1 < p` and `p⁻¹ + q⁻¹ = 1` is exactly the canonical
predicate `p.HolderConjugate q`. -/
recall Real.holderConjugate_iff

/-! ### Definition_7_2 (from Items/Chap07) -/
universe u v

open Filter MeasureTheory
open scoped ENNReal Topology

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [NormedAddCommGroup E]

/-- Definition 7.2: for `1 ≤ p`, a sequence `fₙ : Ω → E` converges to `f` in `L^p(μ)` when each
`fₙ` and `f` belongs to `ℒ^p(μ)` and the associated classes in the canonical space
`MeasureTheory.Lp E p μ` converge. -/
abbrev TendstoInLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure Ω) (fSeq : ℕ → Ω → E)
    (f : Ω → E) : Prop :=
  ∃ h_memLpSeq : ∀ n, MemLp (fSeq n) p μ,
    ∃ h_memLp : MemLp f p μ,
      Tendsto (fun n ↦ (h_memLpSeq n).toLp (fSeq n)) atTop (𝓝 (h_memLp.toLp f))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}

theorem TendstoInLp.memLpSeq (h : TendstoInLp p μ fSeq f) :
    ∀ n, MemLp (fSeq n) p μ := by
  rcases h with ⟨h_memLpSeq, -, -⟩
  exact h_memLpSeq

theorem TendstoInLp.memLp (h : TendstoInLp p μ fSeq f) :
    MemLp f p μ := by
  rcases h with ⟨-, h_memLp, -⟩
  exact h_memLp

/-- Owner-level formulation of `TendstoInLp`: the corresponding elements of
`MeasureTheory.Lp E p μ` converge in the canonical `Lp` space. -/
theorem TendstoInLp.tendsto_toLp (h : TendstoInLp p μ fSeq f) :
    Tendsto (fun n ↦ (h.memLpSeq n).toLp (fSeq n)) atTop (𝓝 (h.memLp.toLp f)) := by
  rcases h with ⟨h_memLpSeq, h_memLp, h_tendsto⟩
  simpa using h_tendsto

/-- The textbook `eLpNorm` criterion is the bridge view of `TendstoInLp`, obtained from the owner
comparison theorem `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`. -/
theorem TendstoInLp.tendsto_eLpNorm (h : TendstoInLp p μ fSeq f) :
    Tendsto (fun n ↦ eLpNorm (fSeq n - f) p μ) atTop (𝓝 0) := by
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq h.memLpSeq f h.memLp).1 h.tendsto_toLp

theorem tendstoInLp_iff_tendsto_eLpNorm :
    TendstoInLp p μ fSeq f ↔
      (∀ n, MemLp (fSeq n) p μ) ∧
        MemLp f p μ ∧
        Tendsto (fun n ↦ eLpNorm (fSeq n - f) p μ) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨h.memLpSeq, h.memLp, h.tendsto_eLpNorm⟩
  · rcases h with ⟨h_memLpSeq, h_memLp, h_tendsto⟩
    refine ⟨h_memLpSeq, h_memLp, ?_⟩
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq h_memLpSeq f h_memLp).2 h_tendsto

/-! ### Exercise_7_2_2 (from Items/Chap07) -/
/- Exercise 7.2.2: Minkowski's inequality for real-valued `ℒ^p(μ)` functions is the canonical
theorem `MeasureTheory.lpNorm_add_le`. The textbook proof route derives this estimate by applying
Jensen's inequality to the concave map `(x, y) ↦ (x^(1/p) + y^(1/p))^p` from Example 7.14. -/
recall MeasureTheory.lpNorm_add_le

/-! ### Exercise_7_2_3 (from Items/Chap07) -/
open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: this is a source-facing bridge built on the canonical `MemLp`/`lpNorm` API. For
-- the forward implication, combine Hölder's inequality with the fact that a bounded measurable
-- random variable on a probability space belongs to every finite `L^q`; this gives integrability
-- of `X * Y` together with the stated bound. For the reverse implication, test the assumed
-- estimate on bounded truncations of `sgn(X) * |X|^(p - 1)` and pass to the limit.
/-- Exercise 7.2.3: if `p` and `q` are Hölder-conjugate exponents, then a real random variable on
a probability space belongs to `ℒ^p(P)` if and only if every bounded measurable real test random
variable `Y` yields an integrable product `X * Y` whose integral is uniformly controlled by a
constant multiple of the `L^q(P)` norm of `Y`. This avoids the total-expectation convention for
nonintegrable functions and matches the textbook bounded-functional interpretation. -/
theorem memLp_iff_exists_expectation_bound_of_bounded_measurable
    {P : Measure Ω} [IsProbabilityMeasure P] {p q : ℝ} {X : Ω → ℝ}
    (hpq : p.HolderConjugate q) :
    MemLp X (ENNReal.ofReal p) P ↔
      ∃ C : NNReal, ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
        (∃ M : NNReal, ∀ ω, |Y ω| ≤ M) →
        Integrable (X * Y) P ∧
          |∫ ω, X ω * Y ω ∂P| ≤ (C : ℝ) * lpNorm Y (ENNReal.ofReal q) P := sorry

end MeasureTheory
