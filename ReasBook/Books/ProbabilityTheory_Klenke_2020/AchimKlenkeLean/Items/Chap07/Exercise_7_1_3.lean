import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open MeasureTheory
open scoped ENNReal Topology

/-- The `n`-th Cesàro average of the nonnegative integer translates of `f`. -/
noncomputable def integerTranslateCesaro (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x ↦
    ((n + 1 : ℝ)⁻¹) * Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))

/-- Integer translation preserves `ℒ^p(λ)` because Lebesgue measure is translation invariant. -/
private theorem integerTranslate_memLp {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume) (k : ℕ) :
    MemLp (fun x ↦ f (x + k)) p volume := by
  simpa [Function.comp, add_comm] using
    hf.comp_measurePreserving (measurePreserving_vadd (k : ℝ) volume)

/-- If `f ∈ ℒ^p(λ)`, then each Cesàro average of its integer translates again belongs to
`ℒ^p(λ)`. -/
private theorem integerTranslateCesaro_memLp {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume)
    (n : ℕ) :
    MemLp (integerTranslateCesaro f n) p volume := by
  have hsum : MemLp (fun x ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))) p volume := by
    classical
    refine Finset.induction_on (Finset.range (n + 1)) ?_ ?_
    · simp
    · intro k s hk hs
      simpa [Finset.sum_insert hk] using (integerTranslate_memLp hf k).add hs
  simpa [integerTranslateCesaro, smul_eq_mul] using hsum.const_smul ((n + 1 : ℝ)⁻¹)

private instance fact_one_le_coe_ennreal_of_fact_one_lt (p : NNReal) [Fact (1 < p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) :=
  ⟨by
    exact_mod_cast (Fact.out : (1 : NNReal) < p).le⟩

/-- Exercise 7.1.3: canonical `Lp`-valued form. For a finite exponent `p > 1`, if
`f ∈ ℒ^p(λ)` on `ℝ`, then the Cesàro averages of the integer translates `x ↦ f (x + k)`
converge to `0` in `Lp ℝ p volume`. -/
-- Proof sketch: view integer translation as a measure-preserving action on
-- `Lp ℝ p volume`, so each translate is an isometric copy of `f`. Prove the
-- claim first for compactly supported continuous functions, where the translates separate and the
-- averages vanish, then extend to general `MemLp` functions by density of nice functions in `L^p`.
theorem integer_translate_cesaro_tendsto_zero_inLp {p : NNReal} [Fact (1 < p)] {f : ℝ → ℝ}
    (hf : MemLp f (p : ℝ≥0∞) volume) :
    Tendsto
      (fun n ↦ (integerTranslateCesaro_memLp hf n).toLp (integerTranslateCesaro f n))
      atTop (𝓝 (0 : Lp ℝ (p : ℝ≥0∞) volume)) := sorry

/-- The textbook `eLpNorm` formulation of Exercise 7.1.3 follows from the canonical `Lp`-valued
convergence statement via `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''`. -/
theorem integer_translate_cesaro_tendsto_zero_in_eLpNorm {p : ℝ} (hp : 1 < p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun n ↦ eLpNorm (integerTranslateCesaro f n) (ENNReal.ofReal p) volume) atTop
      (𝓝 0) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  let p' : NNReal := ⟨p, hp0⟩
  have hp' : (p' : ℝ≥0∞) = ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_eq_coe_nnreal hp0).symm
  haveI : Fact (1 < p') := ⟨by exact_mod_cast hp⟩
  have hf' : MemLp f (p' : ℝ≥0∞) volume := by
    simpa [hp'] using hf
  have hCesaroMemLp : ∀ n, MemLp (integerTranslateCesaro f n) (p' : ℝ≥0∞) volume :=
    integerTranslateCesaro_memLp hf'
  simpa [hp'] using
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ integerTranslateCesaro f n) hCesaroMemLp 0
      MemLp.zero).mp (integer_translate_cesaro_tendsto_zero_inLp hf')
