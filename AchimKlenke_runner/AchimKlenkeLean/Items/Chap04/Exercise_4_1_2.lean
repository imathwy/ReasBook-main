import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

-- Proof sketch: decompose the sigma-finite non-finite measure into countably many measurable
-- pieces of positive finite measure, then choose coefficients so that the resulting simple
-- function has finite `p`-seminorm but infinite `p'`-seminorm. The canonical `Lp` formulation is
-- a witness in the `AEEqFun`-based `L^p` space whose class does not belong to `L^{p'}`; the
-- textbook raw-function statement is the immediate representative-level corollary.
/-- Exercise 4.1.2, canonical `Lp`-space form: if `1 ≤ p' < p ≤ ∞` and `μ` is sigma-finite but not
finite, then there exists an `L^p(μ)` class that does not belong to `L^{p'}(μ)`. -/
theorem exists_mem_Lp_not_mem_Lp_of_sigmaFinite_not_isFiniteMeasure {p' p : ENNReal}
    (hp' : 1 ≤ p') (hpp : p' < p) (hμ : ¬ IsFiniteMeasure μ) :
    ∃ f : Ω →ₘ[μ] ℝ, f ∈ Lp ℝ p μ ∧ f ∉ Lp ℝ p' μ := sorry

/-- Exercise 4.1.2 in textbook representative form: if `1 ≤ p' < p ≤ ∞` and `μ` is sigma-finite
but not finite, then there exists a real-valued function in `ℒ^p(μ)` that does not belong to
`ℒ^{p'}(μ)`. -/
theorem exists_memLp_not_memLp_of_sigmaFinite_not_isFiniteMeasure {p' p : ENNReal}
    (hp' : 1 ≤ p') (hpp : p' < p) (hμ : ¬ IsFiniteMeasure μ) :
    ∃ f : Ω → ℝ, MemLp f p μ ∧ ¬ MemLp f p' μ := by
  rcases exists_mem_Lp_not_mem_Lp_of_sigmaFinite_not_isFiniteMeasure hp' hpp hμ with
    ⟨f, hf, hf'⟩
  refine ⟨f, (Lp.mem_Lp_iff_memLp).1 hf, ?_⟩
  intro hfp'
  exact hf' <| (Lp.mem_Lp_iff_memLp).2 hfp'
