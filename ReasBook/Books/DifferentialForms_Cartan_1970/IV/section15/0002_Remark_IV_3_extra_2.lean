import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap InnerProductSpace

/-- Remark IV.3-extra-2 (1): a complex-valued function on `ℂ` is harmonic on `s` if and only if
its real and imaginary parts are harmonic on `s`. -/
theorem harmonicOnNhd_complex_iff_re_im {f : ℂ → ℂ} {s : Set ℂ} :
    HarmonicOnNhd f s ↔
      HarmonicOnNhd (Complex.re ∘ f) s ∧
        HarmonicOnNhd (Complex.im ∘ f) s := by
  constructor
  · intro hf
    exact ⟨hf.comp_CLM Complex.reCLM, hf.comp_CLM Complex.imCLM⟩
  · rintro ⟨hre, him⟩
    have hpair :
        (inl ℝ ℝ ℝ ∘ Complex.re ∘ f) + (inr ℝ ℝ ℝ ∘ Complex.im ∘ f) =
          Complex.equivRealProdCLM ∘ f := by
      ext z <;> simp [Function.comp]
    refine (harmonicOnNhd_comp_CLE_iff Complex.equivRealProdCLM).1 ?_
    rw [← hpair]
    exact (hre.comp_CLM (inl ℝ ℝ ℝ)).add (him.comp_CLM (inr ℝ ℝ ℝ))

/- Remark IV.3-extra-2 (2): the real and imaginary parts of a complex-valued function are denoted
by `Complex.re ∘ f` and `Complex.im ∘ f`. -/
recall Complex.re
recall Complex.im
