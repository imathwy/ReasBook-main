import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace Set

-- Domain sampling: this file lives in the complex-analysis/harmonic-functions API.
-- The owner-level declarations used here are:
-- `AnalyticAt.harmonicAt_re`,
-- `AnalyticAt.harmonicAt_im`,
-- `AnalyticAt.harmonicAt_log_norm`.

/-- Corollary IV.3-extra-3 (1). The real part of a holomorphic function is harmonic. -/
theorem holomorphic_real_part_harmonicOnNhd {s : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f s) :
    HarmonicOnNhd (fun z ↦ (f z).re) s :=
  fun z hz ↦ (hf z hz).harmonicAt_re

/-- Corollary IV.3-extra-3 (2). The imaginary part of a holomorphic function is harmonic. -/
theorem holomorphic_imaginary_part_harmonicOnNhd {s : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f s) :
    HarmonicOnNhd (fun z ↦ (f z).im) s :=
  fun z hz ↦ (hf z hz).harmonicAt_im

/-- Corollary IV.3-extra-3 (3).
The function `z ↦ log |z|` is harmonic on the punctured complex plane. -/
theorem log_norm_harmonicOnNhd_punctured_plane :
    HarmonicOnNhd (fun z : ℂ ↦ Real.log ‖z‖) ({0}ᶜ : Set ℂ) :=
  fun z hz ↦ analyticAt_id.harmonicAt_log_norm (by simpa using hz)
