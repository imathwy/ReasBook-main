import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace

-- Domain sampling: this source-facing neighborhood statement is the pointwise lift of the
-- canonical owner theorem `AnalyticAt.harmonicAt`.

/-- Proposition 2.I. Any holomorphic function is harmonic. -/
theorem holomorphic_harmonicOnNhd {s : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f s) :
    HarmonicOnNhd f s :=
  fun z hz ↦ (hf z hz).harmonicAt
