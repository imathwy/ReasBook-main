import Mathlib.Analysis.Complex.Harmonic.Analytic

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the canonical harmonic/analytic API was verified directly in
-- `Mathlib/Analysis/Complex/Harmonic/Analytic.lean` and
-- `Mathlib/Analysis/Calculus/ContDiff/Defs.lean`.

/-- Proposition 4.1 (1). A harmonic real-valued function on a subset of the plane is
real-analytic there; the textbook open-set formulation is a special case. -/
theorem harmonicOnNhd_analyticOnNhd {D : Set ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g D) :
    AnalyticOnNhd ℝ g D :=
  fun z hz ↦ HarmonicAt.analyticAt (hg z hz)

/-- Proposition 4.1 (2). A harmonic real-valued function on a subset of the plane is
infinitely differentiable there; the textbook open-set formulation is a special case. -/
theorem harmonicOnNhd_contDiffOn {D : Set ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g D) :
    ContDiffOn ℝ ⊤ g D :=
  (harmonicOnNhd_analyticOnNhd hg).contDiffOn_of_completeSpace
