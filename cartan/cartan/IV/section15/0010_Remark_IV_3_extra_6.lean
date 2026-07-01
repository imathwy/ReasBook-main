import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: the `lean_leansearch` tool was unavailable in this runner, so the
-- statement shape was matched directly against
-- `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` and
-- `AnalyticAt.harmonicAt_re` in mathlib.

open InnerProductSpace Metric Set

/-- Remark IV.3-extra-6. On a disc in `ℂ`, a real-valued function is the real part of a
holomorphic function on that disc if and only if it is harmonic there. -/
theorem harmonicOnNhd_ball_iff_exists_analyticOnNhd_re_eq {c : ℂ} {R : ℝ} {g : ℂ → ℝ} :
    HarmonicOnNhd g (ball c R) ↔
      ∃ F : ℂ → ℂ,
        AnalyticOnNhd ℂ F (ball c R) ∧
          (ball c R).EqOn (fun z ↦ (F z).re) g := by
  constructor
  · exact HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
  · rintro ⟨F, hF, hFg⟩ z hz
    have hEq := hFg.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
    exact (harmonicAt_congr_nhds hEq).1 <| AnalyticAt.harmonicAt_re (hF z hz)
