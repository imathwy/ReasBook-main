import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.cartan.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0007_Remark_III_5_extra_6»

open Filter
open scoped BigOperators Topology
open MeromorphicOn

noncomputable section

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: the weighted logarithmic derivative has the expected local limit
that later feeds the residue computation. -/
lemma tendsto_sub_mul_weighted_logDeriv_eq_order_mul_point
    {g : ℂ → ℂ} {z₀ : ℂ} {k : ℤ}
    (hg : MeromorphicAt g z₀) (horder : meromorphicOrderAt g z₀ = k) :
    Tendsto (fun z ↦ (z - z₀) * (z * logDeriv g z)) (𝓝[≠] z₀) (𝓝 ((k : ℂ) * z₀)) := by
  have hz :
      Tendsto (fun z : ℂ ↦ z) (𝓝[≠] z₀) (𝓝 z₀) := by
    simpa using continuousAt_id.continuousWithinAt.tendsto
  have hlog :
      Tendsto (fun z ↦ (z - z₀) * logDeriv g z) (𝓝[≠] z₀) (𝓝 (k : ℂ)) :=
    tendsto_sub_mul_logDeriv_eq_order (𝕜 := ℂ) (f := g) (z₀ := z₀) (k := k) hg horder
  have hmul :
      Tendsto (fun z ↦ z * ((z - z₀) * logDeriv g z)) (𝓝[≠] z₀) (𝓝 (z₀ * (k : ℂ))) :=
    hz.mul hlog
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Proposition 5.2: a holomorphic kernel of the form `g(w) / (w - z)` realizes the
residue `g z` on any sufficiently small circle contained in the chosen domain. -/
lemma localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall z r ⊆ interior K)
    (hD : Metric.closedBall z r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun w ↦ g w / (w - z)) z (g z) := by
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall z r) := hg.mono hD
  have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul hz_ball

/-- Helper for Proposition 5.2: if `g` is analytic and nonzero at `z`, then `logDeriv g` is
holomorphic at `z`. -/
lemma differentiableAt_logDeriv_of_analyticAt_nonzero
    {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) :
    DifferentiableAt ℂ (logDeriv g) z := by
  have hlog : AnalyticAt ℂ (logDeriv g) z := by
    simpa [logDeriv] using (hg.deriv.div hg hgz)
  exact hlog.differentiableAt
