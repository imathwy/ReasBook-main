import DifferentialForms_Cartan_1970.cartan.IV.section16.«0002_Theorem_IV_4_extra_2»
import DifferentialForms_Cartan_1970.cartan.III.section08.«0003_Corollary_III_2_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Filter InnerProductSpace Metric Real Set Topology

namespace InnerProductSpace.HarmonicContOnCl

/-- Helper for Theorem IV.4-extra-5: a function harmonic on a disc and continuous on its closure
has the mean value property on that disc. -/
theorem hasMeanValuePropertyOn_ball {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : HarmonicContOnCl u (ball c R)) : HasMeanValuePropertyOn u (ball c R) := by
  refine
    { continuousOn := hu.continuousOn.mono subset_closure
      circleAverage_eq := ?_ }
  intro a r hclosed
  -- Restrict the harmonic extension to the smaller disc centered at `a`.
  have hu_small : HarmonicContOnCl u (ball a |r|) := by
    exact hu.mono (ball_subset_closedBall.trans hclosed)
  exact HarmonicContOnCl.circleAverage_eq hu_small

end InnerProductSpace.HarmonicContOnCl

namespace HasMeanValuePropertyOn

/-- Helper for Theorem IV.4-extra-5: subtracting two complex-valued mean-value-property functions
preserves the mean value property. -/
theorem sub {f g : ℂ → ℂ} {D : Set ℂ} (hf : HasMeanValuePropertyOn f D)
    (hg : HasMeanValuePropertyOn g D) : HasMeanValuePropertyOn (f - g) D := by
  refine
    { continuousOn := hf.continuousOn.sub hg.continuousOn
      circleAverage_eq := ?_ }
  intro c R hclosed
  have hf_circle :
      CircleIntegrable f c R :=
    (hf.continuousOn.mono (sphere_subset_closedBall.trans hclosed)).circleIntegrable'
  have hg_circle :
      CircleIntegrable g c R :=
    (hg.continuousOn.mono (sphere_subset_closedBall.trans hclosed)).circleIntegrable'
  -- Subtract the two mean value identities disc by disc.
  calc
    circleAverage (f - g) c R = circleAverage f c R - circleAverage g c R := by
      simpa using Real.circleAverage_fun_sub hf_circle hg_circle
    _ = f c - g c := by rw [hf.circleAverage_eq hclosed, hg.circleAverage_eq hclosed]
    _ = (f - g) c := by simp

/-- Helper for Theorem IV.4-extra-5: a complex-valued function with the mean value property on a
disc and zero boundary values must vanish throughout the disc. -/
lemma eqOn_zero_ball_of_boundary_zero_of_hasMeanValuePropertyOn {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hg_cont : ContinuousOn g (closedBall c R))
    (hg : HasMeanValuePropertyOn g (ball c R)) (hboundary : EqOn g 0 (sphere c R)) :
    EqOn g 0 (ball c R) := by
  have hg_cont_closure : ContinuousOn g (closure (ball c R)) := by
    -- Rewrite the closure of the open disc as the corresponding closed disc.
    simpa [closure_ball c hR.ne'] using hg_cont
  intro z hz
  have hnorm_le : ‖g z‖ ≤ 0 := by
    have hfrontier : ∀ w ∈ frontier (ball c R), ‖g w‖ ≤ 0 := by
      intro w hw
      have hw_sphere : w ∈ sphere c R := by
        simpa [frontier_ball c hR.ne'] using hw
      simp [hboundary hw_sphere]
    -- Apply the boundary maximum principle to the complexified difference.
    exact
      norm_le_boundary_bound_of_hasMeanValuePropertyOn
        isOpen_ball Metric.isBounded_ball hg_cont_closure hg hfrontier z hz
  have hnorm_eq : ‖g z‖ = 0 := le_antisymm hnorm_le (norm_nonneg _)
  exact norm_eq_zero.mp hnorm_eq

/-- Theorem IV.4-extra-5. On an open set `D`, a real-valued function with the mean value property
is harmonic. -/
theorem harmonicOnNhd {D : Set ℂ} {f : ℂ → ℝ} (hf : HasMeanValuePropertyOn f D)
    (hD : IsOpen D) : HarmonicOnNhd f D := by
  intro z hz
  rcases Metric.mem_nhds_iff.mp (hD.mem_nhds hz) with ⟨ε, hε_pos, hεD⟩
  let R : ℝ := ε / 2
  have hR : 0 < R := by
    -- Choose a strictly smaller closed disc around `z` that still lies in `D`.
    dsimp [R]
    linarith
  have hclosed : closedBall z R ⊆ D := by
    intro w hw
    have hw_ball : w ∈ ball z ε := by
      exact closedBall_subset_ball (by
        dsimp [R]
        linarith) hw
    exact hεD hw_ball
  have hf_boundary : ContinuousOn f (sphere z R) := by
    -- The boundary datum is continuous because the whole closed disc stays inside `D`.
    exact hf.continuousOn.mono (sphere_subset_closedBall.trans hclosed)
  rcases dirichlet_problem_disc_exists hf_boundary with ⟨u, hu, hu_boundary⟩
  let uC : ℂ → ℂ := Complex.ofRealCLM ∘ u
  let fC : ℂ → ℂ := Complex.ofRealCLM ∘ f
  let g : ℂ → ℂ := uC - fC
  have hf_ball : HasMeanValuePropertyOn f (ball z R) := by
    refine
      { continuousOn := hf.continuousOn.mono (ball_subset_closedBall.trans hclosed)
        circleAverage_eq := ?_ }
    intro a r ha
    exact hf.circleAverage_eq (Subset.trans ha (ball_subset_closedBall.trans hclosed))
  have huC_mvp : HasMeanValuePropertyOn uC (ball z R) := by
    -- Complexification preserves the mean value property of the harmonic extension.
    simpa [uC, Function.comp_apply] using
      (InnerProductSpace.HarmonicContOnCl.hasMeanValuePropertyOn_ball hu).comp_CLM
        Complex.ofRealCLM
  have hfC_mvp : HasMeanValuePropertyOn fC (ball z R) := by
    -- Complexification also preserves the mean value property of the original function.
    simpa [fC, Function.comp_apply] using hf_ball.comp_CLM Complex.ofRealCLM
  have huC_cont : ContinuousOn uC (closedBall z R) := by
    -- The harmonic extension is continuous on the closed disc, and complexification is continuous.
    simpa [uC, Function.comp_apply] using
      Complex.ofRealCLM.continuous.comp_continuousOn hu.continuousOn_ball
  have hfC_cont : ContinuousOn fC (closedBall z R) := by
    -- The original function is continuous on the same closed disc by restriction from `D`.
    simpa [fC, Function.comp_apply] using
      Complex.ofRealCLM.continuous.comp_continuousOn (hf.continuousOn.mono hclosed)
  have hg_cont : ContinuousOn g (closedBall z R) := by
    -- The comparison function is continuous up to the boundary.
    simpa [g] using huC_cont.sub hfC_cont
  have hg_mvp : HasMeanValuePropertyOn g (ball z R) := by
    -- The difference still has the mean value property.
    simpa [g] using HasMeanValuePropertyOn.sub huC_mvp hfC_mvp
  have hg_boundary : EqOn g 0 (sphere z R) := by
    intro w hw
    -- The Dirichlet solution and the original function agree on the boundary circle.
    have huw : u w = f w := hu_boundary hw
    simp [g, uC, fC, Function.comp_apply, huw]
  have hg_zero : EqOn g 0 (ball z R) :=
    eqOn_zero_ball_of_boundary_zero_of_hasMeanValuePropertyOn hR hg_cont hg_mvp hg_boundary
  have hfu : EqOn f u (ball z R) := by
    intro w hw
    have hgw : g w = 0 := hg_zero hw
    have huC_eq : uC w = fC w := sub_eq_zero.mp hgw
    have hcomplex : (u w : ℂ) = f w := by
      simpa [uC, fC, Function.comp_apply] using huC_eq
    exact Complex.ofReal_injective hcomplex.symm
  have hfu_nhds : f =ᶠ[𝓝 z] u := by
    -- Equality on the whole disc gives equality in a neighborhood of the center.
    exact hfu.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hR))
  -- The harmonic Dirichlet extension agrees with `f` near `z`, so harmonicity transfers back.
  exact (harmonicAt_congr_nhds hfu_nhds).2 (hu.harmonicOnNhd z (mem_ball_self hR))

end HasMeanValuePropertyOn
