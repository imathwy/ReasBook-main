import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

private theorem isConservativeOn_inv_punctured_plane :
    Complex.IsConservativeOn (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) := by
  refine (show DifferentiableOn ℂ (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) from ?_).isConservativeOn
  intro z hz
  exact (differentiableAt_inv (by simpa using hz)).differentiableWithinAt

private theorem not_isExactOn_inv_punctured_plane :
    ¬ Complex.IsExactOn (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) := by
  intro hExact
  rcases hExact with ⟨g, hg⟩
  have hzero : (∮ z in C(0, 1), z⁻¹) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt zero_le_one fun z hz ↦
      (hg z (by simpa using Metric.ne_of_mem_sphere hz one_ne_zero)).hasDerivWithinAt
  exact Complex.two_pi_I_ne_zero <| by
    simpa [hzero] using circleIntegral.integral_sub_center_inv (0 : ℂ) one_ne_zero

private theorem dz_div_z_isClosedOn_punctured_plane :
    IsClosedOn (Complex.realScalarOneForm fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) := by
  intro z hz
  have hz0 : 0 < dist z 0 := by
    simpa using dist_pos.mpr hz
  have hball0 : ∀ {w : ℂ}, w ∈ Metric.ball z (dist z 0) → w ≠ 0 := by
    intro w hw hw0
    have hw' : dist z 0 < dist z 0 := by
      rwa [Metric.mem_ball, dist_comm, hw0] at hw
    exact (lt_irrefl _ hw').elim
  refine ⟨Metric.ball z (dist z 0), Metric.isOpen_ball, Metric.mem_ball_self hz0, ?_, ?_⟩
  · intro w hw
    simpa using hball0 hw
  · have hdiff : DifferentiableOn ℂ (fun w : ℂ ↦ w⁻¹) (Metric.ball z (dist z 0)) := by
      intro w hw
      exact (differentiableAt_inv (hball0 hw)).differentiableWithinAt
    exact hdiff.isExactOn_ball.hasPrimitiveOn

private theorem dz_div_z_not_hasPrimitiveOn_punctured_plane :
    ¬ HasPrimitiveOn ({0}ᶜ : Set ℂ) (Complex.realScalarOneForm fun z : ℂ ↦ z⁻¹) := by
  intro hprimitive
  exact not_isExactOn_inv_punctured_plane hprimitive.isExactOn

/-- Proposition 4.2: on the punctured complex plane `D = {z : ℂ | z ≠ 0}`, the real-linear form
underlying `dz / z` is closed but has no primitive on `D`. -/
theorem dz_div_z_closed_not_hasPrimitiveOn_punctured_plane :
    IsClosedOn (Complex.realScalarOneForm fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) ∧
      ¬ HasPrimitiveOn ({0}ᶜ : Set ℂ) (Complex.realScalarOneForm fun z : ℂ ↦ z⁻¹) :=
  ⟨dz_div_z_isClosedOn_punctured_plane, dz_div_z_not_hasPrimitiveOn_punctured_plane⟩

/-- Equivalent function-level reformulation of Proposition 4.2: on the punctured complex plane,
`z ↦ z⁻¹` is conservative but not exact. -/
theorem dz_div_z_conservative_not_exact_on_punctured_plane :
    Complex.IsConservativeOn (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) ∧
      ¬ Complex.IsExactOn (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) :=
  ⟨isConservativeOn_inv_punctured_plane, not_isExactOn_inv_punctured_plane⟩
