import Mathlib
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22»
import DifferentialForms_Cartan_1970.IV.section16.«0002_Theorem_IV_4_extra_2»

open Filter InnerProductSpace Laplacian Metric Real Set Topology
open scoped BigOperators InnerProductSpace
/-- A real-valued function is subharmonic on `D` if it is continuous there and satisfies the
sub-mean inequality on all sufficiently small circles centered at points of `D`. -/
def IsSubharmonicOn (f : ℂ → ℝ) (D : Set ℂ) : Prop :=
  ContinuousOn f D ∧
    ∀ ⦃a : ℂ⦄, a ∈ D →
      ∃ ε > 0, ∀ ⦃r : ℝ⦄, 0 < r → r < ε →
        Metric.closedBall a r ⊆ D ∧ f a ≤ Real.circleAverage f a r

/-- A subharmonic function is continuous on its domain. -/
theorem IsSubharmonicOn.continuousOn {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D) :
    ContinuousOn f D :=
  hf.1

/-- On each admissible circle, the circle-integrability appearing in the mean inequality is
derived from continuity. -/
theorem IsSubharmonicOn.circleIntegrable {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall a r ⊆ D) :
    CircleIntegrable f a r :=
  (hf.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le

/-- An unfolding theorem for `IsSubharmonicOn`. -/
theorem isSubharmonicOn_iff {f : ℂ → ℝ} {D : Set ℂ} :
    IsSubharmonicOn f D ↔
      ContinuousOn f D ∧
        ∀ ⦃a : ℂ⦄, a ∈ D →
          ∃ ε > 0, ∀ ⦃r : ℝ⦄, 0 < r → r < ε →
            Metric.closedBall a r ⊆ D ∧ f a ≤ Real.circleAverage f a r :=
  Iff.rfl

/-- Helper for Exercise 4: every domain carrying a subharmonic function is open. -/
theorem IsSubharmonicOn.isOpen {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D) :
    IsOpen D := by
  -- Each point in the domain comes with a small closed ball still contained in the domain.
  rw [Metric.isOpen_iff]
  intro a ha
  rcases hf.2 ha with ⟨ε, hε_pos, hε⟩
  have hhalf_pos : 0 < ε / 2 := by positivity
  have hhalf_lt : ε / 2 < ε := by linarith
  rcases hε hhalf_pos hhalf_lt with ⟨hball, _⟩
  refine ⟨ε / 2, hhalf_pos, ?_⟩
  intro z hz
  exact hball (ball_subset_closedBall hz)

/-- Helper for Exercise 4: constant functions are subharmonic on open sets. -/
lemma isSubharmonicOn_const {D : Set ℂ} (hD : IsOpen D) (c : ℝ) :
    IsSubharmonicOn (fun _ ↦ c) D := by
  constructor
  · -- Continuity of a constant function is immediate.
    exact continuousOn_const
  · intro a ha
    rcases Metric.isOpen_iff.mp hD a ha with ⟨ε, hε_pos, hε⟩
    refine ⟨ε, hε_pos, ?_⟩
    intro r hr_pos hr_lt
    refine ⟨?_, ?_⟩
    · -- Shrinking from the ambient open ball gives the required closed-ball inclusion.
      exact (Metric.closedBall_subset_ball hr_lt).trans hε
    · -- The circle average of a constant function is that constant.
      rw [Real.circleAverage_const]

/-- Helper for Exercise 4: nonnegative scalar multiples of subharmonic functions stay
subharmonic. -/
theorem IsSubharmonicOn.smul_nonneg {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D)
    {c : ℝ} (hc : 0 ≤ c) :
    IsSubharmonicOn (fun z ↦ c * f z) D := by
  constructor
  · -- Multiplication by a fixed scalar preserves continuity.
    simpa using
      (continuousOn_const.mul hf.continuousOn :
        ContinuousOn (fun z : ℂ ↦ (fun _ : ℂ ↦ c) z * f z) D)
  · intro a ha
    rcases hf.2 ha with ⟨ε, hε_pos, hε⟩
    refine ⟨ε, hε_pos, ?_⟩
    intro r hr_pos hr_lt
    rcases hε hr_pos hr_lt with ⟨hball, hmean⟩
    refine ⟨hball, ?_⟩
    -- Multiply the sub-mean inequality by the nonnegative scalar and rewrite the average.
    calc
      c * f a ≤ c * Real.circleAverage f a r := mul_le_mul_of_nonneg_left hmean hc
      _ = Real.circleAverage (fun z ↦ c * f z) a r := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (Real.circleAverage_smul (a := c) (f := f) (c := a) (R := r)).symm

/-- Helper for Exercise 4: sums of two subharmonic functions stay subharmonic. -/
theorem IsSubharmonicOn.add {f g : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D)
    (hg : IsSubharmonicOn g D) :
    IsSubharmonicOn (fun z ↦ f z + g z) D := by
  constructor
  · -- Continuity is preserved under pointwise addition.
    exact hf.continuousOn.add hg.continuousOn
  · intro a ha
    rcases hf.2 ha with ⟨εf, hεf_pos, hεf⟩
    rcases hg.2 ha with ⟨εg, hεg_pos, hεg⟩
    refine ⟨min εf εg, lt_min hεf_pos hεg_pos, ?_⟩
    intro r hr_pos hr_lt
    have hrf : r < εf := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hrg : r < εg := lt_of_lt_of_le hr_lt (min_le_right _ _)
    rcases hεf hr_pos hrf with ⟨hballf, hmeanf⟩
    rcases hεg hr_pos hrg with ⟨hballg, hmeang⟩
    refine ⟨hballf, ?_⟩
    -- Use linearity of the circle average on the common admissible circle.
    calc
      f a + g a ≤ Real.circleAverage f a r + Real.circleAverage g a r := add_le_add hmeanf hmeang
      _ = Real.circleAverage (fun z ↦ f z + g z) a r := by
        simpa using
          (Real.circleAverage_add (hf.circleIntegrable hr_pos hballf)
            (hg.circleIntegrable hr_pos hballg)).symm

