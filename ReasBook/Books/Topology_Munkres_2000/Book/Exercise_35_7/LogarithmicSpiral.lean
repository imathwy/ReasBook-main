module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public section

/- The logarithmic spiral in the plane, including its limiting point at the origin. -/
namespace LogarithmicSpiral

/-- The standard parameterization of the logarithmic spiral away from the origin. -/
noncomputable def param (t : ℝ) : ℝ × ℝ :=
  (Real.exp t * Real.cos t, Real.exp t * Real.sin t)

/-- The logarithmic spiral, including its limiting point at the origin. -/
noncomputable def carrier : Set (ℝ × ℝ) :=
  insert (0, 0) (Set.range param)

/-- The explicit radial projection of the plane onto the logarithmic spiral. -/
noncomputable def projection (x : ℝ × ℝ) : ℝ × ℝ :=
  let ρ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)
  (ρ * Real.cos (Real.log ρ), ρ * Real.sin (Real.log ρ))

/-- Helper for Exercise 35.7: the Euclidean radius of a point on the logarithmic spiral is
`Real.exp t`. -/
private lemma radius_param (t : ℝ) :
    Real.sqrt ((param t).1 ^ 2 + (param t).2 ^ 2) = Real.exp t := by
  unfold param
  calc
    Real.sqrt ((Real.exp t * Real.cos t) ^ 2 + (Real.exp t * Real.sin t) ^ 2) =
        Real.sqrt ((Real.exp t) ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2)) := by
      congr 1
      ring
    _ = Real.exp t := by
      rw [Real.cos_sq_add_sin_sq, mul_one, Real.sqrt_sq (Real.exp_pos t).le]

/-- Helper for Exercise 35.7: the explicit projection fixes each parameterized point of the
logarithmic spiral. -/
private lemma projection_param (t : ℝ) : projection (param t) = param t := by
  unfold projection
  rw [radius_param]
  simp only [Real.log_exp]
  rfl

/-- The explicit radial projection lands in the logarithmic spiral. -/
theorem projection_mem (x : ℝ × ℝ) : projection x ∈ carrier := by
  rw [carrier, Set.mem_insert_iff, Set.mem_range]
  let ρ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  rcases hρ.eq_or_lt with hρzero | hρpos
  · left
    simp [projection, ρ, hρzero.symm]
  · right
    refine ⟨Real.log ρ, ?_⟩
    simp [projection, param, ρ, Real.exp_log hρpos]

/-- Helper for Exercise 35.7: multiplying `Real.cos (Real.log r)` by its radius removes the
discontinuity of the logarithm at zero. -/
private lemma continuous_mul_cos_log :
    Continuous (fun r : ℝ ↦ r * Real.cos (Real.log r)) := by
  rw [continuous_iff_continuousAt]
  intro r
  rcases eq_or_ne r 0 with rfl | hr
  · rw [ContinuousAt]
    simpa only [id_eq, zero_mul, mul_comm] using
      bdd_le_mul_tendsto_zero' (1 : ℝ)
        (Filter.Eventually.of_forall fun s ↦ Real.abs_cos_le_one (Real.log s)) continuousAt_id
  · exact continuousAt_id.mul
      (Real.continuous_cos.continuousAt.comp (Real.continuousAt_log hr))

/-- Helper for Exercise 35.7: multiplying `Real.sin (Real.log r)` by its radius removes the
discontinuity of the logarithm at zero. -/
private lemma continuous_mul_sin_log :
    Continuous (fun r : ℝ ↦ r * Real.sin (Real.log r)) := by
  rw [continuous_iff_continuousAt]
  intro r
  rcases eq_or_ne r 0 with rfl | hr
  · rw [ContinuousAt]
    simpa only [id_eq, zero_mul, mul_comm] using
      bdd_le_mul_tendsto_zero' (1 : ℝ)
        (Filter.Eventually.of_forall fun s ↦ Real.abs_sin_le_one (Real.log s)) continuousAt_id
  · exact continuousAt_id.mul
      (Real.continuous_sin.continuousAt.comp (Real.continuousAt_log hr))

/-- The subtype-valued logarithmic-spiral projection is continuous. -/
theorem continuous_projection :
    Continuous (fun x : ℝ × ℝ ↦ (⟨projection x, projection_mem x⟩ : carrier)) := by
  -- The radius is continuous, and the two bounded angular factors extend continuously at zero.
  have continuousRadius : Continuous (fun x : ℝ × ℝ ↦
      Real.sqrt (x.1 ^ 2 + x.2 ^ 2)) :=
    Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2))
  apply Continuous.subtype_mk
  change Continuous (fun x : ℝ × ℝ ↦
    (Real.sqrt (x.1 ^ 2 + x.2 ^ 2) *
        Real.cos (Real.log (Real.sqrt (x.1 ^ 2 + x.2 ^ 2))),
      Real.sqrt (x.1 ^ 2 + x.2 ^ 2) *
        Real.sin (Real.log (Real.sqrt (x.1 ^ 2 + x.2 ^ 2)))))
  simpa only [Function.comp_apply] using
    (continuous_mul_cos_log.comp continuousRadius).prodMk
      (continuous_mul_sin_log.comp continuousRadius)

/-- The continuous map determined by the explicit logarithmic-spiral projection. -/
@[expose]
noncomputable def map : C(ℝ × ℝ, carrier) where
  toFun := fun x ↦ ⟨projection x, projection_mem x⟩
  continuous_toFun := continuous_projection

/-- The explicit logarithmic-spiral projection fixes every point of the spiral. -/
theorem map_leftInverse : Function.LeftInverse map Subtype.val := by
  intro a
  apply Subtype.ext
  change projection (a : ℝ × ℝ) = (a : ℝ × ℝ)
  have ha : (a : ℝ × ℝ) = (0, 0) ∨ ∃ t, param t = (a : ℝ × ℝ) := by
    simpa only [carrier, Set.mem_insert_iff, Set.mem_range] using a.property
  rcases ha with ha | ⟨t, ht⟩
  · rw [ha]
    simp [projection]
  · rw [← ht, projection_param]

/-- The explicit retraction of the plane onto the logarithmic spiral. -/
@[expose]
noncomputable def retraction : Set.Retraction carrier :=
  Set.Retraction.ofContinuousMap map map_leftInverse

/-- The ambient value of the logarithmic-spiral retraction is its explicit formula. -/
theorem retraction_apply (x : ℝ × ℝ) :
    (retraction.apply x : ℝ × ℝ) = projection x := rfl

/-- The logarithmic spiral is a retract of the plane. -/
theorem isRetract : Set.IsRetract carrier :=
  Set.isRetract_iff carrier |>.2 ⟨map, map_leftInverse⟩

end LogarithmicSpiral
