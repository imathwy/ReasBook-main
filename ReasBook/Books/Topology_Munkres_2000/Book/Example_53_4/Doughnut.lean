module

public import Topology_Munkres_2000.Book.Definition_53_4.Torus

public section

open Complex Set

namespace Torus

/-- The explicit rotation map from the product torus to the doughnut surface in `ℂ × ℝ`. -/
noncomputable def doughnutMap : Torus → ℂ × ℝ :=
  fun point ↦
    ((((1 + (point.1 : ℂ).re / 3 : ℝ) : ℂ) * (point.2 : ℂ)),
      (point.1 : ℂ).im / 3)

/-- The doughnut-shaped surface traced by `doughnutMap`. -/
@[expose]
def doughnutSurface : Set (ℂ × ℝ) :=
  range doughnutMap

/-- Every value of `doughnutMap` lies on the doughnut surface. -/
theorem doughnutMap_mem_surface (point : Torus) : doughnutMap point ∈ doughnutSurface :=
  ⟨point, rfl⟩

/-- Helper for Example 53.4: the norm and height of `doughnutMap` recover both circle
coordinates of a torus point. -/
lemma doughnutMap_recoveredComponents (point : Torus) :
    (((3 * (‖(doughnutMap point).1‖ - 1) : ℝ) : ℂ) +
        (3 * (doughnutMap point).2 : ℝ) * I = (point.1 : ℂ)) ∧
      (doughnutMap point).1 / (‖(doughnutMap point).1‖ : ℝ) = (point.2 : ℂ) := by
  -- The meridian's real coordinate makes the radial factor strictly positive.
  have hre_lower : -1 ≤ (point.1 : ℂ).re := by
    have habs := Complex.abs_re_le_norm (point.1 : ℂ)
    rw [Circle.norm_coe] at habs
    linarith [neg_abs_le (point.1 : ℂ).re]
  have hradius_pos : 0 < 1 + (point.1 : ℂ).re / 3 := by
    linarith
  have hradius_ne : ((1 + (point.1 : ℂ).re / 3 : ℝ) : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr hradius_pos.ne'
  -- Multiplicativity of the norm and the unit norm of the longitude recover the radius.
  have hnorm : ‖(doughnutMap point).1‖ = 1 + (point.1 : ℂ).re / 3 := by
    rw [doughnutMap, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
    exact Real.norm_of_nonneg hradius_pos.le
  constructor
  · -- The recovered real and imaginary parts reassemble the meridian coordinate.
    rw [hnorm]
    apply Complex.ext
    · simp only [doughnutMap, add_re, ofReal_re, mul_re, I_re, I_im,
        ofReal_im, mul_zero, zero_mul, sub_zero]
      ring
    · simp only [doughnutMap, add_im, ofReal_im, mul_im, I_re, I_im,
        ofReal_re, mul_one, zero_mul, add_zero]
      ring
  · -- Division by the recovered nonzero radius cancels the radial factor.
    rw [hnorm]
    simp only [doughnutMap]
    exact mul_div_cancel_left₀ (point.2 : ℂ) hradius_ne

/-- Helper for Example 53.4: both coordinate formulas for the explicit inverse lie on the
unit circle. -/
lemma doughnutInverse_components_mem (point : doughnutSurface) :
    (((3 * (‖point.1.1‖ - 1) : ℝ) : ℂ) + (3 * point.1.2 : ℝ) * I ∈
        Submonoid.unitSphere ℂ) ∧
      point.1.1 / (‖point.1.1‖ : ℝ) ∈ Submonoid.unitSphere ℂ := by
  -- Represent the surface point by a torus point, then use coordinate recovery.
  obtain ⟨source, hsource⟩ := point.property
  rw [← hsource]
  have hrecovered := doughnutMap_recoveredComponents source
  constructor
  · rw [hrecovered.1]
    exact source.1.property
  · rw [hrecovered.2]
    exact source.2.property

/-- The explicit inverse from the doughnut surface to the product torus. -/
noncomputable def doughnutInverse (point : doughnutSurface) : Torus :=
  -- The component-membership lemma supplies both proof fields without unfolding the surface.
  (⟨((3 * (‖point.1.1‖ - 1) : ℝ) : ℂ) + (3 * point.1.2 : ℝ) * I,
      (doughnutInverse_components_mem point).1⟩,
    ⟨point.1.1 / (‖point.1.1‖ : ℝ), (doughnutInverse_components_mem point).2⟩)

/-- Helper for Example 53.4: the explicit inverse is a left inverse of the lifted doughnut
parametrization. -/
lemma doughnutInverse_leftInverse :
    Function.LeftInverse doughnutInverse
      (fun point : Torus ↦ ⟨doughnutMap point, doughnutMap_mem_surface point⟩) := by
  intro point
  -- Equality of the two circle coordinates follows from the raw recovery equations.
  apply Prod.ext
  · apply Circle.ext
    exact (doughnutMap_recoveredComponents point).1
  · apply Circle.ext
    exact (doughnutMap_recoveredComponents point).2

/-- The explicit doughnut parametrization is a topological embedding. -/
theorem doughnutMap_isEmbedding : Topology.IsEmbedding doughnutMap := by
  -- The left inverse gives injectivity after passing through the surface subtype.
  have hinjective : Function.Injective doughnutMap := by
    intro x y hxy
    have hlifted :
        (⟨doughnutMap x, doughnutMap_mem_surface x⟩ : doughnutSurface) =
          ⟨doughnutMap y, doughnutMap_mem_surface y⟩ := by
      exact Subtype.ext hxy
    exact doughnutInverse_leftInverse.injective hlifted
  have hcontinuous : Continuous doughnutMap := by
    unfold doughnutMap
    fun_prop
  -- A continuous injection from the compact torus into a Hausdorff space is an embedding.
  exact (hcontinuous.isClosedEmbedding hinjective).isEmbedding

/-- Helper for Example 53.4: the explicit inverse is also a right inverse on the doughnut
surface. -/
lemma doughnutInverse_rightInverse :
    Function.RightInverse doughnutInverse
      (fun point : Torus ↦ ⟨doughnutMap point, doughnutMap_mem_surface point⟩) := by
  intro point
  -- Replace the surface point by a chosen parametrizing point and apply the left-inverse law.
  obtain ⟨source, hsource⟩ := point.property
  have hpoint :
      (⟨doughnutMap source, doughnutMap_mem_surface source⟩ : doughnutSurface) = point := by
    exact Subtype.ext hsource
  rw [← hpoint]
  exact congrArg (fun q : Torus ↦
    (⟨doughnutMap q, doughnutMap_mem_surface q⟩ : doughnutSurface))
      (doughnutInverse_leftInverse source)

/-- Helper for Example 53.4: the explicit inverse is continuous on the doughnut surface. -/
lemma continuous_doughnutInverse : Continuous doughnutInverse := by
  -- The embedding criterion reduces continuity to the continuous surface inclusion.
  refine doughnutMap_isEmbedding.continuous_iff.mpr ?_
  have hcomposition :
      doughnutMap ∘ doughnutInverse = (fun point : doughnutSurface ↦ point.1) := by
    funext point
    exact congrArg Subtype.val (doughnutInverse_rightInverse point)
  rw [hcomposition]
  exact continuous_subtype_val

/-- The product torus is homeomorphic to the familiar doughnut surface. -/
@[expose]
noncomputable def doughnutHomeomorph : Torus ≃ₜ doughnutSurface where
  -- Assemble the explicit maps using the inverse-law and continuity interface proved above.
  toFun point := ⟨doughnutMap point, doughnutMap_mem_surface point⟩
  invFun := doughnutInverse
  left_inv := doughnutInverse_leftInverse
  right_inv := doughnutInverse_rightInverse
  continuous_toFun := doughnutMap_isEmbedding.continuous.subtype_mk doughnutMap_mem_surface
  continuous_invFun := continuous_doughnutInverse

/-- The doughnut homeomorphism has underlying map `doughnutMap`. -/
theorem doughnutHomeomorph_apply (point : Torus) :
    (doughnutHomeomorph point : ℂ × ℝ) = doughnutMap point := rfl

/-- The inverse doughnut homeomorphism is the explicit map `doughnutInverse`. -/
theorem doughnutHomeomorph_symm_apply (point : doughnutSurface) :
    doughnutHomeomorph.symm point = doughnutInverse point := rfl

end Torus
