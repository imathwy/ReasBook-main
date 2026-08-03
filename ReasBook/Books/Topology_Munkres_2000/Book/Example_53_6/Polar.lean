module

public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap

@[expose] public section

open Set

namespace Complex

noncomputable section

/-- Helper for Example 53.6: the complex value represented by positive polar coordinates. -/
def polarForwardValue (zr : Circle × Set.Ioi (0 : ℝ)) : ℂ :=
  (zr.2.1 : ℂ) * (zr.1 : ℂ)

/-- Helper for Example 53.6: a positive radius times a unit direction is nonzero. -/
lemma polarForwardValue_ne_zero (zr : Circle × Set.Ioi (0 : ℝ)) :
    polarForwardValue zr ≠ 0 := by
  exact mul_ne_zero (ofReal_ne_zero.mpr zr.2.2.ne') zr.1.coe_ne_zero

/-- Helper for Example 53.6: positive polar coordinates determine a punctured-plane point. -/
def polarForward (zr : Circle × Set.Ioi (0 : ℝ)) : {z : ℂ // z ≠ 0} :=
  ⟨polarForwardValue zr, polarForwardValue_ne_zero zr⟩

/-- Helper for Example 53.6: the normalized direction of a nonzero complex number. -/
def polarDirectionValue (z : {z : ℂ // z ≠ 0}) : ℂ :=
  z.1 / ‖z.1‖

/-- Helper for Example 53.6: the normalized direction of a nonzero complex number has norm one. -/
lemma polarDirectionValue_mem_circle (z : {z : ℂ // z ≠ 0}) :
    polarDirectionValue z ∈ Submonoid.unitSphere ℂ := by
  -- Dividing by the positive norm places the direction on the unit sphere.
  apply mem_sphere_zero_iff_norm.mpr
  rw [polarDirectionValue, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z.1), div_self (norm_ne_zero_iff.mpr z.2)]

/-- Helper for Example 53.6: normalization gives the unit-circle direction of a nonzero point. -/
def polarDirection (z : {z : ℂ // z ≠ 0}) : Circle :=
  ⟨polarDirectionValue z, polarDirectionValue_mem_circle z⟩

/-- Helper for Example 53.6: a nonzero complex number has positive radius. -/
lemma polarRadius_pos (z : {z : ℂ // z ≠ 0}) : 0 < ‖z.1‖ := by
  exact norm_pos_iff.mpr z.2

/-- Helper for Example 53.6: the norm gives the positive radius of a nonzero point. -/
def polarRadius (z : {z : ℂ // z ≠ 0}) : Set.Ioi (0 : ℝ) :=
  ⟨‖z.1‖, polarRadius_pos z⟩

/-- Helper for Example 53.6: a punctured-plane point determines its direction and radius. -/
def polarInverse (z : {z : ℂ // z ≠ 0}) : Circle × Set.Ioi (0 : ℝ) :=
  (polarDirection z, polarRadius z)

/-- Helper for Example 53.6: the norm of a positive radius times a unit direction is that radius. -/
lemma norm_polarForwardValue (zr : Circle × Set.Ioi (0 : ℝ)) :
    ‖polarForwardValue zr‖ = zr.2.1 := by
  rw [polarForwardValue, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos zr.2.2, Circle.norm_coe, mul_one]

/-- Helper for Example 53.6: normalizing a polar-coordinate value recovers its direction. -/
lemma polarDirection_polarForward (zr : Circle × Set.Ioi (0 : ℝ)) :
    polarDirection (polarForward zr) = zr.1 := by
  -- Cancel the recovered positive radius after reducing equality to complex values.
  apply Circle.ext
  simp only [polarDirection, polarDirectionValue, polarForward]
  rw [norm_polarForwardValue, polarForwardValue]
  apply (div_eq_iff (ofReal_ne_zero.mpr zr.2.2.ne')).mpr
  exact mul_comm _ _

/-- Helper for Example 53.6: taking the radius of a polar-coordinate value recovers its radius. -/
lemma polarRadius_polarForward (zr : Circle × Set.Ioi (0 : ℝ)) :
    polarRadius (polarForward zr) = zr.2 := by
  apply Subtype.ext
  exact norm_polarForwardValue zr

/-- Helper for Example 53.6: converting to Cartesian coordinates and back fixes polar data. -/
lemma polarInverse_polarForward (zr : Circle × Set.Ioi (0 : ℝ)) :
    polarInverse (polarForward zr) = zr := by
  -- The direction and radius specifications establish the two product components.
  apply Prod.ext
  · exact polarDirection_polarForward zr
  · exact polarRadius_polarForward zr

/-- Helper for Example 53.6: scaling a normalized direction by its norm recovers the point. -/
lemma polarForward_polarInverse (z : {z : ℂ // z ≠ 0}) :
  polarForward (polarInverse z) = z := by
  -- Scale the normalized direction and cancel the nonzero norm.
  apply Subtype.ext
  simp only [polarForward, polarForwardValue, polarInverse, polarRadius, polarDirection,
    polarDirectionValue]
  have hnorm : (‖z.1‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.2)
  calc
    (‖z.1‖ : ℂ) * (z.1 / ‖z.1‖) = z.1 * ((‖z.1‖ : ℂ) / ‖z.1‖) := by ring
    _ = z.1 := by rw [div_self hnorm, mul_one]

/-- Helper for Example 53.6: Cartesian conversion is continuous on positive polar coordinates. -/
lemma continuous_polarForward : Continuous polarForward := by
  apply Continuous.subtype_mk
  unfold polarForwardValue
  fun_prop

/-- Helper for Example 53.6: direction and radius vary continuously away from the origin. -/
lemma continuous_polarInverse : Continuous polarInverse := by
  -- The direction quotient is continuous off zero, while the radius is the norm.
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    unfold polarDirectionValue
    apply Continuous.div₀
    · exact continuous_subtype_val
    · exact Complex.continuous_ofReal.comp continuous_subtype_val.norm
    · intro z
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.2)
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.norm

/-- Positive polar coordinates identify `Circle × ℝ₊` with the punctured complex plane. -/
noncomputable def polarHomeomorph : Circle × Set.Ioi (0 : ℝ) ≃ₜ {z : ℂ // z ≠ 0} where
  toFun := polarForward
  invFun := polarInverse
  left_inv := polarInverse_polarForward
  right_inv := polarForward_polarInverse
  continuous_toFun := continuous_polarForward
  continuous_invFun := continuous_polarInverse

/-- Helper for Example 53.6: the polar homeomorphism applies the Cartesian conversion map. -/
@[simp]
lemma polarHomeomorph_apply (zr : Circle × Set.Ioi (0 : ℝ)) :
    polarHomeomorph zr = polarForward zr := by
  rfl

/-- The polar-coordinate covering map of the punctured complex plane. -/
noncomputable def polarTurn : ℝ × Set.Ioi (0 : ℝ) → {z : ℂ // z ≠ 0} :=
  polarHomeomorph ∘ Prod.map Circle.turnExp id

/-- The underlying complex value of `polarTurn` is its polar-coordinate formula. -/
@[simp]
theorem coe_polarTurn (xt : ℝ × Set.Ioi (0 : ℝ)) :
    (polarTurn xt : ℂ) = (xt.2.1 : ℂ) * (Circle.turnExp xt.1 : ℂ) := by
  rw [polarTurn, Function.comp_apply, polarHomeomorph_apply]
  rfl

end

end Complex
