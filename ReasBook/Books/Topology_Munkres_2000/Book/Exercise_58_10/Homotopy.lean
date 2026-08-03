module

public import Topology_Munkres_2000.Book.Definition_55_2.Nonvanishing
public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal
public import Topology_Munkres_2000.Book.Exercise_58_10.VectorField
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homotopy.Basic

noncomputable section

public section

namespace StandardSphere

open scoped unitInterval

/-- Helper for Exercise 58.10: the segment from one unit vector toward the negative of
another avoids zero unless the vectors agree. -/
theorem unitSegmentToNeg_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : y ≠ x) (t : unitInterval) :
    (1 - (t : ℝ)) • y - (t : ℝ) • x ≠ 0 := by
  intro hz
  have heq : (1 - (t : ℝ)) • y = (t : ℝ) • x := sub_eq_zero.mp hz
  have hnorm := congrArg norm heq
  rw [norm_smul, norm_smul, hx, hy, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs] at hnorm
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  rw [abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0] at hnorm
  have ht : (t : ℝ) = 1 / 2 := by
    linarith
  rw [ht] at heq
  norm_num at heq
  exact hne heq

/-- Helper for Exercise 58.10: the normalized segment from a fixed-point-free map
to the antipodal map is defined at every parameter. -/
theorem fixedPointSegment_ne_zero {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_fixed : ∀ x, h x ≠ x)
    (p : unitInterval × StandardSphere n) :
    (1 - (p.1 : ℝ)) • (h p.2 : EuclideanSpace ℝ (Fin (n + 1))) -
        (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
  apply unitSegmentToNeg_ne_zero
  · exact mem_sphere_zero_iff_norm.mp p.2.property
  · exact mem_sphere_zero_iff_norm.mp (h p.2).property
  · exact fun heq ↦ h_fixed p.2 (Subtype.ext heq)

/-- Helper for Exercise 58.10: the normalized fixed-point-free segment lies on the sphere. -/
theorem fixedPointHomotopy_mem {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_fixed : ∀ x, h x ≠ x)
    (p : unitInterval × StandardSphere n) :
    NormedSpace.normalize
      ((1 - (p.1 : ℝ)) • (h p.2 : EuclideanSpace ℝ (Fin (n + 1))) -
        (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (n + 1)))) ∈ StandardSphere n := by
  rw [mem_sphere_zero_iff_norm]
  exact NormedSpace.norm_normalize (fixedPointSegment_ne_zero h h_fixed p)

/-- Helper for Exercise 58.10: a point of the fixed-point-free normalized segment. -/
def fixedPointHomotopyValue {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_fixed : ∀ x, h x ≠ x)
    (p : unitInterval × StandardSphere n) : StandardSphere n :=
  ⟨NormedSpace.normalize
    ((1 - (p.1 : ℝ)) • (h p.2 : EuclideanSpace ℝ (Fin (n + 1))) -
      (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (n + 1)))),
    fixedPointHomotopy_mem h h_fixed p⟩

/-- Helper for Exercise 58.10: the fixed-point-free normalized segment is continuous. -/
theorem continuous_fixedPointHomotopyValue {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_fixed : ∀ x, h x ≠ x) :
    Continuous (fixedPointHomotopyValue h h_fixed) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  unfold NormedSpace.normalize
  apply ContinuousAt.smul (M := ℝ)
  · apply ContinuousAt.inv₀
    · fun_prop
    · exact norm_ne_zero_iff.mpr (fixedPointSegment_ne_zero h h_fixed p)
  · fun_prop

/-- Helper for Exercise 58.10: the fixed-point-free normalized segment starts at the map. -/
theorem fixedPointHomotopyValue_zero {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_fixed : ∀ x, h x ≠ x)
    (x : StandardSphere n) : fixedPointHomotopyValue h h_fixed (0, x) = h x := by
  apply Subtype.ext
  simp [fixedPointHomotopyValue, NormedSpace.normalize_eq_self_of_norm_eq_one,
    mem_sphere_zero_iff_norm.mp (h x).property]

/-- Helper for Exercise 58.10: the fixed-point-free normalized segment ends at the antipode. -/
theorem fixedPointHomotopyValue_one {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_fixed : ∀ x, h x ≠ x)
    (x : StandardSphere n) : fixedPointHomotopyValue h h_fixed (1, x) = antipodal n x := by
  apply Subtype.ext
  simp [fixedPointHomotopyValue, NormedSpace.normalize_eq_self_of_norm_eq_one,
    mem_sphere_zero_iff_norm.mp x.property, antipodal]

/-- A fixed-point-free sphere self-map is homotopic to the antipodal map. -/
theorem homotopic_antipodal_of_fixedPoint_free {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_fixed : ∀ x, h x ≠ x) :
    h.Homotopic (antipodal n) := by
  -- Normalize the straight segment joining `h x` to `-x`.
  exact ⟨{
    toFun := fixedPointHomotopyValue h h_fixed
    continuous_toFun := continuous_fixedPointHomotopyValue h h_fixed
    map_zero_left := fixedPointHomotopyValue_zero h h_fixed
    map_one_left := fixedPointHomotopyValue_one h h_fixed }⟩

/-- A sphere self-map avoiding every antipode is homotopic to the identity. -/
theorem homotopic_id_of_avoids_antipodes {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (h_antipode : ∀ x, h x ≠ -x) :
    h.Homotopic (ContinuousMap.id (StandardSphere n)) := by
  -- Negating `h` converts antipode avoidance into fixed-point avoidance.
  let negH := (antipodal n).comp h
  have negH_fixed : ∀ x, negH x ≠ x := by
    intro x hx
    apply h_antipode x
    apply Subtype.ext
    have hx' := congrArg Subtype.val hx
    simpa [negH, antipodal] using congrArg Neg.neg hx'
  have homotopic := homotopic_antipodal_of_fixedPoint_free negH negH_fixed
  have composed := (ContinuousMap.Homotopic.refl (antipodal n)).comp homotopic
  have left_eq : (antipodal n).comp negH = h := by
    ext x
    simp [negH, antipodal]
  have right_eq :
      (antipodal n).comp (antipodal n) = ContinuousMap.id (StandardSphere n) := by
    ext x
    simp [antipodal]
  rw [left_eq, right_eq] at composed
  exact composed

/-- Helper for Exercise 58.10: normalizing a nonvanishing vector field produces sphere values. -/
theorem normalizedVectorField_mem {n : ℕ} (v : VectorField n)
    (h_nonvanishing : v.IsNonvanishing) (x : StandardSphere n) :
    NormedSpace.normalize (v x) ∈ StandardSphere n := by
  rw [mem_sphere_zero_iff_norm]
  exact NormedSpace.norm_normalize (h_nonvanishing x)

/-- Helper for Exercise 58.10: the normalized form of a nonvanishing vector field is continuous. -/
theorem continuous_normalizedVectorField {n : ℕ} (v : VectorField n)
    (h_nonvanishing : v.IsNonvanishing) :
    Continuous (fun x : StandardSphere n ↦
      (⟨NormedSpace.normalize (v x), normalizedVectorField_mem v h_nonvanishing x⟩ :
        StandardSphere n)) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro x
  unfold NormedSpace.normalize
  apply ContinuousAt.smul (M := ℝ)
  · apply ContinuousAt.inv₀
    · fun_prop
    · exact norm_ne_zero_iff.mpr (h_nonvanishing x)
  · fun_prop

/-- Helper for Exercise 58.10: normalize a nonvanishing tangent vector field to the sphere. -/
def normalizedVectorField {n : ℕ} (v : VectorField n) (h_nonvanishing : v.IsNonvanishing) :
    C(StandardSphere n, StandardSphere n) :=
  ⟨fun x ↦ ⟨NormedSpace.normalize (v x), normalizedVectorField_mem v h_nonvanishing x⟩,
    continuous_normalizedVectorField v h_nonvanishing⟩

/-- A nonvanishing tangent vector field makes the identity homotopic to the antipodal map. -/
theorem homotopic_antipodal_of_nonvanishingTangentField {n : ℕ}
    (v : VectorField n) (h_tangent : v.IsTangent) (h_nonvanishing : v.IsNonvanishing) :
    (ContinuousMap.id (StandardSphere n)).Homotopic (antipodal n) := by
  -- The normalized tangent field avoids both each point and its antipode.
  let w := normalizedVectorField v h_nonvanishing
  have w_tangent : ∀ x : StandardSphere n,
      inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) (w x) = 0 := by
    intro x
    change inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1)))
      (NormedSpace.normalize (v x)) = 0
    have tangent_at : ∀ y : StandardSphere n,
        inner ℝ (y : EuclideanSpace ℝ (Fin (n + 1))) (v y) = 0 := by
      simpa only [VectorField.isTangent_iff] using h_tangent
    rw [NormedSpace.normalize, inner_smul_right, tangent_at x, mul_zero]
  have w_fixed : ∀ x : StandardSphere n, w x ≠ x := by
    intro x hx
    have hinner := w_tangent x
    rw [hx] at hinner
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp x.property
    rw [real_inner_self_eq_norm_sq, hnorm] at hinner
    norm_num at hinner
  have w_antipode : ∀ x : StandardSphere n, w x ≠ -x := by
    intro x hx
    have hinner := w_tangent x
    rw [hx] at hinner
    change inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1)))
      (-(x : EuclideanSpace ℝ (Fin (n + 1)))) = 0 at hinner
    rw [inner_neg_right] at hinner
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp x.property
    rw [real_inner_self_eq_norm_sq, hnorm] at hinner
    norm_num at hinner
  exact (homotopic_id_of_avoids_antipodes w w_antipode).symm.trans
    (homotopic_antipodal_of_fixedPoint_free w w_fixed)

end StandardSphere
