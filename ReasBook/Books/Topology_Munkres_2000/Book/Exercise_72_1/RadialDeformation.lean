module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction

public section

open unitInterval

noncomputable section

/-- Helper for Exercise 72.1: the ambient origin belongs to the closed unit ball. -/
lemma zero_mem_closedUnitBall (m : ℕ) :
    (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ Metric.closedBall 0 1 := by
  -- The origin has distance zero from the center of the unit ball.
  simp

/-- Helper for Exercise 72.1: the center point of the closed unit ball. -/
@[expose] def closedUnitBallCenter (m : ℕ) : ClosedUnitBall m :=
  ⟨0, zero_mem_closedUnitBall m⟩

/-- Helper for Exercise 72.1: the punctured closed unit ball. -/
abbrev PuncturedClosedUnitBall (m : ℕ) :=
  ({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ

/-- Helper for Exercise 72.1: a point of the punctured ball is a nonzero ambient vector. -/
lemma puncturedClosedUnitBall_ne_zero (m : ℕ) (x : PuncturedClosedUnitBall m) :
    (x.1.1 : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
  -- A zero ambient vector would identify the point with the removed center.
  intro hx
  apply x.property
  apply Subtype.ext
  exact hx

/-- Helper for Exercise 72.1: a point of the punctured ball has positive norm. -/
lemma puncturedClosedUnitBall_norm_pos (m : ℕ) (x : PuncturedClosedUnitBall m) :
    0 < ‖(x.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  -- Positivity of the norm is equivalent to nonvanishing.
  exact norm_pos_iff.mpr (puncturedClosedUnitBall_ne_zero m x)

/-- Helper for Exercise 72.1: the positive scalar used by the radial homotopy. -/
def puncturedClosedUnitBall_radialScalar (t : unitInterval)
    {m : ℕ} (x : PuncturedClosedUnitBall m) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) / ‖(x.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖

/-- Helper for Exercise 72.1: the ambient value of the radial homotopy. -/
def puncturedClosedUnitBall_radialValue (t : unitInterval)
    {m : ℕ} (x : PuncturedClosedUnitBall m) : EuclideanSpace ℝ (Fin (m + 1)) :=
  puncturedClosedUnitBall_radialScalar t x • x.1.1

/-- Helper for Exercise 72.1: the radial scalar is strictly positive. -/
lemma puncturedClosedUnitBall_radialScalar_pos (t : unitInterval)
    {m : ℕ} (x : PuncturedClosedUnitBall m) :
    0 < puncturedClosedUnitBall_radialScalar t x := by
  -- The scalar is a convex combination of two positive numbers.
  have ht_nonneg : 0 ≤ (t : ℝ) := t.property.1
  have ht_le_one : (t : ℝ) ≤ 1 := t.property.2
  have hx_norm_pos := puncturedClosedUnitBall_norm_pos m x
  unfold puncturedClosedUnitBall_radialScalar
  by_cases ht_zero : (t : ℝ) = 0
  · simp [ht_zero]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht_le_one)
      (div_pos (lt_of_le_of_ne ht_nonneg (Ne.symm ht_zero)) hx_norm_pos)

/-- Helper for Exercise 72.1: the radial output norm has a linear formula. -/
lemma norm_puncturedClosedUnitBall_radialValue (t : unitInterval)
    {m : ℕ} (x : PuncturedClosedUnitBall m) :
    ‖puncturedClosedUnitBall_radialValue t x‖ =
      (1 - (t : ℝ)) * ‖(x.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ + (t : ℝ) := by
  -- Positivity removes the absolute value from `norm_smul`, and the denominator cancels.
  have hscalar := (puncturedClosedUnitBall_radialScalar_pos t x).le
  have hx_norm_ne : ‖(x.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ ≠ 0 :=
    ne_of_gt (puncturedClosedUnitBall_norm_pos m x)
  rw [puncturedClosedUnitBall_radialValue, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscalar]
  unfold puncturedClosedUnitBall_radialScalar
  field_simp

/-- Helper for Exercise 72.1: the radial homotopy remains in the closed unit ball. -/
lemma puncturedClosedUnitBall_radialValue_mem (t : unitInterval)
    {m : ℕ} (x : PuncturedClosedUnitBall m) :
    puncturedClosedUnitBall_radialValue t x ∈ Metric.closedBall 0 1 := by
  -- The output norm is bounded by the same convex combination with the unit norm.
  rw [Metric.mem_closedBall, dist_zero_right,
    norm_puncturedClosedUnitBall_radialValue]
  have hx_le_one : ‖(x.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := by
    have hx_dist : dist (x.1.1 : EuclideanSpace ℝ (Fin (m + 1))) 0 ≤ 1 :=
      Metric.mem_closedBall.mp x.1.property
    rwa [dist_zero_right] at hx_dist
  have ht_nonneg : 0 ≤ (t : ℝ) := t.property.1
  have ht_le_one : (t : ℝ) ≤ 1 := t.property.2
  nlinarith

/-- Helper for Exercise 72.1: the radial homotopy never reaches the removed center. -/
lemma puncturedClosedUnitBall_radialValue_ne_zero (t : unitInterval)
    {m : ℕ} (x : PuncturedClosedUnitBall m) :
    puncturedClosedUnitBall_radialValue t x ≠ 0 := by
  -- A positive scalar multiple of a nonzero vector remains nonzero.
  exact smul_ne_zero (ne_of_gt (puncturedClosedUnitBall_radialScalar_pos t x))
    (puncturedClosedUnitBall_ne_zero m x)

/-- Helper for Exercise 72.1: the radial homotopy starts at its input. -/
lemma puncturedClosedUnitBall_radialValue_zero {m : ℕ} (x : PuncturedClosedUnitBall m) :
    puncturedClosedUnitBall_radialValue 0 x = x.1.1 := by
  -- At time zero the radial scalar is one.
  simp [puncturedClosedUnitBall_radialValue, puncturedClosedUnitBall_radialScalar]

/-- Helper for Exercise 72.1: the radial homotopy ends at inverse-norm normalization. -/
lemma puncturedClosedUnitBall_radialValue_one {m : ℕ} (x : PuncturedClosedUnitBall m) :
    puncturedClosedUnitBall_radialValue 1 x =
      ‖(x.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ • x.1.1 := by
  -- At time one the scalar is exactly the inverse norm.
  simp [puncturedClosedUnitBall_radialValue, puncturedClosedUnitBall_radialScalar, div_eq_mul_inv]

/-- Helper for Exercise 72.1: every boundary point is fixed throughout the radial homotopy. -/
lemma puncturedClosedUnitBall_radialValue_of_boundary (t : unitInterval)
    {m : ℕ} (x : PuncturedClosedUnitBall m)
    (hx : x.1 ∈ StandardSphere.boundary m) :
    puncturedClosedUnitBall_radialValue t x = x.1.1 := by
  -- Boundary membership makes the input norm one, so the radial scalar simplifies to one.
  have hx_norm := (StandardSphere.mem_boundary_iff_norm_eq m x.1).1 hx
  simp [puncturedClosedUnitBall_radialValue, puncturedClosedUnitBall_radialScalar, hx_norm]


/-- Helper for Exercise 72.1: the lifted boundary inside the punctured closed ball. -/
abbrev PuncturedClosedUnitBallBoundary (m : ℕ) : Set (PuncturedClosedUnitBall m) :=
  {x | x.1 ∈ StandardSphere.boundary m}

/-- Helper for Exercise 72.1: the radial formula depends continuously on time and input. -/
lemma continuous_puncturedClosedUnitBall_radialValue (m : ℕ) :
    Continuous (fun z : unitInterval × PuncturedClosedUnitBall m ↦
      puncturedClosedUnitBall_radialValue z.1 z.2) := by
  -- The only non-polynomial factor is inverse norm, continuous away from the removed center.
  have hnorm : Continuous (fun z : unitInterval × PuncturedClosedUnitBall m ↦
      ‖(z.2.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖) := by
    fun_prop
  have hnorm_ne : ∀ z : unitInterval × PuncturedClosedUnitBall m,
      ‖(z.2.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ ≠ 0 := fun z ↦
    ne_of_gt (puncturedClosedUnitBall_norm_pos m z.2)
  have hinv := hnorm.inv₀ hnorm_ne
  unfold puncturedClosedUnitBall_radialValue puncturedClosedUnitBall_radialScalar
  fun_prop

/-- Helper for Exercise 72.1: the radial formula defines a continuous self-homotopy of the
punctured closed ball. -/
noncomputable def puncturedClosedUnitBall_radialMap (m : ℕ) :
    C(unitInterval × PuncturedClosedUnitBall m, PuncturedClosedUnitBall m) :=
  ⟨fun z ↦ ⟨⟨puncturedClosedUnitBall_radialValue z.1 z.2,
      puncturedClosedUnitBall_radialValue_mem z.1 z.2⟩,
    fun hcenter ↦ puncturedClosedUnitBall_radialValue_ne_zero z.1 z.2
      (congrArg Subtype.val hcenter)⟩,
    (continuous_puncturedClosedUnitBall_radialValue m).subtype_mk
      (fun z ↦ puncturedClosedUnitBall_radialValue_mem z.1 z.2) |>.subtype_mk _⟩

/-- Helper for Exercise 72.1: the radial map starts at the identity. -/
lemma puncturedClosedUnitBall_radialMap_zero (m : ℕ) (x : PuncturedClosedUnitBall m) :
    puncturedClosedUnitBall_radialMap m (0, x) = x := by
  -- Equality of punctured-ball points follows from the ambient time-zero formula.
  apply Subtype.ext
  apply Subtype.ext
  exact puncturedClosedUnitBall_radialValue_zero x

/-- Helper for Exercise 72.1: the radial endpoint lies on the lifted boundary. -/
lemma puncturedClosedUnitBall_radialMap_one_mem (m : ℕ) (x : PuncturedClosedUnitBall m) :
    puncturedClosedUnitBall_radialMap m (1, x) ∈ PuncturedClosedUnitBallBoundary m := by
  -- The endpoint is inverse-norm normalization and therefore has norm one.
  apply (StandardSphere.mem_boundary_iff_norm_eq m _).2
  have hnorm : ‖puncturedClosedUnitBall_radialValue 1 x‖ = 1 := by
    rw [puncturedClosedUnitBall_radialValue_one, norm_smul, Real.norm_eq_abs]
    have hx_norm_pos := puncturedClosedUnitBall_norm_pos m x
    rw [abs_of_pos (inv_pos.mpr hx_norm_pos),
      inv_mul_cancel₀ (ne_of_gt hx_norm_pos)]
  exact hnorm

/-- Helper for Exercise 72.1: the radial map fixes the lifted boundary. -/
lemma puncturedClosedUnitBall_radialMap_of_boundary (m : ℕ) (t : unitInterval)
    (x : PuncturedClosedUnitBall m) (hx : x ∈ PuncturedClosedUnitBallBoundary m) :
    puncturedClosedUnitBall_radialMap m (t, x) = x := by
  -- Equality again reduces to the ambient boundary-fixation formula.
  apply Subtype.ext
  apply Subtype.ext
  exact puncturedClosedUnitBall_radialValue_of_boundary t x hx

/-- Helper for Exercise 72.1: inverse-norm normalization as a continuous boundary-valued map. -/
noncomputable def puncturedClosedUnitBall_normalize (m : ℕ) :
    C(PuncturedClosedUnitBall m, PuncturedClosedUnitBallBoundary m) :=
  ⟨fun x ↦ ⟨puncturedClosedUnitBall_radialMap m (1, x),
      puncturedClosedUnitBall_radialMap_one_mem m x⟩,
    (puncturedClosedUnitBall_radialMap m).continuous.comp (by fun_prop) |>.subtype_mk _⟩

/-- Helper for Exercise 72.1: normalization restricts to the identity on the lifted boundary. -/
lemma puncturedClosedUnitBall_normalize_leftInverse (m : ℕ) :
    Function.LeftInverse (puncturedClosedUnitBall_normalize m) Subtype.val := by
  -- Boundary fixation at time one is precisely the retraction identity.
  intro x
  apply Subtype.ext
  exact puncturedClosedUnitBall_radialMap_of_boundary m 1 x x.property

/-- Helper for Exercise 72.1: the standard radial homotopy is relative to the lifted boundary. -/
noncomputable def puncturedClosedUnitBall_radialHomotopyRel (m : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PuncturedClosedUnitBall m))
      (Set.Retraction.ofContinuousMap (puncturedClosedUnitBall_normalize m)
        (puncturedClosedUnitBall_normalize_leftInverse m)).toAmbient
      (PuncturedClosedUnitBallBoundary m) where
  toHomotopy :=
    { toContinuousMap := puncturedClosedUnitBall_radialMap m
      map_zero_left := puncturedClosedUnitBall_radialMap_zero m
      map_one_left := fun _ ↦ rfl }
  prop' := fun t x hx ↦ puncturedClosedUnitBall_radialMap_of_boundary m t x hx

/-- Helper for Exercise 72.1: the lifted boundary is a deformation retract of the punctured
closed unit ball. -/
lemma puncturedClosedUnitBall_boundary_isDeformationRetract (m : ℕ) :
    Set.IsDeformationRetract (PuncturedClosedUnitBallBoundary m) := by
  -- Package the normalization retraction and its relative radial homotopy.
  rw [Set.isDeformationRetract_iff]
  exact ⟨Set.Retraction.ofContinuousMap (puncturedClosedUnitBall_normalize m)
      (puncturedClosedUnitBall_normalize_leftInverse m),
    ⟨puncturedClosedUnitBall_radialHomotopyRel m⟩⟩

end
