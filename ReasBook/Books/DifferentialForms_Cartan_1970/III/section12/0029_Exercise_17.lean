import Mathlib

open scoped Topology EuclideanSpace

-- Semantic recall tool `lean_leansearch` was unavailable in this environment; I used local
-- Mathlib source inspection instead for complex conjugation, `Metric.sphere`, and
-- `Filter.cocompact`.

-- Declarations for this item will be appended below by the statement pipeline.

/-- The north pole of the unit sphere in `ℝ³`. -/
noncomputable def northPole : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single 2 (1 : ℝ), by simp⟩

/-- Exercise 17 (1): the `x`-coordinate of the inverse stereographic projection from the north
pole. -/
noncomputable def stereographic_x (z : ℂ) : ℝ :=
  2 * z.re / (1 + ‖z‖ ^ (2 : ℕ))

/-- Normal form for the `x`-coordinate of the inverse stereographic projection. -/
theorem stereographic_x_def (z : ℂ) :
    stereographic_x z = 2 * z.re / (1 + ‖z‖ ^ (2 : ℕ)) :=
  rfl

/-- Exercise 17 (2): the `y`-coordinate of the inverse stereographic projection from the north
pole. -/
noncomputable def stereographic_y (z : ℂ) : ℝ :=
  2 * z.im / (1 + ‖z‖ ^ (2 : ℕ))

/-- Normal form for the `y`-coordinate of the inverse stereographic projection. -/
theorem stereographic_y_def (z : ℂ) :
    stereographic_y z = 2 * z.im / (1 + ‖z‖ ^ (2 : ℕ)) :=
  rfl

/-- Exercise 17 (3): the `u`-coordinate of the inverse stereographic projection from the north
pole. -/
noncomputable def stereographic_u (z : ℂ) : ℝ :=
  (‖z‖ ^ (2 : ℕ) - 1) / (1 + ‖z‖ ^ (2 : ℕ))

/-- Normal form for the `u`-coordinate of the inverse stereographic projection. -/
theorem stereographic_u_def (z : ℂ) :
    stereographic_u z = (‖z‖ ^ (2 : ℕ) - 1) / (1 + ‖z‖ ^ (2 : ℕ)) :=
  rfl

/-- Helper for Exercise 17: the explicit ambient-point formula for the inverse stereographic
projection. -/
noncomputable def inverseStereographicPoint (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 (stereographic_x z) +
    EuclideanSpace.single 1 (stereographic_y z) +
      EuclideanSpace.single 2 (stereographic_u z)

/-- Helper for Exercise 17: the textbook inverse stereographic point lies on the unit sphere. -/
theorem inverseStereographicPoint_mem_sphere (z : ℂ) :
    inverseStereographicPoint z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- Route correction: the textbook coordinate formula is stable, while the north-pole chart
  -- basis chosen by `stereographic'` is opaque in Lean. We therefore verify the formula directly.
  rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one, Set.mem_setOf_eq, Fin.sum_univ_three]
  -- The stereographic normalization is the single rational identity `x² + y² + u² = 1`.
  have hnorm : ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
    calc
      ‖z‖ ^ (2 : ℕ) = Complex.normSq z := Complex.sq_norm z
      _ = z.re * z.re + z.im * z.im := by
        simpa using (RCLike.normSq_apply z)
      _ = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by ring
  have hden : (1 + (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ))) ≠ 0 := by positivity
  simp [inverseStereographicPoint, stereographic_x, stereographic_y, stereographic_u, hnorm]
  field_simp [hden]
  ring_nf

/-- The inverse stereographic projection from `ℂ` to the unit sphere with the textbook
normalization. -/
noncomputable def inverseStereographic (z : ℂ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨inverseStereographicPoint z, inverseStereographicPoint_mem_sphere z⟩

/-- Helper for Exercise 17: the inverse stereographic projection has the textbook coordinate
formula in `ℝ³`. -/
theorem inverseStereographic_coordinates (z : ℂ) :
    (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) =
      ![stereographic_x z, stereographic_y z, stereographic_u z] := by
  -- Unpack the subtype value and read off the explicit ambient vector.
  ext i
  fin_cases i
  · simp [inverseStereographic, inverseStereographicPoint]
  · simp [inverseStereographic, inverseStereographicPoint]
  · simp [inverseStereographic, inverseStereographicPoint]

/-- The first coordinate of `inverseStereographic` is the textbook formula `stereographic_x`. -/
theorem inverseStereographic_apply_zero (z : ℂ) :
    (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) 0 = stereographic_x z := by
  -- Read off the first coordinate from the packaged coordinate formula.
  rw [inverseStereographic_coordinates]
  simp

/-- The second coordinate of `inverseStereographic` is the textbook formula `stereographic_y`. -/
theorem inverseStereographic_apply_one (z : ℂ) :
    (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) 1 = stereographic_y z := by
  -- Read off the second coordinate from the packaged coordinate formula.
  rw [inverseStereographic_coordinates]
  simp

/-- The third coordinate of `inverseStereographic` is the textbook formula `stereographic_u`. -/
theorem inverseStereographic_apply_two (z : ℂ) :
    (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) 2 = stereographic_u z := by
  -- Read off the third coordinate from the packaged coordinate formula.
  rw [inverseStereographic_coordinates]
  simp

/-- The stereographic image of the intersection of the unit sphere with the plane
`A * x + B * y + C * u = D`, expressed as a subset of `ℂ`. -/
noncomputable def stereographic_plane_section (A B C D : ℝ) : Set ℂ :=
  {z : ℂ |
    let p : EuclideanSpace ℝ (Fin 3) := inverseStereographic z
    A * p 0 + B * p 1 + C * p 2 = D}

/-- Helper for Exercise 17: membership in a plane section becomes one quadratic equation in the
stereographic coordinate `z`. -/
theorem mem_stereographic_plane_section_iff
    {A B C D : ℝ} {z : ℂ} :
    z ∈ stereographic_plane_section A B C D ↔
      (C - D) * ‖z‖ ^ (2 : ℕ) + 2 * A * z.re + 2 * B * z.im = C + D := by
  have hden : (1 + ‖z‖ ^ (2 : ℕ)) ≠ 0 := by positivity
  -- Expand the plane equation in the textbook coordinates and clear the common denominator.
  have hcoords :
      z ∈ stereographic_plane_section A B C D ↔
        A * stereographic_x z + B * stereographic_y z + C * stereographic_u z = D := by
    simp [stereographic_plane_section, inverseStereographic_apply_zero,
      inverseStereographic_apply_one, inverseStereographic_apply_two]
  rw [hcoords]
  constructor
  · intro hz
    simp [stereographic_x, stereographic_y, stereographic_u] at hz
    field_simp [hden] at hz
    linarith
  · intro hz
    simp [stereographic_x, stereographic_y, stereographic_u]
    field_simp [hden]
    linarith

/-- Helper for Exercise 17: completing the square rewrites the normalized plane equation as a
circle equation in `ℂ`. -/
theorem stereographic_plane_section_circle_equation_iff
    {A B C D : ℝ} (hnorth : C ≠ D) {z : ℂ} :
    ((C - D) * ‖z‖ ^ (2 : ℕ) + 2 * A * z.re + 2 * B * z.im = C + D) ↔
      Complex.normSq
        (z - (((-(A / (C - D)) : ℂ) + (-(B / (C - D)) : ℂ) * Complex.I)))
        = (A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ)) / (C - D) ^ (2 : ℕ) := by
  have hδ : (C - D) ≠ 0 := sub_ne_zero.mpr hnorth
  have hnorm : ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
    calc
      ‖z‖ ^ (2 : ℕ) = Complex.normSq z := Complex.sq_norm z
      _ = z.re * z.re + z.im * z.im := by
        simpa using (RCLike.normSq_apply z)
      _ = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by ring
  have hzsub :
      z - (((-(A / (C - D)) : ℂ) + (-(B / (C - D)) : ℂ) * Complex.I)) =
        ((z.re + A / (C - D) : ℝ) : ℂ) + (z.im + B / (C - D)) * Complex.I := by
    -- Rewrite the shifted center in real and imaginary coordinates.
    apply Complex.ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hcompleted :
      Complex.normSq
        (z - (((-(A / (C - D)) : ℂ) + (-(B / (C - D)) : ℂ) * Complex.I))) =
        (z.re + A / (C - D)) ^ (2 : ℕ) + (z.im + B / (C - D)) ^ (2 : ℕ) := by
    rw [hzsub]
    simpa using Complex.normSq_add_mul_I (z.re + A / (C - D)) (z.im + B / (C - D))
  have hδ2 : (C - D) ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 hδ
  rw [hcompleted]
  constructor
  · intro hz
    -- Clear the square denominator only after moving the right-hand side into `eq_div_iff`.
    rw [hnorm] at hz
    apply (eq_div_iff hδ2).2
    calc
      ((z.re + A / (C - D)) ^ (2 : ℕ) + (z.im + B / (C - D)) ^ (2 : ℕ)) *
          (C - D) ^ (2 : ℕ) =
          (C - D) * ((C - D) * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) + 2 * A * z.re + 2 * B * z.im) +
            (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by
            field_simp [hδ]
            ring
      _ = (C - D) * (C + D) + (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by rw [hz]
      _ = A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ) := by ring
  · intro hz
    -- Reverse the same denominator-clearing argument.
    rw [hnorm]
    have hz' :
        ((z.re + A / (C - D)) ^ (2 : ℕ) + (z.im + B / (C - D)) ^ (2 : ℕ)) *
          (C - D) ^ (2 : ℕ) =
          A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ) := by
      exact (eq_div_iff hδ2).1 hz
    have hz'' :
        (C - D) * ((C - D) * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) + 2 * A * z.re + 2 * B * z.im) +
            (A ^ (2 : ℕ) + B ^ (2 : ℕ)) =
          A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ) := by
      calc
        (C - D) * ((C - D) * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) + 2 * A * z.re + 2 * B * z.im) +
            (A ^ (2 : ℕ) + B ^ (2 : ℕ)) =
            ((z.re + A / (C - D)) ^ (2 : ℕ) + (z.im + B / (C - D)) ^ (2 : ℕ)) *
              (C - D) ^ (2 : ℕ) := by
              field_simp [hδ]
              ring
        _ = A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ) := hz'
    have hz''' :
        (C - D) * ((C - D) * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) + 2 * A * z.re + 2 * B * z.im) =
          (C - D) * (C + D) := by
      nlinarith [hz'']
    exact (mul_left_cancel₀ hδ) <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hz'''

/-- Exercise 17 (4): if a circle on the unit sphere is cut out by a plane
`A * x + B * y + C * u = D` that does not pass through the north pole, then its stereographic
image is a Euclidean circle. -/
theorem stereographic_plane_section_eq_circle
    {A B C D : ℝ}
    (hcircle : D ^ (2 : ℕ) < A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ))
    (hnorth : C ≠ D) :
    stereographic_plane_section A B C D =
      Metric.sphere
        (((-(A / (C - D)) : ℂ) + (-(B / (C - D)) : ℂ) * Complex.I))
        (Real.sqrt
          ((A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ)) /
            (C - D) ^ (2 : ℕ))) := by
  let c : ℂ := ((-(A / (C - D)) : ℂ) + (-(B / (C - D)) : ℂ) * Complex.I)
  let R2 : ℝ := (A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ)) / (C - D) ^ (2 : ℕ)
  have hnum_pos : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ) := by
    nlinarith [hcircle]
  have hden_pos : 0 < (C - D) ^ (2 : ℕ) := by
    have : 0 < (C - D) ^ (2 : ℕ) := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hnorth)]
    exact this
  have hR2_nonneg : 0 ≤ R2 := by
    exact le_of_lt (div_pos hnum_pos hden_pos)
  ext z
  constructor
  · intro hz
    rw [mem_sphere_iff_norm]
    -- Rewrite the plane equation as a completed square before taking square roots.
    have hnormsq : Complex.normSq (z - c) = R2 := by
      exact (stereographic_plane_section_circle_equation_iff (A := A) (B := B) (C := C)
        (D := D) hnorth).mp (mem_stereographic_plane_section_iff.mp hz)
    have hsq : ‖z - c‖ ^ (2 : ℕ) = R2 := by
      simpa [c, R2, Complex.normSq_eq_norm_sq] using hnormsq
    calc
      ‖z - c‖ = Real.sqrt (‖z - c‖ ^ (2 : ℕ)) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt R2 := by rw [hsq]
      _ = Real.sqrt
            ((A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) - D ^ (2 : ℕ)) /
              (C - D) ^ (2 : ℕ)) := by rfl
  · intro hz
    rw [mem_sphere_iff_norm] at hz
    -- Square the Euclidean circle equation and return to the plane-section equation.
    have hsq : ‖z - c‖ ^ (2 : ℕ) = R2 := by
      calc
        ‖z - c‖ ^ (2 : ℕ) = (Real.sqrt R2) ^ (2 : ℕ) := by rw [hz]
        _ = R2 := by rw [Real.sq_sqrt hR2_nonneg]
    have hnormsq : Complex.normSq (z - c) = R2 := by
      simpa [c, R2, Complex.normSq_eq_norm_sq] using hsq
    exact mem_stereographic_plane_section_iff.mpr <|
      (stereographic_plane_section_circle_equation_iff (A := A) (B := B) (C := C)
        (D := D) hnorth).mpr hnormsq

/-- Exercise 17 (5): if the plane `A * x + B * y + C * u = C` passes through the north pole and
cuts out a genuine circle on the unit sphere, then its stereographic image is a line. -/
theorem stereographic_plane_section_eq_line
    {A B C : ℝ}
    (hline : A ≠ 0 ∨ B ≠ 0) :
    stereographic_plane_section A B C C = {z : ℂ | A * z.re + B * z.im = C} := by
  let _ := hline
  -- The north-pole condition cancels the quadratic term, leaving a linear equation in `z`.
  ext z
  constructor
  · intro hz
    have hz' := mem_stereographic_plane_section_iff.mp hz
    ring_nf at hz'
    have hz'' : A * z.re + B * z.im = C := by
      nlinarith [hz']
    simpa [Set.mem_setOf_eq] using hz''
  · intro hz
    have hz0 : A * z.re + B * z.im = C := by
      simpa [Set.mem_setOf_eq] using hz
    have hz' : (C - C) * ‖z‖ ^ (2 : ℕ) + 2 * A * z.re + 2 * B * z.im = C + C := by
      nlinarith [hz0]
    exact mem_stereographic_plane_section_iff.mpr hz'

/-- Exercise 17 (6): two inverse stereographic images are antipodal exactly when
`z₁ * conj z₂ = -1`. -/
theorem inverseStereographic_antipodal_iff
    {z₁ z₂ : ℂ} :
    inverseStereographic z₁ = -inverseStereographic z₂ ↔ z₁ * star z₂ = -1 := by
  let n₁ : ℝ := ‖z₁‖ ^ (2 : ℕ)
  let n₂ : ℝ := ‖z₂‖ ^ (2 : ℕ)
  have hden1 : 1 + n₁ ≠ 0 := by
    positivity
  have hden2 : 1 + n₂ ≠ 0 := by
    positivity
  have hnorm1 : n₁ = z₁.re ^ (2 : ℕ) + z₁.im ^ (2 : ℕ) := by
    calc
      n₁ = Complex.normSq z₁ := by simp [n₁, Complex.normSq_eq_norm_sq]
      _ = z₁.re * z₁.re + z₁.im * z₁.im := by
        simpa using (RCLike.normSq_apply z₁)
      _ = z₁.re ^ (2 : ℕ) + z₁.im ^ (2 : ℕ) := by ring
  have hnorm2 : n₂ = z₂.re ^ (2 : ℕ) + z₂.im ^ (2 : ℕ) := by
    calc
      n₂ = Complex.normSq z₂ := by simp [n₂, Complex.normSq_eq_norm_sq]
      _ = z₂.re * z₂.re + z₂.im * z₂.im := by
        simpa using (RCLike.normSq_apply z₂)
      _ = z₂.re ^ (2 : ℕ) + z₂.im ^ (2 : ℕ) := by ring
  constructor
  · intro h
    have hvec :
        (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3)) =
          -(inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)) := by
      exact congrArg (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        (p : EuclideanSpace ℝ (Fin 3))) h
    have hxcoord : 2 * z₁.re / (1 + n₁) = -(2 * z₂.re / (1 + n₂)) := by
      have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 0) hvec
      simpa [n₁, n₂, stereographic_x, inverseStereographic_apply_zero] using h0
    have hycoord : 2 * z₁.im / (1 + n₁) = -(2 * z₂.im / (1 + n₂)) := by
      have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) hvec
      simpa [n₁, n₂, stereographic_y, inverseStereographic_apply_one] using h1
    have hucoord : (n₁ - 1) / (1 + n₁) = -((n₂ - 1) / (1 + n₂)) := by
      have h2 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 2) hvec
      simpa [n₁, n₂, stereographic_u, inverseStereographic_apply_two] using h2
    have hnormprod : n₁ * n₂ = 1 := by
      field_simp [hden1, hden2] at hucoord
      nlinarith [hucoord]
    have hdenrel1 : 1 + n₁ = n₁ * (1 + n₂) := by
      nlinarith [hnormprod]
    have hzre : z₁.re = -n₁ * z₂.re := by
      field_simp [hden1, hden2] at hxcoord
      rw [hdenrel1] at hxcoord
      nlinarith [hxcoord]
    have hzim : z₁.im = -n₁ * z₂.im := by
      field_simp [hden1, hden2] at hycoord
      rw [hdenrel1] at hycoord
      nlinarith [hycoord]
    -- Reassemble the complex product from its real and imaginary parts.
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hzre, hzim]
    · nlinarith [hnorm2, hnormprod]
    · ring
  · intro h
    have hnormprod : n₁ * n₂ = 1 := by
      have hsq := congrArg Complex.normSq h
      have hsq' : Complex.normSq z₁ * Complex.normSq z₂ = 1 := by
        simpa [Complex.star_def, Complex.normSq_mul, Complex.normSq_conj] using hsq
      simpa [n₁, n₂, Complex.normSq_eq_norm_sq] using hsq'
    have hzmul : z₁ * ((n₂ : ℂ)) = -z₂ := by
      -- Multiply `z₁ * conj z₂ = -1` on the right by `z₂`.
      calc
        z₁ * ((n₂ : ℂ)) = z₁ * (star z₂ * z₂) := by
          rw [Complex.star_def, Complex.conj_mul']
          simp [n₂]
        _ = (z₁ * star z₂) * z₂ := by rw [mul_assoc]
        _ = -z₂ := by rw [h, neg_one_mul]
    have hzre : n₂ * z₁.re = -z₂.re := by
      have hre := congrArg Complex.re hzmul
      simpa [Complex.mul_re, mul_comm, mul_left_comm, mul_assoc] using hre
    have hzim : n₂ * z₁.im = -z₂.im := by
      have him := congrArg Complex.im hzmul
      simpa [Complex.mul_im, mul_comm, mul_left_comm, mul_assoc] using him
    have hdenrel2 : 1 + n₂ = n₂ * (1 + n₁) := by
      nlinarith [hnormprod]
    have hxcoord : 2 * z₁.re / (1 + n₁) = -(2 * z₂.re / (1 + n₂)) := by
      field_simp [hden1, hden2]
      rw [hdenrel2]
      nlinarith [hzre]
    have hycoord : 2 * z₁.im / (1 + n₁) = -(2 * z₂.im / (1 + n₂)) := by
      field_simp [hden1, hden2]
      rw [hdenrel2]
      nlinarith [hzim]
    have hucoord : (n₁ - 1) / (1 + n₁) = -((n₂ - 1) / (1 + n₂)) := by
      field_simp [hden1, hden2]
      nlinarith [hnormprod]
    -- Compare the three textbook coordinates componentwise.
    apply Subtype.ext
    ext i
    fin_cases i
    · simpa [n₁, n₂, stereographic_x, inverseStereographic_apply_zero] using hxcoord
    · simpa [n₁, n₂, stereographic_y, inverseStereographic_apply_one] using hycoord
    · simpa [n₁, n₂, stereographic_u, inverseStereographic_apply_two] using hucoord

/-- Helper for Exercise 17: the squared Euclidean distance between two inverse stereographic
images has the standard rational form. -/
theorem dist_inverseStereographic_sq
    {z₁ z₂ : ℂ} :
    dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
      (inverseStereographic z₂) ^ (2 : ℕ) =
      4 * ‖z₁ - z₂‖ ^ (2 : ℕ) /
        ((1 + ‖z₁‖ ^ (2 : ℕ)) * (1 + ‖z₂‖ ^ (2 : ℕ))) := by
  let n₁ : ℝ := ‖z₁‖ ^ (2 : ℕ)
  let n₂ : ℝ := ‖z₂‖ ^ (2 : ℕ)
  have hden1 : 1 + n₁ ≠ 0 := by
    positivity
  have hden2 : 1 + n₂ ≠ 0 := by
    positivity
  have hnorm1 : n₁ = z₁.re ^ (2 : ℕ) + z₁.im ^ (2 : ℕ) := by
    calc
      n₁ = Complex.normSq z₁ := by simp [n₁, Complex.normSq_eq_norm_sq]
      _ = z₁.re * z₁.re + z₁.im * z₁.im := by
        simpa using (RCLike.normSq_apply z₁)
      _ = z₁.re ^ (2 : ℕ) + z₁.im ^ (2 : ℕ) := by ring
  have hnorm2 : n₂ = z₂.re ^ (2 : ℕ) + z₂.im ^ (2 : ℕ) := by
    calc
      n₂ = Complex.normSq z₂ := by simp [n₂, Complex.normSq_eq_norm_sq]
      _ = z₂.re * z₂.re + z₂.im * z₂.im := by
        simpa using (RCLike.normSq_apply z₂)
      _ = z₂.re ^ (2 : ℕ) + z₂.im ^ (2 : ℕ) := by ring
  have hnormsub : ‖z₁ - z₂‖ ^ (2 : ℕ) = (z₁.re - z₂.re) ^ (2 : ℕ) + (z₁.im - z₂.im) ^ (2 : ℕ) := by
    calc
      ‖z₁ - z₂‖ ^ (2 : ℕ) = Complex.normSq (z₁ - z₂) := Complex.sq_norm (z₁ - z₂)
      _ = (z₁.re - z₂.re) * (z₁.re - z₂.re) + (z₁.im - z₂.im) * (z₁.im - z₂.im) := by
        simpa using (RCLike.normSq_apply (z₁ - z₂))
      _ = (z₁.re - z₂.re) ^ (2 : ℕ) + (z₁.im - z₂.im) ^ (2 : ℕ) := by ring
  -- Expand the three coordinate differences and clear denominators once.
  rw [dist_eq_norm]
  have hnormeq :
      ‖(inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3)) -
          (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3))‖ ^ (2 : ℕ) =
        ∑ i : Fin 3,
          (((inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3)) -
            (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3))) i) ^ (2 : ℕ) :=
    EuclideanSpace.real_norm_sq_eq _
  rw [hnormeq, Fin.sum_univ_three]
  simp [stereographic_x, stereographic_y, stereographic_u,
    inverseStereographic_apply_zero, inverseStereographic_apply_one,
    inverseStereographic_apply_two]
  field_simp [hden1, hden2]
  have hnorm1' : ‖z₁‖ ^ (2 : ℕ) = z₁.re ^ (2 : ℕ) + z₁.im ^ (2 : ℕ) := by
    simpa [n₁] using hnorm1
  have hnorm2' : ‖z₂‖ ^ (2 : ℕ) = z₂.re ^ (2 : ℕ) + z₂.im ^ (2 : ℕ) := by
    simpa [n₂] using hnorm2
  rw [hnorm1', hnorm2', hnormsub]
  ring_nf

/-- Exercise 17 (7): the Euclidean distance between two inverse stereographic images is
`2 |z₁ - z₂| / sqrt ((1 + |z₁|²) (1 + |z₂|²))`. -/
theorem dist_inverseStereographic_eq
    {z₁ z₂ : ℂ} :
    dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
      (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)) =
      2 * ‖z₁ - z₂‖ /
        Real.sqrt ((1 + ‖z₁‖ ^ (2 : ℕ)) * (1 + ‖z₂‖ ^ (2 : ℕ))) := by
  let R : ℝ := (1 + ‖z₁‖ ^ (2 : ℕ)) * (1 + ‖z₂‖ ^ (2 : ℕ))
  have hR_pos : 0 < R := by
    positivity
  have hsq :
      dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
        (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)) ^ (2 : ℕ) =
      (2 * ‖z₁ - z₂‖ / Real.sqrt R) ^ (2 : ℕ) := by
    calc
      dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
          (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)) ^ (2 : ℕ) =
          4 * ‖z₁ - z₂‖ ^ (2 : ℕ) / R := by
            simpa [R] using (dist_inverseStereographic_sq (z₁ := z₁) (z₂ := z₂))
      _ = (2 * ‖z₁ - z₂‖ / Real.sqrt R) ^ (2 : ℕ) := by
        field_simp [R, hR_pos.ne', Real.sqrt_ne_zero'.mpr hR_pos]
        nlinarith [Real.sq_sqrt hR_pos.le]
  -- Identify both nonnegative quantities with the square root of the same square.
  calc
    dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
        (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)) =
        Real.sqrt
          (dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
            (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)) ^ (2 : ℕ)) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]
    _ = Real.sqrt ((2 * ‖z₁ - z₂‖ / Real.sqrt R) ^ (2 : ℕ)) := by rw [hsq]
    _ = 2 * ‖z₁ - z₂‖ / Real.sqrt R := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
          positivity
    _ = 2 * ‖z₁ - z₂‖ /
          Real.sqrt ((1 + ‖z₁‖ ^ (2 : ℕ)) * (1 + ‖z₂‖ ^ (2 : ℕ))) := by
          rfl

/-- Helper for Exercise 17: the distance from an inverse stereographic image to the north pole
has the expected one-variable formula. -/
theorem dist_inverseStereographic_northPole_eq
    (z : ℂ) :
    dist (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) northPole =
      2 / Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)) := by
  let n : ℝ := ‖z‖ ^ (2 : ℕ)
  have hden : 1 + n ≠ 0 := by
    positivity
  have hden_pos : 0 < 1 + n := by
    positivity
  have hnorm : n = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
    calc
      n = Complex.normSq z := by simp [n, Complex.normSq_eq_norm_sq]
      _ = z.re * z.re + z.im * z.im := by
        simpa using (RCLike.normSq_apply z)
      _ = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by ring
  have hsq :
      dist (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) northPole ^ (2 : ℕ) =
        (2 / Real.sqrt (1 + n)) ^ (2 : ℕ) := by
    -- Compute the squared distance to the fixed point `(0,0,1)`.
    rw [dist_eq_norm]
    have hnormeq :
        ‖(inverseStereographic z : EuclideanSpace ℝ (Fin 3)) - northPole‖ ^ (2 : ℕ) =
          ∑ i : Fin 3,
            (((inverseStereographic z : EuclideanSpace ℝ (Fin 3)) - northPole) i) ^ (2 : ℕ) :=
      EuclideanSpace.real_norm_sq_eq _
    rw [hnormeq, Fin.sum_univ_three]
    simp [northPole, n, stereographic_x, stereographic_y, stereographic_u,
      inverseStereographic_apply_zero, inverseStereographic_apply_one,
      inverseStereographic_apply_two]
    field_simp [hden]
    nlinarith [hnorm, Real.sq_sqrt hden_pos.le]
  calc
    dist (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) northPole =
        Real.sqrt
          (dist (inverseStereographic z : EuclideanSpace ℝ (Fin 3)) northPole ^ (2 : ℕ)) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]
    _ = Real.sqrt ((2 / Real.sqrt (1 + n)) ^ (2 : ℕ)) := by rw [hsq]
    _ = 2 / Real.sqrt (1 + n) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
          positivity
    _ = 2 / Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)) := by rfl

/-- Helper for Exercise 17: the inverse stereographic image tends to the north pole along the
cocompact filter on `ℂ`. -/
theorem inverseStereographic_tendsto_northPole :
    Filter.Tendsto (fun z : ℂ ↦ (inverseStereographic z : EuclideanSpace ℝ (Fin 3)))
      (Filter.cocompact ℂ) (𝓝 northPole) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hnormsq :
      Filter.Tendsto (fun z : ℂ ↦ 1 + ‖z‖ ^ (2 : ℕ)) (Filter.cocompact ℂ) Filter.atTop := by
    simpa [Complex.normSq_eq_norm_sq] using
      (tendsto_const_nhds.add_atTop Complex.tendsto_normSq_cocompact_atTop)
  have hsqrt :
      Filter.Tendsto (fun z : ℂ ↦ Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)))
        (Filter.cocompact ℂ) Filter.atTop := by
    exact Real.tendsto_sqrt_atTop.comp hnormsq
  have hinv :
      Filter.Tendsto (fun z : ℂ ↦ (Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)))⁻¹)
        (Filter.cocompact ℂ) (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hsqrt
  -- After rewriting the distance to `northPole`, the limit is the inverse-square-root limit.
  simpa [dist_inverseStereographic_northPole_eq, div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv)

/-- Exercise 17 (8): as `z₂` tends to the point at infinity in `ℂ`, the distance formula tends to
`2 / sqrt (1 + |z₁|²)`, corresponding to the distance from `φ⁻¹(z₁)` to the north pole. -/
theorem dist_inverseStereographic_tendsto_at_infinity
    (z₁ : ℂ) :
    Filter.Tendsto
      (fun z₂ : ℂ ↦
        dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
          (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)))
      (Filter.cocompact ℂ)
      (𝓝 (2 / Real.sqrt (1 + ‖z₁‖ ^ (2 : ℕ)))) := by
  have hdist :
      Filter.Tendsto
        (fun z₂ : ℂ ↦
          dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3))
            (inverseStereographic z₂ : EuclideanSpace ℝ (Fin 3)))
        (Filter.cocompact ℂ)
        (𝓝 (dist (inverseStereographic z₁ : EuclideanSpace ℝ (Fin 3)) northPole)) := by
    -- Compose convergence to `northPole` with continuity of the distance function.
    exact (continuous_const.dist continuous_id).continuousAt.tendsto.comp
      inverseStereographic_tendsto_northPole
  simpa [dist_inverseStereographic_northPole_eq] using hdist
