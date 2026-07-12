import DifferentialForms_Cartan_1970.III.section12.«0038_Exercise_25».RationalDecay
import DifferentialForms_Cartan_1970.III.section12.«0038_Exercise_25».SquareBoundaryPiCotBounds

noncomputable section

open Filter Bornology
open scoped Topology unitInterval

/-- The square boundaries `γ_n` eventually avoid any fixed finite subset of `ℂ`; equivalently,
after discarding finitely many initial contours, every later `γ_n` is disjoint from that set. -/
theorem exercise25_squareBoundary_eventually_disjoint (s : Finset ℂ) :
    ∃ N : ℕ, ∀ n : ℕ,
      Disjoint (Set.range (exercise25SquareBoundary (n + N))) (s : Set ℂ) := by
  classical
  let B : ℝ := ∑ w ∈ s, ‖w‖
  let N : ℕ := Nat.ceil B
  refine ⟨N, fun n => Set.disjoint_left.mpr ?_⟩
  intro z hzboundary hzs
  have hzmem : z ∈ s := by
    simpa using hzs
  have hnorm_le_B : ‖z‖ ≤ B := by
    -- A single nonnegative summand is bounded by the whole finite sum of norms.
    simpa [B] using
      (Finset.single_le_sum (f := fun w : ℂ ↦ ‖w‖) (fun w _ ↦ norm_nonneg _) hzmem :
        ‖z‖ ≤ ∑ w ∈ s, ‖w‖)
  have hradius_le_norm :
      exercise25SquareRadius (n + N) ≤ ‖z‖ :=
    (exercise25_square_boundary_geometry (n + N) hzboundary).2.2.2
  have hB_le_N : B ≤ N := Nat.le_ceil B
  have hN_lt_radius : (N : ℝ) < exercise25SquareRadius (n + N) := by
    -- Every later square has radius strictly larger than the chosen ceiling bound.
    have hN_le_nat : N ≤ n + N := by
      exact Nat.le_add_left N n
    have hN_le_real : (N : ℝ) ≤ (n + N : ℕ) := by
      exact_mod_cast hN_le_nat
    dsimp [exercise25SquareRadius]
    linarith
  have hnorm_lt_radius : ‖z‖ < exercise25SquareRadius (n + N) := by
    exact lt_of_le_of_lt (hnorm_le_B.trans hB_le_N) hN_lt_radius
  exact (not_lt_of_ge hradius_le_norm) hnorm_lt_radius

/-- Helper for Exercise 25: the extension of an affine segment is `C¹` on the unit interval. -/
lemma exercise25_segment_contDiffOn (a b : ℂ) :
    ContDiffOn ℝ 1 (Path.segment a b).extend I := by
  -- The segment extension agrees with the affine line map on the unit interval.
  have hline : ContDiffOn ℝ 1 (ContinuousAffineMap.lineMap (R := ℝ) a b) I :=
    (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) a b)).contDiffOn
  refine hline.congr ?_
  intro t ht
  simpa using Path.eqOn_extend_segment a b ht

/-- Helper for Exercise 25: the square contour never meets a zero of `sin (π z)` because one of
its coordinates is a half-integer side value. -/
lemma exercise25_sin_pi_ne_zero_on_square_boundary (n : ℕ) {z : ℂ}
    (hz : z ∈ Set.range (exercise25SquareBoundary n)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  rcases exercise25_square_boundary_geometry n hz with ⟨_, _, hside, _⟩
  rcases hside with hzre | hzim
  · -- On a vertical side the denominator norm is the positive hyperbolic cosine.
    have hnorm :
        ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.cosh (Real.pi * z.im) :=
      exercise25_norm_sin_pi_of_re_abs_eq_radius n hzre
    intro hzero
    have hpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      rw [hnorm]
      positivity
    simpa [hzero] using hpos.ne'
  · -- On a horizontal side the denominator dominates the positive `sinh (π r_n)` term.
    have hzmul :
        ((Real.pi : ℂ) * z) = (Real.pi * z.re : ℂ) + (Real.pi * z.im) * Complex.I := by
      -- Normalize `π z` to the `x + t I` surface used by the strip estimates.
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, mul_comm]
    obtain ⟨_, hsinh_fixed⟩ := exercise25_hyperbolic_of_im_abs_eq_squareRadius n hzim
    have hsinh_pos : 0 < Real.sinh (Real.pi * exercise25SquareRadius n) := by
      simpa [exercise25SquareRadius, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
        sinh_pi_nat_add_half_pos n
    have hlower :
        Real.sinh (Real.pi * exercise25SquareRadius n) ≤
          ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      calc
        Real.sinh (Real.pi * exercise25SquareRadius n)
            = |Real.sinh (Real.pi * z.im)| := by rw [hsinh_fixed]
        _ ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
              rw [hzmul]
              simpa using
                exercise25_abs_sinh_le_norm_sin_add_mul_I (Real.pi * z.re) (Real.pi * z.im)
    intro hzero
    have hpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := lt_of_lt_of_le hsinh_pos hlower
    simpa [hzero] using hpos.ne'

/-- Helper for Exercise 25: after discarding finitely many initial square contours, the
denominator polynomial is nonzero on every later square boundary. -/
lemma exercise25_square_boundary_denominator_nonzero_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ NQ : ℕ, ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary (n + NQ)), Q.eval z ≠ 0 := by
  classical
  have hQ : Q ≠ 0 := exercise25_denominator_ne_zero_of_degree_gap_two P Q hdeg
  obtain ⟨NQ, hdisj⟩ := exercise25_squareBoundary_eventually_disjoint (Q.roots.toFinset)
  refine ⟨NQ, ?_⟩
  intro n z hz
  have hznot : z ∉ (Q.roots.toFinset : Set ℂ) :=
    Set.disjoint_left.mp (hdisj n) hz
  intro hzero
  have hzroot : z ∈ Q.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact hzero
  exact hznot hzroot

/-- Helper for Exercise 25: each affine side segment of the square contour `γ_n` lies in the
range of the full boundary path. -/
lemma exercise25_square_boundary_side_ranges_subset (n : ℕ) :
    let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
    let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    Set.range (Path.segment z₀ zw) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment zw w) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment w wz) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment wz z₀) ⊆ Set.range (exercise25SquareBoundary n) := by
  let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
  let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The bottom segment is the first side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inl hz
  · -- The right segment is the second side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inl hz
  · -- The top segment is the third side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inl hz
  · -- The left segment is the final side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inr hz

/-- Helper for Exercise 25: once the boundary avoids the zeros of `Q`, the kernel
`(P / Q) π cot (π z)` is a continuous scalar field on the contour image and therefore yields a
curve-integrable scalar `1`-form on each affine side of the square contour. -/
lemma exercise25_square_boundary_integrand_sides_curve_integrable_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
          exercise25SquareRadius (n + N) * Complex.I
        let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
          exercise25SquareRadius (n + N) * Complex.I
        let zw : ℂ := Complex.mk w.re z₀.im
        let wz : ℂ := Complex.mk z₀.re w.im
        CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment z₀ zw) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment zw w) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment w wz) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment wz z₀) := by
  obtain ⟨NQ, hQnz⟩ := exercise25_square_boundary_denominator_nonzero_eventually P Q hdeg
  refine ⟨NQ, ?_⟩
  intro n
  let D : Set ℂ := Set.range (exercise25SquareBoundary (n + NQ))
  let z₀ : ℂ := -(exercise25SquareRadius (n + NQ) : ℂ) -
    exercise25SquareRadius (n + NQ) * Complex.I
  let w : ℂ := (exercise25SquareRadius (n + NQ) : ℂ) +
    exercise25SquareRadius (n + NQ) * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  have hrat :
      ContinuousOn (fun z ↦ P.eval z / Q.eval z) D := by
    -- The rational factor is continuous on the boundary once `Q` has no zeros there.
    refine ContinuousOn.div P.continuous.continuousOn
      Q.continuous.continuousOn ?_
    intro z hz
    exact hQnz n z hz
  have hcot :
      ContinuousOn exercise25PiCot D := by
    have hcos :
        ContinuousOn (fun z : ℂ ↦ Complex.cos ((Real.pi : ℂ) * z)) D := by
      simpa using
        (Complex.continuous_cos.comp ((continuous_const : Continuous fun _ : ℂ ↦ (Real.pi : ℂ)).mul
          continuous_id)).continuousOn
    have hsin :
        ContinuousOn (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z)) D := by
      simpa using
        (Complex.continuous_sin.comp ((continuous_const : Continuous fun _ : ℂ ↦ (Real.pi : ℂ)).mul
          continuous_id)).continuousOn
    have hquot :
        ContinuousOn
          (fun z : ℂ ↦
            Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) D := by
      -- Rewrite `cot` as `cos / sin`, and use the boundary nonvanishing of `sin (π z)`.
      refine ContinuousOn.div hcos hsin ?_
      intro z hz
      exact exercise25_sin_pi_ne_zero_on_square_boundary (n + NQ) hz
    -- Multiplying by the constant factor `π` recovers `exercise25PiCot`.
    simpa [exercise25PiCot, Complex.cot, mul_assoc] using
      (continuousOn_const.mul hquot)
  have hcoeff :
      ContinuousOn (fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) D := by
    -- The full scalar coefficient is the product of the rational factor and the cotangent kernel.
    exact hrat.mul hcot
  have hform :
      ContinuousOn
        (fun z ↦ (((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z)) D := by
    -- Package the scalar coefficient as a continuous complex-linear `1`-form.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
  have hsubsets := exercise25_square_boundary_side_ranges_subset (n + NQ)
  dsimp [z₀, w, zw, wz] at hsubsets
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment z₀ zw) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
      (fun t ↦ hbottom_subset ⟨t, rfl⟩)
  have hright_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment zw w) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
      (fun t ↦ hright_subset ⟨t, rfl⟩)
  have htop_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment w wz) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
      (fun t ↦ htop_subset ⟨t, rfl⟩)
  have hleft_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment wz z₀) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
      (fun t ↦ hleft_subset ⟨t, rfl⟩)
  -- Record the four side integrability statements explicitly for the later ML estimate.
  simpa [z₀, w, zw, wz] using
    ⟨hbottom_int, hright_int, htop_int, hleft_int⟩

/-- Helper for Exercise 25: a `C / r_n^2` bound on the whole square boundary gives the source ML
estimate `2 C / r_n` on any single affine side of `γ_n`. -/
lemma exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
    {φ : ℂ → ℂ} (n : ℕ) {C : ℝ} {a b : ℂ}
    (hsubset : Set.range (Path.segment a b) ⊆ Set.range (exercise25SquareBoundary n))
    (hlength : ‖b - a‖ = 2 * exercise25SquareRadius n)
    (hbound : ∀ z ∈ Set.range (exercise25SquareBoundary n),
      ‖φ z‖ ≤ C / exercise25SquareRadius n ^ (2 : ℕ)) :
    ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖ ≤
      2 * C / exercise25SquareRadius n := by
  let r : ℝ := exercise25SquareRadius n
  have hr_pos : 0 < r := by
    -- Every square radius is `n + 1 / 2`, hence strictly positive.
    dsimp [r, exercise25SquareRadius]
    positivity
  have hsegment :
      ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖ ≤
        (C / r ^ (2 : ℕ)) * ‖b - a‖ := by
    -- Transport the boundary bound to the segment image and invoke the segment ML estimate.
    refine norm_curveIntegral_segment_le ?_
    intro z hz
    have hz' : z ∈ Set.range (Path.segment a b) := by
      simpa [Path.range_segment] using hz
    simpa [Complex.scalarOneForm] using hbound z (hsubset hz')
  calc
    ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖
        ≤ (C / r ^ (2 : ℕ)) * ‖b - a‖ := hsegment
    _ = (C / r ^ (2 : ℕ)) * (2 * exercise25SquareRadius n) := by rw [hlength]
    _ = (C / r ^ (2 : ℕ)) * (2 * r) := by simp [r]
    _ = 2 * C / r := by field_simp [r, hr_pos.ne']

/-- Helper for Exercise 25: once the boundary avoids the zeros of `Q`, the kernel
`(P / Q) π cot (π z)` is a continuous scalar field on the contour image and therefore yields a
curve-integrable scalar `1`-form there. -/
lemma exercise25_square_boundary_integrand_curve_integrable_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
          (exercise25SquareBoundary (n + N)) := by
  obtain ⟨N, hsides⟩ :=
    exercise25_square_boundary_integrand_sides_curve_integrable_eventually P Q hdeg
  refine ⟨N, ?_⟩
  intro n
  let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
    exercise25SquareRadius (n + N) * Complex.I
  let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
    exercise25SquareRadius (n + N) * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  rcases hsides n with ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
  -- Glue the four affine sides back into the square contour.
  simpa [exercise25SquareBoundary, z₀, w, zw, wz, axisParallelRectangleBoundaryPath] using
    (CurveIntegrable.trans hbottom_int
      (CurveIntegrable.trans hright_int
        (CurveIntegrable.trans htop_int hleft_int)))

/-- Helper for Exercise 25: a uniform `C / r_n^2` bound on the scalar coefficient along the square
boundary gives the source ML estimate `‖∮_{γ_n} φ(z) dz‖ ≤ 8 C / r_n`. -/
lemma exercise25_square_boundary_norm_curveIntegral_le
    {φ : ℂ → ℂ} (n : ℕ) {C : ℝ}
    (hsides :
      let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
      let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
      let zw : ℂ := Complex.mk w.re z₀.im
      let wz : ℂ := Complex.mk z₀.re w.im
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀))
    (hbound : ∀ z ∈ Set.range (exercise25SquareBoundary n),
      ‖φ z‖ ≤ C / exercise25SquareRadius n ^ (2 : ℕ)) :
    ‖∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ φ z) dz) z‖ ≤
      8 * C / exercise25SquareRadius n := by
  let r : ℝ := exercise25SquareRadius n
  let z₀ : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  have hz₀ : z₀ = -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I := by
    rfl
  have hw : w = (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I := by
    rfl
  have hzw : zw = (exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I := by
    -- The intermediate lower-right corner has the expected square coordinates.
    apply Complex.ext <;> simp [zw, z₀, w, r]
  have hwz : wz = -(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I := by
    -- The intermediate upper-left corner has the expected square coordinates.
    apply Complex.ext <;> simp [wz, z₀, w, r]
  have hr_nonneg : 0 ≤ exercise25SquareRadius n := by
    dsimp [exercise25SquareRadius]
    positivity
  have htwo_r_nonneg : 0 ≤ 2 * exercise25SquareRadius n := by
    positivity
  have hsides' :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) := by
    simpa [z₀, w, zw, wz, r] using hsides
  rcases hsides' with ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
  have hsubsets :
      Set.range (Path.segment z₀ zw) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment zw w) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment w wz) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment wz z₀) ⊆ Set.range (exercise25SquareBoundary n) := by
    simpa [z₀, w, zw, wz, r] using exercise25_square_boundary_side_ranges_subset n
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_length :
      ‖zw - z₀‖ =
        2 * exercise25SquareRadius n := by
    -- The bottom side is horizontal with Euclidean length `2 r_n`.
    calc
      ‖zw - z₀‖ = ‖(2 * exercise25SquareRadius n : ℂ)‖ := by
        rw [hzw, hz₀]
        ring_nf
      _ = 2 * exercise25SquareRadius n := by
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hright_length :
      ‖w - zw‖ =
        2 * exercise25SquareRadius n := by
    -- The right side is vertical with Euclidean length `2 r_n`.
    calc
      ‖w - zw‖ = ‖(2 * exercise25SquareRadius n : ℂ) * Complex.I‖ := by
        rw [hzw, hw]
        ring_nf
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
      _ = 2 * exercise25SquareRadius n := by
            rw [Complex.norm_I, mul_one]
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have htop_length :
      ‖wz - w‖ =
        2 * exercise25SquareRadius n := by
    -- The top side is again horizontal with Euclidean length `2 r_n`.
    calc
      ‖wz - w‖ = ‖(-2 * exercise25SquareRadius n : ℂ)‖ := by
        rw [hwz, hw]
        ring_nf
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ := by
            have hneg : (-2 * exercise25SquareRadius n : ℂ) =
                -((2 * exercise25SquareRadius n : ℂ)) := by ring
            rw [hneg, norm_neg]
      _ = 2 * exercise25SquareRadius n := by
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hleft_length :
      ‖z₀ - wz‖ =
        2 * exercise25SquareRadius n := by
    -- The left side is vertical with Euclidean length `2 r_n`.
    calc
      ‖z₀ - wz‖ = ‖(-2 * exercise25SquareRadius n : ℂ) * Complex.I‖ := by
        rw [hwz, hz₀]
        ring_nf
      _ = ‖(-2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by
            have hneg : (-2 * exercise25SquareRadius n : ℂ) =
                -((2 * exercise25SquareRadius n : ℂ)) := by ring
            rw [hneg, norm_neg]
      _ = 2 * exercise25SquareRadius n := by
            rw [Complex.norm_I, mul_one]
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hbottom_le :
      ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := z₀) (b := zw) hbottom_subset hbottom_length hbound
  have hright_le :
      ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := zw) (b := w) hright_subset hright_length hbound
  have htop_le :
      ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := w) (b := wz) htop_subset htop_length hbound
  have hleft_le :
      ‖∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := wz) (b := z₀) hleft_subset hleft_length hbound
  have hboundary_eq :
      exercise25SquareBoundary n =
        (Path.segment z₀ zw).trans
          ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
    rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
  -- Expand the square boundary into its four affine sides before summing the one-side estimates.
  rw [hboundary_eq]
  rw [curveIntegral_trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))]
  rw [curveIntegral_trans hright_int (CurveIntegrable.trans htop_int hleft_int)]
  rw [curveIntegral_trans htop_int hleft_int]
  calc
    ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z +
          (∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
            (∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
              ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z))‖
        ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
              (∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
                ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z)‖ := norm_add_le _ _
    _ ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            (‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ +
              ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
                ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            (‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ +
              (‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z‖ +
                ‖∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖)) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 2 * C / exercise25SquareRadius n +
            (2 * C / exercise25SquareRadius n +
              (2 * C / exercise25SquareRadius n + 2 * C / exercise25SquareRadius n)) := by
          gcongr
    _ = 8 * C / exercise25SquareRadius n := by ring
