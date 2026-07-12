import DifferentialForms_Cartan_1970.III.section12.«0034_Exercise_21».NegativeAxisKeyholeCornerFibers

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

/-- Helper for Exercise 21: a circular arc obtained by mapping an affine angle segment through
`circleMap` is differentiable as a path. -/
lemma exercise21_circle_segment_isDifferentiable (ρ α β : ℝ) :
    ((Path.segment α β).map (continuous_circleMap 0 ρ)).IsDifferentiable := by
  -- The angular parameter is affine on `[0, 1]`, so composing it with `circleMap` stays `C¹`.
  rw [Path.IsDifferentiable]
  have hcontDiff :
      ContDiffOn ℝ 1
        (fun t : ℝ ↦ circleMap 0 ρ ((ContinuousAffineMap.lineMap (R := ℝ) α β) t))
        (Set.Icc (0 : ℝ) 1) := by
    simpa [Function.comp] using
      ((contDiff_circleMap 0 ρ).comp
        (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) α β))).contDiffOn
  refine hcontDiff.congr ?_
  intro t ht
  rw [Path.extend_apply _ ht]
  simp [ContinuousAffineMap.coe_lineMap_eq, Path.map_coe, Path.segment_apply,
    AffineMap.lineMap_apply_module]

/-- Helper for Exercise 21: the keyhole contour `δ(r, ε)` is piecewise differentiable because it
is built from two straight segments and two smooth circular arcs. -/
lemma exercise21Delta_isPiecewiseDifferentiable (r ε : ℝ) :
    (exercise21Delta r ε).IsPiecewiseDifferentiable := by
  let θ : ℝ := Real.arctan (ε / r)
  have hupper :
      (Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable _ _
  have hinner :
      ((Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)).IsDifferentiable :=
    exercise21_circle_segment_isDifferentiable ε (Real.pi - θ) (-Real.pi + θ)
  have hlower :
      (Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))).IsDifferentiable :=
    Path.segment_isDifferentiable _ _
  have houter :
      ((Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)).IsDifferentiable :=
    exercise21_circle_segment_isDifferentiable r (-Real.pi + θ) (Real.pi - θ)
  -- Append the four smooth pieces in the source order used to define the keyhole contour.
  have hupper_inner := hupper.trans_of_isDifferentiable hinner
  have hupper_inner_lower := hupper_inner.trans_of_isDifferentiable hlower
  have hall := hupper_inner_lower.trans_of_isDifferentiable houter
  simpa [exercise21Delta, θ] using hall

/-- Helper for Exercise 21: a positive-radius point `circleMap 0 ρ φ` belongs to the principal
slit plane whenever its angle stays strictly between `-π` and `π`. -/
lemma exercise21_mem_slitPlane_circleMap_of_angle {ρ φ : ℝ}
    (hρ : 0 < ρ) (hφ_lower : -Real.pi < φ) (hφ_upper : φ < Real.pi) :
    circleMap 0 ρ φ ∈ Complex.slitPlane := by
  -- If the imaginary part vanishes, the angle must be `0`; otherwise `im ≠ 0` puts the point
  -- in the slit plane immediately.
  by_cases hsin : Real.sin φ = 0
  · have hφ_zero : φ = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hφ_lower hφ_upper).mp hsin
    rw [Complex.mem_slitPlane_iff]
    left
    rw [circleMap_zero_re, hφ_zero, Real.cos_zero]
    simpa using hρ
  · rw [Complex.mem_slitPlane_iff]
    right
    rw [circleMap_zero_im]
    exact mul_ne_zero hρ.ne' hsin

/-- Helper for Exercise 21: equality on one open branch of the keyhole contour forces equality of
the corresponding parameters. This isolates the source-faithful injectivity package needed for the
later simple-loop proof from the breakpoint bookkeeping. -/
lemma exercise21Delta_same_branch_injective
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {s t : I}
    (hbranch :
      (s.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∧ t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) ∨
        (s.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∧ t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) ∨
        (s.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧ t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) ∨
        (s.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) ∧ t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)))
    (hst : exercise21Delta r ε s = exercise21Delta r ε t) :
    s = t := by
  have hr : 0 < r := lt_trans hε hεr
  have hθ := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  rcases hbranch with hupper | hinner | hlower | houter
  · rcases hupper with ⟨hs, ht⟩
    -- On the upper lip, the keyhole is a nonconstant affine interpolation in the radius.
    have hsPath :
        exercise21Delta r ε s =
          AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (s : ℝ)) := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        exercise21Delta r ε t =
          AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (t : ℝ)) := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (s : ℝ)) =
          AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (t : ℝ)) := by
      calc
        AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (s : ℝ)) =
            exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := htPath
    have hEndsNe :
        circleMap 0 r (Real.pi - Real.arctan (ε / r)) ≠
          circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    have hst' : 8 * (s : ℝ) = 8 * (t : ℝ) := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 r (Real.pi - Real.arctan (ε / r)))
        (p₁ := circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
        (c₁ := 8 * (s : ℝ)) (c₂ := 8 * (t : ℝ))).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Recover the subtype equality from the affine radial parameter.
    exact Subtype.ext (by linarith)
  · rcases hinner with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (8 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (8 * (t : ℝ) - 1)
    -- On the inner circle, injectivity comes from the angular window of length `< 2π`.
    have hsPath : exercise21Delta r ε s = circleMap 0 ε α := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hs)
    have htPath : exercise21Delta r ε t = circleMap 0 ε β := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 ε α = circleMap 0 ε β := by
      calc
        circleMap 0 ε α = exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ = circleMap 0 ε β := htPath
    have hsParam : 8 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAngleOrder :
        -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hAnglesNe :
        Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hαmemOpen :
        α ∈ openSegment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |(Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r))| ≤ 2 * Real.pi := by
      have hnonneg :
          0 ≤ (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) := by
        nlinarith [hθ.2, Real.pi_pos]
      rw [abs_of_nonneg hnonneg]
      nlinarith [hθ.1, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := ε)
        (a := Real.pi - Real.arctan (ε / r))
        (b := -Real.pi + Real.arctan (ε / r))
        (by linarith : ε ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 8 * (s : ℝ) - 1 = 8 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := Real.pi - Real.arctan (ε / r))
        (p₁ := -Real.pi + Real.arctan (ε / r))
        (c₁ := 8 * (s : ℝ) - 1) (c₂ := 8 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          nlinarith [hEq, hθ.2, Real.pi_pos]
        exact this.elim
      · exact hEq
    -- The affine angle parameter is injective because the two angular endpoints differ.
    exact Subtype.ext (by linarith)
  · rcases hlower with ⟨hs, ht⟩
    -- The lower lip is the same affine radial model, with the opposite orientation.
    have hsPath :
        exercise21Delta r ε s =
          AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (s : ℝ) - 1) := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        exercise21Delta r ε t =
          AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (t : ℝ) - 1) := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (t : ℝ) - 1) := by
      calc
        AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (s : ℝ) - 1) =
            exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := htPath
    have hEndsNe :
        circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ≠
          circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    have hst' : 4 * (s : ℝ) - 1 = 4 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
        (p₁ := circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
        (c₁ := 4 * (s : ℝ) - 1) (c₂ := 4 * (t : ℝ) - 1)).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Again the subtype equality is read off from the affine radial coordinate.
    exact Subtype.ext (by linarith)
  · rcases houter with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (2 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (2 * (t : ℝ) - 1)
    -- The outer circle uses the same injective angular strip as the inner arc.
    have hsPath : exercise21Delta r ε s = circleMap 0 r α := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self hs)
    have htPath : exercise21Delta r ε t = circleMap 0 r β := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 r α = circleMap 0 r β := by
      calc
        circleMap 0 r α = exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ = circleMap 0 r β := htPath
    have hsParam : 2 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAngleOrder :
        -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hAnglesNe :
        -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hαmemOpen :
        α ∈ openSegment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |(-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r))| ≤ 2 * Real.pi := by
      have hnonpos :
          (-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r)) ≤ 0 := by
        nlinarith [hθ.2, Real.pi_pos]
      rw [abs_of_nonpos hnonpos]
      nlinarith [hθ.1, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := r)
        (a := -Real.pi + Real.arctan (ε / r))
        (b := Real.pi - Real.arctan (ε / r))
        (by linarith : r ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := -Real.pi + Real.arctan (ε / r))
        (p₁ := Real.pi - Real.arctan (ε / r))
        (c₁ := 2 * (s : ℝ) - 1) (c₂ := 2 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          nlinarith [hEq, hθ.2, Real.pi_pos]
        exact this.elim
      · exact hEq
    -- The outer-arc affine angle parameter is likewise injective.
    exact Subtype.ext (by linarith)

/-- Helper for Exercise 21: equality on the keyhole contour can only occur at the same parameter
or at the identified endpoint pair `(0, 1)` / `(1, 0)`. -/
lemma exercise21Delta_simple_eq_or_endpoints
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {s t : I}
    (hst : exercise21Delta r ε s = exercise21Delta r ε t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  have hr : 0 < r := lt_trans hε hεr
  have hbreak := exercise21Delta_breakpoint_values r ε
  rcases exercise21Delta_parameter_cases s with
    hs0 | hsupper | hs18 | hsinner | hs14 | hslower | hs12 | hsouter | hs1
  · have hsEq : s = (0 : I) := Subtype.ext hs0
    -- If `s` is the initial endpoint, `t` must be one of the two parameters for the same corner.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [hsEq] using hbreak.1
    rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 htCorner with ht0 | ht1
    · left
      simpa [hsEq, ht0]
    · right
      left
      simpa [hsEq, ht1]
  · -- Route correction: use the branch geometry already proved for the four open pieces instead of
    -- trying to recurse on the concatenated path itself.
    rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr hsupper with
      ⟨ρs, hρs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr (Or.inl ⟨hsupper, htupper⟩) hst
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (Real.pi - Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr htlower with
        ⟨ρt, hρt, htPath⟩
      have hsIm : 0 < (exercise21Delta r ε s).im := by
        rw [hsPath]
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρs)
        have hre :=
          exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htIm : (exercise21Delta r ε t).im < 0 := by
        rw [htPath]
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρt)
        have hre :=
          exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him : (exercise21Delta r ε s).im = (exercise21Delta r ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = r := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (Real.pi - Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 r αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext hs18
    -- The first interior corner has a singleton fiber.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by simpa [hsEq] using hbreak.2.1
    have htEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr hsinner with
      ⟨αs, hαs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
    · rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (Real.pi - Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.1]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr
        (Or.inr <| Or.inl ⟨hsinner, htinner⟩) hst
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (-Real.pi + Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ε = r := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 r αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hεr, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext hs14
    -- The lower inner corner also has a singleton fiber.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
            simpa [hsEq] using hbreak.2.2.1
    have htEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr hslower with
      ⟨ρs, hρs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
    · rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr htupper with
        ⟨ρt, hρt, htPath⟩
      have hsIm : (exercise21Delta r ε s).im < 0 := by
        rw [hsPath]
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρs)
        have hre :=
          exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htIm : 0 < (exercise21Delta r ε t).im := by
        rw [htPath]
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρt)
        have hre :=
          exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him : (exercise21Delta r ε s).im = (exercise21Delta r ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-Real.pi + Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr
        (Or.inr <| Or.inr <| Or.inl ⟨hslower, htlower⟩) hst
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.2]
      exact this.elim
    · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = r := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-Real.pi + Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 r αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hs12
    -- The lower outer corner has a singleton fiber as well.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
            simpa [hsEq] using hbreak.2.2.2.1
    have htEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr hsouter with
      ⟨αs, hαs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
    · rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          r = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 r αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (Real.pi - Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          r = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 r αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hεr, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          r = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 r αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (-Real.pi + Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr
        (Or.inr <| Or.inr <| Or.inr ⟨hsouter, htouter⟩) hst
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
  · have hsEq : s = (1 : I) := Subtype.ext hs1
    -- The terminal endpoint is the second parameter for the same upper outer corner.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
            simpa [hsEq] using hbreak.2.2.2.2
    rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 htCorner with ht0 | ht1
    · right
      right
      simpa [hsEq, ht0]
    · left
      simpa [hsEq, ht1]

