import DifferentialForms_Cartan_1970.III.section12.«0005_Proposition_3_1».WeightedNormalForm

noncomputable section

open Filter
open MeasureTheory
open UpperHalfPlane
open scoped BigOperators Interval Topology

section

variable {f : ℂ → ℂ} {s : Finset ℂ}

/-- Helper for Proposition 3.1: the source-facing upper-semicircle path starts at `r`. -/
lemma upper_semicircle_path_source_eq (r : ℝ) :
    (r : ℂ) = circleMap 0 r 0 := by
  -- The angle `0` on `circleMap` is exactly the positive real point of radius `r`.
  simp [circleMap_zero]

/-- Helper for Proposition 3.1: the source-facing upper-semicircle path ends at `-r`. -/
lemma upper_semicircle_path_target_eq (r : ℝ) :
    (-(r : ℂ)) = circleMap 0 r Real.pi := by
  -- The angle `π` on `circleMap` is exactly the negative real point of radius `r`.
  simp [circleMap_zero, Complex.exp_pi_mul_I]

/-- Helper for Proposition 3.1: the explicit upper-semicircle path is the angular segment
`0 ≤ θ ≤ π` mapped through `circleMap`. -/
def upperSemicirclePath (r : ℝ) : Path (r : ℂ) (-(r : ℂ)) :=
  (((Path.segment (0 : ℝ) Real.pi).map (continuous_circleMap 0 r)).cast
    (upper_semicircle_path_source_eq r) (upper_semicircle_path_target_eq r))

/-- Helper for Proposition 3.1: the upper-half-disk boundary path is the real diameter
`[-r, r]` followed by the positively oriented upper semicircle. -/
def upperHalfDiskBoundaryPath (r : ℝ) : Path (-(r : ℂ)) (-(r : ℂ)) :=
  (Path.segment (-(r : ℂ)) (r : ℂ)).trans (upperSemicirclePath r)

/-- Helper for Proposition 3.1: evaluating the explicit upper-semicircle path recovers the usual
parameterization `θ = π t`. -/
@[simp] lemma upperSemicirclePath_apply (r : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    upperSemicirclePath r t = circleMap 0 r (Real.pi * (t : ℝ)) := by
  -- Unfold the casted mapped segment and collapse the affine angle parametrization.
  have hline :
      AffineMap.lineMap (0 : ℝ) Real.pi (t : ℝ) = Real.pi * (t : ℝ) := by
    simpa [mul_comm] using
      (show AffineMap.lineMap (0 : ℝ) Real.pi (t : ℝ) = (t : ℝ) * Real.pi by
        simp [AffineMap.lineMap_apply_module])
  simp [upperSemicirclePath, Path.map_coe, Path.segment_apply, hline]

/-- Helper for Proposition 3.1: the explicit upper-semicircle path covers exactly the radius-`r`
circle with angle parameter in `0 ≤ θ ≤ π`. -/
lemma upper_semicircle_path_range_eq_image_Icc (r : ℝ) :
    Set.range (upperSemicirclePath r) = circleMap 0 r '' Set.Icc 0 Real.pi := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Real.pi * (t : ℝ), ?_, ?_⟩
    · -- The path parameter `t ∈ [0, 1]` maps into the source angle interval `[0, π]`.
      constructor
      · exact mul_nonneg Real.pi_pos.le t.2.1
      · nlinarith [Real.pi_pos, t.2.2]
    · -- Evaluate the path using the explicit angular parametrization.
      simpa using upperSemicirclePath_apply r t
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ / Real.pi, ?_⟩, ?_⟩
    · -- Normalize the angle back to a unit-interval parameter.
      constructor
      · exact div_nonneg hθ.1 Real.pi_pos.le
      · calc
          θ / Real.pi ≤ Real.pi / Real.pi := by
            exact div_le_div_of_nonneg_right hθ.2 Real.pi_pos.le
          _ = 1 := by field_simp [Real.pi_ne_zero]
    · -- The rescaled parameter recovers the original angle exactly.
      have hangle : Real.pi * (θ / Real.pi) = θ := by
        field_simp [Real.pi_ne_zero]
      rw [upperSemicirclePath_apply, hangle]

/-- Helper for Proposition 3.1: the boundary path image splits as the union of the diameter and
upper-semicircle images. -/
lemma upper_half_disk_boundary_path_range_eq_union (r : ℝ) :
    Set.range (upperHalfDiskBoundaryPath r) =
      Set.range (Path.segment (-(r : ℂ)) (r : ℂ)) ∪ Set.range (upperSemicirclePath r) := by
  -- Expand the concatenated boundary path into its two source-facing pieces.
  rw [upperHalfDiskBoundaryPath, Path.trans_range]

/-- Helper for Proposition 3.1: evaluating the horizontal diameter segment reads off the real
affine coordinate `x = (2r)t - r`. -/
lemma upper_half_disk_diameter_path_apply (r : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    Path.segment (-(r : ℂ)) (r : ℂ) t = ((((2 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
  -- Unfold the segment path and compute its affine line map explicitly on the real axis.
  apply Complex.ext <;> simp [Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg]
  ring

/-- Helper for Proposition 3.1: on the first half of the boundary parameter interval, the
concatenated contour follows the horizontal diameter branch. -/
lemma upper_half_disk_boundary_eq_diameter_of_le_half (r : ℝ)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : (t : ℝ) ≤ 1 / 2) :
    upperHalfDiskBoundaryPath r t = ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
  -- On the first half of `Path.trans`, the diameter segment is the active source branch.
  have htrans :
      (upperHalfDiskBoundaryPath r).extend t =
        (Path.segment (-(r : ℂ)) (r : ℂ)).extend (2 * (t : ℝ)) := by
    dsimp [upperHalfDiskBoundaryPath]
    exact
      Path.extend_trans_of_le_half
        (γ₁ := Path.segment (-(r : ℂ)) (r : ℂ))
        (γ₂ := upperSemicirclePath r)
        ht
  have hI : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [t.2.1, t.2.2, ht]
  calc
    upperHalfDiskBoundaryPath r t = (upperHalfDiskBoundaryPath r).extend t := by
      simpa using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) t.2)
    _ = (Path.segment (-(r : ℂ)) (r : ℂ)).extend (2 * (t : ℝ)) := htrans
    _ = (Path.segment (-(r : ℂ)) (r : ℂ)) ⟨2 * (t : ℝ), hI⟩ := by
          simpa using
            (Path.extend_apply (γ := Path.segment (-(r : ℂ)) (r : ℂ)) hI)
    _ = ((((2 * r) * (2 * (t : ℝ)) - r : ℝ)) : ℂ) := by
          simpa using upper_half_disk_diameter_path_apply r ⟨2 * (t : ℝ), hI⟩
    _ = ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
          congr 1
          ring

/-- Helper for Proposition 3.1: on the second half of the boundary parameter interval, the
concatenated contour follows the upper semicircle branch. -/
lemma upper_half_disk_boundary_eq_arc_of_half_le (r : ℝ)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : 1 / 2 ≤ (t : ℝ)) :
    upperHalfDiskBoundaryPath r t = circleMap 0 r (Real.pi * (2 * (t : ℝ) - 1)) := by
  -- After the midpoint of `Path.trans`, the upper-semicircle branch takes over.
  have htrans :
      (upperHalfDiskBoundaryPath r).extend t =
        (upperSemicirclePath r).extend (2 * (t : ℝ) - 1) := by
    dsimp [upperHalfDiskBoundaryPath]
    exact
      Path.extend_trans_of_half_le
        (γ₁ := Path.segment (-(r : ℂ)) (r : ℂ))
        (γ₂ := upperSemicirclePath r)
        ht
  have hI : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [t.2.1, t.2.2, ht]
  calc
    upperHalfDiskBoundaryPath r t = (upperHalfDiskBoundaryPath r).extend t := by
      simpa using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) t.2)
    _ = (upperSemicirclePath r).extend (2 * (t : ℝ) - 1) := htrans
    _ = (upperSemicirclePath r) ⟨2 * (t : ℝ) - 1, hI⟩ := by
          simpa using (Path.extend_apply (γ := upperSemicirclePath r) hI)
    _ = circleMap 0 r
          (Real.pi * ((⟨2 * (t : ℝ) - 1, hI⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) := by
          simpa using upperSemicirclePath_apply r ⟨2 * (t : ℝ) - 1, hI⟩
    _ = circleMap 0 r (Real.pi * (2 * (t : ℝ) - 1)) := by
          simp

/-- Helper for Proposition 3.1: on the first half of the source interval, the real-plane
parametrization of the closed semidisk boundary is exactly the affine diameter model. -/
lemma upper_half_disk_boundary_realCurve_eqOn_diameter_interval (r : ℝ) :
    Set.EqOn
      ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (fun t : ℝ ↦ Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)))
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro t ht
  have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact ht.1
    · linarith [ht.2]
  let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
  have hbranch :
      upperHalfDiskBoundaryPath r tI = ((((4 * r) * t - r : ℝ)) : ℂ) := by
    -- On the first half-interval, the boundary path is the explicit diameter branch.
    simpa [tI] using upper_half_disk_boundary_eq_diameter_of_le_half r (t := tI) ht.2
  -- Replace `realCurve` by the original path evaluation before using the explicit branch formula.
  calc
    (upperHalfDiskBoundaryPath r).toClosedPath.realCurve t
        = Complex.equivRealProd
            (((upperHalfDiskBoundaryPath r).toClosedPath.toPath).extend t) := by
            rfl
    _ = Complex.equivRealProd (((upperHalfDiskBoundaryPath r).toClosedPath.toPath) tI) := by
          rw [Path.extend_apply (γ := (upperHalfDiskBoundaryPath r).toClosedPath.toPath) hI]
    _ = Complex.equivRealProd (upperHalfDiskBoundaryPath r tI) := by
          simpa [Path.toClosedPath] using
            congrArg Complex.equivRealProd
              (ClosedPath.toPath_apply ((upperHalfDiskBoundaryPath r).toClosedPath) tI)
    _ = Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)) := by
          rw [hbranch]

/-- Helper for Proposition 3.1: on the second half of the source interval, the real-plane
parametrization of the closed semidisk boundary is exactly the upper-semicircle model. -/
lemma upper_half_disk_boundary_realCurve_eqOn_arc_interval (r : ℝ) :
    Set.EqOn
      ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (fun t : ℝ ↦ Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))))
      (Set.Icc (1 / 2 : ℝ) 1) := by
  intro t ht
  have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · linarith [ht.1]
    · exact ht.2
  let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
  have hbranch :
      upperHalfDiskBoundaryPath r tI = circleMap 0 r (Real.pi * (2 * t - 1)) := by
    -- On the second half-interval, the boundary path is the explicit upper-semicircle branch.
    simpa [tI] using upper_half_disk_boundary_eq_arc_of_half_le r (t := tI) ht.1
  -- As on the diameter branch, first normalize `realCurve` back to the original path.
  calc
    (upperHalfDiskBoundaryPath r).toClosedPath.realCurve t
        = Complex.equivRealProd
            (((upperHalfDiskBoundaryPath r).toClosedPath.toPath).extend t) := by
            rfl
    _ = Complex.equivRealProd (((upperHalfDiskBoundaryPath r).toClosedPath.toPath) tI) := by
          rw [Path.extend_apply (γ := (upperHalfDiskBoundaryPath r).toClosedPath.toPath) hI]
    _ = Complex.equivRealProd (upperHalfDiskBoundaryPath r tI) := by
          simpa [Path.toClosedPath] using
            congrArg Complex.equivRealProd
              (ClosedPath.toPath_apply ((upperHalfDiskBoundaryPath r).toClosedPath) tI)
    _ = Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))) := by
          rw [hbranch]

/-- Helper for Proposition 3.1: the semidisk boundary `realCurve` agrees with the explicit
diameter and semicircle models on the two source subintervals. -/
lemma upper_half_disk_boundary_realCurve_eqOn_piece_intervals (r : ℝ) :
    Set.EqOn
      ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (fun t : ℝ ↦ Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)))
      (Set.Icc (0 : ℝ) (1 / 2)) ∧
      Set.EqOn
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (fun t : ℝ ↦ Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))))
        (Set.Icc (1 / 2 : ℝ) 1) := by
  -- Route correction: normalize the closed-path real parametrization branchwise before building
  -- any boundary charts, so later geometry can stay on explicit affine/circle models.
  exact ⟨upper_half_disk_boundary_realCurve_eqOn_diameter_interval r,
    upper_half_disk_boundary_realCurve_eqOn_arc_interval r⟩

/-- Helper for Proposition 3.1: every diameter-branch point of the explicit semidisk contour lies
on the real axis. -/
lemma upper_half_disk_boundary_im_eq_zero_of_le_half (r : ℝ)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : (t : ℝ) ≤ 1 / 2) :
    (upperHalfDiskBoundaryPath r t).im = 0 := by
  -- The first branch is an explicit real segment.
  rw [upper_half_disk_boundary_eq_diameter_of_le_half r ht]
  simp

/-- Helper for Proposition 3.1: on the open arc branch, the explicit semidisk contour has strictly
positive imaginary part. -/
lemma upper_half_disk_boundary_im_pos_of_mem_Ioo_half_one {r : ℝ} (hr : 0 < r)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : (t : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    0 < (upperHalfDiskBoundaryPath r t).im := by
  -- The second branch is the upper semicircle with angle strictly between `0` and `π`.
  rw [upper_half_disk_boundary_eq_arc_of_half_le r ht.1.le, circleMap_zero_im]
  have hθ : Real.pi * (2 * (t : ℝ) - 1) ∈ Set.Ioo (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
  exact mul_pos hr (Real.sin_pos_of_mem_Ioo hθ)

/-- Helper for Proposition 3.1: on the upper semicircle, `circleMap` is injective on the source
angle interval `0 ≤ θ ≤ π`. -/
lemma upper_semicircle_circleMap_injective {r α β : ℝ} (hr : r ≠ 0)
    (hα : α ∈ Set.Icc (0 : ℝ) Real.pi) (hβ : β ∈ Set.Icc (0 : ℝ) Real.pi)
    (h : circleMap 0 r α = circleMap 0 r β) :
    α = β := by
  -- Equality on the semicircle forces the angular difference to be a `2π` multiple lying in
  -- `(-2π, 2π)`, hence the multiple is zero.
  rw [circleMap_eq_circleMap_iff (c := (0 : ℂ)) hr] at h
  obtain ⟨n, hn⟩ := h
  have hangle : α = β + n * (2 * Real.pi) := by
    have him := congrArg Complex.im hn
    simpa [mul_add, add_mul, mul_assoc] using him
  have hlt_one_real : (n : ℝ) < 1 := by
    nlinarith [hα.2, hβ.1, Real.pi_pos, hangle]
  have hgt_neg_one_real : (-1 : ℝ) < n := by
    nlinarith [hα.1, hβ.2, Real.pi_pos, hangle]
  have hlt_one : n < 1 := by
    exact_mod_cast hlt_one_real
  have hgt_neg_one : -1 < n := by
    exact_mod_cast hgt_neg_one_real
  have hn_zero : n = 0 := by
    omega
  simpa [hn_zero] using hangle

/-- Helper for Proposition 3.1: equality on the semidisk contour can only occur at the same
parameter or at the identified endpoint pair `(0, 1)` / `(1, 0)`. -/
lemma upper_half_disk_boundary_simple_eq_or_endpoints
    {r : ℝ} (hr : 0 < r) {s t : Set.Icc (0 : ℝ) 1}
    (h :
      (upperHalfDiskBoundaryPath r).toClosedPath.toPath s =
        (upperHalfDiskBoundaryPath r).toClosedPath.toPath t) :
    s = t ∨ (s, t) = ((0 : Set.Icc (0 : ℝ) 1), (1 : Set.Icc (0 : ℝ) 1)) ∨
      (s, t) = ((1 : Set.Icc (0 : ℝ) 1), (0 : Set.Icc (0 : ℝ) 1)) := by
  -- Route correction: prove simplicity from the source contour decomposition itself, using the
  -- diameter/arc branch formulas and the imaginary-part separation between those branches.
  have hpath : upperHalfDiskBoundaryPath r s = upperHalfDiskBoundaryPath r t := by
    simpa [Path.toClosedPath] using h
  by_cases hs_half : (s : ℝ) ≤ 1 / 2
  · by_cases ht_half : (t : ℝ) ≤ 1 / 2
    · -- If both parameters are on the diameter branch, the affine coordinate is injective.
      have hs_eq := upper_half_disk_boundary_eq_diameter_of_le_half r hs_half
      have ht_eq := upper_half_disk_boundary_eq_diameter_of_le_half r ht_half
      have hEq :
          ((((4 * r) * (s : ℝ) - r : ℝ)) : ℂ) =
            ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
        simpa [hs_eq, ht_eq] using hpath
      have hre :
          (4 * r) * (s : ℝ) - r = (4 * r) * (t : ℝ) - r := by
        have hre' := congrArg Complex.re hEq
        simpa using hre'
      have hst : (s : ℝ) = (t : ℝ) := by
        nlinarith [hr, hre]
      exact Or.inl (Subtype.ext hst)
    · by_cases ht_one : (t : ℝ) = 1
      · -- Crossing from the diameter to the arc can only happen at the shared endpoint `-r`.
        have hs_eq := upper_half_disk_boundary_eq_diameter_of_le_half r hs_half
        have ht_eq :
            upperHalfDiskBoundaryPath r t = (-(r : ℂ)) := by
          calc
            upperHalfDiskBoundaryPath r t
                = circleMap 0 r (Real.pi * (2 * (t : ℝ) - 1)) := by
                    exact upper_half_disk_boundary_eq_arc_of_half_le r (by
                      have : ¬ (t : ℝ) ≤ 1 / 2 := ht_half
                      linarith [t.2.1])
            _ = circleMap 0 r Real.pi := by
                  rw [ht_one]
                  ring
            _ = (-(r : ℂ)) := by
                  symm
                  exact upper_semicircle_path_target_eq r
        have hEq : ((((4 * r) * (s : ℝ) - r : ℝ)) : ℂ) = (-(r : ℂ)) := by
          simpa [hs_eq, ht_eq] using hpath
        have hre :
            (4 * r) * (s : ℝ) - r = -r := by
          have hre' := congrArg Complex.re hEq
          simpa using hre'
        have hs_zero : (s : ℝ) = 0 := by
          nlinarith [hr, hre]
        have hs_eqI : s = (0 : Set.Icc (0 : ℝ) 1) := Subtype.ext hs_zero
        have ht_eqI : t = (1 : Set.Icc (0 : ℝ) 1) := Subtype.ext ht_one
        exact Or.inr <| Or.inl <| by simpa [hs_eqI, ht_eqI]
      · -- An interior arc point cannot equal a diameter point because their imaginary parts differ.
        have hs_im : (upperHalfDiskBoundaryPath r s).im = 0 :=
          upper_half_disk_boundary_im_eq_zero_of_le_half r hs_half
        have ht_open : (t : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
          constructor
          · have : ¬ (t : ℝ) ≤ 1 / 2 := ht_half
            exact lt_of_not_ge this
          · exact lt_of_le_of_ne t.2.2 (by
              intro ht_eq
              exact ht_one ht_eq)
        have ht_im :
            0 < (upperHalfDiskBoundaryPath r t).im :=
          upper_half_disk_boundary_im_pos_of_mem_Ioo_half_one hr ht_open
        have him := congrArg Complex.im hpath
        rw [hs_im] at him
        linarith
  · by_cases ht_half : (t : ℝ) ≤ 1 / 2
    · by_cases hs_one : (s : ℝ) = 1
      · -- The symmetric branch-crossing case can only occur at the endpoint pair `(1, 0)`.
        have hs_eq :
            upperHalfDiskBoundaryPath r s = (-(r : ℂ)) := by
          calc
            upperHalfDiskBoundaryPath r s
                = circleMap 0 r (Real.pi * (2 * (s : ℝ) - 1)) := by
                    exact upper_half_disk_boundary_eq_arc_of_half_le r (by
                      have : ¬ (s : ℝ) ≤ 1 / 2 := hs_half
                      linarith [s.2.1])
            _ = circleMap 0 r Real.pi := by
                  rw [hs_one]
                  ring
            _ = (-(r : ℂ)) := by
                  symm
                  exact upper_semicircle_path_target_eq r
        have ht_eq := upper_half_disk_boundary_eq_diameter_of_le_half r ht_half
        have hEq : (-(r : ℂ)) = ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
          simpa [hs_eq, ht_eq] using hpath
        have hre :
            -r = (4 * r) * (t : ℝ) - r := by
          have hre' := congrArg Complex.re hEq
          simpa using hre'
        have ht_zero : (t : ℝ) = 0 := by
          nlinarith [hr, hre]
        have hs_eqI : s = (1 : Set.Icc (0 : ℝ) 1) := Subtype.ext hs_one
        have ht_eqI : t = (0 : Set.Icc (0 : ℝ) 1) := Subtype.ext ht_zero
        exact Or.inr <| Or.inr <| by simpa [hs_eqI, ht_eqI]
      · -- Again, an interior arc point cannot meet the diameter because the imaginary part is positive.
        have ht_im : (upperHalfDiskBoundaryPath r t).im = 0 :=
          upper_half_disk_boundary_im_eq_zero_of_le_half r ht_half
        have hs_open : (s : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
          constructor
          · have : ¬ (s : ℝ) ≤ 1 / 2 := hs_half
            exact lt_of_not_ge this
          · exact lt_of_le_of_ne s.2.2 (by
              intro hs_eq
              exact hs_one hs_eq)
        have hs_im :
            0 < (upperHalfDiskBoundaryPath r s).im :=
          upper_half_disk_boundary_im_pos_of_mem_Ioo_half_one hr hs_open
        have him := congrArg Complex.im hpath
        rw [ht_im] at him
        linarith
    · -- If both parameters are on the arc branch, injectivity reduces to angle injectivity on
      -- `[0, π]`.
      have hs_ge : 1 / 2 ≤ (s : ℝ) := by
        have : ¬ (s : ℝ) ≤ 1 / 2 := hs_half
        exact (lt_of_not_ge this).le
      have ht_ge : 1 / 2 ≤ (t : ℝ) := by
        have : ¬ (t : ℝ) ≤ 1 / 2 := ht_half
        exact (lt_of_not_ge this).le
      let α : ℝ := Real.pi * (2 * (s : ℝ) - 1)
      let β : ℝ := Real.pi * (2 * (t : ℝ) - 1)
      have hs_eq := upper_half_disk_boundary_eq_arc_of_half_le r hs_ge
      have ht_eq := upper_half_disk_boundary_eq_arc_of_half_le r ht_ge
      have hcircle : circleMap 0 r α = circleMap 0 r β := by
        simpa [α, β, hs_eq, ht_eq] using hpath
      have hα : α ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor <;> nlinarith [hs_ge, s.2.2, Real.pi_pos]
      have hβ : β ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor <;> nlinarith [ht_ge, t.2.2, Real.pi_pos]
      have hαβ : α = β :=
        upper_semicircle_circleMap_injective (by linarith : r ≠ 0) hα hβ hcircle
      have hst : (s : ℝ) = (t : ℝ) := by
        nlinarith [Real.pi_pos, hαβ]
      exact Or.inl (Subtype.ext hst)

/-- Helper for Proposition 3.1: for positive radius, the horizontal diameter segment has range
exactly the real interval `[-r, r]`. -/
lemma upper_half_disk_diameter_path_range_eq_image_Icc {r : ℝ} (hr : 0 < r) :
    Set.range (Path.segment (-(r : ℂ)) (r : ℂ)) =
      (fun x : ℝ ↦ (x : ℂ)) '' Set.Icc (-r) r := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(2 * r) * (t : ℝ) - r, ?_, ?_⟩
    · -- The affine segment parameter stays inside the diameter interval.
      constructor <;> nlinarith [t.2.1, t.2.2, hr]
    · -- Read the complex segment point in the source real coordinate.
      simpa using (upper_half_disk_diameter_path_apply r t).symm
  · rintro ⟨x, hx, rfl⟩
    let t : Set.Icc (0 : ℝ) 1 := by
      refine ⟨(x + r) / (2 * r), ?_⟩
      -- Rescale the real coordinate back to a unit-interval parameter.
      constructor
      · have htwo : 0 < 2 * r := by positivity
        exact div_nonneg (by linarith [hx.1]) htwo.le
      · have htwo : 0 < 2 * r := by positivity
        have hbound : x + r ≤ 2 * r := by linarith [hx.2]
        have htwo_ne : (2 * r) ≠ 0 := by positivity
        calc
          (x + r) / (2 * r) ≤ (2 * r) / (2 * r) := by
            exact div_le_div_of_nonneg_right hbound htwo.le
          _ = 1 := by field_simp [htwo_ne]
    refine ⟨t, ?_⟩
    have hcoord : (2 * r) * ((t : ℝ)) - r = x := by
      dsimp [t]
      field_simp [hr.ne']
      ring
    -- Substituting that parameter into the affine line map recovers the requested diameter point.
    simpa [hcoord] using upper_half_disk_diameter_path_apply r t

/-- Helper for Proposition 3.1: for a positive radius, the frontier of the closed upper half-disk
is exactly the real diameter `[-r, r]` together with the upper semicircle. -/
lemma frontier_upper_half_disk_eq_diameter_union_upper_arc {r : ℝ} (hr : 0 < r) :
    frontier ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) =
      ((fun x : ℝ ↦ (x : ℂ)) '' Set.Icc (-r) r) ∪ (circleMap 0 r '' Set.Icc 0 Real.pi) := by
  let K : Set ℂ := Metric.closedBall (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
  have hK : K = ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
    -- Normalize the semidisk to the intersection of the closed disk and the closed upper
    -- half-plane so frontier/interior lemmas apply directly.
    ext z
    simp [K, Metric.mem_closedBall, dist_eq_norm]
  have hKclosed : IsClosed K := by
    -- Both defining pieces are closed, so the semidisk itself is closed.
    exact
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : ℂ) r)).inter
        (isClosed_le continuous_const Complex.continuous_im)
  have hKsubset_ball : K ⊆ Metric.closedBall (0 : ℂ) r := by
    intro z hz
    exact hz.1
  have hKsubset_half : K ⊆ {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    exact hz.2
  rw [← hK]
  ext z
  constructor
  · intro hz
    have hzK : z ∈ K := by
      -- Frontier points of the closed semidisk still belong to the semidisk itself.
      simpa [hKclosed.closure_eq] using (frontier_subset_closure hz)
    have hz_split :
        z ∈
          (frontier (Metric.closedBall (0 : ℂ) r) ∩ closure {z : ℂ | 0 ≤ z.im}) ∪
            (closure (Metric.closedBall (0 : ℂ) r) ∩ frontier {z : ℂ | 0 ≤ z.im}) := by
      -- A frontier point of the intersection must come from one of the two defining boundaries.
      exact frontier_inter_subset (Metric.closedBall (0 : ℂ) r) {z : ℂ | 0 ≤ z.im} hz
    rcases hz_split with ⟨hz_ball, _⟩ | ⟨_, hz_half⟩
    · right
      have hz_sphere : z ∈ Metric.sphere (0 : ℂ) r := by
        simpa [frontier_closedBall'] using hz_ball
      have hz_norm : ‖z‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz_sphere
      refine ⟨Complex.arg z, ?_, ?_⟩
      · -- On the closed upper half-plane the principal argument lies in `[0, π]`.
        constructor
        · exact (Complex.arg_nonneg_iff).2 hzK.2
        · exact Complex.arg_le_pi z
      · -- Rebuild the boundary point from its norm and principal argument.
        calc
          circleMap 0 r (Complex.arg z)
              = 0 + r * Complex.exp (Complex.arg z * Complex.I) := by
                  simp [circleMap]
          _ = 0 + ‖z‖ * Complex.exp (Complex.arg z * Complex.I) := by
                rw [hz_norm]
          _ = z := by
                rw [Complex.norm_mul_exp_arg_mul_I]
                ring
    · left
      have hz_im : z.im = 0 := by
        -- The frontier of the closed upper half-plane is the real axis.
        simpa [Complex.frontier_setOf_le_im] using hz_half
      have hz_eq_real : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [hz_im]
      have hz_re_abs : |z.re| ≤ r := by
        exact le_trans (Complex.abs_re_le_norm z) (by
          simpa [K, Metric.mem_closedBall, dist_eq_norm] using hzK.1)
      have hz_re_mem : z.re ∈ Set.Icc (-r) r := by
        exact abs_le.mp hz_re_abs
      exact ⟨z.re, hz_re_mem, hz_eq_real.symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · have hx_abs : |x| ≤ r := by
        exact abs_le.2 hx
      have hzK : ((x : ℂ) : ℂ) ∈ K := by
        constructor
        · simpa [K, Metric.mem_closedBall, dist_eq_norm] using hx_abs
        · simp
      have hz_not_int_half : ((x : ℂ) : ℂ) ∉ interior {z : ℂ | 0 ≤ z.im} := by
        -- Real points lie on the half-plane frontier, so they cannot be interior points.
        simp [Complex.interior_setOf_le_im]
      have hz_not_int_K : ((x : ℂ) : ℂ) ∉ interior K := by
        intro hz_int
        exact hz_not_int_half (interior_mono hKsubset_half hz_int)
      -- Membership in the semidisk plus failure of interior membership is exactly frontier
      -- membership.
      exact (mem_frontier_iff_notMem_interior hzK).2 hz_not_int_K
    · have hzK : circleMap 0 r θ ∈ K := by
        constructor
        · -- Points of the upper semicircle sit on the boundary circle of radius `r`.
          simpa [K, Metric.mem_closedBall, dist_eq_norm, norm_circleMap_upper_semicircle hr.le]
        · exact circleMap_mem_closed_upper_half_plane hr.le hθ
      have hz_not_int_ball :
          circleMap 0 r θ ∉ interior (Metric.closedBall (0 : ℂ) r) := by
        -- A point of norm exactly `r` cannot lie in the open ball.
        simpa [interior_closedBall', hr.ne', Metric.mem_ball, dist_eq_norm,
          norm_circleMap_upper_semicircle hr.le]
      have hz_not_int_K : circleMap 0 r θ ∉ interior K := by
        intro hz_int
        exact hz_not_int_ball (interior_mono hKsubset_ball hz_int)
      -- The arc lies in the semidisk but not in its interior, so it lies on the frontier.
      exact (mem_frontier_iff_notMem_interior hzK).2 hz_not_int_K

/-- Helper for Proposition 3.1: for positive radius, the explicit upper-half-disk contour range is
exactly the frontier of the closed upper half-disk. -/
lemma upper_half_disk_boundary_path_range_eq_frontier {r : ℝ} (hr : 0 < r) :
    Set.range (upperHalfDiskBoundaryPath r) =
      frontier ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
  -- Rewrite the contour range into the diameter-plus-arc union already matched with the frontier.
  rw [upper_half_disk_boundary_path_range_eq_union,
    upper_half_disk_diameter_path_range_eq_image_Icc hr,
    upper_semicircle_path_range_eq_image_Icc,
    frontier_upper_half_disk_eq_diameter_union_upper_arc hr]

/-- Helper for Proposition 3.1: every frontier point of the closed upper half-disk is an analytic
point of the weighted meromorphic normal form, provided the outer semicircle avoids poles. -/
lemma upper_half_disk_frontier_weighted_normal_form_analyticAt
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ} (hr : 0 < r)
    (hboundary :
      ∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0)
    {z : ℂ}
    (hz : z ∈ frontier ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ)) :
    AnalyticAt ℂ
      (fun w ↦
        toMeromorphicNFOn f {w : ℂ | 0 ≤ w.im} w *
          Complex.exp (Complex.I * w))
      z := by
  -- Split the frontier into the real diameter and the upper semicircle, then use the pole-free
  -- hypotheses on each branch to invoke the existing analyticity package.
  rw [frontier_upper_half_disk_eq_diameter_union_upper_arc hr] at hz
  rcases hz with hz | hz
  · rcases hz with ⟨x, hx, rfl⟩
    have hx_not_mem : ((x : ℂ)) ∉ s := by
      intro hxS
      have hxUpper : (x : ℂ) ∈ upperHalfPlaneSet := ((hpoles (x : ℂ)).mpr hxS).2
      have hxim : (0 : ℝ) < ((x : ℂ)).im := by
        simpa [UpperHalfPlane.upperHalfPlaneSet] using hxUpper
      simp at hxim
    -- Real boundary points belong to the closed upper half-plane and avoid the pole finset.
    simpa using
      analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
        (f := f) (s := s) hmeromorphic hreal hpoles (by simp) hx_not_mem
  · rcases hz with ⟨θ, hθ, rfl⟩
    have hz_not_mem : circleMap 0 r θ ∉ s := by
      intro hzS
      have hpole : meromorphicOrderAt f (circleMap 0 r θ) < 0 := ((hpoles _).mpr hzS).1
      exact hboundary θ hθ hpole
    have hzU : circleMap 0 r θ ∈ ({w : ℂ | 0 ≤ w.im} : Set ℂ) := by
      simpa using circleMap_mem_closed_upper_half_plane hr.le hθ
    -- On the semicircular branch, the large-radius hypothesis excludes poles pointwise.
    simpa using
      analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
        (f := f) (s := s) hmeromorphic hreal hpoles hzU hz_not_mem

/-- Helper for Proposition 3.1: a good upper-half-disk radius makes the explicit boundary contour
disjoint from the pole finset, because the contour lies on the frontier while the poles lie in the
interior. -/
lemma upper_half_disk_boundary_disjoint_pole_finset
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ} (hr : 0 < r)
    (hinside : ∀ z ∈ s, ‖z‖ < r) :
    Disjoint (Set.range (upperHalfDiskBoundaryPath r)) (↑s : Set ℂ) := by
  have hsInterior :
      (↑s : Set ℂ) ⊆ interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) :=
    pole_finset_subset_interior_upper_half_disk (f := f) (s := s) hpoles hinside
  rw [upper_half_disk_boundary_path_range_eq_frontier hr]
  refine Set.disjoint_left.2 ?_
  intro z hzFront hzS
  -- Frontier points cannot coincide with points that are already packaged strictly inside the
  -- semidisk.
  exact (Set.disjoint_left.1 disjoint_interior_frontier) (hsInterior hzS) hzFront

/-- Helper for Proposition 3.1: a good radius admits an open owner containing the closed upper
half-disk on which the weighted normal-form integrand is differentiable away from the pole finset.
-/
lemma upper_half_disk_differentiable_owner
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ} (hr : 0 < r)
    (hboundary :
      ∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) :
    ∃ D : Set ℂ,
      IsOpen D ∧
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
        DifferentiableOn ℂ
          (fun z ↦
            toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
              Complex.exp (Complex.I * z))
          (D \ (↑s : Set ℂ)) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let G : ℂ → ℂ := fun z ↦ toMeromorphicNFOn f U z * Complex.exp (Complex.I * z)
  let D : Set ℂ := interior K ∪ {z : ℂ | AnalyticAt ℂ G z}
  have hKU : K ⊆ U := by
    intro z hz
    exact hz.2
  refine ⟨D, ?_, ?_, ?_⟩
  · -- The owner is the union of the semidisk interior with the open analyticity locus of `G`.
    exact isOpen_interior.union (isOpen_analyticAt ℂ G)
  · intro z hzK
    by_cases hzInt : z ∈ interior K
    · exact Or.inl hzInt
    · have hzFront : z ∈ frontier K := (mem_frontier_iff_notMem_interior hzK).2 hzInt
      -- Boundary points are inserted using the frontier analyticity lemma proved just above.
      exact Or.inr <| by
        simpa [G, K, U] using
          upper_half_disk_frontier_weighted_normal_form_analyticAt
            (f := f) (s := s) hmeromorphic hreal hpoles hr hboundary hzFront
  · intro z hz
    rcases hz with ⟨hzD, hzs⟩
    rcases hzD with hzInt | hzAnalytic
    · have hzU : z ∈ U := hKU (interior_subset hzInt)
      have hzAnalytic :
          AnalyticAt ℂ G z := by
        -- Interior points are also covered by the pointwise analyticity statement on `U \ s`.
        simpa [G, U] using
          analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
            (f := f) (s := s) hmeromorphic hreal hpoles hzU hzs
      exact hzAnalytic.differentiableAt.differentiableWithinAt
    · -- Boundary points were inserted precisely because `G` is analytic there.
      exact hzAnalytic.differentiableAt.differentiableWithinAt

/-- Helper for Proposition 3.1: the singleton closed-path family attached to
`upperHalfDiskBoundaryPath r` has union equal to the actual contour range. This is the stable
adapter from the explicit contour to the later `Unit`-indexed `IsOrientedBoundaryOf` API. -/
lemma upper_half_disk_boundary_singleton_iUnion_range (r : ℝ) :
    (⋃ i : Unit,
        Set.range ((((fun _ : Unit ↦ (upperHalfDiskBoundaryPath r).toClosedPath) i).toPath))) =
      Set.range (upperHalfDiskBoundaryPath r) := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    cases i
    -- Collapse the singleton indexed closed-path family back to the explicit contour.
    simpa [Path.toClosedPath] using hi
  · intro hz
    refine Set.mem_iUnion.mpr ?_
    refine ⟨(), ?_⟩
    -- Repackage the explicit contour as the unique member of the singleton family.
    simpa [Path.toClosedPath] using hz

/-- Helper for Proposition 3.1: the explicit upper-semicircle branch is globally differentiable. -/
lemma upper_semicircle_path_isDifferentiable (r : ℝ) :
    (upperSemicirclePath r).IsDifferentiable := by
  -- The upper semicircle is the standard `circleMap` restricted to the affine angle interval
  -- `θ = π t`, so the path is `C¹` on the whole unit interval.
  rw [Path.IsDifferentiable]
  let g : ℝ → ℂ := fun t ↦ circleMap 0 r (Real.pi * t)
  have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ Real.pi * t) := by
    simpa [one_mul] using (contDiff_const.mul contDiff_id)
  have hg : ContDiff ℝ 1 g := by
    simpa [g] using (contDiff_circleMap 0 r).comp hlin
  refine hg.contDiffOn.congr ?_
  intro t ht
  have hpath :
      (upperSemicirclePath r).extend t = circleMap 0 r (Real.pi * t) := by
    rw [Path.extend_apply (γ := upperSemicirclePath r) ht]
    simpa [g] using upperSemicirclePath_apply r ⟨t, ht⟩
  simpa [g] using hpath

/-- Helper for Proposition 3.1: the explicit semidisk contour is piecewise differentiable because
it is the concatenation of a line segment and a smooth upper semicircle. -/
lemma upper_half_disk_boundary_isPiecewiseDifferentiable (r : ℝ) :
    (upperHalfDiskBoundaryPath r).IsPiecewiseDifferentiable := by
  -- Promote the smooth semicircle branch and concatenate it to the already piecewise
  -- differentiable diameter segment.
  exact
    (Path.segment_isPiecewiseDifferentiable (-(r : ℂ)) (r : ℂ)).trans_of_isDifferentiable
      (upper_semicircle_path_isDifferentiable r)

end
