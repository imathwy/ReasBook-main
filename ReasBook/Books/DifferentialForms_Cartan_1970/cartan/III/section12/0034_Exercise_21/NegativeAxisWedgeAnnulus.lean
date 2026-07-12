import DifferentialForms_Cartan_1970.III.section12.«0034_Exercise_21».Exercise21ResidueIntegrand

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

/-- Helper for Exercise 21: the slit around the negative real axis that separates the two
boundary values of the principal logarithm. -/
abbrev exercise21NegativeWedge (r ε : ℝ) : Set ℂ :=
  {z : ℂ | z.re < 0 ∧ |z.im| < (ε / r) * (-z.re)}

/-- Helper for Exercise 21: the compact slit annulus bounded by the keyhole contour `δ(r, ε)`. -/
abbrev exercise21NegativeWedgeAnnulus (r ε : ℝ) : Set ℂ :=
  {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} \ exercise21NegativeWedge r ε

/-- Helper for Exercise 21: the explicit slit annulus lies in `Complex.slitPlane`. -/
lemma exercise21NegativeWedgeAnnulus_subset_slitPlane
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    exercise21NegativeWedgeAnnulus r ε ⊆ Complex.slitPlane := by
  intro z hz
  have hr : 0 < r := lt_trans hε hεr
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hε hz.1.1
  by_cases him : z.im = 0
  · have hre_nonneg : 0 ≤ z.re := by
      by_contra hre_neg
      have hwedge : z ∈ exercise21NegativeWedge r ε := by
        constructor
        · exact lt_of_not_ge hre_neg
        · rw [him, abs_zero]
          have hratio_pos : 0 < ε / r := div_pos hε hr
          have hre_pos : 0 < -z.re := by
            linarith
          have : 0 < (ε / r) * (-z.re) := mul_pos hratio_pos hre_pos
          simpa using this
      exact hz.2 hwedge
    rw [Complex.mem_slitPlane_iff]
    left
    have hz_ne : z ≠ 0 := by
      intro hz0
      simpa [hz0] using hnorm_pos.ne'
    have hre_ne : z.re ≠ 0 := by
      intro hre_zero
      apply hz_ne
      apply Complex.ext <;> simp [hre_zero, him]
    exact lt_of_le_of_ne hre_nonneg (Ne.symm hre_ne)
  · rw [Complex.mem_slitPlane_iff]
    exact Or.inr him

/-- Helper for Exercise 21: the removed negative wedge is open because it is cut out by two strict
inequalities in the real and imaginary coordinates. -/
lemma isOpen_exercise21NegativeWedge (r ε : ℝ) :
    IsOpen (exercise21NegativeWedge r ε) := by
  have hre : IsOpen {z : ℂ | z.re < 0} :=
    isOpen_lt continuous_re continuous_const
  have him :
      IsOpen {z : ℂ | |z.im| < (ε / r) * (-z.re)} := by
    simpa using
      isOpen_lt (continuous_abs.comp continuous_im) (continuous_const.mul continuous_re.neg)
  -- The slit wedge is exactly the intersection of those two open half-space conditions.
  simpa [exercise21NegativeWedge, Set.setOf_and] using hre.inter him

/-- Helper for Exercise 21: the radial constraints alone define a closed annulus. -/
lemma isClosed_exercise21ClosedAnnulus (r ε : ℝ) :
    IsClosed {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
  -- Both radius inequalities are closed conditions, so their intersection is closed as well.
  simpa [Set.setOf_and] using
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

lemma isClosed_exercise21NegativeWedgeAnnulus (r ε : ℝ) :
    IsClosed (exercise21NegativeWedgeAnnulus r ε) := by
  -- Rewrite the set difference as an intersection with the wedge complement.
  simpa [exercise21NegativeWedgeAnnulus, Set.diff_eq, Set.setOf_and] using
    (isClosed_exercise21ClosedAnnulus r ε).inter
      (isOpen_exercise21NegativeWedge r ε).isClosed_compl

/-- Helper for Exercise 21: every point of the slit annulus has norm at most `r`, so the whole
region lies in the closed ball centered at `0` with radius `r`. -/
lemma exercise21NegativeWedgeAnnulus_subset_closedBall (r ε : ℝ) :
    exercise21NegativeWedgeAnnulus r ε ⊆ Metric.closedBall (0 : ℂ) r := by
  intro z hz
  -- The outer annulus inequality is exactly the closed-ball bound.
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact hz.1.2

/-- Helper for Exercise 21: the slit annulus is compact as a closed subset of the closed ball of
radius `r`. -/
lemma isCompact_exercise21NegativeWedgeAnnulus (r ε : ℝ) :
    IsCompact (exercise21NegativeWedgeAnnulus r ε) := by
  -- The closed-ball owner keeps the compactness proof independent of the slit geometry details.
  refine (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset
    (isClosed_exercise21NegativeWedgeAnnulus r ε) ?_
  exact exercise21NegativeWedgeAnnulus_subset_closedBall r ε

/-- Helper for Exercise 21: the closed annulus owner has frontier exactly the inner and outer
boundary circles. This isolates the radial part of the slit-annulus frontier before the wedge
geometry is reintroduced. -/
lemma exercise21ClosedAnnulus_frontier_eq
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    frontier {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} =
      Metric.sphere (0 : ℂ) r ∪ Metric.sphere (0 : ℂ) ε := by
  have hannulus :
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} =
        Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) ε := by
    ext z
    -- The annulus is the outer closed ball with the inner open ball removed.
    simp [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, sub_zero, not_lt, and_comm]
  rw [hannulus]
  rw [frontier_diff_open_of_isClosed Metric.isClosed_closedBall Metric.isOpen_ball]
  rw [frontier_closedBall', frontier_ball (0 : ℂ) hε.ne']
  have hsphere_outer :
      Metric.sphere (0 : ℂ) r \ Metric.ball (0 : ℂ) ε = Metric.sphere (0 : ℂ) r := by
    ext z
    constructor
    · intro hz
      exact hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      intro hzball
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hzball
      linarith
  have hsphere_inner :
      Metric.closedBall (0 : ℂ) r ∩ Metric.sphere (0 : ℂ) ε = Metric.sphere (0 : ℂ) ε := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      refine ⟨?_, hz⟩
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      linarith
  -- The surviving pieces are exactly the outer and inner boundary circles.
  rw [hsphere_outer, hsphere_inner]

lemma exercise21_upper_lip_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap r ε (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ r ε t.2
    · -- The upper radial segment only changes the radius.
      simpa [Path.segment_apply] using
        (exercise21_lineMap_circleMap_same_angle
          r ε (Real.pi - Real.arctan (ε / r)) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ r ε := by
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric radius parameter back into the segment path parameter.
    simpa [Path.segment_apply] using
      exercise21_lineMap_circleMap_same_angle
        r ε (Real.pi - Real.arctan (ε / r)) t

lemma exercise21_inner_arc_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (((Path.segment (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))).map (continuous_circleMap 0 ε))) =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          t.2
    · -- The mapped angular segment is exactly the circle image of the affine angle parameter.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the angle parameter through the mapped path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

lemma exercise21_lower_lip_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap ε r (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ ε r t.2
    · -- The lower radial segment likewise only changes the radius.
      simpa [Path.segment_apply] using
        (exercise21_lineMap_circleMap_same_angle
          ε r (-Real.pi + Real.arctan (ε / r)) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ ε r := by
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the lower-lip radius parameter back into the segment path parameter.
    simpa [Path.segment_apply] using
      exercise21_lineMap_circleMap_same_angle
        ε r (-Real.pi + Real.arctan (ε / r)) t

lemma exercise21_outer_arc_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (((Path.segment (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))).map (continuous_circleMap 0 r))) =
      (fun φ : ℝ ↦ circleMap 0 r φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          t.2
    · -- The outer arc is the circle image of the affine angle segment.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the angle parameter through the mapped outer path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

theorem exercise21Delta_range_eq_geometric_piece_union
    (r ε : ℝ) :
    Set.range (exercise21Delta r ε) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ∪
        (fun φ : ℝ ↦ circleMap 0 ε φ) ''
          Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r ∪
        (fun φ : ℝ ↦ circleMap 0 r φ) ''
          Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  -- Rewrite the four canonical path-piece ranges into their geometric radius/angle images.
  rw [exercise21Delta_range_eq_four_piece_union]
  dsimp
  -- Rewrite each of the four canonical pieces through its geometric radius/angle image.
  rw [exercise21_upper_lip_range_eq_geometric, exercise21_inner_arc_range_eq_geometric,
    exercise21_lower_lip_range_eq_geometric, exercise21_outer_arc_range_eq_geometric]

lemma exercise21NegativeWedge_upper_lip_mem_frontier
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) :
    circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) ∈ frontier (exercise21NegativeWedge r ε) := by
  let z : ℂ := circleMap 0 ρ (Real.pi - Real.arctan (ε / r))
  have hr : 0 < r := lt_trans hε hεr
  have hratio_pos : 0 < ε / r := div_pos hε hr
  have hre_neg : z.re < 0 := by
    -- The upper lip lies on the negative-real side of the slit.
    simpa [z] using exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ρ) hρ
  have hline : z.im = -((ε / r) * z.re) := by
    -- The upper lip is exactly the upper boundary line of the wedge.
    simpa [z] using exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρ)
  have him_pos : 0 < z.im := by
    have hneg_re_pos : 0 < -z.re := by linarith
    rw [hline]
    nlinarith
  have habs : |z.im| = (ε / r) * (-z.re) := by
    -- On the upper lip the imaginary part is positive, so the absolute value drops.
    rw [abs_of_pos him_pos, hline]
    ring
  have hz_not_mem : z ∉ exercise21NegativeWedge r ε := by
    -- The lip point satisfies the wedge inequality with equality, not strictly.
    intro hz
    have : |z.im| < (ε / r) * (-z.re) := hz.2
    rw [habs] at this
    exact lt_irrefl _ this
  have hz_closure : z ∈ closure (exercise21NegativeWedge r ε) := by
    -- Moving a tiny distance straight downward enters the open wedge.
    refine Metric.mem_closure_iff.2 ?_
    intro δ hδ
    let η : ℝ := min (δ / 2) (z.im / 2)
    have hη_pos : 0 < η := by
      refine lt_min ?_ ?_
      · linarith
      · linarith
    have hη_lt_im : η < z.im := by
      have hhalf_lt : z.im / 2 < z.im := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt
    let w : ℂ := z - (η : ℂ) * Complex.I
    refine ⟨w, ?_, ?_⟩
    · -- The perturbed point still has negative real part and now satisfies the wedge inequality
      -- strictly.
      refine ⟨?_, ?_⟩
      · simpa [w] using hre_neg
      · have hw_im : w.im = z.im - η := by
          simp [w]
        have hw_im_pos : 0 < w.im := by
          rw [hw_im]
          linarith
        calc
          |w.im| = z.im - η := by simpa [hw_im] using (abs_of_pos hw_im_pos)
          _ < z.im := by linarith
          _ = (ε / r) * (-z.re) := by
                rw [hline]
                ring
          _ = (ε / r) * (-w.re) := by simp [w]
    · -- The perturbation size is exactly `η`, so the point can be chosen inside any ball.
      have hη_lt_δ : η < δ := by
        have hη_le : η ≤ δ / 2 := min_le_left _ _
        linarith
      rw [dist_eq_norm]
      have hsub : z - w = (η : ℂ) * Complex.I := by
        simp [w]
      rw [hsub, norm_mul, Complex.norm_I, mul_one]
      simpa [Complex.norm_real, abs_of_nonneg hη_pos.le] using hη_lt_δ
  -- Combine the closure witness with the fact that boundary points of an open set lie outside it.
  rw [frontier_eq_closure_inter_closure]
  refine ⟨hz_closure, ?_⟩
  rw [closure_compl]
  exact fun hz_int ↦ hz_not_mem (interior_subset hz_int)

/-- Helper for Exercise 21: every point on the lower slit lip is also a boundary point of the
removed negative wedge, because moving slightly upward enters the wedge while the boundary value
itself again occurs with equality. -/
lemma exercise21NegativeWedge_lower_lip_mem_frontier
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) :
    circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) ∈ frontier (exercise21NegativeWedge r ε) := by
  let z : ℂ := circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))
  have hr : 0 < r := lt_trans hε hεr
  have hratio_pos : 0 < ε / r := div_pos hε hr
  have hre_neg : z.re < 0 := by
    -- The lower lip lies on the same negative-real side of the slit.
    simpa [z] using exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ρ) hρ
  have hline : z.im = (ε / r) * z.re := by
    -- The lower lip is the lower boundary line of the wedge.
    simpa [z] using exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρ)
  have him_neg : z.im < 0 := by
    have hneg_re_pos : 0 < -z.re := by linarith
    rw [hline]
    nlinarith
  have habs : |z.im| = (ε / r) * (-z.re) := by
    -- On the lower lip the imaginary part is negative, so the absolute value contributes a minus.
    rw [abs_of_neg him_neg, hline]
    ring
  have hz_not_mem : z ∉ exercise21NegativeWedge r ε := by
    -- The lower lip also satisfies the wedge inequality only with equality.
    intro hz
    have : |z.im| < (ε / r) * (-z.re) := hz.2
    rw [habs] at this
    exact lt_irrefl _ this
  have hz_closure : z ∈ closure (exercise21NegativeWedge r ε) := by
    -- Moving a tiny distance straight upward enters the open wedge.
    refine Metric.mem_closure_iff.2 ?_
    intro δ hδ
    let η : ℝ := min (δ / 2) ((-z.im) / 2)
    have hη_pos : 0 < η := by
      refine lt_min ?_ ?_
      · linarith
      · linarith
    have hη_lt_neg_im : η < -z.im := by
      have hhalf_lt : (-z.im) / 2 < -z.im := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt
    let w : ℂ := z + (η : ℂ) * Complex.I
    refine ⟨w, ?_, ?_⟩
    · -- The perturbed point still has negative real part and now satisfies the wedge inequality
      -- strictly.
      refine ⟨?_, ?_⟩
      · simpa [w] using hre_neg
      · have hw_im : w.im = z.im + η := by
          simp [w]
        have hw_im_neg : w.im < 0 := by
          rw [hw_im]
          linarith
        calc
          |w.im| = -(z.im + η) := by simpa [hw_im] using (abs_of_neg hw_im_neg)
          _ < -z.im := by linarith
          _ = (ε / r) * (-z.re) := by
                rw [hline]
                ring
          _ = (ε / r) * (-w.re) := by simp [w]
    · -- The perturbation size is again exactly `η`.
      have hη_lt_δ : η < δ := by
        have hη_le : η ≤ δ / 2 := min_le_left _ _
        linarith
      rw [dist_eq_norm]
      have hsub : z - w = -((η : ℂ) * Complex.I) := by
        simp [w]
      rw [hsub, norm_neg, norm_mul, Complex.norm_I, mul_one]
      simpa [Complex.norm_real, abs_of_nonneg hη_pos.le] using hη_lt_δ
  -- The lower lip is likewise the meeting set of the wedge and its complement.
  rw [frontier_eq_closure_inter_closure]
  refine ⟨hz_closure, ?_⟩
  rw [closure_compl]
  exact fun hz_int ↦ hz_not_mem (interior_subset hz_int)

/-- Helper for Exercise 21: the geometric upper lip piece already lies in the closed-annulus part
of the wedge frontier. This packages the easy inclusion needed before the harder converse rewrite. -/
lemma exercise21NegativeWedge_upper_lip_image_subset_annulus_frontier
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε) := by
  rintro z ⟨ρ, hρ, rfl⟩
  have hρIcc : ρ ∈ Set.Icc ε r := by
    rcases Set.mem_uIcc.mp hρ with hρ' | hρ'
    · linarith [hρ'.1, hρ'.2, hεr]
    · exact hρ'
  refine ⟨?_, ?_⟩
  · -- The radius parameter already places the point in the closed annulus.
    show ε ≤ ‖circleMap 0 ρ (Real.pi - Real.arctan (ε / r))‖ ∧
        ‖circleMap 0 ρ (Real.pi - Real.arctan (ε / r))‖ ≤ r
    rw [norm_circleMap_zero, abs_of_nonneg (le_trans hε.le hρIcc.1)]
    exact hρIcc
  · -- Every upper-lip point is a frontier point of the removed wedge.
    exact exercise21NegativeWedge_upper_lip_mem_frontier r ε ρ hε hεr (lt_of_lt_of_le hε hρIcc.1)

/-- Helper for Exercise 21: the geometric lower lip piece also lies in the closed-annulus part of
the wedge frontier. -/
lemma exercise21NegativeWedge_lower_lip_image_subset_annulus_frontier
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε) := by
  rintro z ⟨ρ, hρ, rfl⟩
  have hρIcc : ρ ∈ Set.Icc ε r := by
    rcases Set.mem_uIcc.mp hρ with hρ' | hρ'
    · exact hρ'
    · linarith [hρ'.1, hρ'.2, hεr]
  refine ⟨?_, ?_⟩
  · -- The lower-lip radius parameter obeys the same annulus bounds.
    show ε ≤ ‖circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))‖ ∧
        ‖circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))‖ ≤ r
    rw [norm_circleMap_zero, abs_of_nonneg (le_trans hε.le hρIcc.1)]
    exact hρIcc
  · -- Every lower-lip point is again a wedge-frontier point.
    exact exercise21NegativeWedge_lower_lip_mem_frontier r ε ρ hε hεr (lt_of_lt_of_le hε hρIcc.1)

/-- Helper for Exercise 21: a point on the upper slit boundary line with negative real part is
the corresponding upper-lip circle point for a unique positive radius. -/
lemma exercise21_eq_circleMap_upper_of_re_neg_line
    (r ε : ℝ) {z : ℂ}
    (hre : z.re < 0) (hline : z.im = -((ε / r) * z.re)) :
    ∃ ρ > 0, z = circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) := by
  let ρ : ℝ := -z.re / Real.cos (Real.arctan (ε / r))
  have hcos_pos : 0 < Real.cos (Real.arctan (ε / r)) := Real.cos_arctan_pos (ε / r)
  have hcos_ne : Real.cos (Real.arctan (ε / r)) ≠ 0 := hcos_pos.ne'
  have hρ_pos : 0 < ρ := by
    -- The boundary-line radius is positive because both `-re z` and `cos (arctan _)` are.
    dsimp [ρ]
    exact div_pos (by linarith) hcos_pos
  refine ⟨ρ, hρ_pos, ?_⟩
  -- Compare the explicit line point with the circle parametrization coordinatewise.
  rw [Complex.ext_iff]
  constructor
  · rw [circleMap_zero_re, Real.cos_pi_sub]
    dsimp [ρ]
    field_simp [hcos_ne]
  · rw [circleMap_zero_im, Real.sin_pi_sub, hline]
    dsimp [ρ]
    field_simp [hcos_ne]
    rw [Real.sin_arctan, Real.cos_arctan]
    ring

/-- Helper for Exercise 21: a point on the lower slit boundary line with negative real part is
the corresponding lower-lip circle point for a unique positive radius. -/
lemma exercise21_eq_circleMap_lower_of_re_neg_line
    (r ε : ℝ) {z : ℂ}
    (hre : z.re < 0) (hline : z.im = (ε / r) * z.re) :
    ∃ ρ > 0, z = circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) := by
  let ρ : ℝ := -z.re / Real.cos (Real.arctan (ε / r))
  have hcos_pos : 0 < Real.cos (Real.arctan (ε / r)) := Real.cos_arctan_pos (ε / r)
  have hcos_ne : Real.cos (Real.arctan (ε / r)) ≠ 0 := hcos_pos.ne'
  have hρ_pos : 0 < ρ := by
    -- The same radius formula works on the lower boundary line.
    dsimp [ρ]
    exact div_pos (by linarith) hcos_pos
  have hsin :
      Real.sin (-Real.pi + Real.arctan (ε / r)) = -Real.sin (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.sin_sub]
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) = -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  refine ⟨ρ, hρ_pos, ?_⟩
  -- The lower-lip parametrization uses the same positive radius with the opposite branch angle.
  rw [Complex.ext_iff]
  constructor
  · rw [circleMap_zero_re, hcos]
    dsimp [ρ]
    field_simp [hcos_ne]
  · rw [circleMap_zero_im, hsin, hline]
    dsimp [ρ]
    field_simp [hcos_ne]
    rw [Real.sin_arctan, Real.cos_arctan]
    ring

/-- Helper for Exercise 21: inside the closed annulus, the wedge-frontier piece is exactly the
union of the two slit lips. This is the source-faithful converse rewrite missing from the global
frontier proof. -/
lemma exercise21NegativeWedgeAnnulus_annulusFrontier_eq_lip_union
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε)) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rcases hz with ⟨hzAnn, hzFront⟩
    have hr : 0 < r := lt_trans hε hεr
    have hκ_pos : 0 < ε / r := div_pos hε hr
    have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hε hzAnn.1
    have hzClosure : z ∈ closure (exercise21NegativeWedge r ε) := by
      rw [(isOpen_exercise21NegativeWedge r ε).frontier_eq, Set.mem_diff] at hzFront
      exact hzFront.1
    have hz_not_mem : z ∉ exercise21NegativeWedge r ε := by
      rw [(isOpen_exercise21NegativeWedge r ε).frontier_eq, Set.mem_diff] at hzFront
      exact hzFront.2
    have hz_re_nonpos : z.re ≤ 0 := by
      -- The wedge lies in the nonpositive-real half-plane, so every closure point does too.
      have hsubset :
          exercise21NegativeWedge r ε ⊆ {w : ℂ | w.re ≤ 0} := by
        intro w hw
        exact hw.1.le
      exact (closure_minimal hsubset (isClosed_le continuous_re continuous_const)) hzClosure
    have hz_abs_le : |z.im| ≤ (ε / r) * (-z.re) := by
      -- The closure also preserves the weak version of the boundary-line inequality.
      have hsubset :
          exercise21NegativeWedge r ε ⊆ {w : ℂ | |w.im| ≤ (ε / r) * (-w.re)} := by
        intro w hw
        exact hw.2.le
      exact
        (closure_minimal hsubset
          (isClosed_le (continuous_abs.comp continuous_im) (continuous_const.mul continuous_re.neg)))
          hzClosure
    have hz_re_ne : z.re ≠ 0 := by
      intro hre_zero
      have him_zero : z.im = 0 := by
        have him_abs_zero : |z.im| = 0 := by
          apply le_antisymm
          · simpa [hre_zero] using hz_abs_le
          · exact abs_nonneg _
        exact abs_eq_zero.mp him_abs_zero
      have hz_zero : z = 0 := by
        apply Complex.ext <;> simp [hre_zero, him_zero]
      exact hnorm_pos.ne' (by simpa [hz_zero])
    have hz_re_neg : z.re < 0 := lt_of_le_of_ne hz_re_nonpos hz_re_ne
    have hz_abs_ge : (ε / r) * (-z.re) ≤ |z.im| := by
      -- If the inequality were still strict, the point would lie inside the open wedge.
      by_contra hlt
      exact hz_not_mem ⟨hz_re_neg, lt_of_not_ge hlt⟩
    have hz_abs_eq : |z.im| = (ε / r) * (-z.re) := le_antisymm hz_abs_le hz_abs_ge
    by_cases him_nonneg : 0 ≤ z.im
    · have him_line : z.im = -((ε / r) * z.re) := by
        -- On the upper branch, the absolute value drops and produces the upper lip line.
        rw [abs_of_nonneg him_nonneg] at hz_abs_eq
        linarith
      rcases exercise21_eq_circleMap_upper_of_re_neg_line r ε hz_re_neg him_line with
        ⟨ρ, hρ_pos, rfl⟩
      left
      refine ⟨ρ, ?_, rfl⟩
      rw [Set.uIcc_of_gt hεr]
      simpa [norm_circleMap_zero, abs_of_nonneg hρ_pos.le] using hzAnn
    · have him_line : z.im = (ε / r) * z.re := by
        -- On the lower branch, the absolute value contributes the sign change.
        rw [abs_of_neg (lt_of_not_ge him_nonneg)] at hz_abs_eq
        linarith
      rcases exercise21_eq_circleMap_lower_of_re_neg_line r ε hz_re_neg him_line with
        ⟨ρ, hρ_pos, rfl⟩
      right
      refine ⟨ρ, ?_, rfl⟩
      rw [Set.uIcc_of_lt hεr]
      simpa [norm_circleMap_zero, abs_of_nonneg hρ_pos.le] using hzAnn
  · intro z hz
    rcases hz with hz | hz
    · exact (exercise21NegativeWedge_upper_lip_image_subset_annulus_frontier r ε hε hεr) hz
    · exact (exercise21NegativeWedge_lower_lip_image_subset_annulus_frontier r ε hε hεr) hz

/-- Helper for Exercise 21: the two slit-lip geometric images already lie in the normalized split
frontier expression for the slit annulus. This isolates the wedge-frontier half of the source
picture before the surviving-circle classification is added. -/
lemma exercise21NegativeWedgeAnnulus_frontier_split_contains_lips
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ((fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r) ⊆
      ((Metric.sphere (0 : ℂ) r ∪ Metric.sphere (0 : ℂ) ε) \ exercise21NegativeWedge r ε) ∪
        ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε)) := by
  intro z hz
  rcases hz with hz | hz
  · -- The upper lip already lands in the wedge-frontier summand of the split frontier formula.
    exact Or.inr
      ((exercise21NegativeWedge_upper_lip_image_subset_annulus_frontier r ε hε hεr) hz)
  · -- The same packaging applies to the lower slit lip.
    exact Or.inr
      ((exercise21NegativeWedge_lower_lip_image_subset_annulus_frontier r ε hε hεr) hz)

/-- Helper for Exercise 21: on the nonnegative half of `[-π, π]`, surviving the deleted wedge is
equivalent to staying below the upper slit angle `π - arctan (ε / r)`. -/
lemma exercise21_surviving_angle_nonneg_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi) :
    (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ))) ↔
      φ ≤ Real.pi - Real.arctan (ε / r) := by
  let κ : ℝ := ε / r
  let θ : ℝ := Real.arctan κ
  have hr : 0 < r := lt_trans hε hεr
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact div_pos hε hr
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact Real.arctan_pos.mpr hκ_pos
  have hθ_lt : θ < Real.pi / 2 := by
    dsimp [θ]
    exact Real.arctan_lt_pi_div_two κ
  by_cases hhalf : φ ≤ Real.pi / 2
  · have hcos_nonneg : 0 ≤ Real.cos φ := by
      -- On the first half of `[0, π]`, the cosine never enters the deleted wedge.
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1], hhalf⟩
    constructor
    · -- The upper slit angle is strictly larger than `π / 2`, so this branch is automatic.
      intro _
      dsimp [θ] at hθ_lt ⊢
      linarith
    · -- A nonnegative cosine rules out the wedge inequality immediately.
      intro _
      rintro ⟨hcos_neg, _⟩
      exact not_lt_of_ge hcos_nonneg hcos_neg
  · let ψ : ℝ := Real.pi - φ
    have hhalf_lt : Real.pi / 2 < φ := lt_of_not_ge hhalf
    have hψ_Ioo : ψ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [ψ]
      constructor <;> linarith [hφ.2]
    have hsin_nonneg : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφ
    have habs : |Real.sin φ| = Real.sin φ := abs_of_nonneg hsin_nonneg
    have hnegcos_pos : 0 < -Real.cos φ := by
      -- On the second half of `[0, π]`, reflect across `π / 2` to recover a positive cosine.
      have hcosψ_pos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo hψ_Ioo
      simpa [ψ, Real.cos_pi_sub] using hcosψ_pos
    have hwedge_iff :
        (Real.cos φ < 0 ∧ |Real.sin φ| < κ * (-Real.cos φ)) ↔ Real.tan ψ < κ := by
      constructor
      · intro hbad
        have hdiv : Real.sin φ / (-Real.cos φ) < κ := by
          have hmul : Real.sin φ < κ * (-Real.cos φ) := by
            simpa [habs] using hbad.2
          exact (div_lt_iff₀ hnegcos_pos).2 <| by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        -- Re-express the slope inequality on the reflected acute angle.
        simpa [ψ, Real.tan_eq_sin_div_cos, Real.sin_pi_sub, Real.cos_pi_sub] using hdiv
      · intro htan
        refine ⟨?_, ?_⟩
        · linarith
        have hdiv : Real.sin φ / (-Real.cos φ) < κ := by
          simpa [ψ, Real.tan_eq_sin_div_cos, Real.sin_pi_sub, Real.cos_pi_sub] using htan
        have hmul : Real.sin φ < κ * (-Real.cos φ) := (div_lt_iff₀ hnegcos_pos).1 hdiv
        simpa [habs] using hmul
    have htan_iff : Real.tan ψ < κ ↔ ψ < θ := by
      -- Both angles lie in `(-π/2, π/2)`, so `tan` is strictly monotone here.
      rw [← Real.tan_arctan κ]
      exact Real.strictMonoOn_tan.lt_iff_lt hψ_Ioo (Real.arctan_mem_Ioo κ)
    -- Convert the reflected-angle inequality back to the original angle `φ`.
    calc
      (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < κ * (-Real.cos φ))) ↔ ¬ Real.tan ψ < κ := by
        rw [hwedge_iff]
      _ ↔ ¬ ψ < θ := by rw [htan_iff]
      _ ↔ θ ≤ ψ := by rw [not_lt]
      _ ↔ φ ≤ Real.pi - Real.arctan (ε / r) := by
        constructor <;> intro h
        · dsimp [ψ, θ] at h ⊢
          linarith
        · dsimp [ψ, θ] at h ⊢
          linarith

/-- Helper for Exercise 21: inside `[-π, π]`, surviving the deleted wedge is exactly membership in
the angular interval between the two slit-boundary angles. -/
lemma exercise21_surviving_angle_mem_uIcc_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (-Real.pi) Real.pi) :
    (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ))) ↔
      φ ∈ Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  let θ : ℝ := Real.arctan (ε / r)
  let α : ℝ := Real.pi - θ
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact Real.arctan_pos.mpr (div_pos hε hr)
  have hθ_lt : θ < Real.pi / 2 := by
    dsimp [θ]
    exact Real.arctan_lt_pi_div_two (ε / r)
  have hα_pos : 0 < α := by
    dsimp [α]
    linarith
  have hlow : -Real.pi + θ < Real.pi - θ := by
    dsimp [θ]
    linarith [Real.pi_pos, hθ_lt]
  by_cases hφ_nonneg : 0 ≤ φ
  · have hφ_nonneg' : φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hφ_nonneg, hφ.2⟩
    have hmem :
        φ ∈ Set.uIcc (-Real.pi + θ) (Real.pi - θ) ↔ φ ≤ α := by
      rw [Set.uIcc_of_lt hlow]
      constructor
      · intro hz
        simpa [α, θ] using hz.2
      · intro hz
        refine ⟨?_, ?_⟩
        · dsimp [α, θ] at hz ⊢
          linarith
        · simpa [α, θ] using hz
    -- On the nonnegative half-line, membership in the surviving interval is exactly the upper bound.
    simpa [θ, α] using
      (exercise21_surviving_angle_nonneg_iff r ε hε hεr hφ_nonneg').trans hmem.symm
  · let ψ : ℝ := -φ
    have hφ_neg : φ < 0 := lt_of_not_ge hφ_nonneg
    have hψ_nonneg : ψ ∈ Set.Icc (0 : ℝ) Real.pi := by
      dsimp [ψ]
      constructor
      · linarith
      · have hupper : -φ ≤ Real.pi := by
          linarith [hφ.1]
        simpa using hupper
    have hsymm :
        (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ))) ↔
          (¬ (Real.cos ψ < 0 ∧ |Real.sin ψ| < (ε / r) * (-Real.cos ψ))) := by
      -- The deleted wedge is symmetric with respect to reflection across the real axis.
      dsimp [ψ]
      simp [Real.cos_neg, Real.sin_neg]
    have hmem :
        φ ∈ Set.uIcc (-Real.pi + θ) (Real.pi - θ) ↔ ψ ≤ α := by
      rw [Set.uIcc_of_lt hlow]
      constructor
      · intro hz
        have hlower : -Real.pi + θ ≤ φ := hz.1
        dsimp [ψ, α, θ]
        linarith
      · intro hz
        refine ⟨?_, ?_⟩
        · dsimp [ψ, α, θ] at hz ⊢
          linarith
        · dsimp [α, θ]
          have hφα : φ < α := by
            linarith [hφ_neg, hα_pos]
          exact hφα.le
    -- Reflect negative angles to the nonnegative branch handled above.
    exact hsymm.trans <|
      (exercise21_surviving_angle_nonneg_iff r ε hε hεr hψ_nonneg).trans hmem.symm

/-- Helper for Exercise 21: a positive-radius circle point survives the deleted wedge exactly when
its angle lies in the surviving principal-argument interval. -/
lemma exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (-Real.pi) Real.pi) :
    circleMap 0 ρ φ ∉ exercise21NegativeWedge r ε ↔
      φ ∈ Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  have hmem :
      circleMap 0 ρ φ ∈ exercise21NegativeWedge r ε ↔
        (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ)) := by
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · -- Positive radius lets us divide the real-part inequality by `ρ`.
        have hre : ρ * Real.cos φ < 0 := by
          simpa [exercise21NegativeWedge, circleMap_zero_re] using hz.1
        nlinarith
      · have him :
            |ρ * Real.sin φ| < (ε / r) * (-(ρ * Real.cos φ)) := by
          simpa [exercise21NegativeWedge, circleMap_zero_re, circleMap_zero_im]
            using hz.2
        have him' : ρ * |Real.sin φ| < ρ * ((ε / r) * (-Real.cos φ)) := by
          simpa [abs_mul, abs_of_pos hρ, mul_assoc, mul_left_comm, mul_comm] using him
        nlinarith
    · intro hz
      refine ⟨?_, ?_⟩
      · -- Conversely, multiplying by the positive radius recovers the circle-point inequality.
        have hre : ρ * Real.cos φ < 0 := by
          nlinarith
        simpa [circleMap_zero_re] using hre
      · have him' : ρ * |Real.sin φ| < ρ * ((ε / r) * (-Real.cos φ)) :=
          by nlinarith
        simpa [circleMap_zero_re, circleMap_zero_im, abs_mul, abs_of_pos hρ,
          mul_assoc, mul_left_comm, mul_comm] using him'
  -- Reduce the circle-point statement to the pure angular classifier.
  rw [show circleMap 0 ρ φ ∉ exercise21NegativeWedge r ε ↔
      ¬ circleMap 0 ρ φ ∈ exercise21NegativeWedge r ε by simp]
  rw [hmem]
  exact exercise21_surviving_angle_mem_uIcc_iff r ε hε hεr hφ

/-- Helper for Exercise 21: on any positive-radius circle centered at the origin, deleting the
negative wedge leaves exactly the image of the surviving argument interval. -/
lemma exercise21NegativeWedge_sphere_diff_eq_arc_image
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) :
    Metric.sphere (0 : ℂ) ρ \ exercise21NegativeWedge r ε =
      (fun φ : ℝ ↦ circleMap 0 ρ φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  ext z
  constructor
  · intro hz
    have hz_sphere : z ∈ Metric.sphere (0 : ℂ) ρ := hz.1
    have hnorm : ‖z‖ = ρ := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz_sphere
      simpa [abs_of_pos hρ] using hz_sphere
    have hz_eq : circleMap 0 ρ z.arg = z := by
      -- Reconstruct the sphere point from its norm and principal argument.
      apply Complex.ext_norm_arg
      · simpa [norm_circleMap_zero, abs_of_pos hρ] using hnorm.symm
      · rw [circleMap_zero, Complex.arg_real_mul _ hρ, Complex.arg_exp_mul_I, Complex.toIocMod_arg]
    have harg : z.arg ∈ Set.Icc (-Real.pi) Real.pi := ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    refine ⟨z.arg, ?_, hz_eq⟩
    have hz_not_mem : circleMap 0 ρ z.arg ∉ exercise21NegativeWedge r ε := by
      simpa [hz_eq] using hz.2
    exact
      (exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
        r ε ρ hε hεr hρ harg).1 hz_not_mem
  · rintro ⟨φ, hφ, rfl⟩
    have hθ_pos : 0 < Real.arctan (ε / r) := by
      have hr : 0 < r := lt_trans hε hεr
      exact Real.arctan_pos.mpr (div_pos hε hr)
    have hinterval :
        -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
      have hlt_pi : Real.arctan (ε / r) < Real.pi := by
        linarith [Real.arctan_lt_pi_div_two (ε / r), Real.pi_pos]
      have hleft : -Real.pi + Real.arctan (ε / r) < 0 := by
        linarith
      have hright : 0 ≤ Real.pi - Real.arctan (ε / r) := by
        linarith [Real.arctan_lt_pi_div_two (ε / r)]
      exact lt_of_lt_of_le hleft hright
    have hφIcc : φ ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIcc_of_lt hinterval] at hφ
      refine ⟨?_, ?_⟩
      · exact le_trans (by linarith [hθ_pos]) hφ.1
      · exact le_trans hφ.2 (by linarith [hθ_pos])
    refine ⟨?_, ?_⟩
    · exact circleMap_mem_sphere 0 hρ.le φ
    · exact
        (exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
          r ε ρ hε hεr hρ hφIcc).2 hφ

/-- Helper for Exercise 21: the surviving part of the outer boundary circle is exactly the outer
arc image used in the source contour decomposition. -/
lemma exercise21NegativeWedge_outerSphere_diff_eq_outer_arc_image
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Metric.sphere (0 : ℂ) r \ exercise21NegativeWedge r ε =
      (fun φ : ℝ ↦ circleMap 0 r φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  -- Specialize the positive-radius circle classifier to the outer radius `r`.
  exact exercise21NegativeWedge_sphere_diff_eq_arc_image r ε r hε hεr (lt_trans hε hεr)

/-- Helper for Exercise 21: the surviving part of the inner boundary circle is exactly the inner
arc image used in the source contour decomposition. -/
lemma exercise21NegativeWedge_innerSphere_diff_eq_inner_arc_image
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Metric.sphere (0 : ℂ) ε \ exercise21NegativeWedge r ε =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) := by
  -- The inner arc uses the same surviving angular interval, but written in the clockwise order.
  simpa [Set.uIcc, min_comm, max_comm] using
    (exercise21NegativeWedge_sphere_diff_eq_arc_image r ε ε hε hεr hε)

/-- Helper for Exercise 21: once the two fixed-radius classifiers are available, the surviving
circle part of the slit-annulus frontier is exactly the union of the two circle-arc images. -/
lemma exercise21NegativeWedgeAnnulus_surviving_circles_eq_arc_union
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ((Metric.sphere (0 : ℂ) r ∪ Metric.sphere (0 : ℂ) ε) \ exercise21NegativeWedge r ε) =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) ∪
      (fun φ : ℝ ↦ circleMap 0 r φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  ext z
  constructor
  · intro hz
    have hz_not_mem : z ∉ exercise21NegativeWedge r ε := hz.2
    rcases hz.1 with hz_outer | hz_inner
    · -- A surviving outer-circle point belongs to the outer arc image.
      right
      simpa [exercise21NegativeWedge_outerSphere_diff_eq_outer_arc_image r ε hε hεr] using
        (show z ∈ Metric.sphere (0 : ℂ) r \ exercise21NegativeWedge r ε from
          ⟨hz_outer, hz_not_mem⟩)
    · -- A surviving inner-circle point belongs to the inner arc image.
      left
      simpa [exercise21NegativeWedge_innerSphere_diff_eq_inner_arc_image r ε hε hεr] using
        (show z ∈ Metric.sphere (0 : ℂ) ε \ exercise21NegativeWedge r ε from
          ⟨hz_inner, hz_not_mem⟩)
  · rintro (hz | hz)
    · -- Repackage the inner arc image back into the surviving inner sphere.
      have hz' : z ∈ Metric.sphere (0 : ℂ) ε \ exercise21NegativeWedge r ε := by
        simpa [exercise21NegativeWedge_innerSphere_diff_eq_inner_arc_image r ε hε hεr] using hz
      exact ⟨Or.inr hz'.1, hz'.2⟩
    · -- Repackage the outer arc image back into the surviving outer sphere.
      have hz' : z ∈ Metric.sphere (0 : ℂ) r \ exercise21NegativeWedge r ε := by
        simpa [exercise21NegativeWedge_outerSphere_diff_eq_outer_arc_image r ε hε hεr] using hz
      exact ⟨Or.inl hz'.1, hz'.2⟩

/-- Helper for Exercise 21: the frontier of the slit annulus is exactly the range of the explicit
keyhole contour. -/
theorem exercise21NegativeWedgeAnnulus_frontier_eq_range
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    frontier (exercise21NegativeWedgeAnnulus r ε) = Set.range (exercise21Delta r ε) := by
  -- Split the slit-annulus frontier into the surviving circles and the wedge-frontier lips.
  rw [show exercise21NegativeWedgeAnnulus r ε =
      ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} \ exercise21NegativeWedge r ε) by
        rfl]
  rw [frontier_diff_open_of_isClosed
      (isClosed_exercise21ClosedAnnulus r ε) (isOpen_exercise21NegativeWedge r ε)]
  -- Rewrite the radial frontier and the slit-frontier piece into the four geometric contour parts.
  rw [exercise21ClosedAnnulus_frontier_eq r ε hε hεr,
    exercise21NegativeWedgeAnnulus_surviving_circles_eq_arc_union r ε hε hεr,
    exercise21NegativeWedgeAnnulus_annulusFrontier_eq_lip_union r ε hε hεr,
    exercise21Delta_range_eq_geometric_piece_union]
  simp [Set.union_assoc, Set.union_left_comm, Set.union_comm]

