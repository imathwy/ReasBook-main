import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2».FiniteExcisionBoundary
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».ShiftedLogResidueData
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeRange

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: the open positive wedge removed from the annulus in the
source-faithful fixed-parameter model of the keyhole contour. -/
abbrev positiveAxisWedge (R ε : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ |z.im| < (ε / R) * z.re}

/-- Helper for Remark III.6-extra-7: the compact wedge-annulus whose frontier should match
`positiveAxisKeyhole R ε`. -/
abbrev positiveAxisWedgeAnnulus (R ε : ℝ) : Set ℂ :=
  {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} \ positiveAxisWedge R ε

/-- Helper for Remark III.6-extra-7: the removed positive wedge is open because it is cut out by
two strict inequalities in the real and imaginary coordinates. -/
lemma isOpen_positiveAxisWedge (R ε : ℝ) :
    IsOpen (positiveAxisWedge R ε) := by
  have hre : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have him : IsOpen {z : ℂ | |z.im| < (ε / R) * z.re} := by
    simpa using
      isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)
  -- The slit wedge is exactly the intersection of the positive-real half-space with the
  -- strict slope inequality.
  simpa [positiveAxisWedge, Set.setOf_and] using hre.inter him

/-- Helper for Remark III.6-extra-7: the slit wedge-annulus is closed because it is a closed
annulus with the open positive wedge removed. -/
lemma isClosed_positiveAxisWedgeAnnulus (R ε : ℝ) :
    IsClosed (positiveAxisWedgeAnnulus R ε) := by
  have hclosed_annulus : IsClosed {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    simpa [Set.setOf_and] using
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  -- Rewrite the set difference as an intersection with the wedge complement.
  simpa [positiveAxisWedgeAnnulus, Set.diff_eq, Set.setOf_and] using
    hclosed_annulus.inter (isOpen_positiveAxisWedge R ε).isClosed_compl

/-- Helper for Remark III.6-extra-7: every point of the slit wedge-annulus has norm at most `R`,
so the whole region lies in the closed ball centered at `0` with radius `R`. -/
lemma positiveAxisWedgeAnnulus_subset_closedBall (R ε : ℝ) :
    positiveAxisWedgeAnnulus R ε ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  -- The outer annulus inequality is exactly the closed-ball bound.
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact hz.1.2

/-- Helper for Remark III.6-extra-7: the slit wedge-annulus is compact as a closed subset of the
closed ball of radius `R`. -/
lemma isCompact_positiveAxisWedgeAnnulus (R ε : ℝ) :
    IsCompact (positiveAxisWedgeAnnulus R ε) := by
  -- The closed-ball owner keeps the compactness proof independent of the slit geometry details.
  refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    (isClosed_positiveAxisWedgeAnnulus R ε) ?_
  exact positiveAxisWedgeAnnulus_subset_closedBall R ε

/-- Helper for Remark III.6-extra-7: once the positive wedge is removed from the annulus, every
remaining point avoids the shifted branch cut `[0, ∞)`, so the whole wedge-annulus lies in the
domain of `z ↦ Complex.log (-z)`. -/
lemma positiveAxisWedgeAnnulus_subset_shiftedLogDomain
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    positiveAxisWedgeAnnulus R ε ⊆ shiftedLogDomain := by
  intro z hz
  rcases hz with ⟨hzAnnulus, hzNotWedge⟩
  have hR : 0 < R := lt_trans hε hεR
  have hz_ne_zero : z ≠ 0 := by
    -- The annulus constraints force `‖z‖ ≥ ε > 0`, so the center is excluded.
    intro hz0
    have hnorm_nonpos : ε ≤ 0 := by
      simpa [hz0] using hzAnnulus.1
    linarith
  change -z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hz_im : z.im = 0
  · -- On the real axis, being outside the removed positive wedge forces the real part to be
    -- negative, which exactly means `-z` lies in the principal slit plane.
    by_cases hz_re_pos : 0 < z.re
    · have hz_mem_wedge : z ∈ positiveAxisWedge R ε := by
        refine ⟨hz_re_pos, ?_⟩
        have hslope : 0 < (ε / R) * z.re := by
          exact mul_pos (div_pos hε hR) hz_re_pos
        simpa [positiveAxisWedge, hz_im, abs_zero] using hslope
      exact (hzNotWedge hz_mem_wedge).elim
    · have hz_re_ne : z.re ≠ 0 := by
        intro hz_re
        apply hz_ne_zero
        apply Complex.ext <;> simp [hz_re, hz_im]
      have hz_re_neg : z.re < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hz_re_pos) (by simpa [eq_comm] using hz_re_ne)
      exact Or.inl (by simpa using neg_pos.mpr hz_re_neg)
  · -- Away from the real axis, the shifted branch is already regular because `-z` is not on the
    -- slit.
    exact Or.inr (by simpa using hz_im)

/-- Helper for Remark III.6-extra-7: the closed annulus owner has frontier exactly the inner and
outer boundary circles. This isolates the radial part of the slit-annulus frontier before the
positive-axis wedge geometry is reintroduced. -/
lemma positiveAxisClosedAnnulus_frontier_eq
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    frontier {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} =
      Metric.sphere (0 : ℂ) R ∪ Metric.sphere (0 : ℂ) ε := by
  have hannulus :
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} =
        Metric.closedBall (0 : ℂ) R \ Metric.ball (0 : ℂ) ε := by
    -- Rewrite the annulus as the outer closed ball with the inner open ball removed.
    ext z
    simp [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, sub_zero, not_lt, and_comm]
  rw [hannulus]
  rw [frontier_diff_open_of_isClosed Metric.isClosed_closedBall Metric.isOpen_ball]
  rw [frontier_closedBall', frontier_ball (0 : ℂ) hε.ne']
  have hsphere_outer :
      Metric.sphere (0 : ℂ) R \ Metric.ball (0 : ℂ) ε = Metric.sphere (0 : ℂ) R := by
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
      Metric.closedBall (0 : ℂ) R ∩ Metric.sphere (0 : ℂ) ε = Metric.sphere (0 : ℂ) ε := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      refine ⟨?_, hz⟩
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      linarith
  -- The surviving radial pieces are exactly the outer and inner boundary circles.
  rw [hsphere_outer, hsphere_inner]

/-- Helper for Remark III.6-extra-7: every point on the upper slit lip is a boundary point of the
removed positive wedge, because moving slightly downward enters the wedge while the lip itself
satisfies the wedge inequality only with equality. -/
lemma positiveAxisWedge_upper_lip_mem_frontier
    (R ε ρ : ℝ) (hε : 0 < ε) (hεR : ε < R) (hρ : 0 < ρ) :
    circleMap 0 ρ (positiveAxisKeyholeAngle R ε) ∈ frontier (positiveAxisWedge R ε) := by
  let z : ℂ := circleMap 0 ρ (positiveAxisKeyholeAngle R ε)
  have hR : 0 < R := lt_trans hε hεR
  have hre_pos : 0 < z.re := by
    -- The upper lip lies on the positive-real side of the slit.
    simpa [z] using positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ρ) hρ
  have hline : z.im = (ε / R) * z.re := by
    -- The upper lip is exactly the upper boundary line of the wedge.
    simpa [z] using positiveAxisKeyhole_upper_lip_line R ε ρ
  have him_pos : 0 < z.im := by
    rw [hline]
    exact mul_pos (div_pos hε hR) hre_pos
  have habs : |z.im| = (ε / R) * z.re := by
    -- On the upper lip the imaginary part is positive, so the absolute value drops.
    rw [abs_of_pos him_pos, hline]
  have hz_not_mem : z ∉ positiveAxisWedge R ε := by
    -- The upper lip satisfies the wedge inequality with equality, not strictly.
    intro hz
    have : |z.im| < (ε / R) * z.re := hz.2
    rw [habs] at this
    exact lt_irrefl _ this
  have hz_closure : z ∈ closure (positiveAxisWedge R ε) := by
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
    · -- The perturbed point still has positive real part and now satisfies the wedge inequality
      -- strictly.
      refine ⟨?_, ?_⟩
      · simpa [w] using hre_pos
      · have hw_im : w.im = z.im - η := by
          simp [w]
        have hw_im_pos : 0 < w.im := by
          rw [hw_im]
          linarith
        calc
          |w.im| = z.im - η := by simpa [hw_im] using (abs_of_pos hw_im_pos)
          _ < z.im := by linarith
          _ = (ε / R) * z.re := hline
          _ = (ε / R) * w.re := by simp [w]
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

/-- Helper for Remark III.6-extra-7: every point on the lower slit lip is likewise a boundary
point of the removed positive wedge, because moving slightly upward enters the wedge while the lip
itself again satisfies the wedge inequality only with equality. -/
lemma positiveAxisWedge_lower_lip_mem_frontier
    (R ε ρ : ℝ) (hε : 0 < ε) (hεR : ε < R) (hρ : 0 < ρ) :
    circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) ∈ frontier (positiveAxisWedge R ε) := by
  let z : ℂ := circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)
  have hR : 0 < R := lt_trans hε hεR
  have hre_pos : 0 < z.re := by
    -- The lower lip stays on the same positive-real side of the slit.
    simpa [z] using positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ρ) hρ
  have hline : z.im = -((ε / R) * z.re) := by
    -- The lower lip is exactly the lower boundary line of the wedge.
    simpa [z] using positiveAxisKeyhole_lower_lip_line R ε ρ
  have him_neg : z.im < 0 := by
    rw [hline]
    exact neg_neg_of_pos (mul_pos (div_pos hε hR) hre_pos)
  have habs : |z.im| = (ε / R) * z.re := by
    -- On the lower lip the absolute value contributes a minus sign.
    rw [abs_of_neg him_neg, hline]
    ring
  have hz_not_mem : z ∉ positiveAxisWedge R ε := by
    -- The lower lip also satisfies the wedge inequality only with equality.
    intro hz
    have : |z.im| < (ε / R) * z.re := hz.2
    rw [habs] at this
    exact lt_irrefl _ this
  have hz_closure : z ∈ closure (positiveAxisWedge R ε) := by
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
    · -- The perturbed point still has positive real part and now satisfies the wedge inequality
      -- strictly.
      refine ⟨?_, ?_⟩
      · simpa [w] using hre_pos
      · have hw_im : w.im = z.im + η := by
          simp [w]
        have hw_im_neg : w.im < 0 := by
          rw [hw_im]
          linarith
        calc
          |w.im| = -(z.im + η) := by simpa [hw_im] using (abs_of_neg hw_im_neg)
          _ < -z.im := by linarith
          _ = (ε / R) * z.re := by
                rw [hline]
                ring
          _ = (ε / R) * w.re := by simp [w]
    · -- The perturbation size is again exactly `η`.
      have hη_lt_δ : η < δ := by
        have hη_le : η ≤ δ / 2 := min_le_left _ _
        linarith
      rw [dist_eq_norm]
      have hsub : z - w = -((η : ℂ) * Complex.I) := by
        simp [w]
      rw [hsub, norm_neg, norm_mul, Complex.norm_I, mul_one]
      simpa [Complex.norm_real, abs_of_nonneg hη_pos.le] using hη_lt_δ
  -- The lower lip is again the meeting set of the wedge and its complement.
  rw [frontier_eq_closure_inter_closure]
  refine ⟨hz_closure, ?_⟩
  rw [closure_compl]
  exact fun hz_int ↦ hz_not_mem (interior_subset hz_int)

/-- Helper for Remark III.6-extra-7: the geometric upper-lip image already lies in the annulus
part of the wedge frontier. This packages the radial control and the wedge-frontier witness
before the global frontier theorem recombines the four contour pieces. -/
lemma positiveAxisWedge_upper_lip_image_subset_annulus_frontier
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeUpperAngle R ε)) '' Set.uIcc R ε ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} ∩ frontier (positiveAxisWedge R ε) := by
  rintro z ⟨ρ, hρ, rfl⟩
  have hρIcc : ρ ∈ Set.Icc ε R := by
    rcases Set.mem_uIcc.mp hρ with hρ' | hρ'
    · linarith [hρ'.1, hρ'.2, hεR]
    · exact hρ'
  refine ⟨?_, ?_⟩
  · -- The radius parameter already puts the point on the closed annulus.
    show ε ≤ ‖circleMap 0 ρ (positiveAxisKeyholeUpperAngle R ε)‖ ∧
        ‖circleMap 0 ρ (positiveAxisKeyholeUpperAngle R ε)‖ ≤ R
    rw [norm_circleMap_zero, abs_of_nonneg (le_trans hε.le hρIcc.1)]
    exact hρIcc
  · -- Every upper-lip point is a wedge-frontier point.
    exact positiveAxisWedge_upper_lip_mem_frontier
      R ε ρ hε hεR (lt_of_lt_of_le hε hρIcc.1)

/-- Helper for Remark III.6-extra-7: the geometric lower-lip image likewise lies in the annulus
part of the wedge frontier. The only transport is the repaired lower-angle spelling. -/
lemma positiveAxisWedge_lower_lip_image_subset_annulus_frontier
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε)) '' Set.uIcc ε R ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} ∩ frontier (positiveAxisWedge R ε) := by
  rintro z ⟨ρ, hρ, rfl⟩
  have hρIcc : ρ ∈ Set.Icc ε R := by
    rcases Set.mem_uIcc.mp hρ with hρ' | hρ'
    · exact hρ'
    · linarith [hρ'.1, hρ'.2, hεR]
  refine ⟨?_, ?_⟩
  · -- The radius parameter again stays between `ε` and `R`.
    show ε ≤ ‖circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε)‖ ∧
        ‖circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε)‖ ≤ R
    rw [norm_circleMap_zero, abs_of_nonneg (le_trans hε.le hρIcc.1)]
    exact hρIcc
  · -- Rewrite the repaired lower angle back to the already-proved frontier witness.
    simpa [positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R ε ρ] using
      (positiveAxisWedge_lower_lip_mem_frontier
        R ε ρ hε hεR (lt_of_lt_of_le hε hρIcc.1))

/-- Helper for Remark III.6-extra-7: a point on the upper slit boundary line with positive real
part is the corresponding upper-lip circle point for a unique positive radius. -/
lemma positiveAxis_eq_circleMap_upper_of_re_pos_line
    (R ε : ℝ) {z : ℂ}
    (hre : 0 < z.re) (hline : z.im = (ε / R) * z.re) :
    ∃ ρ > 0, z = circleMap 0 ρ (positiveAxisKeyholeUpperAngle R ε) := by
  let ρ : ℝ := z.re / Real.cos (Real.arctan (ε / R))
  have hcos_pos : 0 < Real.cos (Real.arctan (ε / R)) := Real.cos_arctan_pos (ε / R)
  have hcos_ne : Real.cos (Real.arctan (ε / R)) ≠ 0 := hcos_pos.ne'
  have hρ_pos : 0 < ρ := by
    -- The radius is positive because both the real part and the cosine denominator are positive.
    dsimp [ρ]
    exact div_pos hre hcos_pos
  refine ⟨ρ, hρ_pos, ?_⟩
  -- Compare the explicit line point with the circle parametrization coordinatewise.
  rw [Complex.ext_iff]
  constructor
  · rw [circleMap_zero_re, positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle]
    dsimp [ρ]
    field_simp [hcos_ne]
  · rw [circleMap_zero_im, positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle, hline]
    dsimp [ρ]
    field_simp [hcos_ne]
    rw [Real.sin_arctan, Real.cos_arctan]
    ring

/-- Helper for Remark III.6-extra-7: a point on the lower slit boundary line with positive real
part is the corresponding repaired lower-lip circle point for a unique positive radius. -/
lemma positiveAxis_eq_circleMap_lower_of_re_pos_line
    (R ε : ℝ) {z : ℂ}
    (hre : 0 < z.re) (hline : z.im = -((ε / R) * z.re)) :
    ∃ ρ > 0, z = circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε) := by
  let ρ : ℝ := z.re / Real.cos (Real.arctan (ε / R))
  have hcos_pos : 0 < Real.cos (Real.arctan (ε / R)) := Real.cos_arctan_pos (ε / R)
  have hcos_ne : Real.cos (Real.arctan (ε / R)) ≠ 0 := hcos_pos.ne'
  have hρ_pos : 0 < ρ := by
    -- The same radius formula works on the reflected lower boundary line.
    dsimp [ρ]
    exact div_pos hre hcos_pos
  have hold :
      z = circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) := by
    rw [Complex.ext_iff]
    constructor
    · rw [circleMap_zero_re, positiveAxisKeyholeAngle, Real.cos_neg]
      dsimp [ρ]
      field_simp [hcos_ne]
    · rw [circleMap_zero_im, positiveAxisKeyholeAngle, hline]
      dsimp [ρ]
      field_simp [hcos_ne]
      rw [Real.sin_neg, Real.sin_arctan, Real.cos_arctan]
      ring
  refine ⟨ρ, hρ_pos, ?_⟩
  -- Rewrite the old lower-angle point to the repaired `2π - θ` spelling used by the contour.
  simpa [positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R ε ρ] using hold

/-- Helper for Remark III.6-extra-7: on the upper half of the circle, surviving the deleted wedge
is exactly the lower-bound condition `θ ≤ φ`. This isolates the one-sided angular comparison used
later to classify the surviving major arc. -/
lemma positiveAxis_surviving_angle_on_upper_half_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi) :
    (¬ (0 < Real.cos φ ∧ |Real.sin φ| < (ε / R) * Real.cos φ)) ↔
      positiveAxisKeyholeUpperAngle R ε ≤ φ := by
  let κ : ℝ := ε / R
  let θ : ℝ := positiveAxisKeyholeUpperAngle R ε
  have hθ :
      0 < θ ∧ θ < Real.pi / 2 := by
    simpa [θ, positiveAxisKeyholeUpperAngle] using
      positiveAxisKeyhole_angle_bounds hε hεR
  by_cases hhalf : φ ≤ Real.pi / 2
  · constructor
    · intro hnot
      by_contra hlt
      have hlt' : φ < θ := lt_of_not_ge hlt
      have hφIoo : φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor
        · linarith [hφ.1]
        · exact lt_trans hlt' hθ.2
      have hcos_pos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo hφIoo
      have hsin_nonneg : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφ
      have htan_lt : Real.tan φ < κ := by
        rw [← Real.tan_arctan κ]
        refine (Real.strictMonoOn_tan.lt_iff_lt hφIoo (Real.arctan_mem_Ioo κ)).2 ?_
        simpa [κ, θ, positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle] using hlt
      have hdiv : Real.sin φ / Real.cos φ < κ := by
        simpa [Real.tan_eq_sin_div_cos, κ] using htan_lt
      have hmul : Real.sin φ < κ * Real.cos φ := (div_lt_iff₀ hcos_pos).1 hdiv
      apply hnot
      refine ⟨hcos_pos, ?_⟩
      simpa [abs_of_nonneg hsin_nonneg, κ] using hmul
    · intro hθle
      rintro ⟨hcos_pos, hsin_lt⟩
      have hhalf' : φ < Real.pi / 2 := by
        by_contra hnotlt
        have hge : Real.pi / 2 ≤ φ := le_of_not_gt hnotlt
        have hcos_nonneg : 0 ≤ Real.cos (Real.pi - φ) := by
          refine Real.cos_nonneg_of_mem_Icc ?_
          constructor <;> linarith [hge, hφ.2]
        have hcos_nonpos : Real.cos φ ≤ 0 := by
          have : 0 ≤ -Real.cos φ := by simpa [Real.cos_pi_sub] using hcos_nonneg
          linarith
        exact not_lt_of_ge hcos_nonpos hcos_pos
      have hφIoo : φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor
        · linarith [hφ.1]
        · exact hhalf'
      have hsin_nonneg : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφ
      have hdiv : Real.sin φ / Real.cos φ < κ := by
        have hmul : Real.sin φ < κ * Real.cos φ := by
          simpa [abs_of_nonneg hsin_nonneg, κ] using hsin_lt
        exact (div_lt_iff₀ hcos_pos).2 hmul
      have htan_lt : Real.tan φ < κ := by
        simpa [Real.tan_eq_sin_div_cos, κ] using hdiv
      rw [← Real.tan_arctan κ] at htan_lt
      have hltθ :=
        (Real.strictMonoOn_tan.lt_iff_lt hφIoo (Real.arctan_mem_Ioo κ)).1 htan_lt
      have : φ < θ := by
        simpa [κ, θ, positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle] using hltθ
      exact not_lt_of_ge hθle this
  · have hhalf_lt : Real.pi / 2 < φ := lt_of_not_ge hhalf
    have hcos_nonneg : 0 ≤ Real.cos (Real.pi - φ) := by
      refine Real.cos_nonneg_of_mem_Icc ?_
      constructor <;> linarith [hhalf_lt, hφ.2]
    have hcos_nonpos : Real.cos φ ≤ 0 := by
      have : 0 ≤ -Real.cos φ := by simpa [Real.cos_pi_sub] using hcos_nonneg
      linarith
    constructor
    · intro _
      linarith [hθ.2]
    · intro _
      rintro ⟨hcos_pos, _⟩
      exact not_lt_of_ge hcos_nonpos hcos_pos

/-- Helper for Remark III.6-extra-7: on `[0, 2π]`, a circle point survives the deleted wedge
exactly when its angle lies on the source-faithful major arc between the two slit-boundary
angles. -/
lemma positiveAxis_surviving_angle_mem_uIcc_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (¬ (0 < Real.cos φ ∧ |Real.sin φ| < (ε / R) * Real.cos φ)) ↔
      φ ∈ Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  have hθ :
      0 < positiveAxisKeyholeUpperAngle R ε ∧
        positiveAxisKeyholeUpperAngle R ε < Real.pi / 2 := by
    simpa [positiveAxisKeyholeUpperAngle] using positiveAxisKeyhole_angle_bounds hε hεR
  have hlower_gt_pi : Real.pi < positiveAxisKeyholeLowerAngle R ε := by
    dsimp [positiveAxisKeyholeLowerAngle, positiveAxisKeyholeAngle]
    linarith [hθ.2, Real.pi_pos]
  rw [Set.uIcc_of_le (le_of_lt horder.1)]
  by_cases hle_pi : φ ≤ Real.pi
  · have hφ' : φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hφ.1, hle_pi⟩
    have hmem :
        φ ∈ Set.Icc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) ↔
          positiveAxisKeyholeUpperAngle R ε ≤ φ := by
      constructor
      · intro hz
        exact hz.1
      · intro hz
        refine ⟨hz, ?_⟩
        exact le_of_lt (lt_of_le_of_lt hle_pi hlower_gt_pi)
    exact
      (positiveAxis_surviving_angle_on_upper_half_iff R ε hε hεR hφ').trans hmem.symm
  · let ψ : ℝ := 2 * Real.pi - φ
    have hψ : ψ ∈ Set.Icc (0 : ℝ) Real.pi := by
      dsimp [ψ]
      constructor
      · linarith [hφ.2]
      · linarith [lt_of_not_ge hle_pi, hφ.1]
    have hsymm :
        (¬ (0 < Real.cos φ ∧ |Real.sin φ| < (ε / R) * Real.cos φ)) ↔
          (¬ (0 < Real.cos ψ ∧ |Real.sin ψ| < (ε / R) * Real.cos ψ)) := by
      have hbad :
          (0 < Real.cos φ ∧ |Real.sin φ| < (ε / R) * Real.cos φ) ↔
            (0 < Real.cos ψ ∧ |Real.sin ψ| < (ε / R) * Real.cos ψ) := by
        dsimp [ψ]
        rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
        simp [abs_neg]
      exact not_congr hbad
    have hmem :
        φ ∈ Set.Icc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) ↔
          positiveAxisKeyholeUpperAngle R ε ≤ ψ := by
      constructor
      · intro hz
        have hz' : φ ≤ positiveAxisKeyholeLowerAngle R ε := hz.2
        dsimp [ψ, positiveAxisKeyholeLowerAngle, positiveAxisKeyholeUpperAngle,
          positiveAxisKeyholeAngle] at hz' ⊢
        linarith
      · intro hz
        refine ⟨?_, ?_⟩
        · have hpi_lt : Real.pi < φ := lt_of_not_ge hle_pi
          linarith [hpi_lt, hθ.2]
        ·
          dsimp [ψ, positiveAxisKeyholeLowerAngle, positiveAxisKeyholeUpperAngle,
            positiveAxisKeyholeAngle] at hz ⊢
          linarith
    exact
      hsymm.trans <|
        (positiveAxis_surviving_angle_on_upper_half_iff R ε hε hεR hψ).trans hmem.symm

/-- Helper for Remark III.6-extra-7: a positive-radius circle point survives the deleted wedge
exactly when its angle lies in the repaired major-arc interval. -/
lemma positiveAxisWedge_circleMap_not_mem_iff_majorArc
    (R ε ρ : ℝ) (hε : 0 < ε) (hεR : ε < R) (hρ : 0 < ρ) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    circleMap 0 ρ φ ∉ positiveAxisWedge R ε ↔
      φ ∈ Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  have hmem :
      circleMap 0 ρ φ ∈ positiveAxisWedge R ε ↔
        (0 < Real.cos φ ∧ |Real.sin φ| < (ε / R) * Real.cos φ) := by
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · have hre : 0 < ρ * Real.cos φ := by
          simpa [positiveAxisWedge, circleMap_zero_re] using hz.1
        nlinarith
      · have him :
            |ρ * Real.sin φ| < (ε / R) * (ρ * Real.cos φ) := by
          simpa [positiveAxisWedge, circleMap_zero_re, circleMap_zero_im] using hz.2
        have him' : ρ * |Real.sin φ| < ρ * ((ε / R) * Real.cos φ) := by
          simpa [abs_mul, abs_of_pos hρ, mul_assoc, mul_left_comm, mul_comm] using him
        nlinarith
    · intro hz
      refine ⟨?_, ?_⟩
      · have hre : 0 < ρ * Real.cos φ := by
          nlinarith
        simpa [circleMap_zero_re] using hre
      · have him' : ρ * |Real.sin φ| < ρ * ((ε / R) * Real.cos φ) := by
          nlinarith
        simpa [circleMap_zero_re, circleMap_zero_im, abs_mul, abs_of_pos hρ, mul_assoc,
          mul_left_comm, mul_comm] using him'
  -- Reduce the circle-point statement to the angular classifier.
  rw [show circleMap 0 ρ φ ∉ positiveAxisWedge R ε ↔
      ¬ circleMap 0 ρ φ ∈ positiveAxisWedge R ε by simp]
  rw [hmem]
  exact positiveAxis_surviving_angle_mem_uIcc_iff R ε hε hεR hφ

/-- Helper for Remark III.6-extra-7: on a fixed positive-radius sphere, deleting the positive
wedge leaves exactly the major-arc image used by the repaired keyhole contour. -/
lemma positiveAxisWedge_sphereDiff_eq_majorArcImage
    (R ε ρ : ℝ) (hε : 0 < ε) (hεR : ε < R) (hρ : 0 < ρ) :
    Metric.sphere (0 : ℂ) ρ \ positiveAxisWedge R ε =
      (fun φ : ℝ ↦ circleMap 0 ρ φ) ''
        Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  ext z
  constructor
  · intro hz
    have hz_sphere : z ∈ Metric.sphere (0 : ℂ) ρ := hz.1
    have hnorm : ‖z‖ = ρ := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz_sphere
      simpa [abs_of_pos hρ] using hz_sphere
    have hz_eq_arg : circleMap 0 ρ z.arg = z := by
      -- Rebuild the sphere point from its norm and principal argument before normalizing the angle
      -- into `[0, 2π]`.
      rw [circleMap_zero, ← hnorm]
      simpa using Complex.norm_mul_exp_arg_mul_I z
    by_cases hzarg : z.arg < 0
    · let φ : ℝ := z.arg + 2 * Real.pi
      have hφ : φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
        constructor
        · dsimp [φ]
          linarith [Complex.neg_pi_lt_arg z]
        · dsimp [φ]
          linarith [Complex.arg_le_pi z]
      have hz_eq : circleMap 0 ρ φ = z := by
        calc
          circleMap 0 ρ φ = circleMap 0 ρ z.arg := by
            dsimp [φ]
            simpa using (periodic_circleMap 0 ρ z.arg)
          _ = z := hz_eq_arg
      refine ⟨φ, ?_, hz_eq⟩
      have hz_not_mem : circleMap 0 ρ φ ∉ positiveAxisWedge R ε := by
        simpa [hz_eq] using hz.2
      exact
        (positiveAxisWedge_circleMap_not_mem_iff_majorArc R ε ρ hε hεR hρ hφ).1 hz_not_mem
    · refine ⟨z.arg, ?_, hz_eq_arg⟩
      have harg : z.arg ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
        constructor
        · exact le_of_not_gt hzarg
        · linarith [Complex.arg_le_pi z]
      have hz_not_mem : circleMap 0 ρ z.arg ∉ positiveAxisWedge R ε := by
        simpa [hz_eq_arg] using hz.2
      exact
        (positiveAxisWedge_circleMap_not_mem_iff_majorArc R ε ρ hε hεR hρ harg).1 hz_not_mem
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨circleMap_mem_sphere 0 hρ.le φ, ?_⟩
    exact
      (positiveAxisWedge_circleMap_not_mem_iff_majorArc R ε ρ hε hεR hρ
        (by
          rw [Set.uIcc_of_le (le_of_lt (positiveAxisKeyhole_majorArc_angle_order
            (R := R) (ε := ε) hε hεR).1)] at hφ
          have hθ :
              0 < positiveAxisKeyholeUpperAngle R ε := by
            simpa [positiveAxisKeyholeUpperAngle] using
              (positiveAxisKeyhole_angle_bounds hε hεR).1
          constructor
          · exact le_trans hθ.le hφ.1
          · have hlower_lt : positiveAxisKeyholeLowerAngle R ε < 2 * Real.pi :=
              (positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR).2
            exact le_trans hφ.2 hlower_lt.le)).2 hφ

/-- Helper for Remark III.6-extra-7: the surviving part of the outer boundary circle is exactly
the outer major-arc image used in the contour range decomposition. -/
lemma positiveAxisWedge_outerSphere_diff_eq_outer_arc_image
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    Metric.sphere (0 : ℂ) R \ positiveAxisWedge R ε =
      (fun φ : ℝ ↦ circleMap 0 R φ) ''
        Set.uIcc (positiveAxisKeyholeLowerAngle R ε) (positiveAxisKeyholeUpperAngle R ε) := by
  -- The outer arc uses the same major-arc interval, written with the contour's endpoint order.
  simpa [Set.uIcc, min_comm, max_comm] using
    (positiveAxisWedge_sphereDiff_eq_majorArcImage
      R ε R hε hεR (lt_trans hε hεR))

/-- Helper for Remark III.6-extra-7: the surviving part of the inner boundary circle is exactly
the inner major-arc image used in the contour range decomposition. -/
lemma positiveAxisWedge_innerSphere_diff_eq_inner_arc_image
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    Metric.sphere (0 : ℂ) ε \ positiveAxisWedge R ε =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  exact positiveAxisWedge_sphereDiff_eq_majorArcImage R ε ε hε hεR hε

/-- Helper for Remark III.6-extra-7: once the fixed-radius circle classifiers are available, the
surviving circle part of the slit-annulus frontier is exactly the union of the inner and outer
major-arc images. -/
lemma positiveAxisWedgeAnnulus_surviving_circles_eq_majorArc_images
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    ((Metric.sphere (0 : ℂ) R ∪ Metric.sphere (0 : ℂ) ε) \ positiveAxisWedge R ε) =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) ∪
      (fun φ : ℝ ↦ circleMap 0 R φ) ''
        Set.uIcc (positiveAxisKeyholeLowerAngle R ε) (positiveAxisKeyholeUpperAngle R ε) := by
  ext z
  constructor
  · intro hz
    have hz_not_mem : z ∉ positiveAxisWedge R ε := hz.2
    rcases hz.1 with hz_outer | hz_inner
    · -- A surviving outer-circle point belongs to the outer major-arc image.
      right
      simpa [positiveAxisWedge_outerSphere_diff_eq_outer_arc_image R ε hε hεR] using
        (show z ∈ Metric.sphere (0 : ℂ) R \ positiveAxisWedge R ε from
          ⟨hz_outer, hz_not_mem⟩)
    · -- A surviving inner-circle point belongs to the inner major-arc image.
      left
      simpa [positiveAxisWedge_innerSphere_diff_eq_inner_arc_image R ε hε hεR] using
        (show z ∈ Metric.sphere (0 : ℂ) ε \ positiveAxisWedge R ε from
          ⟨hz_inner, hz_not_mem⟩)
  · rintro (hz | hz)
    · -- Repackage the inner major arc back into the surviving inner sphere.
      have hz' : z ∈ Metric.sphere (0 : ℂ) ε \ positiveAxisWedge R ε := by
        simpa [positiveAxisWedge_innerSphere_diff_eq_inner_arc_image R ε hε hεR] using hz
      exact ⟨Or.inr hz'.1, hz'.2⟩
    · -- Repackage the outer major arc back into the surviving outer sphere.
      have hz' : z ∈ Metric.sphere (0 : ℂ) R \ positiveAxisWedge R ε := by
        simpa [positiveAxisWedge_outerSphere_diff_eq_outer_arc_image R ε hε hεR] using hz
      exact ⟨Or.inl hz'.1, hz'.2⟩

/-- Helper for Remark III.6-extra-7: inside the closed annulus, the wedge-frontier piece is
exactly the union of the two slit lips. This is the owner-side converse rewrite needed by the
global frontier theorem. -/
lemma positiveAxisWedgeAnnulus_annulusInter_frontier_wedge_eq_lip_union
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} ∩ frontier (positiveAxisWedge R ε)) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeUpperAngle R ε)) '' Set.uIcc R ε ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε)) '' Set.uIcc ε R := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rcases hz with ⟨hzAnn, hzFront⟩
    have hR : 0 < R := lt_trans hε hεR
    have hzClosure : z ∈ closure (positiveAxisWedge R ε) := by
      rw [(isOpen_positiveAxisWedge R ε).frontier_eq, Set.mem_diff] at hzFront
      exact hzFront.1
    have hz_not_mem : z ∉ positiveAxisWedge R ε := by
      rw [(isOpen_positiveAxisWedge R ε).frontier_eq, Set.mem_diff] at hzFront
      exact hzFront.2
    have hz_re_nonneg : 0 ≤ z.re := by
      -- The wedge lies in the nonnegative-real half-plane, so every closure point does too.
      have hsubset : positiveAxisWedge R ε ⊆ {w : ℂ | 0 ≤ w.re} := by
        intro w hw
        exact hw.1.le
      exact
        (closure_minimal hsubset (isClosed_le continuous_const Complex.continuous_re))
          hzClosure
    have hz_abs_le : |z.im| ≤ (ε / R) * z.re := by
      -- The closure also preserves the weak boundary-line inequality.
      have hsubset :
          positiveAxisWedge R ε ⊆ {w : ℂ | |w.im| ≤ (ε / R) * w.re} := by
        intro w hw
        exact hw.2.le
      exact
        (closure_minimal hsubset
          (isClosed_le (continuous_abs.comp Complex.continuous_im)
            (continuous_const.mul Complex.continuous_re)))
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
      have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hε hzAnn.1
      exact hnorm_pos.ne' (by simpa [hz_zero])
    have hz_re_pos : 0 < z.re := lt_of_le_of_ne hz_re_nonneg hz_re_ne.symm
    have hz_abs_ge : (ε / R) * z.re ≤ |z.im| := by
      -- If the inequality were still strict, the point would lie inside the open wedge.
      by_contra hlt
      exact hz_not_mem ⟨hz_re_pos, lt_of_not_ge hlt⟩
    have hz_abs_eq : |z.im| = (ε / R) * z.re := le_antisymm hz_abs_le hz_abs_ge
    by_cases him_nonneg : 0 ≤ z.im
    · have him_line : z.im = (ε / R) * z.re := by
        -- On the upper branch, the absolute value drops and yields the upper lip line.
        rw [abs_of_nonneg him_nonneg] at hz_abs_eq
        exact hz_abs_eq
      rcases positiveAxis_eq_circleMap_upper_of_re_pos_line R ε hz_re_pos him_line with
        ⟨ρ, hρ_pos, rfl⟩
      left
      refine ⟨ρ, ?_, rfl⟩
      rw [Set.uIcc_of_gt hεR]
      simpa [norm_circleMap_zero, abs_of_nonneg hρ_pos.le] using hzAnn
    · have him_line : z.im = -((ε / R) * z.re) := by
        -- On the lower branch, the absolute value contributes the sign change.
        rw [abs_of_neg (lt_of_not_ge him_nonneg)] at hz_abs_eq
        linarith
      rcases positiveAxis_eq_circleMap_lower_of_re_pos_line R ε hz_re_pos him_line with
        ⟨ρ, hρ_pos, rfl⟩
      right
      refine ⟨ρ, ?_, rfl⟩
      rw [Set.uIcc_of_lt hεR]
      simpa [norm_circleMap_zero, abs_of_nonneg hρ_pos.le] using hzAnn
  · intro z hz
    rcases hz with hz | hz
    · exact (positiveAxisWedge_upper_lip_image_subset_annulus_frontier R ε hε hεR) hz
    · exact (positiveAxisWedge_lower_lip_image_subset_annulus_frontier R ε hε hεR) hz


/-- Helper for Remark III.6-extra-7: the negative real point on the outer circle survives the
positive-axis slit and therefore still lies on the frontier of the slit annulus. This is the
geometric witness that the owner frontier contains the major arc around angle `π`. -/
lemma positiveAxisWedgeAnnulus_negative_real_frontier_point
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    circleMap 0 R Real.pi ∈ frontier (positiveAxisWedgeAnnulus R ε) := by
  have hR : 0 < R := lt_trans hε hεR
  have hclosedAnnulusEq :
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} =
        Metric.closedBall (0 : ℂ) R \ Metric.ball (0 : ℂ) ε := by
    -- Rewrite the closed annulus in the metric `closedBall \ ball` form used by the frontier API.
    ext z
    simp [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, sub_zero, not_lt, and_comm,
      and_left_comm, and_assoc]
  have hball :
      Metric.closedBall (0 : ℂ) ε ⊆ interior (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    have hz_norm : ‖z‖ ≤ ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    -- Every point with norm at most `ε` lies strictly inside the larger closed ball of radius `R`.
    refine Metric.ball_subset_interior_closedBall ?_
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt hz_norm hεR
  have hfrontierAnnulus :
      circleMap 0 R Real.pi ∈ frontier ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}) := by
    rw [hclosedAnnulusEq]
    -- The negative real point lies on the outer boundary sphere of the annulus.
    rw [frontier_diff_ball_eq_of_closedBall_subset_interior
      (a := (0 : ℂ)) (r := ε) hε Metric.isClosed_closedBall hball]
    left
    rw [frontier_closedBall' (0 : ℂ) R]
    simpa [Metric.mem_sphere, dist_eq_norm, norm_circleMap_zero, abs_of_pos hR]
  have hwedge :
      circleMap 0 R Real.pi ∉ positiveAxisWedge R ε := by
    intro hwedge
    rw [positiveAxisWedge] at hwedge
    have hre_nonpos : (circleMap 0 R Real.pi).re ≤ 0 := by
      simp [circleMap_zero_re, Real.cos_pi, hR.le]
    -- The removed wedge only lives on the positive-real side, so the negative-real point survives.
    exact (not_lt_of_ge hre_nonpos hwedge.1).elim
  -- Split the slit-annulus frontier into the surviving annulus frontier and the slit-boundary
  -- frontier, then place the negative-real point in the surviving outer-circle branch.
  rw [positiveAxisWedgeAnnulus,
    frontier_diff_open_of_isClosed
      (A := {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R})
      (W := positiveAxisWedge R ε)
      (by
        simpa [Set.setOf_and] using
          (isClosed_le continuous_const continuous_norm).inter
            (isClosed_le continuous_norm continuous_const))
      (isOpen_positiveAxisWedge R ε)]
  exact Or.inl ⟨hfrontierAnnulus, hwedge⟩
