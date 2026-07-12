import DifferentialForms_Cartan_1970.III.section12.«0034_Exercise_21».NegativeAxisWedgeAnnulus

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval
/-- Helper for Exercise 21: an open ball contained in `K` gives a smaller concentric closed ball
contained in `interior K`. This keeps the pole-ball packaging separate from the boundary proof. -/
lemma exercise21_closedBall_subset_interior_of_ball_subset
    {K : Set ℂ} {c : ℂ} {ρ R : ℝ}
    (hρR : ρ < R) (hball : Metric.ball c R ⊆ K) :
    Metric.closedBall c ρ ⊆ interior K := by
  -- Upgrade the open-ball inclusion to an interior inclusion, then shrink the radius once.
  have hsubset : Metric.ball c R ⊆ interior K :=
    (IsOpen.subset_interior_iff Metric.isOpen_ball).2 hball
  exact (Metric.closedBall_subset_ball hρR).trans hsubset

/-- Helper for Exercise 21: a point within distance `ρ` of a center `c` has norm within `ρ` of
`‖c‖`. This is the annulus-control bridge for the explicit residue balls. -/
lemma exercise21_norm_bounds_of_dist_lt {z c : ℂ} {ρ : ℝ}
    (hz : dist z c < ρ) :
    ‖c‖ - ρ < ‖z‖ ∧ ‖z‖ < ‖c‖ + ρ := by
  -- Convert the distance estimate into the standard norm-difference estimate.
  have hdist : ‖z - c‖ < ρ := by
    simpa [dist_eq_norm] using hz
  have hclose : |‖z‖ - ‖c‖| < ρ :=
    lt_of_le_of_lt (abs_norm_sub_norm_le z c) hdist
  constructor
  · linarith [(abs_lt.mp hclose).1]
  · linarith [(abs_lt.mp hclose).2]

/-- Helper for Exercise 21: distance control implies control of the real coordinate. -/
lemma exercise21_re_close_of_dist_lt {z c : ℂ} {ρ : ℝ}
    (hz : dist z c < ρ) :
    |z.re - c.re| < ρ := by
  -- The real part is bounded by the complex norm of the displacement.
  have hdist : ‖z - c‖ < ρ := by
    simpa [dist_eq_norm] using hz
  exact lt_of_le_of_lt (by simpa [sub_re] using abs_re_le_norm (z - c)) hdist

/-- Helper for Exercise 21: distance control implies control of the imaginary coordinate. -/
lemma exercise21_im_close_of_dist_lt {z c : ℂ} {ρ : ℝ}
    (hz : dist z c < ρ) :
    |z.im - c.im| < ρ := by
  -- The imaginary part is bounded by the same displacement norm.
  have hdist : ‖z - c‖ < ρ := by
    simpa [dist_eq_norm] using hz
  exact lt_of_le_of_lt (by simpa [sub_im] using abs_im_le_norm (z - c)) hdist

/-- Helper for Exercise 21: a small ball around `1` stays inside the slit annulus because its
points keep positive real part and stay between the two radial bounds. -/
lemma exercise21_ball_one_subset_negative_wedge_annulus
    (r ε ρ : ℝ)
    (hρε : ρ ≤ 1 - ε) (hρr : ρ ≤ r - 1) (hρone : ρ ≤ 1) :
    Metric.ball (1 : ℂ) ρ ⊆ exercise21NegativeWedgeAnnulus r ε := by
  intro z hz
  have hnorm := exercise21_norm_bounds_of_dist_lt (c := (1 : ℂ)) hz
  have hre_close : |z.re - 1| < ρ :=
    exercise21_re_close_of_dist_lt (c := (1 : ℂ)) hz
  have hεnorm : ε < ‖z‖ := by
    have : 1 - ρ < ‖z‖ := by
      simpa using hnorm.1
    linarith
  have hnormr : ‖z‖ < r := by
    have : ‖z‖ < 1 + ρ := by
      simpa using hnorm.2
    linarith
  refine ⟨⟨le_of_lt hεnorm, le_of_lt hnormr⟩, ?_⟩
  -- Positive real part keeps the whole ball away from the removed negative wedge.
  intro hwedge
  have hre_pos : 0 < z.re := by
    have hre_lt : -ρ < z.re - 1 := (abs_lt.mp hre_close).1
    linarith
  linarith [hwedge.1, hre_pos]

/-- Helper for Exercise 21: a small ball around `a i` stays inside the slit annulus. The norm
bounds keep the ball in the annulus, while the positive imaginary part keeps it out of the slit. -/
lemma exercise21_ball_pos_imag_subset_negative_wedge_annulus
    (a r ε ρ : ℝ) (ha : 0 < a) (hεa : ε < a) (har : a < r)
    (hρε : ρ ≤ a - ε) (hρr : ρ ≤ r - a) (hρa : ρ ≤ a / 2) :
    Metric.ball ((a : ℂ) * Complex.I) ρ ⊆ exercise21NegativeWedgeAnnulus r ε := by
  intro z hz
  have hnorm := exercise21_norm_bounds_of_dist_lt (c := (a : ℂ) * Complex.I) hz
  have hre_close : |z.re| < ρ := by
    simpa using exercise21_re_close_of_dist_lt (c := (a : ℂ) * Complex.I) hz
  have him_close : |z.im - a| < ρ := by
    simpa using exercise21_im_close_of_dist_lt (c := (a : ℂ) * Complex.I) hz
  have hεnorm : ε < ‖z‖ := by
    have : a - ρ < ‖z‖ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.1
    linarith
  have hnormr : ‖z‖ < r := by
    have : ‖z‖ < a + ρ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.2
    linarith
  refine ⟨⟨le_of_lt hεnorm, le_of_lt hnormr⟩, ?_⟩
  intro hwedge
  have hr : 0 < r := lt_trans ha har
  have hεr : ε < r := lt_trans hεa har
  have hratio : ε / r < 1 := (div_lt_one hr).2 hεr
  have him_gt_half : a / 2 < z.im := by
    have hlower : -ρ < z.im - a := (abs_lt.mp him_close).1
    linarith
  have him_abs : ρ < |z.im| := by
    have hz_im_pos : 0 < z.im := lt_trans (show 0 < a / 2 by positivity) him_gt_half
    have hρlt : ρ < z.im := by
      linarith
    simpa [abs_of_pos hz_im_pos] using hρlt
  have hneg_re_nonneg : 0 ≤ -z.re := by linarith [hwedge.1]
  have hneg_re_lt : -z.re < ρ := by
    have hleft : -ρ < z.re := (abs_lt.mp hre_close).1
    linarith
  have hwedge_small : (ε / r) * (-z.re) < ρ := by
    nlinarith
  linarith [hwedge.2, him_abs, hwedge_small]

/-- Helper for Exercise 21: the companion ball around `-a i` also stays inside the slit annulus.
Here the negative imaginary part keeps the ball away from the removed wedge. -/
lemma exercise21_ball_neg_imag_subset_negative_wedge_annulus
    (a r ε ρ : ℝ) (ha : 0 < a) (hεa : ε < a) (har : a < r)
    (hρε : ρ ≤ a - ε) (hρr : ρ ≤ r - a) (hρa : ρ ≤ a / 2) :
    Metric.ball (-((a : ℂ) * Complex.I)) ρ ⊆ exercise21NegativeWedgeAnnulus r ε := by
  intro z hz
  have hnorm := exercise21_norm_bounds_of_dist_lt (c := -((a : ℂ) * Complex.I)) hz
  have hre_close : |z.re| < ρ := by
    simpa using exercise21_re_close_of_dist_lt (c := -((a : ℂ) * Complex.I)) hz
  have him_close : |z.im + a| < ρ := by
    simpa using exercise21_im_close_of_dist_lt (c := -((a : ℂ) * Complex.I)) hz
  have hεnorm : ε < ‖z‖ := by
    have : a - ρ < ‖z‖ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.1
    linarith
  have hnormr : ‖z‖ < r := by
    have : ‖z‖ < a + ρ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.2
    linarith
  refine ⟨⟨le_of_lt hεnorm, le_of_lt hnormr⟩, ?_⟩
  intro hwedge
  have hr : 0 < r := lt_trans ha har
  have hεr : ε < r := lt_trans hεa har
  have hratio : ε / r < 1 := (div_lt_one hr).2 hεr
  have him_lt_half : z.im < -(a / 2) := by
    have hupper : z.im + a < ρ := (abs_lt.mp him_close).2
    linarith
  have him_abs : ρ < |z.im| := by
    have hz_im_neg : z.im < 0 := lt_trans him_lt_half (by linarith)
    have : ρ < -z.im := by linarith
    simpa [abs_of_neg hz_im_neg] using this
  have hneg_re_nonneg : 0 ≤ -z.re := by linarith [hwedge.1]
  have hneg_re_lt : -z.re < ρ := by
    have hleft : -ρ < z.re := (abs_lt.mp hre_close).1
    linarith
  have hwedge_small : (ε / r) * (-z.re) < ρ := by
    nlinarith
  linarith [hwedge.2, him_abs, hwedge_small]

/-- Helper for Exercise 21: explicit residue-circle radii around `1`, `a i`, and `-a i` stay
inside the slit annulus and avoid the other poles. -/
lemma exercise21_negative_wedge_annulus_pole_ball_data
    (a r ε : ℝ) (hε : 0 < ε) (hεa : ε < a) (har : a < r) (hε1 : ε < 1) (h1r : 1 < r) :
    let K := exercise21NegativeWedgeAnnulus r ε
    ∃ ρ₁ ρ₂ ρ₃ : ℝ,
      K ⊆ Complex.slitPlane ∧
      0 < ρ₁ ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆
          Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₂ ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
          Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₃ ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
          Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ) := by
  let K := exercise21NegativeWedgeAnnulus r ε
  let ρ₁ : ℝ := min (1 - ε) (min (r - 1) 1) / 4
  let ρ₂ : ℝ := min (a - ε) (min (r - a) a) / 4
  let ρ₃ : ℝ := ρ₂
  have ha : 0 < a := lt_trans hε hεa
  have hr : 0 < r := lt_trans ha har
  have hK_subset : K ⊆ Complex.slitPlane :=
    exercise21NegativeWedgeAnnulus_subset_slitPlane r ε hε (lt_trans hεa har)
  have hρ₁_pos : 0 < ρ₁ := by
    dsimp [ρ₁]
    refine div_pos ?_ (by norm_num)
    refine lt_min (sub_pos.mpr hε1) ?_
    exact lt_min (sub_pos.mpr h1r) zero_lt_one
  have hρ₂_pos : 0 < ρ₂ := by
    dsimp [ρ₂]
    refine div_pos ?_ (by norm_num)
    refine lt_min (sub_pos.mpr hεa) ?_
    exact lt_min (sub_pos.mpr har) ha
  have hρ₁_lt : ρ₁ < min (1 - ε) (min (r - 1) 1) := by
    dsimp [ρ₁]
    have hpos : 0 < min (1 - ε) (min (r - 1) 1) := by
      refine lt_min (sub_pos.mpr hε1) ?_
      exact lt_min (sub_pos.mpr h1r) zero_lt_one
    nlinarith
  have hρ₂_lt : ρ₂ < min (a - ε) (min (r - a) a) := by
    dsimp [ρ₂]
    have hpos : 0 < min (a - ε) (min (r - a) a) := by
      refine lt_min (sub_pos.mpr hεa) ?_
      exact lt_min (sub_pos.mpr har) ha
    nlinarith
  have hρ₁_lt_one : ρ₁ < 1 := by
    have hmin : min (1 - ε) (min (r - 1) 1) ≤ 1 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact lt_of_lt_of_le hρ₁_lt hmin
  have hρ₂_lt_a : ρ₂ < a := by
    have hmin : min (a - ε) (min (r - a) a) ≤ a := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact lt_of_lt_of_le hρ₂_lt hmin
  have hball₁ :
      Metric.ball (1 : ℂ) (2 * ρ₁) ⊆ K := by
    -- The quarter-minimum radius leaves room both for the annulus bounds and for `re > 0`.
    refine exercise21_ball_one_subset_negative_wedge_annulus r ε (2 * ρ₁) ?_ ?_ ?_
    · have hhalf : 2 * ρ₁ = min (1 - ε) (min (r - 1) 1) / 2 := by
        dsimp [ρ₁]
        ring_nf
      rw [hhalf]
      have hmin : min (1 - ε) (min (r - 1) 1) / 2 ≤ 1 - ε := by
        have := min_le_left (1 - ε) (min (r - 1) 1)
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₁ = min (1 - ε) (min (r - 1) 1) / 2 := by
        dsimp [ρ₁]
        ring_nf
      rw [hhalf]
      have hmin : min (1 - ε) (min (r - 1) 1) / 2 ≤ r - 1 := by
        have h' := min_le_right (1 - ε) (min (r - 1) 1)
        have h'' := min_le_left (r - 1) 1
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₁ = min (1 - ε) (min (r - 1) 1) / 2 := by
        dsimp [ρ₁]
        ring_nf
      rw [hhalf]
      have hmin : min (1 - ε) (min (r - 1) 1) / 2 ≤ 1 := by
        have h' := min_le_right (1 - ε) (min (r - 1) 1)
        have h'' := min_le_right (r - 1) 1
        nlinarith
      exact hmin
  have hball₂ :
      Metric.ball ((a : ℂ) * Complex.I) (2 * ρ₂) ⊆ K := by
    -- The same quarter-minimum radius keeps the imaginary poles inside the annulus and away from
    -- the slit because `|im z|` stays larger than `|re z|`.
    refine exercise21_ball_pos_imag_subset_negative_wedge_annulus a r ε (2 * ρ₂) ha hεa har ?_ ?_ ?_
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a - ε := by
        have := min_le_left (a - ε) (min (r - a) a)
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ r - a := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_left (r - a) a
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a / 2 := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_right (r - a) a
        nlinarith
      exact hmin
  have hball₃ :
      Metric.ball (-((a : ℂ) * Complex.I)) (2 * ρ₃) ⊆ K := by
    -- The lower imaginary pole uses the same radius and the same annulus estimate with `im < 0`.
    dsimp [ρ₃]
    refine exercise21_ball_neg_imag_subset_negative_wedge_annulus a r ε (2 * ρ₂) ha hεa har ?_ ?_ ?_
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a - ε := by
        have := min_le_left (a - ε) (min (r - a) a)
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ r - a := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_left (r - a) a
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a / 2 := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_right (r - a) a
        nlinarith
      exact hmin
  have hK₁ : Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K :=
    exercise21_closedBall_subset_interior_of_ball_subset
      (by nlinarith [hρ₁_pos]) hball₁
  have hK₂ : Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K :=
    exercise21_closedBall_subset_interior_of_ball_subset
      (by nlinarith [hρ₂_pos]) hball₂
  have hK₃ : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K := by
    dsimp [ρ₃]
    exact exercise21_closedBall_subset_interior_of_ball_subset
      (by nlinarith [hρ₂_pos]) hball₃
  refine ⟨ρ₁, ρ₂, ρ₃, hK_subset, hρ₁_pos, hK₁, ?_, hρ₂_pos, hK₂, ?_, ?_, hK₃, ?_⟩
  · intro z hz
    refine ⟨hK_subset (interior_subset (hK₁ hz)), ?_⟩
    intro hzbad
    rcases hzbad with hzbad | hzbad
    · subst z
      have hdist : 1 ≤ dist (1 : ℂ) ((a : ℂ) * Complex.I) := by
        simpa [dist_eq_norm] using abs_re_le_norm ((1 : ℂ) - (a : ℂ) * Complex.I)
      have hmem : dist (1 : ℂ) ((a : ℂ) * Complex.I) ≤ ρ₁ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
    · subst z
      have hdist : 1 ≤ dist (1 : ℂ) (-((a : ℂ) * Complex.I)) := by
        simpa [dist_eq_norm] using abs_re_le_norm ((1 : ℂ) - (-((a : ℂ) * Complex.I)))
      have hmem : dist (1 : ℂ) (-((a : ℂ) * Complex.I)) ≤ ρ₁ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
  · intro z hz
    refine ⟨hK_subset (interior_subset (hK₂ hz)), ?_⟩
    intro hzbad
    rcases hzbad with hzbad | hzbad
    · subst z
      have hdist : a ≤ dist ((a : ℂ) * Complex.I) (1 : ℂ) := by
        simpa [dist_eq_norm, abs_of_nonneg ha.le] using
          abs_im_le_norm (((a : ℂ) * Complex.I) - (1 : ℂ))
      have hmem : dist ((a : ℂ) * Complex.I) (1 : ℂ) ≤ ρ₂ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
    · subst z
      have hdist : a ≤ dist ((a : ℂ) * Complex.I) (-((a : ℂ) * Complex.I)) := by
        have : a + a ≤ dist ((a : ℂ) * Complex.I) (-((a : ℂ) * Complex.I)) := by
          simpa [dist_eq_norm, abs_of_nonneg (show 0 ≤ a + a by positivity)] using
            abs_im_le_norm (((a : ℂ) * Complex.I) - (-((a : ℂ) * Complex.I)))
        linarith
      have hmem : dist ((a : ℂ) * Complex.I) (-((a : ℂ) * Complex.I)) ≤ ρ₂ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
  · simpa [ρ₃] using hρ₂_pos
  · intro z hz
    refine ⟨hK_subset (interior_subset (hK₃ hz)), ?_⟩
    intro hzbad
    rcases hzbad with hzbad | hzbad
    · subst z
      have hdist : a ≤ dist (-((a : ℂ) * Complex.I)) (1 : ℂ) := by
        simpa [dist_eq_norm, abs_of_neg (show -a < 0 by linarith)] using
          abs_im_le_norm ((-((a : ℂ) * Complex.I)) - (1 : ℂ))
      have hmem : dist (-((a : ℂ) * Complex.I)) (1 : ℂ) ≤ ρ₃ := by
        simpa [Metric.mem_closedBall, ρ₃, dist_comm] using hz
      linarith
    · subst z
      have hdist : a ≤ dist (-((a : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) := by
        have : a + a ≤ dist (-((a : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) := by
          have hneg : -a - a < 0 := by linarith
          simpa [dist_eq_norm, two_mul, abs_of_neg hneg] using
            abs_im_le_norm ((-((a : ℂ) * Complex.I)) - ((a : ℂ) * Complex.I))
        linarith
      have hmem : dist (-((a : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) ≤ ρ₃ := by
        simpa [Metric.mem_closedBall, ρ₃, dist_comm] using hz
      linarith

