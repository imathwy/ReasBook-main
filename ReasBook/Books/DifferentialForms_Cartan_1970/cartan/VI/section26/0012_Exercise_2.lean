import DifferentialForms_Cartan_1970.cartan.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0015_Exercise_5»

open Set

/-- Helper for Exercise 2: for concentric discs, strict containment of the closed inner disc in
the open outer disc forces the inner radius to be strictly smaller than the outer radius. -/
lemma radii_lt_of_closedBall_subset_ball_same_center
    {c : ℂ} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁)
    (hsubset : Metric.closedBall c ρ₁ ⊆ Metric.ball c ρ₂) :
    ρ₁ < ρ₂ := by
  let z : ℂ := c + ρ₁
  -- Put the rightmost point of the inner circle into the assumed subset.
  have hz_closed : z ∈ Metric.closedBall c ρ₁ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, z, Complex.norm_real, abs_of_nonneg hρ₁.le]
  have hz_ball : z ∈ Metric.ball c ρ₂ := hsubset hz_closed
  -- Reading ball membership in norm form yields the required strict radius inequality.
  simpa [Metric.mem_ball, dist_eq_norm, z, Complex.norm_real, abs_of_nonneg hρ₁.le] using hz_ball

/-- Helper for Exercise 2: membership in the centered shell is exactly the pair of strict norm
inequalities between the two radii. -/
lemma mem_centered_shell_iff
    {c z : ℂ} {ρ₁ ρ₂ : ℝ} :
    z ∈ Metric.ball c ρ₂ \ Metric.closedBall c ρ₁ ↔
      ρ₁ < ‖z - c‖ ∧ ‖z - c‖ < ρ₂ := by
  constructor
  · intro hz
    rcases hz with ⟨hz_ball, hz_closed⟩
    -- Translate shell membership into the corresponding metric inequalities.
    have hz_lt : ‖z - c‖ < ρ₂ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz_ball
    have hz_gt : ρ₁ < ‖z - c‖ := by
      have hz_not : ¬ ‖z - c‖ ≤ ρ₁ := by
        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hz_closed
      exact lt_of_not_ge hz_not
    exact ⟨hz_gt, hz_lt⟩
  · rintro ⟨hz_gt, hz_lt⟩
    -- Conversely, the strict norm bounds give shell membership directly.
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz_lt
    · have hz_not : ¬ ‖z - c‖ ≤ ρ₁ := not_le_of_gt hz_gt
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hz_not

/-- Helper for Exercise 2: membership in the standard annulus with outer radius `1` is the
expected pair of real norm inequalities. -/
lemma mem_standard_annulus_iff {r : ℝ} (hr : 0 ≤ r) {z : ℂ} :
    z ∈ complexOpenAnnulus (ENNReal.ofReal r) 1 ↔ r < ‖z‖ ∧ ‖z‖ < 1 := by
  rw [complexOpenAnnulus]
  constructor
  · rintro ⟨hz_left, hz_right⟩
    -- Convert the `ENNReal` inequalities defining the annulus back to real inequalities.
    have hz_left' : r < ‖z‖₊ := (ENNReal.ofReal_lt_coe_iff hr).1 hz_left
    exact ⟨by exact_mod_cast hz_left', by exact_mod_cast hz_right⟩
  · rintro ⟨hz_left, hz_right⟩
    -- The converse is the same coercion step in the forward direction.
    have hz_left' : r < ‖z‖₊ := by
      exact_mod_cast hz_left
    exact ⟨(ENNReal.ofReal_lt_coe_iff hr).2 hz_left', by exact_mod_cast hz_right⟩

/-- Helper for Exercise 2: a concentric shell is sent to a standard annulus by the affine
homography `z ↦ (z - c) / ρ₂`. -/
lemma concentric_shell_to_standard_annulus_bijOn
    {c : ℂ} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₁ < ρ₂) :
    ∃ α β γ δ : ℂ,
      ∃ r : ℝ,
        0 < r ∧
          r < 1 ∧
            α * δ - β * γ ≠ 0 ∧
              (∀ z ∈ Metric.ball c ρ₂ \ Metric.closedBall c ρ₁, γ * z + δ ≠ 0) ∧
                BijOn (homographic_map α β γ δ)
                  (Metric.ball c ρ₂ \ Metric.closedBall c ρ₁)
                  (complexOpenAnnulus (ENNReal.ofReal r) 1) := by
  have hρ₂_ne : (ρ₂ : ℂ) ≠ 0 := by
    exact_mod_cast hρ₂.ne'
  have hρ₂_real_ne : ρ₂ ≠ 0 := hρ₂.ne'
  have hr_nonneg : 0 ≤ ρ₁ / ρ₂ := le_of_lt (div_pos hρ₁ hρ₂)
  refine ⟨1, -c, 0, ρ₂, ρ₁ / ρ₂, div_pos hρ₁ hρ₂, ?_, ?_, ?_, ?_⟩
  · -- The annulus ratio is strictly below `1` because the shell radii are strictly ordered.
    field_simp [hρ₂_real_ne]
    linarith
  · -- The affine homography has nonzero determinant because its denominator is the
    -- nonzero scalar `ρ₂`.
    simpa using hρ₂_ne
  · intro z hz
    -- The denominator is constant, so there is no pole on the shell.
    simp [hρ₂_ne]
  · -- Prove bijectivity by writing the explicit inverse `w ↦ ρ₂ w + c`.
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      have hz_shell : ρ₁ < ‖z - c‖ ∧ ‖z - c‖ < ρ₂ := (mem_centered_shell_iff).1 hz
      have hnorm :
          ‖homographic_map 1 (-c) 0 ρ₂ z‖ = ‖z - c‖ / ρ₂ := by
        -- Rewrite the affine homography and simplify its norm.
        simpa [homographic_map, Complex.norm_real, abs_of_pos hρ₂, sub_eq_add_neg] using
          (norm_div (z - c) (ρ₂ : ℂ))
      have hleft : ρ₁ / ρ₂ < ‖z - c‖ / ρ₂ := by
        field_simp [hρ₂_real_ne]
        exact hz_shell.1
      have hright : ‖z - c‖ / ρ₂ < 1 := by
        field_simp [hρ₂_real_ne]
        exact hz_shell.2
      -- The normalized point lies in the standard annulus exactly when its norm lies between the
      -- two normalized radii.
      simpa [mem_standard_annulus_iff hr_nonneg, hnorm] using ⟨hleft, hright⟩
    · let g : ℂ → ℂ := fun w ↦ (ρ₂ : ℂ) * w + c
      have hg_left :
          Set.LeftInvOn g (homographic_map 1 (-c) 0 ρ₂)
            (Metric.ball c ρ₂ \ Metric.closedBall c ρ₁) := by
        intro z hz
        -- The explicit inverse cancels the affine normalization pointwise on the shell.
        change (ρ₂ : ℂ) * homographic_map 1 (-c) 0 ρ₂ z + c = z
        rw [homographic_map]
        field_simp [hρ₂_ne]
        ring
      exact hg_left.injOn
    · intro w hw
      let z : ℂ := (ρ₂ : ℂ) * w + c
      have hw_annulus : ρ₁ / ρ₂ < ‖w‖ ∧ ‖w‖ < 1 :=
        (mem_standard_annulus_iff hr_nonneg).1 hw
      have hnorm : ‖z - c‖ = ρ₂ * ‖w‖ := by
        -- Undoing the affine normalization scales norms by the outer radius.
        simpa [z, norm_mul, Complex.norm_real, abs_of_pos hρ₂]
      refine ⟨z, ?_, ?_⟩
      · have hz_left' : ρ₁ < ‖w‖ * ρ₂ := by
          have hw_left := hw_annulus.1
          field_simp [hρ₂_real_ne] at hw_left
          simpa [mul_comm] using hw_left
        have hz_left : ρ₁ < ‖z - c‖ := by
          rw [hnorm]
          simpa [mul_comm] using hz_left'
        have hz_right' : ρ₂ * ‖w‖ < ρ₂ := by
          nlinarith [hw_annulus.2, hρ₂]
        have hz_right : ‖z - c‖ < ρ₂ := by
          rw [hnorm]
          exact hz_right'
        -- The inverse image point lies back in the original shell.
        exact (mem_centered_shell_iff).2 ⟨hz_left, hz_right⟩
      · -- Evaluating the homography on the explicit inverse recovers the original annulus point.
        change homographic_map 1 (-c) 0 ρ₂ ((ρ₂ : ℂ) * w + c) = w
        rw [homographic_map]
        field_simp [hρ₂_ne]
        ring

/-- Helper for Exercise 2: if the inner closed disc lies strictly inside the outer open disc, then
the resulting shell is connected. -/
lemma shell_isConnected_of_closedBall_subset_ball
    {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁)
    (hinside : Metric.closedBall c₁ ρ₁ ⊆ Metric.ball c₂ ρ₂) :
    IsConnected (Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁) := by
  let shell : Set ℂ := Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁
  -- Thicken the compact inner disc slightly while staying inside the outer ball.
  obtain ⟨ε, hε_pos, hε_subset⟩ :=
    (isCompact_closedBall c₁ ρ₁).exists_thickening_subset_open Metric.isOpen_ball hinside
  rw [thickening_closedBall hε_pos hρ₁.le] at hε_subset
  let σ : ℝ := ρ₁ + ε / 2
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ]
    linarith
  have hσ_gt : ρ₁ < σ := by
    dsimp [σ]
    linarith
  have hσ_lt : σ < ε + ρ₁ := by
    dsimp [σ]
    linarith
  have hσ_closed :
      Metric.closedBall c₁ σ ⊆ Metric.ball c₂ ρ₂ :=
    (Metric.closedBall_subset_ball hσ_lt).trans hε_subset
  have hsphere_subset_shell :
      Metric.sphere c₁ σ ⊆ shell := by
    intro z hz
    refine ⟨hσ_closed (Metric.sphere_subset_closedBall hz), ?_⟩
    have hz_dist : dist z c₁ = σ := by
      rwa [Metric.mem_sphere] at hz
    have hz_gt : ρ₁ < dist z c₁ := by
      rwa [hz_dist]
    simpa [Metric.mem_closedBall, not_le] using hz_gt
  let x₀ : ℂ := c₁ + σ
  have hx₀_sphere : x₀ ∈ Metric.sphere c₁ σ := by
    simp [x₀, Metric.mem_sphere, dist_eq_norm, Complex.norm_real, abs_of_nonneg hσ_nonneg]
  have hsphere_path :
      IsPathConnected (Metric.sphere c₁ σ) :=
    isPathConnected_sphere (by simp) c₁ hσ_nonneg
  -- Join every shell point to the intermediate sphere by a radial segment, then move along that
  -- connected sphere.
  have hshell_path :
      IsPathConnected shell := by
    refine ⟨x₀, hsphere_subset_shell hx₀_sphere, ?_⟩
    intro z hz
    let r : ℝ := dist z c₁
    have hr_gt : ρ₁ < r := by
      exact lt_of_not_ge (by simpa [r, Metric.mem_closedBall] using hz.2)
    have hr_nonneg : 0 ≤ r := dist_nonneg
    have hr_ne : r ≠ 0 := by
      linarith
    let proj : ℂ := c₁ + (σ / r) • (z - c₁)
    have hproj_sub : proj - c₁ = (σ / r) • (z - c₁) := by
      simp [proj]
    have hr_eq : ‖z - c₁‖ = r := by
      simp [r, dist_eq_norm]
    have hproj_sphere : proj ∈ Metric.sphere c₁ σ := by
      have hmul : (σ / r) * r = σ := by
        field_simp [hr_ne]
      have hproj_norm : ‖proj - c₁‖ = σ := by
        calc
          ‖proj - c₁‖ = ‖σ / r‖ * ‖z - c₁‖ := by
            rw [hproj_sub, norm_smul]
          _ = (σ / r) * r := by
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hσ_nonneg hr_nonneg), hr_eq]
          _ = σ := hmul
      simpa [Metric.mem_sphere, dist_eq_norm] using hproj_norm
    have hproj_mem_shell : proj ∈ shell := hsphere_subset_shell hproj_sphere
    have hradial_segment :
        segment ℝ proj z ⊆ shell := by
      intro y hy
      refine ⟨(convex_ball c₂ ρ₂).segment_subset hproj_mem_shell.1 hz.1 hy, ?_⟩
      rw [segment_eq_image_lineMap] at hy
      rcases hy with ⟨t, ht, rfl⟩
      have ht_nonneg : 0 ≤ (t : ℝ) := ht.1
      have ht_one_nonneg : 0 ≤ 1 - (t : ℝ) := by
        exact sub_nonneg.mpr ht.2
      have hσ_div_r_pos : 0 < σ / r := by
        have hσ_pos : 0 < σ := lt_trans hρ₁ hσ_gt
        exact div_pos hσ_pos (lt_trans hρ₁ hr_gt)
      have hcoeff_nonneg : 0 ≤ (1 - (t : ℝ)) * (σ / r) + (t : ℝ) := by
        nlinarith [ht_nonneg, ht_one_nonneg, hσ_div_r_pos]
      have hline :
          AffineMap.lineMap proj z t - c₁ =
            (((1 - (t : ℝ)) * (σ / r) + (t : ℝ)) : ℝ) • (z - c₁) := by
        rw [AffineMap.lineMap_apply_module]
        simp [smul_eq_mul, proj, sub_eq_add_neg]
        ring
      have hdist :
          dist (AffineMap.lineMap proj z t) c₁ =
            (1 - (t : ℝ)) * σ + (t : ℝ) * r := by
        calc
          dist (AffineMap.lineMap proj z t) c₁ = ‖AffineMap.lineMap proj z t - c₁‖ := by
            rw [dist_eq_norm]
          _ = |((1 - (t : ℝ)) * (σ / r) + (t : ℝ))| * ‖z - c₁‖ := by
            rw [hline, norm_smul, Real.norm_eq_abs]
          _ = (((1 - (t : ℝ)) * (σ / r) + (t : ℝ)) : ℝ) * r := by
            rw [abs_of_nonneg hcoeff_nonneg, hr_eq]
          _ = (1 - (t : ℝ)) * σ + (t : ℝ) * r := by
            field_simp [hr_ne]
      have hdist_gt : ρ₁ < dist (AffineMap.lineMap proj z t) c₁ := by
        rw [hdist]
        by_cases ht_one : (t : ℝ) = 1
        · subst ht_one
          simpa using hr_gt
        · have ht_lt_one : (t : ℝ) < 1 := lt_of_le_of_ne ht.2 ht_one
          nlinarith [hσ_gt, hr_gt, ht_nonneg, ht_lt_one]
      simpa [Metric.mem_closedBall, not_le] using hdist_gt
    have hbase_to_proj :
        JoinedIn shell x₀ proj :=
      (hsphere_path.joinedIn x₀ hx₀_sphere proj hproj_sphere).mono hsphere_subset_shell
    have hproj_to_z :
        JoinedIn shell proj z :=
      JoinedIn.of_segment_subset hradial_segment
    exact hbase_to_proj.trans hproj_to_z
  exact hshell_path.isConnected

/-- Helper for Exercise 2: the given connected open domain is exactly the shell between the two
frontier circles. -/
lemma domain_eq_nested_circle_shell_of_frontier_two_circles
    {D : Set ℂ} {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hD_open : IsOpen D)
    (hD_connected : IsConnected D)
    (hρ₁ : 0 < ρ₁)
    (hfrontier : frontier D = Metric.sphere c₁ ρ₁ ∪ Metric.sphere c₂ ρ₂)
    (hinside : Metric.closedBall c₁ ρ₁ ⊆ Metric.ball c₂ ρ₂) :
    D = Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁ := by
  let shell : Set ℂ := Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁
  have hρ₂ : 0 < ρ₂ := by
    have hc₁_ball : c₁ ∈ Metric.ball c₂ ρ₂ := hinside (by simpa [Metric.mem_closedBall] using hρ₁.le)
    have hc₁_lt : dist c₁ c₂ < ρ₂ := by
      simpa [Metric.mem_ball] using hc₁_ball
    exact lt_of_le_of_lt dist_nonneg hc₁_lt
  have hshell_connected : IsConnected shell :=
    shell_isConnected_of_closedBall_subset_ball hρ₁ hinside
  -- First force every point of `D` into the shell by connectedness of the distance functions to
  -- the two circle centers.
  have hdist_ne_inner : ∀ z ∈ D, dist z c₁ ≠ ρ₁ := by
    intro z hz hdist
    have hz_not_frontier : z ∉ frontier D := by
      intro hz_frontier
      have : z ∈ D ∩ frontier D := ⟨hz, hz_frontier⟩
      simpa [hD_open.inter_frontier_eq] using this
    apply hz_not_frontier
    rw [hfrontier]
    exact Or.inl (by rwa [Metric.mem_sphere])
  have hdist_ne_outer : ∀ z ∈ D, dist z c₂ ≠ ρ₂ := by
    intro z hz hdist
    have hz_not_frontier : z ∉ frontier D := by
      intro hz_frontier
      have : z ∈ D ∩ frontier D := ⟨hz, hz_frontier⟩
      simpa [hD_open.inter_frontier_eq] using this
    apply hz_not_frontier
    rw [hfrontier]
    exact Or.inr (by rwa [Metric.mem_sphere])
  have hdist_c₂_cont : ContinuousOn (fun z : ℂ ↦ dist z c₂) D :=
    (continuous_id.dist continuous_const).continuousOn
  have hdist_c₁_cont : ContinuousOn (fun z : ℂ ↦ dist z c₁) D :=
    (continuous_id.dist continuous_const).continuousOn
  have houter_lt :
      Set.MapsTo (fun z ↦ dist z c₂) D (Set.Iio ρ₂) := by
    rcases hD_connected.isPreconnected.mapsTo_Ioi_or_Iio
        (f := fun z ↦ dist z c₂) hdist_c₂_cont hdist_ne_outer with
      houter_gt | houter_lt
    · let z₁ : ℂ := c₁ + ρ₁
      exfalso
      have hz₁_sphere : z₁ ∈ Metric.sphere c₁ ρ₁ := by
        simp [z₁, Metric.mem_sphere, dist_eq_norm, Complex.norm_real, abs_of_nonneg hρ₁.le]
      have hz₁_frontier : z₁ ∈ frontier D := by
        rw [hfrontier]
        exact Or.inl hz₁_sphere
      have hclosure :
          closure D ⊆ {z | ρ₂ ≤ dist z c₂} := by
        refine closure_minimal ?_ (isClosed_le continuous_const (continuous_id.dist continuous_const))
        intro z hz
        have hz_gt : ρ₂ < dist z c₂ := houter_gt hz
        exact le_of_lt hz_gt
      have hz₁_ge : ρ₂ ≤ dist z₁ c₂ :=
        hclosure (frontier_subset_closure hz₁_frontier)
      have hz₁_lt : dist z₁ c₂ < ρ₂ := by
        simpa [Metric.mem_ball] using hinside (Metric.sphere_subset_closedBall hz₁_sphere)
      exact (not_lt_of_ge hz₁_ge) hz₁_lt
    · exact houter_lt
  have hinner_gt :
      Set.MapsTo (fun z ↦ dist z c₁) D (Set.Ioi ρ₁) := by
    rcases hD_connected.isPreconnected.mapsTo_Ioi_or_Iio
        (f := fun z ↦ dist z c₁) hdist_c₁_cont hdist_ne_inner with
      hinner_gt | hinner_lt
    · exact hinner_gt
    · let z₂ : ℂ := c₂ + ρ₂
      exfalso
      have hz₂_sphere : z₂ ∈ Metric.sphere c₂ ρ₂ := by
        simp [z₂, Metric.mem_sphere, dist_eq_norm, Complex.norm_real, abs_of_nonneg hρ₂.le]
      have hz₂_not_inner : z₂ ∉ Metric.closedBall c₁ ρ₁ := by
        intro hz₂_closed
        have hz₂_ball : z₂ ∈ Metric.ball c₂ ρ₂ := hinside hz₂_closed
        have hz₂_lt : dist z₂ c₂ < ρ₂ := by
          simpa [Metric.mem_ball] using hz₂_ball
        have hz₂_eq : dist z₂ c₂ = ρ₂ := by
          rwa [Metric.mem_sphere] at hz₂_sphere
        exact lt_irrefl ρ₂ (hz₂_eq ▸ hz₂_lt)
      have hz₂_frontier : z₂ ∈ frontier D := by
        rw [hfrontier]
        exact Or.inr hz₂_sphere
      have hclosure :
          closure D ⊆ Metric.closedBall c₁ ρ₁ := by
        refine closure_minimal ?_ Metric.isClosed_closedBall
        intro z hz
        exact by simpa [Metric.mem_closedBall] using le_of_lt (hinner_lt hz)
      exact hz₂_not_inner (hclosure (frontier_subset_closure hz₂_frontier))
  have hsubset_shell : D ⊆ shell := by
    intro z hz
    refine ⟨houter_lt hz, ?_⟩
    simpa [Metric.mem_closedBall, not_le] using hinner_gt hz
  -- With the frontier removed, `D` is a relatively clopen nonempty subset of the connected shell,
  -- so connectedness forces equality.
  have hfrontier_disjoint : Disjoint (frontier D) shell := by
    rw [hfrontier]
    refine disjoint_union_left.2 ⟨?_, ?_⟩
    · refine disjoint_left.2 ?_
      intro z hz_inner hz_shell
      exact hz_shell.2 (Metric.sphere_subset_closedBall hz_inner)
    · refine disjoint_left.2 ?_
      intro z hz_outer hz_shell
      have hz_lt : dist z c₂ < ρ₂ := by
        simpa [Metric.mem_ball] using hz_shell.1
      have hz_eq : dist z c₂ = ρ₂ := by
        rwa [Metric.mem_sphere] at hz_outer
      exact lt_irrefl ρ₂ (hz_eq ▸ hz_lt)
  have hclopen : IsClopen (((↑) : shell → ℂ) ⁻¹' D) := by
    simpa using isClopen_preimage_val (u := D) (v := shell) hD_open hfrontier_disjoint
  have hrel_nonempty : (((↑) : shell → ℂ) ⁻¹' D).Nonempty := by
    obtain ⟨z, hz⟩ := hD_connected.nonempty
    exact ⟨⟨z, hsubset_shell hz⟩, by simpa⟩
  haveI : PreconnectedSpace shell :=
    Subtype.preconnectedSpace hshell_connected.isPreconnected
  have hrel_univ : (((↑) : shell → ℂ) ⁻¹' D) = Set.univ :=
    IsClopen.eq_univ hclopen hrel_nonempty
  have hshell_subset : shell ⊆ D := by
    intro z hz
    have : (⟨z, hz⟩ : shell) ∈ (((↑) : shell → ℂ) ⁻¹' D) := by
      rw [hrel_univ]
      simp
    simpa using this
  exact subset_antisymm hsubset_shell hshell_subset

/-- Helper for Exercise 2: the common limiting-point ratio map converts the circle equation based
on `Complex.normSq (z - a)` into a linear inequality in the ratio norm. -/
lemma circle_ratio_normSq_factorization
    {a p q r : ℝ} (hq : q ≠ a) (hr : (a - p) * (a - q) = r ^ 2) (z : ℂ) :
    Complex.normSq (z - (p : ℂ)) - ((a - p) / (a - q)) * Complex.normSq (z - (q : ℂ)) =
      (1 - (a - p) / (a - q)) * (Complex.normSq (z - (a : ℂ)) - r ^ 2) := by
  rcases z with ⟨x, y⟩
  -- Expand the three `normSq` terms in coordinates and clear the single scalar denominator.
  simp [Complex.normSq]
  field_simp [hq]
  ring_nf at hr ⊢
  have hfactor : r ^ 2 - (-(a * p) - a * q + a ^ 2 + p * q) = 0 := by
    nlinarith
  have hzero : (p - q) * (r ^ 2 - (-(a * p) - a * q + a ^ 2 + p * q)) = 0 := by
    simp [hfactor]
  calc
    -(a * p * x * 2) + a * p ^ 2 + a * q * x * 2 - a * q ^ 2 + p * q ^ 2 + p * x ^ 2 + p * y ^ 2 -
        p ^ 2 * q - q * x ^ 2 - q * y ^ 2
      =
        (-(a * p * x * 2) + a * q * x * 2 + a ^ 2 * p - a ^ 2 * q - p * r ^ 2 + p * x ^ 2 +
          p * y ^ 2 + q * r ^ 2 - q * x ^ 2 - q * y ^ 2) +
          (p - q) * (r ^ 2 - (-(a * p) - a * q + a ^ 2 + p * q)) := by
            ring
    _ =
        -(a * p * x * 2) + a * q * x * 2 + a ^ 2 * p - a ^ 2 * q - p * r ^ 2 + p * x ^ 2 +
          p * y ^ 2 + q * r ^ 2 - q * x ^ 2 - q * y ^ 2 := by
            rw [hzero, add_zero]

/-- Helper for Exercise 2: if two circles are nested with distinct centers, then the point of the
inner circle lying farthest along the center line still belongs to the outer ball, so the center
distance plus the inner radius is strictly smaller than the outer radius. -/
lemma center_dist_add_inner_radius_lt_outer_radius_of_nested_circles
    {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hc : c₁ ≠ c₂)
    (hρ₁ : 0 < ρ₁)
    (hinside : Metric.closedBall c₁ ρ₁ ⊆ Metric.ball c₂ ρ₂) :
    dist c₁ c₂ + ρ₁ < ρ₂ := by
  let d : ℝ := dist c₁ c₂
  have hd_pos : 0 < d := by
    -- Distinct centers give a positive center distance.
    simpa [d, dist_eq_norm] using (norm_pos_iff.mpr (sub_ne_zero.mpr hc))
  have hd_ne : d ≠ 0 := hd_pos.ne'
  let t : ℝ := ρ₁ / d
  let z : ℂ := c₁ + (t : ℂ) * (c₁ - c₂)
  have hz_sub_c₁ : z - c₁ = (t : ℂ) * (c₁ - c₂) := by
    simp [z, sub_eq_add_neg]
  have hz_closed : z ∈ Metric.closedBall c₁ ρ₁ := by
    have hz_dist : dist z c₁ = ρ₁ := by
      -- Scale the center-direction vector so that its length is exactly the inner radius.
      calc
        dist z c₁ = ‖z - c₁‖ := by rw [dist_eq_norm]
        _ = ‖(t : ℂ) * (c₁ - c₂)‖ := by rw [hz_sub_c₁]
        _ = ‖(t : ℂ)‖ * ‖c₁ - c₂‖ := by rw [norm_mul]
        _ = |t| * d := by simp [Complex.norm_real, d, dist_eq_norm]
        _ = t * d := by
          rw [abs_of_nonneg]
          exact div_nonneg hρ₁.le hd_pos.le
        _ = ρ₁ := by
          dsimp [t]
          field_simp [hd_ne]
    simpa [Metric.mem_closedBall] using hz_dist.le
  have hz_ball : z ∈ Metric.ball c₂ ρ₂ := hinside hz_closed
  have hz_lt : dist z c₂ < ρ₂ := by
    simpa [Metric.mem_ball] using hz_ball
  have hz_sub_c₂ : z - c₂ = (1 + (t : ℂ)) * (c₁ - c₂) := by
    -- Move the translated point back to the outer center and factor out the shared direction.
    dsimp [z]
    ring
  have hnorm_one_add_t : ‖1 + (t : ℂ)‖ = |1 + t| := by
    simpa using (RCLike.norm_ofReal (K := ℂ) (1 + t))
  have hz_dist : dist z c₂ = d + ρ₁ := by
    -- The chosen point lies exactly `ρ₁` farther from `c₂` along the center line.
    calc
      dist z c₂ = ‖z - c₂‖ := by rw [dist_eq_norm]
      _ = ‖(1 + (t : ℂ)) * (c₁ - c₂)‖ := by rw [hz_sub_c₂]
      _ = ‖1 + (t : ℂ)‖ * ‖c₁ - c₂‖ := by rw [norm_mul]
      _ = |1 + t| * d := by rw [hnorm_one_add_t]; simp [d, dist_eq_norm]
      _ = (1 + t) * d := by
        rw [abs_of_nonneg]
        have ht_nonneg : 0 ≤ t := div_nonneg hρ₁.le hd_pos.le
        linarith
      _ = d + ρ₁ := by
        dsimp [t]
        field_simp [hd_ne]
  -- Reading the outer-ball membership of this extremal point gives the strict radius gap.
  linarith

/-- Helper for Exercise 2: once the center distance and radii satisfy Cartan's strict nesting
gap, the real limiting-point quadratic has positive discriminant and its two roots `p < q`
satisfy the expected Vieta identities. -/
lemma real_limiting_pair_vieta
    {d ρ₁ ρ₂ : ℝ}
    (hd : 0 < d)
    (hρ₁ : 0 < ρ₁)
    (hgap : d + ρ₁ < ρ₂) :
    let s : ℝ := (d ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / d
    let Δ : ℝ := s ^ 2 - 4 * ρ₂ ^ 2
    let p : ℝ := (s - Real.sqrt Δ) / 2
    let q : ℝ := (s + Real.sqrt Δ) / 2
    0 ≤ Δ ∧ p * q = ρ₂ ^ 2 ∧ (d - p) * (d - q) = ρ₁ ^ 2 ∧ p < q := by
  dsimp
  set s : ℝ := (d ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / d with hs
  set Δ : ℝ := s ^ 2 - 4 * ρ₂ ^ 2 with hΔ
  set p : ℝ := (s - Real.sqrt Δ) / 2 with hp
  set q : ℝ := (s + Real.sqrt Δ) / 2 with hq
  have hd_ne : d ≠ 0 := hd.ne'
  have hρ₂ : 0 < ρ₂ := by
    -- The strict gap immediately forces the outer radius to be positive.
    linarith
  have houter_sq_pos : 0 < ρ₂ ^ 2 - (d + ρ₁) ^ 2 := by
    -- This is the textbook inequality `(d + ρ₁)^2 < ρ₂^2`.
    nlinarith
  have hinner_sq_le : (d - ρ₁) ^ 2 ≤ (d + ρ₁) ^ 2 := by
    -- The smaller absolute center-line offset is bounded by the larger one.
    nlinarith
  have hinner_sq_pos : 0 < ρ₂ ^ 2 - (d - ρ₁) ^ 2 := by
    -- The second quadratic factor stays positive because `(d - ρ₁)^2` is no larger.
    nlinarith
  have hΔ_factor :
      Δ = ((ρ₂ ^ 2 - (d + ρ₁) ^ 2) * (ρ₂ ^ 2 - (d - ρ₁) ^ 2)) / d ^ 2 := by
    -- Factor the discriminant into the two source-geometric center-line terms.
    rw [hΔ, hs]
    field_simp [hd_ne]
    ring
  have hΔ_pos : 0 < Δ := by
    -- Every factor in the discriminant expression is positive under the strict nesting gap.
    rw [hΔ_factor]
    refine div_pos ?_ (sq_pos_of_ne_zero hd_ne)
    positivity
  have hΔ_nonneg : 0 ≤ Δ := le_of_lt hΔ_pos
  have hsqrt_sq : Real.sqrt Δ ^ 2 = Δ := by
    exact Real.sq_sqrt hΔ_nonneg
  have hpq : p * q = ρ₂ ^ 2 := by
    -- Multiply the two quadratic roots and substitute the discriminant definition.
    rw [hp, hq]
    nlinarith [hΔ, hsqrt_sq]
  have hsum : p + q = s := by
    -- The two roots also sum to the normalized center-line parameter `s`.
    rw [hp, hq]
    ring
  have hs_circle : d ^ 2 - d * s + ρ₂ ^ 2 = ρ₁ ^ 2 := by
    -- Rewriting `s` recovers the second circle equation on the center line.
    rw [hs]
    field_simp [hd_ne]
    ring
  have hinner : (d - p) * (d - q) = ρ₁ ^ 2 := by
    -- Expand the product and replace `p + q` and `p q` by the Vieta data.
    nlinarith [hpq, hsum, hs_circle]
  have hp_lt_hq : p < q := by
    -- The roots are distinct because the discriminant is strictly positive.
    rw [hp, hq]
    have hsqrt_pos : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ_pos
    nlinarith
  exact ⟨hΔ_nonneg, hpq, hinner, hp_lt_hq⟩

/-- Helper for Exercise 2: evaluating the limiting-point quadratic at `d`, `d + ρ₁`, and `ρ₂`
produces the sign pattern used in Cartan's center-line argument. -/
lemma real_limiting_pair_centerline_signs
    {d ρ₁ ρ₂ p q : ℝ}
    (hd : 0 < d)
    (hρ₁ : 0 < ρ₁)
    (hgap : d + ρ₁ < ρ₂)
    (hpq : p * q = ρ₂ ^ 2)
    (hinner : (d - p) * (d - q) = ρ₁ ^ 2)
    (hsum : p + q = (d ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / d) :
    0 < (d - p) * (d - q) ∧
      ((d + ρ₁) - p) * ((d + ρ₁) - q) < 0 ∧
      (ρ₂ - p) * (ρ₂ - q) < 0 := by
  have hd_ne : d ≠ 0 := hd.ne'
  have hρ₂ : 0 < ρ₂ := by
    -- The strict nesting gap already forces the outer radius to be positive.
    linarith
  have hd_sign : 0 < (d - p) * (d - q) := by
    -- The inner-circle equation identifies the first value with `ρ₁ ^ 2`.
    rw [hinner]
    positivity
  have hmid_eval :
      d * (((d + ρ₁) - p) * ((d + ρ₁) - q)) =
        ρ₁ * ((d + ρ₁) ^ 2 - ρ₂ ^ 2) := by
    -- Rewrite the quadratic at `d + ρ₁` using the Vieta relations.
    calc
      d * (((d + ρ₁) - p) * ((d + ρ₁) - q)) =
          d * (d + ρ₁) ^ 2 - d * (p + q) * (d + ρ₁) + d * (p * q) := by
            ring
      _ =
          d * (d + ρ₁) ^ 2 -
            d * (((d ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / d)) * (d + ρ₁) +
              d * (ρ₂ ^ 2) := by
                rw [hsum, hpq]
      _ = ρ₁ * ((d + ρ₁) ^ 2 - ρ₂ ^ 2) := by
            field_simp [hd_ne]
            ring
  have hmid_rhs_neg : ρ₁ * ((d + ρ₁) ^ 2 - ρ₂ ^ 2) < 0 := by
    -- The center-line point `d + ρ₁` still lies strictly inside the outer circle.
    have hsquare_neg : (d + ρ₁) ^ 2 - ρ₂ ^ 2 < 0 := by
      nlinarith [hgap]
    exact mul_neg_of_pos_of_neg hρ₁ hsquare_neg
  have hmid_sign : ((d + ρ₁) - p) * ((d + ρ₁) - q) < 0 := by
    -- Divide the negative evaluation by the positive scalar `d`.
    nlinarith [hmid_eval, hd, hmid_rhs_neg]
  have houter_eval :
      d * ((ρ₂ - p) * (ρ₂ - q)) =
        ρ₂ * (ρ₁ ^ 2 - (ρ₂ - d) ^ 2) := by
    -- The same Vieta rewrite at `ρ₂` exposes the second textbook sign.
    calc
      d * ((ρ₂ - p) * (ρ₂ - q)) =
          d * ρ₂ ^ 2 - d * (p + q) * ρ₂ + d * (p * q) := by
            ring
      _ =
          d * ρ₂ ^ 2 - d * (((d ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / d)) * ρ₂ + d * (ρ₂ ^ 2) := by
            rw [hsum, hpq]
      _ = ρ₂ * (ρ₁ ^ 2 - (ρ₂ - d) ^ 2) := by
            field_simp [hd_ne]
            ring
  have houter_rhs_neg : ρ₂ * (ρ₁ ^ 2 - (ρ₂ - d) ^ 2) < 0 := by
    -- Cartan's gap is equivalent to `ρ₁ < ρ₂ - d`, hence the bracket is negative.
    have hgap' : ρ₁ < ρ₂ - d := by
      linarith
    have hsquare_neg : ρ₁ ^ 2 - (ρ₂ - d) ^ 2 < 0 := by
      nlinarith [hgap']
    exact mul_neg_of_pos_of_neg hρ₂ hsquare_neg
  have houter_sign : (ρ₂ - p) * (ρ₂ - q) < 0 := by
    -- Again divide by the positive center distance.
    nlinarith [houter_eval, hd, houter_rhs_neg]
  exact ⟨hd_sign, hmid_sign, houter_sign⟩

/-- Helper for Exercise 2: the center-line sign pattern forces the limiting points to satisfy the
strict order `0 < d < p < d + ρ₁ < ρ₂ < q`, and therefore the annulus ratio lies in `(0, 1)`. -/
lemma real_limiting_pair_order_of_signs
    {d ρ₁ ρ₂ p q : ℝ}
    (hd : 0 < d)
    (hρ₁ : 0 < ρ₁)
    (hgap : d + ρ₁ < ρ₂)
    (hp_lt_hq : p < q)
    (hd_sign : 0 < (d - p) * (d - q))
    (hmid_sign : ((d + ρ₁) - p) * ((d + ρ₁) - q) < 0)
    (houter_sign : (ρ₂ - p) * (ρ₂ - q) < 0) :
    0 < p ∧ d < p ∧ p < d + ρ₁ ∧ ρ₂ < q ∧
      0 < ((q / p) * ((d - p) / (d - q))) ∧
      ((q / p) * ((d - p) / (d - q))) < 1 := by
  have hp_lt_mid : p < d + ρ₁ := by
    -- A negative product can only occur between the two ordered roots.
    by_contra hp_ge
    have hmid_le_p : d + ρ₁ ≤ p := not_lt.mp hp_ge
    have hmid_sub_p : d + ρ₁ - p ≤ 0 := sub_nonpos.mpr hmid_le_p
    have hmid_sub_q : d + ρ₁ - q < 0 := sub_neg.mpr (lt_of_le_of_lt hmid_le_p hp_lt_hq)
    have hnonneg : 0 ≤ ((d + ρ₁) - p) * ((d + ρ₁) - q) := by
      nlinarith
    linarith
  have hmid_lt_q : d + ρ₁ < q := by
    -- The same sign argument excludes the point from the region to the right of `q`.
    by_contra hq_le
    have hq_le_mid : q ≤ d + ρ₁ := not_lt.mp hq_le
    have hmid_sub_p : 0 < d + ρ₁ - p := by
      exact sub_pos.mpr (lt_of_lt_of_le hp_lt_hq hq_le_mid)
    have hmid_sub_q : 0 ≤ d + ρ₁ - q := sub_nonneg.mpr hq_le_mid
    have hnonneg : 0 ≤ ((d + ρ₁) - p) * ((d + ρ₁) - q) := by
      nlinarith
    linarith
  have hp_lt_outer : p < ρ₂ := by
    -- Evaluating at `ρ₂` gives the same interval placement for the outer boundary point.
    by_contra hp_ge
    have houter_le_p : ρ₂ ≤ p := not_lt.mp hp_ge
    have houter_sub_p : ρ₂ - p ≤ 0 := sub_nonpos.mpr houter_le_p
    have houter_sub_q : ρ₂ - q < 0 := sub_neg.mpr (lt_of_le_of_lt houter_le_p hp_lt_hq)
    have hnonneg : 0 ≤ (ρ₂ - p) * (ρ₂ - q) := by
      nlinarith
    linarith
  have houter_lt_q : ρ₂ < q := by
    -- And it cannot lie to the right of `q` either.
    by_contra hq_le
    have hq_le_outer : q ≤ ρ₂ := not_lt.mp hq_le
    have houter_sub_p : 0 < ρ₂ - p := by
      exact sub_pos.mpr (lt_of_lt_of_le hp_lt_hq hq_le_outer)
    have houter_sub_q : 0 ≤ ρ₂ - q := sub_nonneg.mpr hq_le_outer
    have hnonneg : 0 ≤ (ρ₂ - p) * (ρ₂ - q) := by
      nlinarith
    linarith
  have hd_lt_q : d < q := by
    -- The point `d` lies to the left of `q` because `d + ρ₁` already does.
    linarith
  have hd_lt_p : d < p := by
    -- Since the value at `d` is positive, `d` cannot lie between the two roots.
    by_contra hp_le
    have hp_le_d : p ≤ d := not_lt.mp hp_le
    have hd_sub_p : 0 ≤ d - p := sub_nonneg.mpr hp_le_d
    have hd_sub_q : d - q < 0 := sub_neg.mpr hd_lt_q
    have hnonpos : (d - p) * (d - q) ≤ 0 := by
      nlinarith
    linarith
  have hp_pos : 0 < p := by
    -- Positivity of `p` follows from the already-positive center distance.
    linarith
  have hq_pos : 0 < q := lt_trans hp_pos hp_lt_hq
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hdq_ne : d - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hd_lt_q)
  have hqd_pos : 0 < q - d := sub_pos.mpr hd_lt_q
  have hratio_pos : 0 < ((q / p) * ((d - p) / (d - q))) := by
    -- Every factor is positive after noting that both differences from `d` are negative.
    have hq_div_p : 0 < q / p := div_pos hq_pos hp_pos
    have hdiff_div : 0 < (d - p) / (d - q) := by
      exact div_pos_of_neg_of_neg (sub_neg.mpr hd_lt_p) (sub_neg.mpr hd_lt_q)
    exact mul_pos hq_div_p hdiff_div
  have hratio_eq :
      ((q / p) * ((d - p) / (d - q))) = (q * (p - d)) / (p * (q - d)) := by
    -- Rewrite the radius ratio using only positive denominator factors.
    field_simp [hp_ne, hdq_ne]
    ring
  have hratio_lt : ((q / p) * ((d - p) / (d - q))) < 1 := by
    -- Cross-multiplication reduces the final bound to the strict root ordering `p < q`.
    rw [hratio_eq]
    have hden_pos : 0 < p * (q - d) := mul_pos hp_pos hqd_pos
    have hcross : q * (p - d) < p * (q - d) := by
      nlinarith
    have hdiv_lt :
        (q * (p - d)) / (p * (q - d)) < (p * (q - d)) / (p * (q - d)) := by
      exact div_lt_div_of_pos_right hcross hden_pos
    simpa [hden_pos.ne'] using hdiv_lt
  exact ⟨hp_pos, hd_lt_p, hp_lt_mid, houter_lt_q, hratio_pos, hratio_lt⟩

/-- Helper for Cartan section26 0012_Exercise_2: rotating by a unit complex scalar and translating
by `c₂` identifies the original shell with the normalized shell centered at `0` and `d`. -/
lemma mem_normalizedShell_iff
    {c₁ c₂ u z : ℂ} {ρ₁ ρ₂ d : ℝ}
    (hu_norm : ‖u‖ = 1)
    (hu_center : u * (c₁ - c₂) = (d : ℂ)) :
    z ∈ Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁ ↔
      u * (z - c₂) ∈ Metric.ball 0 ρ₂ \ Metric.closedBall (d : ℂ) ρ₁ := by
  constructor
  · intro hz
    rcases hz with ⟨hz_ball, hz_closed⟩
    refine ⟨?_, ?_⟩
    · -- The affine normalization preserves the outer distance because `u` has unit norm.
      have hdist :
          dist (u * (z - c₂)) 0 = dist z c₂ := by
        rw [dist_eq_norm, dist_eq_norm, sub_zero]
        simpa [norm_mul, hu_norm]
      rw [Metric.mem_ball]
      rw [hdist]
      exact hz_ball
    · -- The inner-center shift becomes `d` after the same normalization.
      have hdist :
          dist (u * (z - c₂)) (d : ℂ) = dist z c₁ := by
        rw [dist_eq_norm,
          show u * (z - c₂) - (d : ℂ) = u * (z - c₁) by
            calc
              u * (z - c₂) - (d : ℂ) = u * (z - c₂) - u * (c₁ - c₂) := by
                  rw [hu_center]
              _ = u * ((z - c₂) - (c₁ - c₂)) := by ring
              _ = u * (z - c₁) := by ring,
          dist_eq_norm]
        simpa [norm_mul, hu_norm]
      intro hz_mem
      apply hz_closed
      have hz_dist : dist (u * (z - c₂)) (d : ℂ) ≤ ρ₁ := by
        simpa [Metric.mem_closedBall] using hz_mem
      rw [Metric.mem_closedBall, ← hdist]
      exact hz_dist
  · intro hz
    rcases hz with ⟨hz_ball, hz_closed⟩
    refine ⟨?_, ?_⟩
    · -- The same norm preservation brings the normalized outer ball back to the original one.
      have hdist :
          dist (u * (z - c₂)) 0 = dist z c₂ := by
        rw [dist_eq_norm, dist_eq_norm, sub_zero]
        simpa [norm_mul, hu_norm]
      rw [Metric.mem_ball] at hz_ball ⊢
      rw [← hdist]
      exact hz_ball
    · -- And the normalized inner closed ball pulls back to the original inner closed ball.
      have hdist :
          dist (u * (z - c₂)) (d : ℂ) = dist z c₁ := by
        rw [dist_eq_norm,
          show u * (z - c₂) - (d : ℂ) = u * (z - c₁) by
            calc
              u * (z - c₂) - (d : ℂ) = u * (z - c₂) - u * (c₁ - c₂) := by
                  rw [hu_center]
              _ = u * ((z - c₂) - (c₁ - c₂)) := by ring
              _ = u * (z - c₁) := by ring,
          dist_eq_norm]
        simpa [norm_mul, hu_norm]
      intro hz_mem
      apply hz_closed
      have hz_dist : dist z c₁ ≤ ρ₁ := by
        simpa [Metric.mem_closedBall] using hz_mem
      rw [Metric.mem_closedBall, hdist]
      exact hz_dist

/-- Helper for Cartan section26 0012_Exercise_2: the outer boundary inequality for the normalized
limiting-point ratio is exactly the normalized outer-ball inequality in `Complex.normSq` form. -/
lemma outerRatio_normSq_lt_one_iff
    {p q ρ₂ lam : ℝ} {ζ : ℂ}
    (hpq : p * q = ρ₂ ^ 2)
    (hp_pos : 0 < p)
    (hq_pos : 0 < q)
    (hp_lt_hq : p < q)
    (hlam_sq : lam ^ 2 = q / p)
    (hζq : ζ ≠ q) :
    Complex.normSq (((lam : ℂ) * (ζ - p) / (ζ - q)) : ℂ) < 1 ↔
      Complex.normSq ζ < ρ₂ ^ 2 := by
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hζq' : ζ - (q : ℂ) ≠ 0 := sub_ne_zero.mpr hζq
  have hden_pos : 0 < Complex.normSq (ζ - (q : ℂ)) := by
    rw [Complex.normSq_pos]
    exact hζq'
  have hlam_sq' : Complex.normSq (lam : ℂ) = q / p := by
    simpa [Complex.normSq_ofReal, pow_two] using hlam_sq
  have hfactor :
      Complex.normSq (ζ - (p : ℂ)) - (p / q) * Complex.normSq (ζ - (q : ℂ)) =
        (1 - p / q) * (Complex.normSq ζ - ρ₂ ^ 2) := by
    have houter : (0 - p) * (0 - q) = ρ₂ ^ 2 := by
      simpa using hpq
    -- Route correction: isolate the `a = 0` factorization before converting to an annulus bound.
    simpa using
      (circle_ratio_normSq_factorization (a := 0) (p := p) (q := q) (r := ρ₂) hq_ne houter ζ)
  have hcoeff_pos : 0 < 1 - p / q := by
    have hdiv_lt : p / q < 1 := by
      exact (div_lt_iff₀ hq_pos).2 (by simpa using hp_lt_hq)
    linarith
  constructor
  · intro hratio
    -- First clear the positive denominator `Complex.normSq (ζ - q)`.
    have hratio' :
        ((q / p) * Complex.normSq (ζ - (p : ℂ))) / Complex.normSq (ζ - (q : ℂ)) < 1 := by
      simpa [Complex.normSq_div, Complex.normSq_mul, hlam_sq'] using hratio
    have hcross : (q / p) * Complex.normSq (ζ - (p : ℂ)) < Complex.normSq (ζ - (q : ℂ)) := by
      simpa using (div_lt_iff₀ hden_pos).1 hratio'
    have hscaled :
        (p / q) * ((q / p) * Complex.normSq (ζ - (p : ℂ))) <
          (p / q) * Complex.normSq (ζ - (q : ℂ)) := by
      exact mul_lt_mul_of_pos_left hcross (div_pos hp_pos hq_pos)
    have hineq :
        Complex.normSq (ζ - (p : ℂ)) - (p / q) * Complex.normSq (ζ - (q : ℂ)) < 0 := by
      have hscaled' :
          Complex.normSq (ζ - (p : ℂ)) < (p / q) * Complex.normSq (ζ - (q : ℂ)) := by
        calc
          Complex.normSq (ζ - (p : ℂ))
              = (p / q) * ((q / p) * Complex.normSq (ζ - (p : ℂ))) := by
                  field_simp [hp_ne, hq_ne]
          _ < (p / q) * Complex.normSq (ζ - (q : ℂ)) := hscaled
      linarith
    -- Then the positive factor `1 - p / q` preserves the sign of the factorized term.
    rw [hfactor] at hineq
    nlinarith [hineq, hcoeff_pos]
  · intro houter
    -- Reverse the same algebraic steps to recover the annulus outer inequality.
    have hineq :
        Complex.normSq (ζ - (p : ℂ)) - (p / q) * Complex.normSq (ζ - (q : ℂ)) < 0 := by
      rw [hfactor]
      nlinarith [houter, hcoeff_pos]
    have hscaled :
        Complex.normSq (ζ - (p : ℂ)) < (p / q) * Complex.normSq (ζ - (q : ℂ)) := by
      linarith
    have hcross :
        (q / p) * Complex.normSq (ζ - (p : ℂ)) < Complex.normSq (ζ - (q : ℂ)) := by
      calc
        (q / p) * Complex.normSq (ζ - (p : ℂ))
            < (q / p) * ((p / q) * Complex.normSq (ζ - (q : ℂ))) := by
                exact mul_lt_mul_of_pos_left hscaled (div_pos hq_pos hp_pos)
        _ = Complex.normSq (ζ - (q : ℂ)) := by
              field_simp [hp_ne, hq_ne]
    have hratio' :
        ((q / p) * Complex.normSq (ζ - (p : ℂ))) / Complex.normSq (ζ - (q : ℂ)) < 1 := by
      exact (div_lt_iff₀ hden_pos).2 (by simpa using hcross)
    simpa [Complex.normSq_div, Complex.normSq_mul, hlam_sq'] using hratio'

/-- Helper for Cartan section26 0012_Exercise_2: the inner boundary inequality for the normalized
limiting-point ratio is exactly the normalized inner-circle inequality in `Complex.normSq` form. -/
lemma innerRatio_sq_lt_normSq_iff
    {d p q ρ₁ lam r : ℝ} {ζ : ℂ}
    (hinner : (d - p) * (d - q) = ρ₁ ^ 2)
    (hp_pos : 0 < p)
    (hq_pos : 0 < q)
    (hp_lt_hq : p < q)
    (hd_lt_p : d < p)
    (hlam_sq : lam ^ 2 = q / p)
    (hr_sq : r ^ 2 = (q / p) * ((d - p) / (d - q)))
    (hζq : ζ ≠ q) :
    r ^ 2 < Complex.normSq (((lam : ℂ) * (ζ - p) / (ζ - q)) : ℂ) ↔
      ρ₁ ^ 2 < Complex.normSq (ζ - (d : ℂ)) := by
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hq_pos' : 0 < q / p := div_pos hq_pos hp_pos
  have hd_lt_q : d < q := lt_trans hd_lt_p hp_lt_hq
  have hdq_ne : d - q ≠ 0 := sub_ne_zero.mpr (by linarith)
  have hζq' : ζ - (q : ℂ) ≠ 0 := sub_ne_zero.mpr hζq
  have hden_pos : 0 < Complex.normSq (ζ - (q : ℂ)) := by
    rw [Complex.normSq_pos]
    exact hζq'
  have hlam_sq' : Complex.normSq (lam : ℂ) = q / p := by
    simpa [Complex.normSq_ofReal, pow_two] using hlam_sq
  have hfactor :
      Complex.normSq (ζ - (p : ℂ)) - ((d - p) / (d - q)) * Complex.normSq (ζ - (q : ℂ)) =
        (1 - (d - p) / (d - q)) * (Complex.normSq (ζ - (d : ℂ)) - ρ₁ ^ 2) := by
    -- Route correction: handle the `a = d` factorization on its own before any annulus packaging.
    simpa using
      (circle_ratio_normSq_factorization (a := d) (p := p) (q := q) (r := ρ₁)
        (by linarith) hinner ζ)
  have hcoeff_pos : 0 < 1 - (d - p) / (d - q) := by
    have hdq_neg : d - q < 0 := by
      linarith
    have hratio_lt_one : (d - p) / (d - q) < 1 := by
      exact (div_lt_iff_of_neg hdq_neg).2 (by linarith)
    linarith
  constructor
  · intro hratio
    -- First normalize the ratio inequality back to the linear factorization inequality.
    have hratio' :
        (q / p) * ((d - p) / (d - q)) <
          ((q / p) * Complex.normSq (ζ - (p : ℂ))) / Complex.normSq (ζ - (q : ℂ)) := by
      simpa [Complex.normSq_div, Complex.normSq_mul, hlam_sq', hr_sq] using hratio
    have hcross0 :
        ((q / p) * ((d - p) / (d - q))) * Complex.normSq (ζ - (q : ℂ)) <
          (q / p) * Complex.normSq (ζ - (p : ℂ)) := by
      exact (lt_div_iff₀ hden_pos).1 hratio'
    have hcross :
        ((d - p) / (d - q)) * Complex.normSq (ζ - (q : ℂ)) <
          Complex.normSq (ζ - (p : ℂ)) := by
      nlinarith [hcross0, hq_pos']
    have hineq :
        0 <
          Complex.normSq (ζ - (p : ℂ)) - ((d - p) / (d - q)) * Complex.normSq (ζ - (q : ℂ)) := by
      linarith
    -- Then the positive factor `1 - (d - p) / (d - q)` preserves positivity.
    rw [hfactor] at hineq
    nlinarith [hineq, hcoeff_pos]
  · intro hinner'
    -- Reverse the same factorization route back to the ratio inequality.
    have hineq :
        0 <
          Complex.normSq (ζ - (p : ℂ)) - ((d - p) / (d - q)) * Complex.normSq (ζ - (q : ℂ)) := by
      rw [hfactor]
      nlinarith [hinner', hcoeff_pos]
    have hcross :
        ((d - p) / (d - q)) * Complex.normSq (ζ - (q : ℂ)) <
          Complex.normSq (ζ - (p : ℂ)) := by
      linarith
    have hdiv :
        (d - p) / (d - q) <
          Complex.normSq (ζ - (p : ℂ)) / Complex.normSq (ζ - (q : ℂ)) := by
      exact (lt_div_iff₀ hden_pos).2 hcross
    have hratio' :
        (q / p) * ((d - p) / (d - q)) <
          ((q / p) * Complex.normSq (ζ - (p : ℂ))) / Complex.normSq (ζ - (q : ℂ)) := by
      have hcross0 :
          ((q / p) * ((d - p) / (d - q))) * Complex.normSq (ζ - (q : ℂ)) <
            (q / p) * Complex.normSq (ζ - (p : ℂ)) := by
        nlinarith [hcross, hq_pos']
      exact (lt_div_iff₀ hden_pos).2 hcross0
    simpa [Complex.normSq_div, Complex.normSq_mul, hlam_sq', hr_sq] using hratio'

/-- Helper for Cartan section26 0012_Exercise_2: the limiting-point ratio sends the normalized
shell to the standard annulus with inner radius `r` and outer radius `1`. -/
lemma limitingRatio_mem_standardAnnulus_iff
    {d p q ρ₁ ρ₂ lam r : ℝ} {ζ : ℂ}
    (hpq : p * q = ρ₂ ^ 2)
    (hinner : (d - p) * (d - q) = ρ₁ ^ 2)
    (hρ₁_pos : 0 < ρ₁)
    (hρ₂_pos : 0 < ρ₂)
    (hp_pos : 0 < p)
    (hq_pos : 0 < q)
    (hp_lt_hq : p < q)
    (hd_lt_p : d < p)
    (hρ₂_lt_q : ρ₂ < q)
    (hlam_sq : lam ^ 2 = q / p)
    (hr_nonneg : 0 ≤ r)
    (hr_pos : 0 < r)
    (hr_sq : r ^ 2 = (q / p) * ((d - p) / (d - q))) :
    ζ ∈ Metric.ball 0 ρ₂ \ Metric.closedBall (d : ℂ) ρ₁ ↔
      ((lam : ℂ) * (ζ - p) / (ζ - q)) ∈ complexOpenAnnulus (ENNReal.ofReal r) 1 := by
  constructor
  · intro hζ
    rcases hζ with ⟨hζ_ball, hζ_closed⟩
    have hζq : ζ ≠ q := by
      intro hζq
      have hq_lt : q < ρ₂ := by
        simpa [hζq, Metric.mem_ball, dist_eq_norm, Complex.norm_real, abs_of_pos hq_pos] using hζ_ball
      linarith
    have houter_sq : Complex.normSq ζ < ρ₂ ^ 2 := by
      have houter : ‖ζ‖ < ρ₂ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hζ_ball
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_lt_sq₀ (norm_nonneg _) hρ₂_pos.le).2 houter
    have hinner_sq : ρ₁ ^ 2 < Complex.normSq (ζ - (d : ℂ)) := by
      have hinner : ρ₁ < ‖ζ - (d : ℂ)‖ := by
        have hnot : ¬ ‖ζ - (d : ℂ)‖ ≤ ρ₁ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hζ_closed
        exact lt_of_not_ge hnot
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_lt_sq₀ hρ₁_pos.le (norm_nonneg _)).2 hinner
    have hleft_sq :
        r ^ 2 < Complex.normSq (((lam : ℂ) * (ζ - p) / (ζ - q)) : ℂ) :=
      (innerRatio_sq_lt_normSq_iff hinner hp_pos hq_pos hp_lt_hq hd_lt_p hlam_sq hr_sq hζq).2
        hinner_sq
    have hright_sq :
        Complex.normSq (((lam : ℂ) * (ζ - p) / (ζ - q)) : ℂ) < 1 :=
      (outerRatio_normSq_lt_one_iff hpq hp_pos hq_pos hp_lt_hq hlam_sq hζq).2 houter_sq
    have hleft : r < ‖((lam : ℂ) * (ζ - p) / (ζ - q) : ℂ)‖ := by
      have hleft_sq' := hleft_sq
      rw [Complex.normSq_eq_norm_sq] at hleft_sq'
      exact (sq_lt_sq₀ hr_nonneg (norm_nonneg _)).1 hleft_sq'
    have hright : ‖((lam : ℂ) * (ζ - p) / (ζ - q) : ℂ)‖ < 1 := by
      have hright_sq' := hright_sq
      rw [Complex.normSq_eq_norm_sq] at hright_sq'
      have hright_sq'' : ‖((lam : ℂ) * (ζ - p) / (ζ - q) : ℂ)‖ ^ 2 < 1 ^ 2 := by
        simpa [one_pow] using hright_sq'
      exact (sq_lt_sq₀ (norm_nonneg _) zero_le_one).1 hright_sq''
    -- Reassemble the two normalized norm inequalities into annulus membership.
    exact (mem_standard_annulus_iff hr_nonneg).2 ⟨hleft, hright⟩
  · intro hζ
    have hannulus := (mem_standard_annulus_iff hr_nonneg).1 hζ
    have hζq : ζ ≠ q := by
      intro hζq
      have hnorm_gt : r < ‖((lam : ℂ) * (ζ - p) / (ζ - q) : ℂ)‖ := hannulus.1
      simp [hζq] at hnorm_gt
      linarith
    have hleft_sq :
        r ^ 2 < Complex.normSq (((lam : ℂ) * (ζ - p) / (ζ - q)) : ℂ) := by
      have hleft_sq' : r ^ 2 < ‖((lam : ℂ) * (ζ - p) / (ζ - q) : ℂ)‖ ^ 2 :=
        (sq_lt_sq₀ hr_nonneg (norm_nonneg _)).2 hannulus.1
      rwa [Complex.normSq_eq_norm_sq]
    have hright_sq :
        Complex.normSq (((lam : ℂ) * (ζ - p) / (ζ - q)) : ℂ) < 1 := by
      have hright_sq' : ‖((lam : ℂ) * (ζ - p) / (ζ - q) : ℂ)‖ ^ 2 < 1 ^ 2 :=
        (sq_lt_sq₀ (norm_nonneg _) zero_le_one).2 hannulus.2
      rw [Complex.normSq_eq_norm_sq]
      simpa [one_pow] using hright_sq'
    have hinner_sq : ρ₁ ^ 2 < Complex.normSq (ζ - (d : ℂ)) :=
      (innerRatio_sq_lt_normSq_iff hinner hp_pos hq_pos hp_lt_hq hd_lt_p hlam_sq hr_sq hζq).1
        hleft_sq
    have houter_sq : Complex.normSq ζ < ρ₂ ^ 2 :=
      (outerRatio_normSq_lt_one_iff hpq hp_pos hq_pos hp_lt_hq hlam_sq hζq).1 hright_sq
    have houter : ‖ζ‖ < ρ₂ := by
      have houter_sq' := houter_sq
      rw [Complex.normSq_eq_norm_sq] at houter_sq'
      exact (sq_lt_sq₀ (norm_nonneg _) hρ₂_pos.le).1 houter_sq'
    have hinner : ρ₁ < ‖ζ - (d : ℂ)‖ := by
      have hinner_sq' := hinner_sq
      rw [Complex.normSq_eq_norm_sq] at hinner_sq'
      exact (sq_lt_sq₀ hρ₁_pos.le (norm_nonneg _)).1 hinner_sq'
    -- Convert the two recovered norm inequalities back to shell membership.
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using houter
    · simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hinner

/-- Helper for Cartan section26 0012_Exercise_2: the normalized limiting-point ratio is bijective
between the normalized shell and the standard annulus. -/
lemma normalizedLimitingRatio_bijOn
    {d p q ρ₁ ρ₂ lam r : ℝ}
    (hpq : p * q = ρ₂ ^ 2)
    (hinner : (d - p) * (d - q) = ρ₁ ^ 2)
    (hρ₁_pos : 0 < ρ₁)
    (hρ₂_pos : 0 < ρ₂)
    (hp_pos : 0 < p)
    (hq_pos : 0 < q)
    (hp_lt_hq : p < q)
    (hd_lt_p : d < p)
    (hρ₂_lt_q : ρ₂ < q)
    (hlam_sq : lam ^ 2 = q / p)
    (hlam_one : 1 < lam)
    (hr_nonneg : 0 ≤ r)
    (hr_pos : 0 < r)
    (hr_sq : r ^ 2 = (q / p) * ((d - p) / (d - q))) :
    BijOn (fun ζ : ℂ ↦ ((lam : ℂ) * (ζ - p) / (ζ - q)))
      (Metric.ball 0 ρ₂ \ Metric.closedBall (d : ℂ) ρ₁)
      (complexOpenAnnulus (ENNReal.ofReal r) 1) := by
  let W : ℂ → ℂ := fun ζ ↦ ((lam : ℂ) * (ζ - p) / (ζ - q))
  let Psi : ℂ → ℂ := fun w ↦ ((q : ℂ) * w - (lam * p : ℝ)) / (w - lam)
  have hlam_ne : (lam : ℂ) ≠ 0 := by
    exact_mod_cast (show lam ≠ 0 by linarith [hlam_one])
  have hqp_ne : (q : ℂ) - p ≠ 0 := by
    have hqp_real : q ≠ p := by
      intro hqp
      linarith [hp_lt_hq, hqp]
    exact sub_ne_zero.mpr (by exact_mod_cast hqp_real)
  refine ⟨?_, ?_, ?_⟩
  · intro ζ hζ
    -- The shell/annulus equivalence already packages the normalized maps-to statement.
    simpa [W] using
      (limitingRatio_mem_standardAnnulus_iff hpq hinner hρ₁_pos hρ₂_pos hp_pos hq_pos hp_lt_hq
        hd_lt_p hρ₂_lt_q hlam_sq hr_nonneg hr_pos hr_sq).1 hζ
  · have hleftInv :
        Set.LeftInvOn Psi W (Metric.ball 0 ρ₂ \ Metric.closedBall (d : ℂ) ρ₁) := by
      intro ζ hζ
      have hζq : ζ ≠ q := by
        intro hζq
        have hq_lt : q < ρ₂ := by
          simpa [hζq, Metric.mem_ball, dist_eq_norm, Complex.norm_real, abs_of_pos hq_pos] using hζ.1
        linarith
      -- The explicit inverse cancels the limiting-point ratio on the shell.
      change
        (((q : ℂ) * (((lam : ℂ) * (ζ - p) / (ζ - q))) - (lam * p : ℝ)) /
          ((((lam : ℂ) * (ζ - p) / (ζ - q))) - lam)) = ζ
      field_simp [sub_ne_zero.mpr hζq, hlam_ne, hqp_ne]
      norm_num
      ring
    exact hleftInv.injOn
  · intro w hw
    have hw_ne_lam : w ≠ lam := by
      intro hw_eq
      have hw_lt : ‖w‖ < 1 := (mem_standard_annulus_iff hr_nonneg).1 hw |>.2
      subst hw_eq
      have : lam < 1 := by
        simpa [Complex.norm_real, abs_of_pos (lt_trans zero_lt_one hlam_one)] using hw_lt
      linarith
    refine ⟨Psi w, ?_, ?_⟩
    · have himage : W (Psi w) ∈ complexOpenAnnulus (ENNReal.ofReal r) 1 := by
        have hPsi : W (Psi w) = w := by
          -- The same explicit inverse also gives surjectivity from annulus points.
          change
            ((lam : ℂ) * ((((q : ℂ) * w - (lam * p : ℝ)) / (w - lam)) - p) /
              ((((q : ℂ) * w - (lam * p : ℝ)) / (w - lam)) - q)) = w
          field_simp [sub_ne_zero.mpr hw_ne_lam, hlam_ne, hqp_ne]
          norm_num
          ring_nf
          have hden_ne : (lam : ℂ) * q - (lam : ℂ) * p ≠ 0 := by
            rw [show (lam : ℂ) * q - (lam : ℂ) * p = (lam : ℂ) * (q - p) by ring]
            exact mul_ne_zero hlam_ne hqp_ne
          calc
            (lam : ℂ) * q * w * ((lam : ℂ) * q - (lam : ℂ) * p)⁻¹ -
                (lam : ℂ) * w * p * ((lam : ℂ) * q - (lam : ℂ) * p)⁻¹
              = w * (((lam : ℂ) * q - (lam : ℂ) * p) * ((lam : ℂ) * q - (lam : ℂ) * p)⁻¹) := by
                  ring
            _ = w := by
                  rw [mul_inv_cancel₀ hden_ne, mul_one]
        simpa [hPsi] using hw
      simpa [W] using
        (limitingRatio_mem_standardAnnulus_iff hpq hinner hρ₁_pos hρ₂_pos hp_pos hq_pos hp_lt_hq
          hd_lt_p hρ₂_lt_q hlam_sq hr_nonneg hr_pos hr_sq).2 himage
    · -- And evaluating the ratio on the inverse formula recovers the target point.
      change
        ((lam : ℂ) * ((((q : ℂ) * w - (lam * p : ℝ)) / (w - lam)) - p) /
          ((((q : ℂ) * w - (lam * p : ℝ)) / (w - lam)) - q)) = w
      field_simp [sub_ne_zero.mpr hw_ne_lam, hlam_ne, hqp_ne]
      norm_num
      ring_nf
      have hden_ne : (lam : ℂ) * q - (lam : ℂ) * p ≠ 0 := by
        rw [show (lam : ℂ) * q - (lam : ℂ) * p = (lam : ℂ) * (q - p) by ring]
        exact mul_ne_zero hlam_ne hqp_ne
      calc
        (lam : ℂ) * q * w * ((lam : ℂ) * q - (lam : ℂ) * p)⁻¹ -
            (lam : ℂ) * w * p * ((lam : ℂ) * q - (lam : ℂ) * p)⁻¹
          = w * (((lam : ℂ) * q - (lam : ℂ) * p) * ((lam : ℂ) * q - (lam : ℂ) * p)⁻¹) := by
              ring
        _ = w := by
              rw [mul_inv_cancel₀ hden_ne, mul_one]

-- Route correction: the nonconcentric branch should not jump directly to the final `BijOn`
-- packaging. The stable source-faithful frontier is now:
--   1. construct real limiting points for the two nested circles,
--   2. use `real_limiting_pair_vieta` plus the center-line order inequalities,
--   3. use `circle_ratio_normSq_factorization` to prove the normalized shell/annulus equivalence,
--   4. package the explicit inverse of the normalized ratio map and conjugate back.
-- TODO: carry out exactly that limiting-point normalization route.
lemma nonconcentric_shell_to_standard_annulus_bijOn
    {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hc : c₁ ≠ c₂)
    (hρ₁ : 0 < ρ₁)
    (hinside : Metric.closedBall c₁ ρ₁ ⊆ Metric.ball c₂ ρ₂) :
    ∃ α β γ δ : ℂ,
      ∃ r : ℝ,
        0 < r ∧
          r < 1 ∧
            α * δ - β * γ ≠ 0 ∧
              (∀ z ∈ Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁, γ * z + δ ≠ 0) ∧
                BijOn (homographic_map α β γ δ)
                  (Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁)
                  (complexOpenAnnulus (ENNReal.ofReal r) 1) := by
  -- The source-faithful nonconcentric route starts by extracting the strict radius gap
  -- `dist c₁ c₂ + ρ₁ < ρ₂` along the center line.
  have hgap : dist c₁ c₂ + ρ₁ < ρ₂ :=
    center_dist_add_inner_radius_lt_outer_radius_of_nested_circles hc hρ₁ hinside
  have hρ₂ : 0 < ρ₂ := by
    -- In particular the outer radius is positive, so the later normalization has a genuine shell.
    have hsum_pos : 0 < dist c₁ c₂ + ρ₁ := by
      linarith [(dist_nonneg : 0 ≤ dist c₁ c₂), hρ₁]
    linarith
  have hdist_pos : 0 < dist c₁ c₂ := by
    -- The nonconcentric branch works over the positive center distance.
    simpa [dist_eq_norm] using (norm_pos_iff.mpr (sub_ne_zero.mpr hc))
  have hvieta :
      let s : ℝ := ((dist c₁ c₂) ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / dist c₁ c₂
      let Δ : ℝ := s ^ 2 - 4 * ρ₂ ^ 2
      let p : ℝ := (s - Real.sqrt Δ) / 2
      let q : ℝ := (s + Real.sqrt Δ) / 2
      0 ≤ Δ ∧ p * q = ρ₂ ^ 2 ∧ (dist c₁ c₂ - p) * (dist c₁ c₂ - q) = ρ₁ ^ 2 ∧ p < q := by
    -- This records the quadratic part of Cartan's limiting-point construction.
    simpa using
      (real_limiting_pair_vieta
        (d := dist c₁ c₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
        hdist_pos hρ₁ hgap)
  set s : ℝ := ((dist c₁ c₂) ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / dist c₁ c₂ with hs
  set Δ : ℝ := s ^ 2 - 4 * ρ₂ ^ 2 with hΔ
  set p : ℝ := (s - Real.sqrt Δ) / 2 with hp
  set q : ℝ := (s + Real.sqrt Δ) / 2 with hq
  have hvieta' :
      0 ≤ Δ ∧ p * q = ρ₂ ^ 2 ∧
        (dist c₁ c₂ - p) * (dist c₁ c₂ - q) = ρ₁ ^ 2 ∧ p < q := by
    -- Unpack the Vieta identities for the concrete limiting points `p < q`.
    simpa [hs, hΔ, hp, hq] using hvieta
  have hsum : p + q = ((dist c₁ c₂) ^ 2 + ρ₂ ^ 2 - ρ₁ ^ 2) / dist c₁ c₂ := by
    -- The chosen roots sum to the normalized center-line parameter.
    rw [hp, hq]
    ring
  have hsigns :
      0 < (dist c₁ c₂ - p) * (dist c₁ c₂ - q) ∧
        ((dist c₁ c₂ + ρ₁) - p) * ((dist c₁ c₂ + ρ₁) - q) < 0 ∧
        (ρ₂ - p) * (ρ₂ - q) < 0 := by
    -- Evaluate Cartan's quadratic at the three source points on the center line.
    exact
      real_limiting_pair_centerline_signs
        (d := dist c₁ c₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (p := p) (q := q)
        hdist_pos hρ₁ hgap hvieta'.2.1 hvieta'.2.2.1 hsum
  have horder :
      0 < p ∧ dist c₁ c₂ < p ∧ p < dist c₁ c₂ + ρ₁ ∧ ρ₂ < q ∧
        0 < ((q / p) * ((dist c₁ c₂ - p) / (dist c₁ c₂ - q))) ∧
        ((q / p) * ((dist c₁ c₂ - p) / (dist c₁ c₂ - q))) < 1 := by
    -- Turn the sign pattern into the root order and the annulus-radius bound.
    exact
      real_limiting_pair_order_of_signs
        (d := dist c₁ c₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (p := p) (q := q)
        hdist_pos hρ₁ hgap hvieta'.2.2.2 hsigns.1 hsigns.2.1 hsigns.2.2
  have hp_pos : 0 < p := horder.1
  have hp_lt_hq : p < q := hvieta'.2.2.2
  have hd_lt_p : dist c₁ c₂ < p := horder.2.1
  have hρ₂_lt_q : ρ₂ < q := horder.2.2.2.1
  have hratio_pos : 0 < ((q / p) * ((dist c₁ c₂ - p) / (dist c₁ c₂ - q))) := horder.2.2.2.2.1
  have hratio_lt : ((q / p) * ((dist c₁ c₂ - p) / (dist c₁ c₂ - q))) < 1 := horder.2.2.2.2.2
  have hq_pos : 0 < q := lt_trans hp_pos hp_lt_hq
  set lam : ℝ := Real.sqrt (q / p) with hlam
  set r : ℝ := Real.sqrt ((q / p) * ((dist c₁ c₂ - p) / (dist c₁ c₂ - q))) with hr
  have hlam_sq : lam ^ 2 = q / p := by
    rw [hlam, Real.sq_sqrt]
    exact le_of_lt (div_pos hq_pos hp_pos)
  have hlam_one : 1 < lam := by
    rw [hlam]
    have hq_div_p_gt : 1 < q / p := by
      have hdiv := div_lt_div_of_pos_right hp_lt_hq hp_pos
      simpa [hp_pos.ne'] using hdiv
    simpa using (Real.sqrt_lt_sqrt (show 0 ≤ (1 : ℝ) by norm_num) hq_div_p_gt)
  have hr_pos : 0 < r := by
    rw [hr]
    exact Real.sqrt_pos_of_pos hratio_pos
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_lt_one : r < 1 := by
    rw [hr]
    have hsqrt_lt := Real.sqrt_lt_sqrt (le_of_lt hratio_pos) hratio_lt
    simpa using hsqrt_lt
  have hr_sq : r ^ 2 = (q / p) * ((dist c₁ c₂ - p) / (dist c₁ c₂ - q)) := by
    rw [hr, Real.sq_sqrt]
    exact le_of_lt hratio_pos
  let u : ℂ := star (c₁ - c₂) / dist c₁ c₂
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    have hu_sq : ‖star (c₁ - c₂) / dist c₁ c₂‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div]
      have hconj : Complex.normSq (star (c₁ - c₂)) = Complex.normSq (c₁ - c₂) := by
        simpa using (Complex.normSq_conj (c₁ - c₂))
      rw [hconj, Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, dist_eq_norm]
      have hnorm_ne : ‖c₁ - c₂‖ ≠ 0 := by
        simpa [dist_eq_norm] using hdist_pos.ne'
      field_simp [hnorm_ne]
    have hu_sq' : ‖star (c₁ - c₂) / dist c₁ c₂‖ ^ 2 = 1 ^ 2 := by
      simpa [one_pow] using hu_sq
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hu_sq'
  have hu_center : u * (c₁ - c₂) = (dist c₁ c₂ : ℂ) := by
    dsimp [u]
    have hconjmul : star (c₁ - c₂) * (c₁ - c₂) = (Complex.normSq (c₁ - c₂) : ℂ) := by
      simpa using (Complex.normSq_eq_conj_mul_self (z := c₁ - c₂)).symm
    calc
      star (c₁ - c₂) / dist c₁ c₂ * (c₁ - c₂)
          = (star (c₁ - c₂) * (c₁ - c₂)) / dist c₁ c₂ := by
              rw [div_eq_mul_inv]
              ring_nf
      _ = ((Complex.normSq (c₁ - c₂) : ℂ) / dist c₁ c₂) := by rw [hconjmul]
      _ = (((dist c₁ c₂) ^ 2 : ℝ) : ℂ) / dist c₁ c₂ := by
            rw [Complex.normSq_eq_norm_sq, dist_eq_norm]
      _ = (dist c₁ c₂ : ℂ) := by
            field_simp [show (dist c₁ c₂ : ℂ) ≠ 0 by exact_mod_cast hdist_pos.ne']
            norm_num
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    have : (0 : ℝ) = 1 := by
      simpa [hu_zero] using hu_norm
    norm_num at this
  let W : ℂ → ℂ := fun ζ ↦ ((lam : ℂ) * (ζ - p) / (ζ - q))
  have hnormalized :
      BijOn W (Metric.ball 0 ρ₂ \ Metric.closedBall (dist c₁ c₂ : ℂ) ρ₁)
        (complexOpenAnnulus (ENNReal.ofReal r) 1) := by
    simpa [W] using
      (normalizedLimitingRatio_bijOn (d := dist c₁ c₂) (hpq := hvieta'.2.1)
        (hinner := hvieta'.2.2.1) hρ₁ hρ₂ hp_pos hq_pos hp_lt_hq hd_lt_p hρ₂_lt_q
        hlam_sq hlam_one hr_nonneg hr_pos hr_sq)
  let α : ℂ := (lam : ℂ) * u
  let β : ℂ := -((lam : ℂ) * (u * c₂ + p))
  let γ : ℂ := u
  let δ : ℂ := -(u * c₂ + q)
  have hmap_eq : ∀ z : ℂ, homographic_map α β γ δ z = W (u * (z - c₂)) := by
    intro z
    dsimp [α, β, γ, δ, W, homographic_map]
    field_simp
    ring
  refine ⟨α, β, γ, δ, r, hr_pos, hr_lt_one, ?_, ?_, ?_⟩
  · have hlam_ne : (lam : ℂ) ≠ 0 := by
      exact_mod_cast (show lam ≠ 0 by linarith [hlam_one])
    have hpq_real : p ≠ q := ne_of_lt hp_lt_hq
    -- The transported homography keeps the same nonzero determinant as the normalized ratio map.
    dsimp [α, β, γ, δ]
    rw [show ((lam : ℂ) * u) * (-(u * c₂ + q)) - (-((lam : ℂ) * (u * c₂ + p))) * u =
      (lam : ℂ) * u * (p - q) by ring]
    exact mul_ne_zero (mul_ne_zero hlam_ne hu_ne)
      (sub_ne_zero.mpr (by exact_mod_cast hpq_real))
  · intro z hz
    have hz_norm :
        u * (z - c₂) ∈ Metric.ball 0 ρ₂ \ Metric.closedBall (dist c₁ c₂ : ℂ) ρ₁ := by
      exact (mem_normalizedShell_iff (d := dist c₁ c₂) hu_norm hu_center).1 hz
    have hzq : u * (z - c₂) ≠ q := by
      intro hzq
      have hq_lt : q < ρ₂ := by
        simpa [hzq, Metric.mem_ball, dist_eq_norm, Complex.norm_real, abs_of_pos hq_pos] using
          hz_norm.1
      linarith
    -- Pole avoidance reduces to the already-used fact that the normalized coordinate never hits `q`.
    dsimp [γ, δ]
    rw [show u * z + -(u * c₂ + q) = u * (z - c₂) - q by ring]
    exact sub_ne_zero.mpr hzq
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      have hz_norm :
          u * (z - c₂) ∈ Metric.ball 0 ρ₂ \ Metric.closedBall (dist c₁ c₂ : ℂ) ρ₁ := by
        exact (mem_normalizedShell_iff (d := dist c₁ c₂) hu_norm hu_center).1 hz
      have himage := hnormalized.1 hz_norm
      -- After transport, the normalized ratio is exactly the requested homography.
      simpa [hmap_eq z] using himage
    · intro z₁ hz₁ z₂ hz₂ hEq
      have hz₁_norm :
          u * (z₁ - c₂) ∈ Metric.ball 0 ρ₂ \ Metric.closedBall (dist c₁ c₂ : ℂ) ρ₁ := by
        exact (mem_normalizedShell_iff (d := dist c₁ c₂) hu_norm hu_center).1 hz₁
      have hz₂_norm :
          u * (z₂ - c₂) ∈ Metric.ball 0 ρ₂ \ Metric.closedBall (dist c₁ c₂ : ℂ) ρ₁ := by
        exact (mem_normalizedShell_iff (d := dist c₁ c₂) hu_norm hu_center).1 hz₂
      have hnormEq : W (u * (z₁ - c₂)) = W (u * (z₂ - c₂)) := by
        simpa [hmap_eq z₁, hmap_eq z₂] using hEq
      have hsubEq : u * (z₁ - c₂) = u * (z₂ - c₂) :=
        hnormalized.2.1 hz₁_norm hz₂_norm hnormEq
      have hsubEq' : z₁ - c₂ = z₂ - c₂ := by
        exact mul_left_cancel₀ hu_ne hsubEq
      have hEq' := congrArg (fun w : ℂ ↦ w + c₂) hsubEq'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq'
    · intro w hw
      rcases hnormalized.2.2 hw with ⟨ζ, hζ_norm, hζ_eq⟩
      let z : ℂ := star u * ζ + c₂
      have hz_normEq : u * (z - c₂) = ζ := by
        have hu_normSq : Complex.normSq u = 1 := by
          rw [Complex.normSq_eq_norm_sq, hu_norm]
          norm_num
        have hmulconj : u * star u = Complex.normSq u := by
          simpa using (Complex.mul_conj u)
        dsimp [z]
        calc
          u * (star u * ζ + c₂ - c₂) = u * (star u * ζ) := by ring
          _ = (u * star u) * ζ := by ring
          _ = (Complex.normSq u : ℂ) * ζ := by rw [hmulconj]
          _ = ζ := by simp [hu_normSq]
      have hz :
          z ∈ Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁ := by
        have : u * (z - c₂) ∈ Metric.ball 0 ρ₂ \ Metric.closedBall (dist c₁ c₂ : ℂ) ρ₁ := by
          simpa [hz_normEq] using hζ_norm
        exact (mem_normalizedShell_iff (d := dist c₁ c₂) hu_norm hu_center).2 this
      refine ⟨z, hz, ?_⟩
      calc
        homographic_map α β γ δ z = W (u * (z - c₂)) := hmap_eq z
        _ = W ζ := by rw [hz_normEq]
        _ = w := hζ_eq

/-- Cartan section26 0012_Exercise_2: if `D` is a connected open subset of `ℂ` whose frontier is
the union of two
circles, with the first closed disc lying strictly inside the second open disc, then some
homographic transformation maps `D` bijectively onto the standard annulus `r < ‖z‖ < 1`. Using
the project annulus owner, this target is `complexOpenAnnulus (ENNReal.ofReal r) 1`. -/
theorem exists_homographic_bijOn_standardAnnulus_of_frontier_two_circles
    {D : Set ℂ} {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hD_open : IsOpen D)
    (hD_connected : IsConnected D)
    (hρ₁ : 0 < ρ₁)
    (hfrontier : frontier D = Metric.sphere c₁ ρ₁ ∪ Metric.sphere c₂ ρ₂)
    (hinside : Metric.closedBall c₁ ρ₁ ⊆ Metric.ball c₂ ρ₂) :
    ∃ α β γ δ : ℂ,
      ∃ r : ℝ,
        0 < r ∧
          r < 1 ∧
            α * δ - β * γ ≠ 0 ∧
              (∀ z ∈ D, γ * z + δ ≠ 0) ∧
                BijOn (homographic_map α β γ δ) D (complexOpenAnnulus (ENNReal.ofReal r) 1) := by
  -- First identify the geometric domain with the shell bounded by the two circles.
  have hshell :
      D = Metric.ball c₂ ρ₂ \ Metric.closedBall c₁ ρ₁ :=
    domain_eq_nested_circle_shell_of_frontier_two_circles
      hD_open hD_connected hρ₁ hfrontier hinside
  by_cases hc : c₁ = c₂
  · subst c₁
    -- In the concentric case, the shell is normalized by an affine homography.
    have hρ : ρ₁ < ρ₂ := radii_lt_of_closedBall_subset_ball_same_center hρ₁ hinside
    have hρ₂ : 0 < ρ₂ := lt_trans hρ₁ hρ
    simpa [hshell] using
      concentric_shell_to_standard_annulus_bijOn (c := c₂) hρ₁ hρ₂ hρ
  · -- The remaining nonconcentric case is the classical limiting-points construction.
    simpa [hshell] using
      nonconcentric_shell_to_standard_annulus_bijOn hc hρ₁ hinside
