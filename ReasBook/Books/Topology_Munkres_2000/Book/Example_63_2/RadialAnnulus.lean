module

public import Mathlib

public section

open Set

namespace AlexanderHornGeometry

/-- Helper for Example 63.2: the closed radial annulus with inner radius `r` and outer
radius `R`. -/
def closedRadialAnnulus (c : ℂ) (r R : ℝ) : Set ℂ :=
  Metric.closedBall c R \ Metric.ball c r

/-- Helper for Example 63.2: membership in a closed radial annulus is exactly a pair
of lower and upper distance bounds. -/
lemma mem_closedRadialAnnulus_iff {c z : ℂ} {r R : ℝ} :
    z ∈ closedRadialAnnulus c r R ↔ r ≤ dist z c ∧ dist z c ≤ R := by
  -- Expand the set difference and translate ball membership into distance inequalities.
  simp only [closedRadialAnnulus, mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, not_lt]
  exact and_comm

/-- Helper for Example 63.2: the closed radial annulus lies in its outer closed ball. -/
lemma closedRadialAnnulus_subset_closedBall (c : ℂ) (r R : ℝ) :
    closedRadialAnnulus c r R ⊆ Metric.closedBall c R := by
  -- Project the outer-ball component of membership in the defining set difference.
  intro z hz
  exact hz.1

/-- Helper for Example 63.2: annulus membership is equivalent to lying between the two
radial bounds. -/
lemma closedRadialAnnulus_dist_bounds (c : ℂ) (r R : ℝ)
    (z : closedRadialAnnulus c r R) :
    r ≤ dist (z : ℂ) c ∧ dist (z : ℂ) c ≤ R := by
  -- Read the lower bound from the removed open ball and the upper bound from the closed ball.
  constructor
  · simpa only [Metric.mem_ball, not_lt] using z.property.2
  · simpa only [Metric.mem_closedBall] using z.property.1

/-- Helper for Example 63.2: every closed radial annulus is compact. -/
lemma isCompact_closedRadialAnnulus (c : ℂ) (r R : ℝ) :
    IsCompact (closedRadialAnnulus c r R) := by
  -- Remove an open inner ball from the compact outer closed ball.
  exact (isCompact_closedBall c R).diff Metric.isOpen_ball

/-- Helper for Example 63.2: every closed radial annulus is closed. -/
lemma isClosed_closedRadialAnnulus (c : ℂ) (r R : ℝ) :
    IsClosed (closedRadialAnnulus c r R) := by
  -- Compact subsets of the complex plane are closed.
  exact (isCompact_closedRadialAnnulus c r R).isClosed

/-- Helper for Example 63.2: radial interpolation from the outer circle to the inner
circle takes values in the unit interval. -/
lemma radialAnnulusTime_mem (c : ℂ) {r R : ℝ} (hrR : r < R)
    (z : closedRadialAnnulus c r R) :
    (R - dist (z : ℂ) c) / (R - r) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Annulus membership places the radius between the two endpoint radii.
  have hzOuter : dist (z : ℂ) c ≤ R := by
    simpa only [closedRadialAnnulus, mem_sdiff, Metric.mem_closedBall] using z.property.1
  have hzInner : r ≤ dist (z : ℂ) c := by
    simpa only [closedRadialAnnulus, mem_sdiff, Metric.mem_ball, not_lt] using z.property.2
  -- Dividing the two nonnegative radial gaps by the positive collar width gives `[0,1]`.
  constructor
  · exact div_nonneg (sub_nonneg.mpr hzOuter) (sub_nonneg.mpr hrR.le)
  · exact (div_le_one (sub_pos.mpr hrR)).mpr (by linarith)

/-- Helper for Example 63.2: the normalized radial collar sends an annulus to time
cross the outer boundary circle. -/
noncomputable def radialAnnulusCollar (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    closedRadialAnnulus c r R → unitInterval × ℂ :=
  fun z ↦
    (⟨(R - dist (z : ℂ) c) / (R - r), radialAnnulusTime_mem c hrR z⟩,
      c + (R / dist (z : ℂ) c) • ((z : ℂ) - c))

/-- Helper for Example 63.2: every point of the closed radial annulus has positive
distance from its center. -/
lemma dist_center_pos_of_mem_closedRadialAnnulus (c : ℂ) {r R : ℝ} (hr : 0 < r)
    (z : closedRadialAnnulus c r R) : 0 < dist (z : ℂ) c := by
  -- The excluded inner ball gives a positive lower bound on the radius.
  have hzInner : r ≤ dist (z : ℂ) c := by
    simpa only [closedRadialAnnulus, mem_sdiff, Metric.mem_ball, not_lt] using z.property.2
  exact hr.trans_le hzInner

/-- Helper for Example 63.2: the spatial coordinate of the radial collar lies on the
outer boundary circle. -/
lemma radialAnnulusProjection_mem_sphere (c : ℂ) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (z : closedRadialAnnulus c r R) :
    c + (R / dist (z : ℂ) c) • ((z : ℂ) - c) ∈ Metric.sphere c R := by
  -- Positivity of both radii lets the normalization cancel the original radius.
  have hdPos : 0 < dist (z : ℂ) c :=
    dist_center_pos_of_mem_closedRadialAnnulus c hr z
  have hRPos : 0 < R := hr.trans hrR
  rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos hRPos hdPos), ← dist_eq_norm]
  exact div_mul_cancel₀ R hdPos.ne'

/-- Helper for Example 63.2: the spatial projection stored by the radial collar lies
on the outer boundary sphere. -/
lemma radialAnnulusCollar_snd_mem_sphere (c : ℂ) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (z : closedRadialAnnulus c r R) :
    (radialAnnulusCollar c r R hr hrR z).2 ∈ Metric.sphere c R := by
  -- Expose the collar's named spatial projection and apply its normalization theorem.
  exact radialAnnulusProjection_mem_sphere c hr hrR z

/-- Helper for Example 63.2: the radial collar varies continuously across the closed
annulus. -/
lemma continuous_radialAnnulusCollar (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    Continuous (radialAnnulusCollar c r R hr hrR) := by
  -- The radius stays nonzero on the annulus, so radial division is continuous there.
  have hdist : Continuous
      (fun z : closedRadialAnnulus c r R ↦ dist (z : ℂ) c) :=
    continuous_subtype_val.dist continuous_const
  have hdistNe : ∀ z : closedRadialAnnulus c r R, dist (z : ℂ) c ≠ 0 :=
    fun z ↦ (dist_center_pos_of_mem_closedRadialAnnulus c hr z).ne'
  have htime : Continuous
      (fun z : closedRadialAnnulus c r R ↦
        (R - dist (z : ℂ) c) / (R - r)) :=
    (continuous_const.sub hdist).div_const (R - r)
  have htimeSubtype : Continuous
      (fun z : closedRadialAnnulus c r R ↦
        (⟨(R - dist (z : ℂ) c) / (R - r),
          radialAnnulusTime_mem c hrR z⟩ : unitInterval)) :=
    htime.subtype_mk _
  have hscale : Continuous
      (fun z : closedRadialAnnulus c r R ↦ R / dist (z : ℂ) c) :=
    continuous_const.div hdist hdistNe
  have hspace : Continuous
      (fun z : closedRadialAnnulus c r R ↦
        c + (R / dist (z : ℂ) c) • ((z : ℂ) - c)) :=
    continuous_const.add (hscale.smul (continuous_subtype_val.sub continuous_const))
  exact htimeSubtype.prodMk hspace

/-- Helper for Example 63.2: the radial collar is injective. -/
lemma injective_radialAnnulusCollar (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    Function.Injective (radialAnnulusCollar c r R hr hrR) := by
  -- Time recovers the radius, after which the nonzero radial scaling recovers the point.
  intro x y hxy
  have htime := congrArg (fun p : unitInterval × ℂ ↦ (p.1 : ℝ)) hxy
  have hwidthNe : R - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hrR)
  have hdist : dist (x : ℂ) c = dist (y : ℂ) c := by
    dsimp only [radialAnnulusCollar] at htime
    field_simp [hwidthNe] at htime
    linarith
  have hspace := congrArg Prod.snd hxy
  dsimp only [radialAnnulusCollar] at hspace
  rw [hdist] at hspace
  have hRPos : 0 < R := hr.trans hrR
  have hyDistPos : 0 < dist (y : ℂ) c :=
    dist_center_pos_of_mem_closedRadialAnnulus c hr y
  have hscaleNe : R / dist (y : ℂ) c ≠ 0 :=
    div_ne_zero hRPos.ne' hyDistPos.ne'
  have hsub : (x : ℂ) - c = (y : ℂ) - c :=
    smul_right_injective ℂ hscaleNe (add_left_cancel hspace)
  exact Subtype.ext (sub_left_inj.mp hsub)

/-- Helper for Example 63.2: the radial collar is a closed embedding. -/
lemma radialAnnulusCollar_isClosedEmbedding (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) :
    Topology.IsClosedEmbedding (radialAnnulusCollar c r R hr hrR) := by
  -- Compactness of the closed annulus upgrades the continuous injection to a closed embedding.
  letI : CompactSpace (closedRadialAnnulus c r R) :=
    isCompact_iff_compactSpace.mp
      ((isCompact_closedBall c R).diff Metric.isOpen_ball)
  exact (continuous_radialAnnulusCollar c r R hr hrR).isClosedEmbedding
    (injective_radialAnnulusCollar c r R hr hrR)

/-- Helper for Example 63.2: the radial collar covers exactly time cross the outer
boundary circle. -/
lemma range_radialAnnulusCollar (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    Set.range (radialAnnulusCollar c r R hr hrR) =
      Set.univ ×ˢ Metric.sphere c R := by
  -- Reconstruct the radius linearly from time and rescale each outer-circle point inward.
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨Set.mem_univ _, radialAnnulusProjection_mem_sphere c hr hrR z⟩
  · rintro p hp
    have htNonneg : 0 ≤ (p.1 : ℝ) := p.1.property.1
    have htLeOne : (p.1 : ℝ) ≤ 1 := p.1.property.2
    have hwidthPos : 0 < R - r := sub_pos.mpr hrR
    have hwidthNe : R - r ≠ 0 := hwidthPos.ne'
    have hRPos : 0 < R := hr.trans hrR
    have hRNe : R ≠ 0 := hRPos.ne'
    let ρ : ℝ := R - (R - r) * (p.1 : ℝ)
    have hρLower : r ≤ ρ := by
      dsimp only [ρ]
      nlinarith
    have hρUpper : ρ ≤ R := by
      dsimp only [ρ]
      nlinarith
    have hρPos : 0 < ρ := hr.trans_le hρLower
    have hρNe : ρ ≠ 0 := hρPos.ne'
    have hpSphere : dist p.2 c = R := by
      simpa only [Metric.mem_sphere] using hp.2
    let z : ℂ := c + (ρ / R) • (p.2 - c)
    have hzDist : dist z c = ρ := by
      dsimp only [z]
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hρPos hRPos), ← dist_eq_norm, hpSphere]
      exact div_mul_cancel₀ ρ hRNe
    have hzMem : z ∈ closedRadialAnnulus c r R := by
      constructor
      · simpa only [Metric.mem_closedBall, hzDist] using hρUpper
      · simpa only [Metric.mem_ball, hzDist, not_lt] using hρLower
    let zs : closedRadialAnnulus c r R := ⟨z, hzMem⟩
    refine ⟨zs, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp only [radialAnnulusCollar]
      rw [show dist (zs : ℂ) c = ρ from hzDist]
      dsimp only [ρ]
      field_simp [hwidthNe]
      ring
    · dsimp only [radialAnnulusCollar, zs]
      rw [hzDist]
      dsimp only [z]
      rw [add_sub_cancel_left, smul_smul]
      have hscale : (R / ρ) * (ρ / R) = 1 := by
        field_simp [hRNe, hρNe]
      rw [hscale, one_smul, add_sub_cancel]

/-- Helper for Example 63.2: the radial collar identifies the closed annulus with time
cross the outer boundary circle. -/
noncomputable def radialAnnulusHomeomorph (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) :
    closedRadialAnnulus c r R ≃ₜ
      ((Set.univ : Set unitInterval) ×ˢ Metric.sphere c R) :=
  (radialAnnulusCollar_isClosedEmbedding c r R hr hrR).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_radialAnnulusCollar c r R hr hrR))

/-- Helper for Example 63.2: forgetting the radial-homeomorphism range proof recovers
the collar formula. -/
lemma radialAnnulusHomeomorph_apply_coe (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (z : closedRadialAnnulus c r R) :
    ((radialAnnulusHomeomorph c r R hr hrR z :
      ((Set.univ : Set unitInterval) ×ˢ Metric.sphere c R)) : unitInterval × ℂ) =
        radialAnnulusCollar c r R hr hrR z := by
  -- Both canonical range restrictions retain the collar's underlying point.
  rfl

/-- Helper for Example 63.2: the radial collar is the identity parameterization on its
outer boundary. -/
lemma radialAnnulusCollar_apply_of_dist_eq_outer (c : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (z : closedRadialAnnulus c r R)
    (hz : dist (z : ℂ) c = R) :
    radialAnnulusCollar c r R hr hrR z = (0, (z : ℂ)) := by
  -- At the outer radius, normalized time is zero and spatial rescaling is one.
  apply Prod.ext
  · apply Subtype.ext
    dsimp only [radialAnnulusCollar]
    rw [hz]
    simp only [sub_self, zero_div, Set.Icc.coe_zero]
  · dsimp only [radialAnnulusCollar]
    rw [hz, div_self (hr.trans hrR).ne', one_smul, add_sub_cancel]

/-- Helper for Example 63.2: the radial collar reaches normalized time one on its inner
boundary. -/
lemma radialAnnulusCollar_apply_of_dist_eq_inner (c : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (z : closedRadialAnnulus c r R)
    (hz : dist (z : ℂ) c = r) :
    radialAnnulusCollar c r R hr hrR z =
      (1, c + (R / r) • ((z : ℂ) - c)) := by
  -- At the inner radius, normalized time is one and the displayed radial scale remains.
  apply Prod.ext
  · apply Subtype.ext
    dsimp only [radialAnnulusCollar]
    rw [hz, div_self (sub_pos.mpr hrR).ne']
    exact Set.Icc.coe_one
  · dsimp only [radialAnnulusCollar]
    rw [hz]

/-- Helper for Example 63.2: the collar time and normalized boundary point reconstruct
the original annulus point by radial interpolation. -/
lemma radialAnnulusReconstruct_collar (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (z : closedRadialAnnulus c r R) :
    c + ((R - (R - r) * ((radialAnnulusCollar c r R hr hrR z).1 : ℝ)) / R) •
        ((radialAnnulusCollar c r R hr hrR z).2 - c) = (z : ℂ) := by
  -- Recover the original radius from time, then cancel the two reciprocal radial scales.
  have hR : 0 < R := hr.trans hrR
  have hd : 0 < dist (z : ℂ) c := dist_center_pos_of_mem_closedRadialAnnulus c hr z
  have hgap : R - r ≠ 0 := (sub_pos.mpr hrR).ne'
  have hradius :
      R - (R - r) * ((R - dist (z : ℂ) c) / (R - r)) = dist (z : ℂ) c := by
    field_simp [hgap]
    ring
  have hscale : (dist (z : ℂ) c / R) * (R / dist (z : ℂ) c) = 1 := by
    field_simp [hR.ne', hd.ne']
  dsimp only [radialAnnulusCollar, Prod.fst, Prod.snd, Subtype.coe_mk]
  rw [hradius, add_sub_cancel_left, smul_smul, hscale, one_smul, add_sub_cancel]

end AlexanderHornGeometry
