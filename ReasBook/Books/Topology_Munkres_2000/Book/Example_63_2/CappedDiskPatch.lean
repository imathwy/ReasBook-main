module

public import Topology_Munkres_2000.Book.Example_63_2.RadialAnnulus
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

public section

open Set

namespace AlexanderHornGeometry

/-- Helper for Example 63.2: the standard unbraided surface obtained by capping two
disjoint radial collars and leaving the plane fixed away from their outer disks. -/
noncomputable def twoCappedDiskPatch (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) : ℂ → unitInterval × ℂ :=
  fun z ↦
    @dite (unitInterval × ℂ)
      (z ∈ Metric.closedBall c₀ r)
      (Classical.propDecidable _)
      (fun _ ↦ (1, c₀ + (R / r) • (z - c₀)))
      (fun _ ↦
        @dite (unitInterval × ℂ)
          (z ∈ Metric.closedBall c₁ r)
          (Classical.propDecidable _)
          (fun _ ↦ (1, c₁ + (R / r) • (z - c₁)))
          (fun _ ↦
            @dite (unitInterval × ℂ)
              (z ∈ closedRadialAnnulus c₀ r R)
              (Classical.propDecidable _)
              (fun h₀ ↦ radialAnnulusCollar c₀ r R hr hrR ⟨z, h₀⟩)
              (fun _ ↦
                @dite (unitInterval × ℂ)
                  (z ∈ closedRadialAnnulus c₁ r R)
                  (Classical.propDecidable _)
                  (fun h₁ ↦ radialAnnulusCollar c₁ r R hr hrR ⟨z, h₁⟩)
                  (fun _ ↦ (0, z)))))

/-- Helper for Example 63.2: the generic capped patch uses the flat left cap on the
first inner disk. -/
lemma twoCappedDiskPatch_apply_leftCap (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) {z : ℂ}
    (hz : z ∈ Metric.closedBall c₀ r) :
    twoCappedDiskPatch c₀ c₁ r R hr hrR z =
      (1, c₀ + (R / r) • (z - c₀)) := by
  -- The first cap is the leading branch of the finite gluing.
  simp only [twoCappedDiskPatch, dif_pos hz]

/-- Helper for Example 63.2: disjoint outer disks make the generic capped patch use the
flat right cap on the second inner disk. -/
lemma twoCappedDiskPatch_apply_rightCap (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R))
    {z : ℂ} (hz : z ∈ Metric.closedBall c₁ r) :
    twoCappedDiskPatch c₀ c₁ r R hr hrR z =
      (1, c₁ + (R / r) • (z - c₁)) := by
  -- The first branch is impossible because both inner disks lie in disjoint outer disks.
  have hzOuter : z ∈ Metric.closedBall c₁ R := by
    rw [Metric.mem_closedBall] at hz ⊢
    exact hz.trans hrR.le
  have hnotLeft : z ∉ Metric.closedBall c₀ r := by
    intro hleft
    have hleftOuter : z ∈ Metric.closedBall c₀ R := by
      rw [Metric.mem_closedBall] at hleft ⊢
      exact hleft.trans hrR.le
    exact Set.disjoint_left.mp hdisjoint hleftOuter hzOuter
  simp only [twoCappedDiskPatch, dif_neg hnotLeft, dif_pos hz]

/-- Helper for Example 63.2: on the first closed collar, the generic patch is exactly
the canonical radial-annulus parameterization. -/
lemma twoCappedDiskPatch_apply_leftAnnulus (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R))
    (z : closedRadialAnnulus c₀ r R) :
    twoCappedDiskPatch c₀ c₁ r R hr hrR z =
      radialAnnulusCollar c₀ r R hr hrR z := by
  -- Disjoint outer disks exclude the second cap throughout the first collar.
  have hzOuter : (z : ℂ) ∈ Metric.closedBall c₀ R :=
    closedRadialAnnulus_subset_closedBall c₀ r R z.property
  have hnotRight : (z : ℂ) ∉ Metric.closedBall c₁ r := by
    intro hright
    have hrightOuter : (z : ℂ) ∈ Metric.closedBall c₁ R := by
      rw [Metric.mem_closedBall] at hright ⊢
      exact hright.trans hrR.le
    exact Set.disjoint_left.mp hdisjoint hzOuter hrightOuter
  by_cases hinner : (z : ℂ) ∈ Metric.closedBall c₀ r
  · -- On the common seam, the flat cap equals the collar's terminal formula.
    have hdistUpper : dist (z : ℂ) c₀ ≤ r := by
      simpa only [Metric.mem_closedBall] using hinner
    have hdist : dist (z : ℂ) c₀ = r :=
      le_antisymm hdistUpper (closedRadialAnnulus_dist_bounds c₀ r R z).1
    rw [twoCappedDiskPatch_apply_leftCap c₀ c₁ r R hr hrR hinner]
    exact (radialAnnulusCollar_apply_of_dist_eq_inner c₀ hr hrR z hdist).symm
  · -- Away from the seam, the first annulus branch is selected directly.
    simp only [twoCappedDiskPatch, dif_neg hinner, dif_neg hnotRight, dif_pos z.property]

/-- Helper for Example 63.2: on the second closed collar, the generic patch is exactly
the canonical radial-annulus parameterization. -/
lemma twoCappedDiskPatch_apply_rightAnnulus (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R))
    (z : closedRadialAnnulus c₁ r R) :
    twoCappedDiskPatch c₀ c₁ r R hr hrR z =
      radialAnnulusCollar c₁ r R hr hrR z := by
  -- Disjoint outer disks exclude both branches belonging to the first capped disk.
  have hzOuter : (z : ℂ) ∈ Metric.closedBall c₁ R :=
    closedRadialAnnulus_subset_closedBall c₁ r R z.property
  have hnotLeftInner : (z : ℂ) ∉ Metric.closedBall c₀ r := by
    intro hleft
    have hleftOuter : (z : ℂ) ∈ Metric.closedBall c₀ R := by
      rw [Metric.mem_closedBall] at hleft ⊢
      exact hleft.trans hrR.le
    exact Set.disjoint_left.mp hdisjoint hleftOuter hzOuter
  have hnotLeftAnnulus : (z : ℂ) ∉ closedRadialAnnulus c₀ r R := by
    intro hleft
    exact Set.disjoint_left.mp hdisjoint
      (closedRadialAnnulus_subset_closedBall c₀ r R hleft) hzOuter
  by_cases hinner : (z : ℂ) ∈ Metric.closedBall c₁ r
  · -- On the common seam, the flat cap equals the collar's terminal formula.
    have hdistUpper : dist (z : ℂ) c₁ ≤ r := by
      simpa only [Metric.mem_closedBall] using hinner
    have hdist : dist (z : ℂ) c₁ = r :=
      le_antisymm hdistUpper (closedRadialAnnulus_dist_bounds c₁ r R z).1
    rw [twoCappedDiskPatch_apply_rightCap c₀ c₁ r R hr hrR hdisjoint hinner]
    exact (radialAnnulusCollar_apply_of_dist_eq_inner c₁ hr hrR z hdist).symm
  · -- Away from the seam, branch priority reaches the second annulus directly.
    simp only [twoCappedDiskPatch, dif_neg hnotLeftInner, dif_neg hinner,
      dif_neg hnotLeftAnnulus, dif_pos z.property]

/-- Helper for Example 63.2: outside the two open outer disks, including their boundary
circles, the generic patch is the zero-height inclusion. -/
lemma twoCappedDiskPatch_apply_closedExterior (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) {z : ℂ}
    (h₀ : z ∉ Metric.ball c₀ R) (h₁ : z ∉ Metric.ball c₁ R) :
    twoCappedDiskPatch c₀ c₁ r R hr hrR z = (0, z) := by
  -- No point outside an open outer disk can lie in its strictly smaller inner disk.
  have hinner₀ : z ∉ Metric.closedBall c₀ r := by
    intro hz
    apply h₀
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    exact hz.trans_lt hrR
  have hinner₁ : z ∉ Metric.closedBall c₁ r := by
    intro hz
    apply h₁
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    exact hz.trans_lt hrR
  by_cases hannulus₀ : z ∈ closedRadialAnnulus c₀ r R
  · -- The only possible collar point is on the outer seam, where the collar has time zero.
    have hdistUpper := (closedRadialAnnulus_dist_bounds c₀ r R ⟨z, hannulus₀⟩).2
    have hdistLower : R ≤ dist z c₀ := by
      simpa only [Metric.mem_ball, not_lt] using h₀
    have hdist : dist z c₀ = R := le_antisymm hdistUpper hdistLower
    rw [twoCappedDiskPatch, dif_neg hinner₀, dif_neg hinner₁, dif_pos hannulus₀]
    exact radialAnnulusCollar_apply_of_dist_eq_outer c₀ hr hrR ⟨z, hannulus₀⟩ hdist
  · by_cases hannulus₁ : z ∈ closedRadialAnnulus c₁ r R
    · -- The second outer seam obeys the same endpoint normalization.
      have hdistUpper := (closedRadialAnnulus_dist_bounds c₁ r R ⟨z, hannulus₁⟩).2
      have hdistLower : R ≤ dist z c₁ := by
        simpa only [Metric.mem_ball, not_lt] using h₁
      have hdist : dist z c₁ = R := le_antisymm hdistUpper hdistLower
      rw [twoCappedDiskPatch, dif_neg hinner₀, dif_neg hinner₁,
        dif_neg hannulus₀, dif_pos hannulus₁]
      exact radialAnnulusCollar_apply_of_dist_eq_outer c₁ hr hrR ⟨z, hannulus₁⟩ hdist
    · -- With both collar branches absent, the definition reaches the exterior branch.
      simp only [twoCappedDiskPatch, dif_neg hinner₀, dif_neg hinner₁,
        dif_neg hannulus₀, dif_neg hannulus₁]

/-- Helper for Example 63.2: off both outer disks the generic capped patch is the
zero-height inclusion of the plane. -/
lemma twoCappedDiskPatch_apply_exterior (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) {z : ℂ}
    (h₀ : z ∉ Metric.closedBall c₀ R) (h₁ : z ∉ Metric.closedBall c₁ R) :
    twoCappedDiskPatch c₀ c₁ r R hr hrR z = (0, z) := by
  -- Inner disks and annuli are all contained in their corresponding outer disks.
  have hinner₀ : z ∉ Metric.closedBall c₀ r := by
    intro hz
    apply h₀
    rw [Metric.mem_closedBall] at hz ⊢
    exact hz.trans hrR.le
  have hinner₁ : z ∉ Metric.closedBall c₁ r := by
    intro hz
    apply h₁
    rw [Metric.mem_closedBall] at hz ⊢
    exact hz.trans hrR.le
  have hannulus₀ : z ∉ closedRadialAnnulus c₀ r R := by
    exact fun hz ↦ h₀ (closedRadialAnnulus_subset_closedBall c₀ r R hz)
  have hannulus₁ : z ∉ closedRadialAnnulus c₁ r R := by
    exact fun hz ↦ h₁ (closedRadialAnnulus_subset_closedBall c₁ r R hz)
  simp only [twoCappedDiskPatch, dif_neg hinner₀, dif_neg hinner₁,
    dif_neg hannulus₀, dif_neg hannulus₁]

/-- Helper for Example 63.2: the two inner disks, two collars, and closed exterior
form a finite closed cover of the complex plane. -/
lemma twoCappedDiskPatch_closedCover (c₀ c₁ : ℂ) (r R : ℝ) (hrR : r < R) :
    (((Metric.closedBall c₀ r ∪ Metric.closedBall c₁ r) ∪
        closedRadialAnnulus c₀ r R) ∪ closedRadialAnnulus c₁ r R) ∪
        (Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ = Set.univ := by
  -- A point not in an inner disk or its collar cannot lie in the corresponding open outer disk.
  ext z
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_cases hinner₀ : z ∈ Metric.closedBall c₀ r
  · exact Or.inl (Or.inl (Or.inl (Or.inl hinner₀)))
  by_cases hinner₁ : z ∈ Metric.closedBall c₁ r
  · exact Or.inl (Or.inl (Or.inl (Or.inr hinner₁)))
  by_cases hannulus₀ : z ∈ closedRadialAnnulus c₀ r R
  · exact Or.inl (Or.inl (Or.inr hannulus₀))
  by_cases hannulus₁ : z ∈ closedRadialAnnulus c₁ r R
  · exact Or.inl (Or.inr hannulus₁)
  refine Or.inr ?_
  intro hzUnion
  rcases hzUnion with hz₀ | hz₁
  · have hdistLower : r ≤ dist z c₀ := by
      have hnotLe : ¬ dist z c₀ ≤ r := by
        simpa only [Metric.mem_closedBall] using hinner₀
      exact (lt_of_not_ge hnotLe).le
    have hdistUpper : dist z c₀ ≤ R := by
      have hlt : dist z c₀ < R := by
        simpa only [Metric.mem_ball] using hz₀
      exact hlt.le
    exact hannulus₀ (mem_closedRadialAnnulus_iff.mpr ⟨hdistLower, hdistUpper⟩)
  · have hdistLower : r ≤ dist z c₁ := by
      have hnotLe : ¬ dist z c₁ ≤ r := by
        simpa only [Metric.mem_closedBall] using hinner₁
      exact (lt_of_not_ge hnotLe).le
    have hdistUpper : dist z c₁ ≤ R := by
      have hlt : dist z c₁ < R := by
        simpa only [Metric.mem_ball] using hz₁
      exact hlt.le
    exact hannulus₁ (mem_closedRadialAnnulus_iff.mpr ⟨hdistLower, hdistUpper⟩)

/-- Helper for Example 63.2: the generic capped patch is continuous on the first cap. -/
lemma continuousOn_twoCappedDiskPatch_leftCap (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) :
    ContinuousOn (twoCappedDiskPatch c₀ c₁ r R hr hrR)
      (Metric.closedBall c₀ r) := by
  -- Compare the patch with the globally continuous affine cap formula.
  have hcap : Continuous
      (fun z : ℂ ↦ ((1 : unitInterval), c₀ + (R / r) • (z - c₀))) := by
    fun_prop
  exact hcap.continuousOn.congr
    (fun _ hz ↦ twoCappedDiskPatch_apply_leftCap c₀ c₁ r R hr hrR hz)

/-- Helper for Example 63.2: with disjoint outer disks, the generic capped patch is
continuous on the second cap. -/
lemma continuousOn_twoCappedDiskPatch_rightCap (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R)) :
    ContinuousOn (twoCappedDiskPatch c₀ c₁ r R hr hrR)
      (Metric.closedBall c₁ r) := by
  -- Compare the patch with the globally continuous affine cap formula.
  have hcap : Continuous
      (fun z : ℂ ↦ ((1 : unitInterval), c₁ + (R / r) • (z - c₁))) := by
    fun_prop
  exact hcap.continuousOn.congr
    (fun _ hz ↦ twoCappedDiskPatch_apply_rightCap c₀ c₁ r R hr hrR hdisjoint hz)

/-- Helper for Example 63.2: with disjoint outer disks, the generic capped patch is
continuous on the first collar. -/
lemma continuousOn_twoCappedDiskPatch_leftAnnulus (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R)) :
    ContinuousOn (twoCappedDiskPatch c₀ c₁ r R hr hrR)
      (closedRadialAnnulus c₀ r R) := by
  -- Restriction to the annulus is the canonical continuous radial collar.
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict :
      (closedRadialAnnulus c₀ r R).restrict
          (twoCappedDiskPatch c₀ c₁ r R hr hrR) =
        radialAnnulusCollar c₀ r R hr hrR := by
    funext z
    exact twoCappedDiskPatch_apply_leftAnnulus c₀ c₁ r R hr hrR hdisjoint z
  rw [hrestrict]
  exact continuous_radialAnnulusCollar c₀ r R hr hrR

/-- Helper for Example 63.2: with disjoint outer disks, the generic capped patch is
continuous on the second collar. -/
lemma continuousOn_twoCappedDiskPatch_rightAnnulus (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R)) :
    ContinuousOn (twoCappedDiskPatch c₀ c₁ r R hr hrR)
      (closedRadialAnnulus c₁ r R) := by
  -- Restriction to the annulus is the canonical continuous radial collar.
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict :
      (closedRadialAnnulus c₁ r R).restrict
          (twoCappedDiskPatch c₀ c₁ r R hr hrR) =
        radialAnnulusCollar c₁ r R hr hrR := by
    funext z
    exact twoCappedDiskPatch_apply_rightAnnulus c₀ c₁ r R hr hrR hdisjoint z
  rw [hrestrict]
  exact continuous_radialAnnulusCollar c₁ r R hr hrR

/-- Helper for Example 63.2: the generic capped patch is continuous on the closed
exterior of the two outer disks. -/
lemma continuousOn_twoCappedDiskPatch_closedExterior (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) :
    ContinuousOn (twoCappedDiskPatch c₀ c₁ r R hr hrR)
      ((Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ) := by
  -- On this closed region the patch agrees with the zero-height plane inclusion.
  have hbottom : Continuous (fun z : ℂ ↦ ((0 : unitInterval), z)) :=
    continuous_const.prodMk continuous_id
  refine hbottom.continuousOn.congr ?_
  intro z hz
  have h₀ : z ∉ Metric.ball c₀ R := fun hz₀ ↦ hz (Or.inl hz₀)
  have h₁ : z ∉ Metric.ball c₁ R := fun hz₁ ↦ hz (Or.inr hz₁)
  exact twoCappedDiskPatch_apply_closedExterior c₀ c₁ r R hr hrR h₀ h₁

/-- Helper for Example 63.2: disjoint outer disks make the generic two-cap patch
continuous on the whole plane. -/
lemma continuous_twoCappedDiskPatch (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R)) :
    Continuous (twoCappedDiskPatch c₀ c₁ r R hr hrR) := by
  -- Paste the five continuous restrictions across the finite closed cover.
  have hcaps := (continuousOn_twoCappedDiskPatch_leftCap c₀ c₁ r R hr hrR).union_of_isClosed
    (continuousOn_twoCappedDiskPatch_rightCap c₀ c₁ r R hr hrR hdisjoint)
    Metric.isClosed_closedBall Metric.isClosed_closedBall
  have hleft := hcaps.union_of_isClosed
    (continuousOn_twoCappedDiskPatch_leftAnnulus c₀ c₁ r R hr hrR hdisjoint)
    (Metric.isClosed_closedBall.union Metric.isClosed_closedBall)
    (isClosed_closedRadialAnnulus c₀ r R)
  have hright := hleft.union_of_isClosed
    (continuousOn_twoCappedDiskPatch_rightAnnulus c₀ c₁ r R hr hrR hdisjoint)
    ((Metric.isClosed_closedBall.union Metric.isClosed_closedBall).union
      (isClosed_closedRadialAnnulus c₀ r R))
    (isClosed_closedRadialAnnulus c₁ r R)
  have hall := hright.union_of_isClosed
    (continuousOn_twoCappedDiskPatch_closedExterior c₀ c₁ r R hr hrR)
    (((Metric.isClosed_closedBall.union Metric.isClosed_closedBall).union
      (isClosed_closedRadialAnnulus c₀ r R)).union
        (isClosed_closedRadialAnnulus c₁ r R))
    ((Metric.isOpen_ball.union Metric.isOpen_ball).isClosed_compl)
  rw [twoCappedDiskPatch_closedCover c₀ c₁ r R hrR] at hall
  exact continuousOn_univ.mp hall

/-- Helper for Example 63.2: scaling an inner disk of positive radius by `R / r`
lands in the corresponding outer disk. -/
lemma radialScale_mem_closedBall (c z : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hz : z ∈ Metric.closedBall c r) :
    c + (R / r) • (z - c) ∈ Metric.closedBall c R := by
  -- Scaling multiplies the radial distance by the positive factor `R / r`.
  have hR : 0 < R := hr.trans hrR
  have hzDist : dist z c ≤ r := by
    simpa only [Metric.mem_closedBall] using hz
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos hR hr), ← dist_eq_norm]
  calc
    R / r * dist z c ≤ R / r * r :=
      mul_le_mul_of_nonneg_left hzDist (div_pos hR hr).le
    _ = R := div_mul_cancel₀ R hr.ne'

/-- Helper for Example 63.2: radial interpolation recovers a planar point from the
time and spatial coordinates of the generic patch. -/
noncomputable def twoCappedDiskPatchRecover (c₀ c₁ : ℂ) (r R : ℝ) :
    unitInterval × ℂ → ℂ :=
  fun p ↦
    @dite ℂ
      (p.2 ∈ Metric.closedBall c₀ R)
      (Classical.propDecidable _)
      (fun _ ↦ c₀ + ((R - (R - r) * (p.1 : ℝ)) / R) • (p.2 - c₀))
      (fun _ ↦
        @dite ℂ
          (p.2 ∈ Metric.closedBall c₁ R)
          (Classical.propDecidable _)
          (fun _ ↦ c₁ + ((R - (R - r) * (p.1 : ℝ)) / R) • (p.2 - c₁))
          (fun _ ↦ p.2))

/-- Helper for Example 63.2: recovery after the generic patch is the identity on the
first inner cap. -/
lemma twoCappedDiskPatchRecover_leftCap (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) {z : ℂ}
    (hz : z ∈ Metric.closedBall c₀ r) :
    twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR z) = z := by
  -- The cap lands in the first outer disk; interpolation at time one reverses its scale.
  have houter := radialScale_mem_closedBall c₀ z r R hr hrR hz
  rw [twoCappedDiskPatch_apply_leftCap c₀ c₁ r R hr hrR hz]
  simp only [twoCappedDiskPatchRecover, dif_pos houter, Set.Icc.coe_one,
    add_sub_cancel_left, smul_smul]
  have hR : R ≠ 0 := (hr.trans hrR).ne'
  have hscale : ((R - (R - r) * 1) / R) * (R / r) = 1 := by
    field_simp [hR, hr.ne']
    ring
  rw [hscale, one_smul, add_sub_cancel]

/-- Helper for Example 63.2: recovery after the generic patch is the identity on the
second inner cap. -/
lemma twoCappedDiskPatchRecover_rightCap (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R))
    {z : ℂ} (hz : z ∈ Metric.closedBall c₁ r) :
    twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR z) = z := by
  -- The second cap lands only in its outer disk, so recovery selects its radial formula.
  have houter := radialScale_mem_closedBall c₁ z r R hr hrR hz
  have hnotLeft : c₁ + (R / r) • (z - c₁) ∉ Metric.closedBall c₀ R := by
    exact fun hleft ↦ Set.disjoint_left.mp hdisjoint hleft houter
  rw [twoCappedDiskPatch_apply_rightCap c₀ c₁ r R hr hrR hdisjoint hz]
  simp only [twoCappedDiskPatchRecover, dif_neg hnotLeft, dif_pos houter,
    Set.Icc.coe_one, add_sub_cancel_left, smul_smul]
  have hR : R ≠ 0 := (hr.trans hrR).ne'
  have hscale : ((R - (R - r) * 1) / R) * (R / r) = 1 := by
    field_simp [hR, hr.ne']
    ring
  rw [hscale, one_smul, add_sub_cancel]

/-- Helper for Example 63.2: recovery after the generic patch is the identity on the
first radial collar. -/
lemma twoCappedDiskPatchRecover_leftAnnulus (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R))
    (z : closedRadialAnnulus c₀ r R) :
    twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR z) = (z : ℂ) := by
  -- The collar's spatial coordinate is on the first outer sphere, and its owner API reconstructs `z`.
  have hspatialSphere := radialAnnulusCollar_snd_mem_sphere c₀ hr hrR z
  have hspatialBall : (radialAnnulusCollar c₀ r R hr hrR z).2 ∈
      Metric.closedBall c₀ R := Metric.sphere_subset_closedBall hspatialSphere
  rw [twoCappedDiskPatch_apply_leftAnnulus c₀ c₁ r R hr hrR hdisjoint z]
  simp only [twoCappedDiskPatchRecover, dif_pos hspatialBall]
  exact radialAnnulusReconstruct_collar c₀ r R hr hrR z

/-- Helper for Example 63.2: recovery after the generic patch is the identity on the
second radial collar. -/
lemma twoCappedDiskPatchRecover_rightAnnulus (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R))
    (z : closedRadialAnnulus c₁ r R) :
    twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR z) = (z : ℂ) := by
  -- Disjoint outer disks force recovery to select the second collar before reconstructing `z`.
  have hspatialSphere := radialAnnulusCollar_snd_mem_sphere c₁ hr hrR z
  have hspatialBall : (radialAnnulusCollar c₁ r R hr hrR z).2 ∈
      Metric.closedBall c₁ R := Metric.sphere_subset_closedBall hspatialSphere
  have hnotLeft : (radialAnnulusCollar c₁ r R hr hrR z).2 ∉
      Metric.closedBall c₀ R :=
    fun hleft ↦ Set.disjoint_left.mp hdisjoint hleft hspatialBall
  rw [twoCappedDiskPatch_apply_rightAnnulus c₀ c₁ r R hr hrR hdisjoint z]
  simp only [twoCappedDiskPatchRecover, dif_neg hnotLeft, dif_pos hspatialBall]
  exact radialAnnulusReconstruct_collar c₁ r R hr hrR z

/-- Helper for Example 63.2: recovery after the generic patch is the identity on the
closed exterior of the two outer disks. -/
lemma twoCappedDiskPatchRecover_closedExterior (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) {z : ℂ}
    (h₀ : z ∉ Metric.ball c₀ R) (h₁ : z ∉ Metric.ball c₁ R) :
    twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR z) = z := by
  -- At time zero the recovery formula fixes either outer boundary; elsewhere it returns `z`.
  rw [twoCappedDiskPatch_apply_closedExterior c₀ c₁ r R hr hrR h₀ h₁]
  by_cases hz₀ : z ∈ Metric.closedBall c₀ R
  · simp only [twoCappedDiskPatchRecover, dif_pos hz₀, Set.Icc.coe_zero,
      mul_zero, sub_zero, div_self (hr.trans hrR).ne', one_smul, add_sub_cancel]
  · by_cases hz₁ : z ∈ Metric.closedBall c₁ R
    · simp only [twoCappedDiskPatchRecover, dif_neg hz₀, dif_pos hz₁,
        Set.Icc.coe_zero, mul_zero, sub_zero, div_self (hr.trans hrR).ne',
        one_smul, add_sub_cancel]
    · simp only [twoCappedDiskPatchRecover, dif_neg hz₀, dif_neg hz₁]

/-- Helper for Example 63.2: radial recovery is a left inverse to the generic capped
patch when the two outer disks are disjoint. -/
lemma twoCappedDiskPatchRecover_apply (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R))
    (z : ℂ) :
    twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR z) = z := by
  -- Dispatch through the same finite closed cover used in the continuity proof.
  have hzCover : z ∈
      ((((Metric.closedBall c₀ r ∪ Metric.closedBall c₁ r) ∪
          closedRadialAnnulus c₀ r R) ∪ closedRadialAnnulus c₁ r R) ∪
          (Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ) := by
    rw [twoCappedDiskPatch_closedCover c₀ c₁ r R hrR]
    exact Set.mem_univ z
  rcases hzCover with (((hinner₀ | hinner₁) | hannulus₀) | hannulus₁) | hexterior
  · exact twoCappedDiskPatchRecover_leftCap c₀ c₁ r R hr hrR hinner₀
  · exact twoCappedDiskPatchRecover_rightCap c₀ c₁ r R hr hrR hdisjoint hinner₁
  · exact twoCappedDiskPatchRecover_leftAnnulus c₀ c₁ r R hr hrR hdisjoint
      ⟨z, hannulus₀⟩
  · exact twoCappedDiskPatchRecover_rightAnnulus c₀ c₁ r R hr hrR hdisjoint
      ⟨z, hannulus₁⟩
  · have h₀ : z ∉ Metric.ball c₀ R := fun hz₀ ↦ hexterior (Or.inl hz₀)
    have h₁ : z ∉ Metric.ball c₁ R := fun hz₁ ↦ hexterior (Or.inr hz₁)
    exact twoCappedDiskPatchRecover_closedExterior c₀ c₁ r R hr hrR h₀ h₁

/-- Helper for Example 63.2: the generic two-cap patch is injective when its two outer
disks are disjoint. -/
lemma injective_twoCappedDiskPatch (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R)) :
    Function.Injective (twoCappedDiskPatch c₀ c₁ r R hr hrR) := by
  -- Apply the explicit radial left inverse to equal patch values.
  intro x y hxy
  calc
    x = twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR x) :=
      (twoCappedDiskPatchRecover_apply c₀ c₁ r R hr hrR hdisjoint x).symm
    _ = twoCappedDiskPatchRecover c₀ c₁ r R
        (twoCappedDiskPatch c₀ c₁ r R hr hrR y) := congrArg _ hxy
    _ = y := twoCappedDiskPatchRecover_apply c₀ c₁ r R hr hrR hdisjoint y

/-- Helper for Example 63.2: the zero-height inclusion of the complex plane is a
closed embedding into the unit cylinder. -/
lemma zeroHeightComplexPlane_isClosedEmbedding :
    Topology.IsClosedEmbedding (fun z : ℂ ↦ ((0 : unitInterval), z)) := by
  -- Its range is the closed zero slice, and the second projection is a left inverse.
  refine ⟨isEmbedding_prodMkRight (0 : unitInterval), ?_⟩
  have hrange : Set.range (fun z : ℂ ↦ ((0 : unitInterval), z)) =
      ({0} : Set unitInterval) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_range, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ,
      and_true, Prod.exists]
    constructor
    · rintro ⟨_, rfl, rfl⟩
      rfl
    · intro hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
  rw [hrange]
  exact isClosed_singleton.prod isClosed_univ

/-- Helper for Example 63.2: the generic two-cap patch sends closed sets to closed
sets when its outer disks are disjoint. -/
lemma isClosedMap_twoCappedDiskPatch (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R)) :
    IsClosedMap (twoCappedDiskPatch c₀ c₁ r R hr hrR) := by
  -- Decompose each closed source set along the same five-piece closed cover.
  intro S hS
  have hcontinuous := continuous_twoCappedDiskPatch c₀ c₁ r R hr hrR hdisjoint
  have hleftCap : IsClosed
      (twoCappedDiskPatch c₀ c₁ r R hr hrR '' (S ∩ Metric.closedBall c₀ r)) :=
    (((isCompact_closedBall c₀ r).inter_left hS).image hcontinuous).isClosed
  have hrightCap : IsClosed
      (twoCappedDiskPatch c₀ c₁ r R hr hrR '' (S ∩ Metric.closedBall c₁ r)) :=
    (((isCompact_closedBall c₁ r).inter_left hS).image hcontinuous).isClosed
  have hleftAnnulus : IsClosed
      (twoCappedDiskPatch c₀ c₁ r R hr hrR ''
        (S ∩ closedRadialAnnulus c₀ r R)) :=
    (((isCompact_closedRadialAnnulus c₀ r R).inter_left hS).image hcontinuous).isClosed
  have hrightAnnulus : IsClosed
      (twoCappedDiskPatch c₀ c₁ r R hr hrR ''
        (S ∩ closedRadialAnnulus c₁ r R)) :=
    (((isCompact_closedRadialAnnulus c₁ r R).inter_left hS).image hcontinuous).isClosed
  have hclosedExterior : IsClosed ((Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ) :=
    (Metric.isOpen_ball.union Metric.isOpen_ball).isClosed_compl
  have hexteriorImage :
      twoCappedDiskPatch c₀ c₁ r R hr hrR ''
          (S ∩ (Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ) =
        (fun z : ℂ ↦ ((0 : unitInterval), z)) ''
          (S ∩ (Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ) := by
    apply Set.image_congr
    intro z hz
    have h₀ : z ∉ Metric.ball c₀ R := fun hz₀ ↦ hz.2 (Or.inl hz₀)
    have h₁ : z ∉ Metric.ball c₁ R := fun hz₁ ↦ hz.2 (Or.inr hz₁)
    exact twoCappedDiskPatch_apply_closedExterior c₀ c₁ r R hr hrR h₀ h₁
  have hexterior : IsClosed
      (twoCappedDiskPatch c₀ c₁ r R hr hrR ''
        (S ∩ (Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ)) := by
    rw [hexteriorImage]
    exact zeroHeightComplexPlane_isClosedEmbedding.isClosedMap _
      (hS.inter hclosedExterior)
  have himageDecomposition :
      twoCappedDiskPatch c₀ c₁ r R hr hrR '' S =
        (((twoCappedDiskPatch c₀ c₁ r R hr hrR '' (S ∩ Metric.closedBall c₀ r) ∪
          twoCappedDiskPatch c₀ c₁ r R hr hrR '' (S ∩ Metric.closedBall c₁ r)) ∪
          twoCappedDiskPatch c₀ c₁ r R hr hrR ''
            (S ∩ closedRadialAnnulus c₀ r R)) ∪
          twoCappedDiskPatch c₀ c₁ r R hr hrR ''
            (S ∩ closedRadialAnnulus c₁ r R)) ∪
          twoCappedDiskPatch c₀ c₁ r R hr hrR ''
            (S ∩ (Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ) := by
    calc
      twoCappedDiskPatch c₀ c₁ r R hr hrR '' S =
          twoCappedDiskPatch c₀ c₁ r R hr hrR '' (S ∩ Set.univ) := by
        rw [Set.inter_univ]
      _ = twoCappedDiskPatch c₀ c₁ r R hr hrR ''
          (S ∩ ((((Metric.closedBall c₀ r ∪ Metric.closedBall c₁ r) ∪
            closedRadialAnnulus c₀ r R) ∪ closedRadialAnnulus c₁ r R) ∪
              (Metric.ball c₀ R ∪ Metric.ball c₁ R)ᶜ)) := by
        rw [twoCappedDiskPatch_closedCover c₀ c₁ r R hrR]
      _ = _ := by
        simp only [Set.inter_union_distrib_left, Set.image_union]
  rw [himageDecomposition]
  exact (((hleftCap.union hrightCap).union hleftAnnulus).union hrightAnnulus).union
    hexterior

/-- Helper for Example 63.2: the generic unbraided two-cap patch is a closed embedding
when the two outer disks are disjoint. -/
lemma twoCappedDiskPatch_isClosedEmbedding (c₀ c₁ : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hdisjoint : Disjoint (Metric.closedBall c₀ R) (Metric.closedBall c₁ R)) :
    Topology.IsClosedEmbedding (twoCappedDiskPatch c₀ c₁ r R hr hrR) := by
  -- Assemble continuity, the explicit radial left inverse, and the closed-image decomposition.
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_twoCappedDiskPatch c₀ c₁ r R hr hrR hdisjoint)
    (injective_twoCappedDiskPatch c₀ c₁ r R hr hrR hdisjoint)
    (isClosedMap_twoCappedDiskPatch c₀ c₁ r R hr hrR hdisjoint)

end AlexanderHornGeometry
