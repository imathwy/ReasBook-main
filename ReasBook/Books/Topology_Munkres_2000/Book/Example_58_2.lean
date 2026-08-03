module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Example_58_2.PlanarFigureEight

public section

namespace PlanarFigureEight
noncomputable section
open scoped ComplexConjugate

/-- Helper for Example 58.2: the midpoint of the two punctures. -/
private def midpoint (p q : ℂ) : ℂ :=
  (p + q) / 2

/-- Helper for Example 58.2: the squared distance from the midpoint. -/
private def radialNormSq (p q z : ℂ) : ℝ :=
  Complex.normSq (z - midpoint p q)

/-- Helper for Example 58.2: the radial size of the tangent figure eight in the
direction of `z` from the midpoint. -/
private def radialWidth (p q z : ℂ) : ℝ :=
  |((z - midpoint p q) * conj (q - p)).re|

/-- Helper for Example 58.2: the common exterior of the two open disks bounded by
the circles of the planar figure eight. -/
private def outsidePunctureDisks (p q : ℂ) : Set ℂ :=
  {z | dist p q / 2 ≤ dist z p ∧ dist p q / 2 ≤ dist z q}

/-- Helper for Example 58.2: the two tangent circles are the midpoint-radial locus
`radialNormSq = radialWidth`. -/
private lemma mem_carrier_iff_radialEquation (p q z : ℂ) :
    z ∈ carrier p q ↔ radialNormSq p q z = radialWidth p q z := by
  -- Squaring the two circle equations removes the square roots in the complex norm.
  rw [mem_carrier_iff]
  have hr : 0 ≤ dist p q / 2 := div_nonneg dist_nonneg zero_le_two
  rw [← sq_eq_sq₀ dist_nonneg hr, ← sq_eq_sq₀ dist_nonneg hr]
  simp only [Complex.dist_eq, div_pow, ← Complex.normSq_eq_norm_sq]
  have hN : 0 ≤ Complex.normSq (z - midpoint p q) := Complex.normSq_nonneg _
  let A : ℝ := ((z - midpoint p q) * conj (q - p)).re
  change _ ↔ Complex.normSq (z - midpoint p q) = |A|
  -- In midpoint coordinates the two circle equations are `N + A = 0` and `N - A = 0`.
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA]
    dsimp [A] at *
    norm_num [midpoint, Complex.normSq_apply, Complex.mul_re] at *
    constructor
    · intro h
      rcases h with h | h
      · nlinarith
      · nlinarith
    · intro h
      right
      nlinarith
  · rw [abs_of_nonpos hA]
    dsimp [A] at *
    norm_num [midpoint, Complex.normSq_apply, Complex.mul_re] at *
    constructor
    · intro h
      rcases h with h | h
      · nlinarith
      · nlinarith
    · intro h
      left
      nlinarith

/-- Helper for Example 58.2: being outside both tangent puncture disks is the
midpoint-radial inequality `radialWidth ≤ radialNormSq`. -/
private lemma mem_outsidePunctureDisks_iff_radialWidth_le (p q z : ℂ) :
    z ∈ outsidePunctureDisks p q ↔ radialWidth p q z ≤ radialNormSq p q z := by
  -- Squared distances turn the two exterior conditions into opposite linear bounds.
  change (dist p q / 2 ≤ dist z p ∧ dist p q / 2 ≤ dist z q) ↔ _
  have hr : 0 ≤ dist p q / 2 := div_nonneg dist_nonneg zero_le_two
  rw [← sq_le_sq₀ hr dist_nonneg, ← sq_le_sq₀ hr dist_nonneg]
  simp only [Complex.dist_eq, div_pow, ← Complex.normSq_eq_norm_sq]
  have hN : 0 ≤ Complex.normSq (z - midpoint p q) := Complex.normSq_nonneg _
  let A : ℝ := ((z - midpoint p q) * conj (q - p)).re
  change _ ↔ |A| ≤ Complex.normSq (z - midpoint p q)
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA]
    dsimp [A] at *
    norm_num [midpoint, Complex.normSq_apply, Complex.mul_re] at *
    constructor
    · rintro ⟨hp, hq⟩
      nlinarith
    · intro h
      constructor
      · nlinarith
      · nlinarith
  · rw [abs_of_nonpos hA]
    dsimp [A] at *
    norm_num [midpoint, Complex.normSq_apply, Complex.mul_re] at *
    constructor
    · rintro ⟨hp, hq⟩
      nlinarith
    · intro h
      constructor
      · nlinarith
      · nlinarith

/-- Helper for Example 58.2: the factor that radially pushes a point to at least
distance `r` from `c`. -/
private def radialPushScale (c : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  max 1 (r / dist z c)

/-- Helper for Example 58.2: interpolation from a point to its radial push away
from `c`. -/
private def radialPushValue (c : ℂ) (r : ℝ) (t : unitInterval) (z : ℂ) : ℂ :=
  c + (1 + (t : ℝ) * (radialPushScale c r z - 1)) • (z - c)

/-- Helper for Example 58.2: a radial push factor is at least one. -/
private lemma one_le_radialPushScale (c : ℂ) (r : ℝ) (z : ℂ) :
    1 ≤ radialPushScale c r z := by
  -- The maximum defining the scale always dominates its first entry.
  exact le_max_left _ _

/-- Helper for Example 58.2: every interpolation coefficient in a radial push is
between one and its endpoint scale. -/
private lemma radialPushCoefficient_bounds (c : ℂ) (r : ℝ)
    (t : unitInterval) (z : ℂ) :
    1 ≤ 1 + (t : ℝ) * (radialPushScale c r z - 1) ∧
      1 + (t : ℝ) * (radialPushScale c r z - 1) ≤ radialPushScale c r z := by
  -- This is the affine interval between `1` and a scale no smaller than `1`.
  have hs := one_le_radialPushScale c r z
  constructor
  · nlinarith [t.2.1]
  · nlinarith [t.2.2]

/-- Helper for Example 58.2: radial pushing multiplies distance from the center by
the interpolation coefficient. -/
private lemma dist_radialPushValue_center (c : ℂ) (r : ℝ)
    (t : unitInterval) (z : ℂ) :
    dist (radialPushValue c r t z) c =
      (1 + (t : ℝ) * (radialPushScale c r z - 1)) * dist z c := by
  -- Subtract the center and use positivity of the real interpolation coefficient.
  have hk := (radialPushCoefficient_bounds c r t z).1
  rw [Complex.dist_eq, Complex.dist_eq]
  simp only [radialPushValue, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans hk), norm_sub_rev]

/-- Helper for Example 58.2: the radial push starts at the original point. -/
private lemma radialPushValue_zero (c : ℂ) (r : ℝ) (z : ℂ) :
    radialPushValue c r 0 z = z := by
  -- At time zero the interpolation coefficient is one.
  simp [radialPushValue]

/-- Helper for Example 58.2: points already at least radius `r` from the center
are fixed throughout the radial push. -/
private lemma radialPushValue_eq_of_radius_le (c : ℂ) {r : ℝ} (hr : 0 < r)
    (t : unitInterval) {z : ℂ} (hz : r ≤ dist z c) :
    radialPushValue c r t z = z := by
  -- The quotient is at most one, so the maximum scale is exactly one.
  have hdist : 0 < dist z c := lt_of_lt_of_le hr hz
  have hquot : r / dist z c ≤ 1 := (div_le_one hdist).2 hz
  rw [radialPushValue, radialPushScale, max_eq_left hquot]
  simp

/-- Helper for Example 58.2: the endpoint of a radial push lies outside the open
disk of radius `r`. -/
private lemma radius_le_dist_radialPushValue_one (c : ℂ) {r : ℝ}
    {z : ℂ} (hz : z ≠ c) :
    r ≤ dist (radialPushValue c r 1 z) c := by
  -- At time one the new distance is `max 1 (r / dist z c) * dist z c`.
  rw [dist_radialPushValue_center]
  norm_num
  have hd : 0 < dist z c := dist_pos.mpr hz
  calc
    r = (r / dist z c) * dist z c := (div_mul_cancel₀ r hd.ne').symm
    _ ≤ radialPushScale c r z * dist z c :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hd.le

/-- Helper for Example 58.2: a radial push never reaches its center when it starts
away from that center. -/
private lemma radialPushValue_ne_center (c : ℂ) (r : ℝ) (t : unitInterval)
    {z : ℂ} (hz : z ≠ c) : radialPushValue c r t z ≠ c := by
  -- Its distance from the center is a coefficient at least one times a positive distance.
  intro heq
  have hd : 0 < dist z c := dist_pos.mpr hz
  have hk := (radialPushCoefficient_bounds c r t z).1
  have hdist := dist_radialPushValue_center c r t z
  rw [heq, dist_self] at hdist
  nlinarith

/-- Helper for Example 58.2: while a point inside the radius-`r` disk is pushed,
it remains in the corresponding closed disk. -/
private lemma dist_radialPushValue_center_le_radius_of_lt (c : ℂ) {r : ℝ}
    (t : unitInterval) {z : ℂ} (hz : z ≠ c) (hzr : dist z c < r) :
    dist (radialPushValue c r t z) c ≤ r := by
  -- In the active case the endpoint scale is exactly `r / dist z c`.
  have hd : 0 < dist z c := dist_pos.mpr hz
  have hscale : radialPushScale c r z = r / dist z c := by
    rw [radialPushScale, max_eq_right]
    exact (one_le_div hd).2 hzr.le
  rw [dist_radialPushValue_center]
  calc
    (1 + (t : ℝ) * (radialPushScale c r z - 1)) * dist z c ≤
        radialPushScale c r z * dist z c :=
      mul_le_mul_of_nonneg_right (radialPushCoefficient_bounds c r t z).2 hd.le
    _ = r := by rw [hscale, div_mul_cancel₀ r hd.ne']

/-- Helper for Example 58.2: pushing inside one of two tangent disks cannot hit
the center of the other disk. -/
private lemma radialPushValue_ne_otherCenter (c d : ℂ) {r : ℝ} (hr : 0 < r)
    (hcd : dist c d = 2 * r) (t : unitInterval) {z : ℂ}
    (hzc : z ≠ c) (hzd : z ≠ d) : radialPushValue c r t z ≠ d := by
  -- Outside the active disk the map is fixed; inside it stays too close to `c` to equal `d`.
  by_cases hzrad : r ≤ dist z c
  · rw [radialPushValue_eq_of_radius_le c hr t hzrad]
    exact hzd
  · intro heq
    have hle := dist_radialPushValue_center_le_radius_of_lt c t hzc (lt_of_not_ge hzrad)
    rw [heq, dist_comm d c, hcd] at hle
    nlinarith

/-- Helper for Example 58.2: a radial push in one tangent disk preserves the
exterior of the other tangent disk. -/
private lemma radius_le_dist_radialPushValue_other (c d : ℂ) {r : ℝ} (hr : 0 < r)
    (hcd : dist c d = 2 * r) (t : unitInterval) {z : ℂ}
    (hzc : z ≠ c) (hzd : r ≤ dist z d) :
    r ≤ dist (radialPushValue c r t z) d := by
  -- In the active disk, the triangle inequality separates the image from the other center.
  by_cases hzrad : r ≤ dist z c
  · rwa [radialPushValue_eq_of_radius_le c hr t hzrad]
  · have hle := dist_radialPushValue_center_le_radius_of_lt c t hzc (lt_of_not_ge hzrad)
    have htriangle := dist_triangle c (radialPushValue c r t z) d
    rw [hcd, dist_comm c] at htriangle
    nlinarith

/-- Helper for Example 58.2: every point of the figure eight lies outside both
open disks bounded by its circles. -/
private lemma mem_outsidePunctureDisks_of_mem_carrier (p q z : ℂ)
    (hz : z ∈ carrier p q) : z ∈ outsidePunctureDisks p q := by
  -- On either circle, the triangle inequality supplies the distance to the other center.
  rw [mem_carrier_iff] at hz
  change dist p q / 2 ≤ dist z p ∧ dist p q / 2 ≤ dist z q
  rcases hz with hp | hq
  · constructor
    · exact hp.ge
    · have htriangle := dist_triangle p z q
      rw [dist_comm p z, hp] at htriangle
      nlinarith
  · constructor
    · have htriangle := dist_triangle p z q
      rw [dist_comm p z, hq] at htriangle
      nlinarith
    · exact hq.ge

/-- Helper for Example 58.2: the first disk-expansion stage, viewed in the ambient
complex plane. -/
private def firstExpansionValue (p q : ℂ) (t : unitInterval)
    (z : TwoPuncturePlane p q) : ℂ :=
  radialPushValue p (dist p q / 2) t z

/-- Helper for Example 58.2: the first disk-expansion stage avoids both punctures. -/
private lemma firstExpansionValue_mem (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    (z : TwoPuncturePlane p q) :
    firstExpansionValue p q t z ≠ p ∧ firstExpansionValue p q t z ≠ q := by
  -- The radial push avoids its own center and stays inside the disk disjoint from `q`.
  have hr : 0 < dist p q / 2 := div_pos (dist_pos.mpr hpq) zero_lt_two
  have hpqdist : dist p q = 2 * (dist p q / 2) := by ring
  constructor
  · exact radialPushValue_ne_center p (dist p q / 2) t z.property.1
  · exact radialPushValue_ne_otherCenter p q hr hpqdist t z.property.1 z.property.2

/-- Helper for Example 58.2: the subtype-valued first disk-expansion stage. -/
private def firstExpansionPoint (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    (z : TwoPuncturePlane p q) : TwoPuncturePlane p q :=
  ⟨firstExpansionValue p q t z, firstExpansionValue_mem p q hpq t z⟩

/-- Helper for Example 58.2: the first disk-expansion stage is continuous. -/
private lemma continuous_firstExpansionPoint (p q : ℂ) (hpq : p ≠ q) :
    Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      firstExpansionPoint p q hpq x.1 x.2 := by
  -- All operations are continuous because the source subtype excludes the denominator center.
  apply Continuous.subtype_mk
  unfold firstExpansionValue radialPushValue radialPushScale
  fun_prop (disch := aesop)

/-- Helper for Example 58.2: the first disk-expansion as a continuous homotopy map. -/
private def firstExpansion (p q : ℂ) (hpq : p ≠ q) :
    C(unitInterval × TwoPuncturePlane p q, TwoPuncturePlane p q) :=
  ⟨fun x ↦ firstExpansionPoint p q hpq x.1 x.2,
    continuous_firstExpansionPoint p q hpq⟩

/-- Helper for Example 58.2: the endpoint map of the first disk-expansion. -/
private def firstExpansionMap (p q : ℂ) (hpq : p ≠ q) :
    C(TwoPuncturePlane p q, TwoPuncturePlane p q) :=
  (firstExpansion p q hpq).comp
    ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩

/-- Helper for Example 58.2: the first expansion starts at the identity. -/
private lemma firstExpansion_zero (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) : firstExpansion p q hpq (0, z) = z := by
  -- This is the zero-time specification of the radial push.
  apply Subtype.ext
  exact radialPushValue_zero p (dist p q / 2) z

/-- Helper for Example 58.2: the first expansion ends at `firstExpansionMap`. -/
private lemma firstExpansion_one (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) :
    firstExpansion p q hpq (1, z) = firstExpansionMap p q hpq z := by
  -- Both sides evaluate the same subtype-valued endpoint.
  rfl

/-- Helper for Example 58.2: the first expansion fixes the figure-eight carrier. -/
private lemma firstExpansion_fixed (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    {z : TwoPuncturePlane p q} (hz : z ∈ inComplement p q) :
    firstExpansion p q hpq (t, z) = z := by
  -- Carrier points are outside the first open disk, where the radial push is the identity.
  have hr : 0 < dist p q / 2 := div_pos (dist_pos.mpr hpq) zero_lt_two
  have hzout := mem_outsidePunctureDisks_of_mem_carrier p q z (mem_inComplement_iff p q z |>.mp hz)
  apply Subtype.ext
  exact radialPushValue_eq_of_radius_le p hr t hzout.1

/-- Helper for Example 58.2: the first disk-expansion is a homotopy relative to
the figure eight. -/
private def firstExpansionHomotopyRel (p q : ℂ) (hpq : p ≠ q) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (TwoPuncturePlane p q))
      (firstExpansionMap p q hpq) (inComplement p q) :=
  { toHomotopy :=
      { toContinuousMap := firstExpansion p q hpq
        map_zero_left := firstExpansion_zero p q hpq
        map_one_left := firstExpansion_one p q hpq }
    prop' := firstExpansion_fixed p q hpq }

/-- Helper for Example 58.2: the second disk-expansion stage, applied after the
first endpoint and viewed in the ambient complex plane. -/
private def secondExpansionValue (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    (z : TwoPuncturePlane p q) : ℂ :=
  radialPushValue q (dist p q / 2) t (firstExpansionPoint p q hpq 1 z)

/-- Helper for Example 58.2: the second disk-expansion stage avoids both punctures. -/
private lemma secondExpansionValue_mem (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    (z : TwoPuncturePlane p q) :
    secondExpansionValue p q hpq t z ≠ p ∧ secondExpansionValue p q hpq t z ≠ q := by
  -- Apply the two-center avoidance lemma with `q` as the active center.
  have hr : 0 < dist p q / 2 := div_pos (dist_pos.mpr hpq) zero_lt_two
  have hqpdist : dist q p = 2 * (dist p q / 2) := by
    rw [dist_comm]
    ring
  let y := firstExpansionPoint p q hpq 1 z
  constructor
  · exact radialPushValue_ne_otherCenter q p hr hqpdist t y.property.2 y.property.1
  · exact radialPushValue_ne_center q (dist p q / 2) t y.property.2

/-- Helper for Example 58.2: the subtype-valued second disk-expansion stage. -/
private def secondExpansionPoint (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    (z : TwoPuncturePlane p q) : TwoPuncturePlane p q :=
  ⟨secondExpansionValue p q hpq t z, secondExpansionValue_mem p q hpq t z⟩

/-- Helper for Example 58.2: the second disk-expansion stage is continuous. -/
private lemma continuous_secondExpansionPoint (p q : ℂ) (hpq : p ≠ q) :
    Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      secondExpansionPoint p q hpq x.1 x.2 := by
  -- Continuity follows by composing the first endpoint with the same radial-push formula.
  apply Continuous.subtype_mk
  have hy : Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      ((firstExpansionPoint p q hpq 1 x.2 : TwoPuncturePlane p q) : ℂ) :=
    continuous_subtype_val.comp ((firstExpansionMap p q hpq).continuous.comp continuous_snd)
  have hdenom : ∀ x : unitInterval × TwoPuncturePlane p q,
      dist ((firstExpansionPoint p q hpq 1 x.2 : TwoPuncturePlane p q) : ℂ) q ≠ 0 := by
    intro x
    exact (dist_ne_zero.mpr (firstExpansionPoint p q hpq 1 x.2).property.2)
  have hscale : Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      radialPushScale q (dist p q / 2) (firstExpansionPoint p q hpq 1 x.2) := by
    unfold radialPushScale
    exact continuous_const.max (continuous_const.div (hy.dist continuous_const) hdenom)
  have ht : Continuous fun x : unitInterval × TwoPuncturePlane p q ↦ (x.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hcoeff : Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      (1 : ℝ) + (x.1 : ℝ) *
        (radialPushScale q (dist p q / 2) (firstExpansionPoint p q hpq 1 x.2) - 1) :=
    continuous_const.add (ht.mul (hscale.sub continuous_const))
  have hvalue : Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      q + ((1 : ℝ) + (x.1 : ℝ) *
        (radialPushScale q (dist p q / 2) (firstExpansionPoint p q hpq 1 x.2) - 1)) •
          (((firstExpansionPoint p q hpq 1 x.2 : TwoPuncturePlane p q) : ℂ) - q) :=
    continuous_const.add (hcoeff.smul (hy.sub continuous_const))
  exact hvalue

/-- Helper for Example 58.2: the second disk-expansion as a continuous homotopy map. -/
private def secondExpansion (p q : ℂ) (hpq : p ≠ q) :
    C(unitInterval × TwoPuncturePlane p q, TwoPuncturePlane p q) :=
  ⟨fun x ↦ secondExpansionPoint p q hpq x.1 x.2,
    continuous_secondExpansionPoint p q hpq⟩

/-- Helper for Example 58.2: the endpoint after expanding both puncture disks. -/
private def punctureDiskExpansionMap (p q : ℂ) (hpq : p ≠ q) :
    C(TwoPuncturePlane p q, TwoPuncturePlane p q) :=
  (secondExpansion p q hpq).comp
    ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩

/-- Helper for Example 58.2: the second expansion starts at the first endpoint map. -/
private lemma secondExpansion_zero (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) :
    secondExpansion p q hpq (0, z) = firstExpansionMap p q hpq z := by
  -- At time zero the second radial push leaves the first endpoint unchanged.
  apply Subtype.ext
  exact radialPushValue_zero q (dist p q / 2) (firstExpansionPoint p q hpq 1 z)

/-- Helper for Example 58.2: the second expansion ends at the combined endpoint map. -/
private lemma secondExpansion_one (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) :
    secondExpansion p q hpq (1, z) = punctureDiskExpansionMap p q hpq z := by
  -- Both sides evaluate the same combined endpoint.
  rfl

/-- Helper for Example 58.2: the second expansion fixes the figure-eight carrier. -/
private lemma secondExpansion_fixed (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    {z : TwoPuncturePlane p q} (hz : z ∈ inComplement p q) :
    secondExpansion p q hpq (t, z) = firstExpansionMap p q hpq z := by
  -- The first endpoint is `z`, and carrier points are outside the second open disk.
  have hr : 0 < dist p q / 2 := div_pos (dist_pos.mpr hpq) zero_lt_two
  have hzout := mem_outsidePunctureDisks_of_mem_carrier p q z (mem_inComplement_iff p q z |>.mp hz)
  have hfirst := firstExpansion_fixed p q hpq 1 hz
  have hfirstVal : ((firstExpansionPoint p q hpq 1 z : TwoPuncturePlane p q) : ℂ) = z :=
    congrArg Subtype.val hfirst
  apply Subtype.ext
  calc
    ((secondExpansion p q hpq (t, z) : TwoPuncturePlane p q) : ℂ) =
        radialPushValue q (dist p q / 2) t (firstExpansionPoint p q hpq 1 z) := rfl
    _ = radialPushValue q (dist p q / 2) t z := congrArg _ hfirstVal
    _ = z := radialPushValue_eq_of_radius_le q hr t hzout.2
    _ = ((firstExpansionMap p q hpq z : TwoPuncturePlane p q) : ℂ) := hfirstVal.symm

/-- Helper for Example 58.2: the second disk-expansion is relative to the figure eight. -/
private def secondExpansionHomotopyRel (p q : ℂ) (hpq : p ≠ q) :
    ContinuousMap.HomotopyRel (firstExpansionMap p q hpq)
      (punctureDiskExpansionMap p q hpq) (inComplement p q) :=
  { toHomotopy :=
      { toContinuousMap := secondExpansion p q hpq
        map_zero_left := secondExpansion_zero p q hpq
        map_one_left := secondExpansion_one p q hpq }
    prop' := secondExpansion_fixed p q hpq }

/-- Helper for Example 58.2: after both disk expansions, the endpoint lies in the
common exterior of the two puncture disks. -/
private lemma punctureDiskExpansionMap_mem_outside (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) :
    (punctureDiskExpansionMap p q hpq z : ℂ) ∈ outsidePunctureDisks p q := by
  -- The second push reaches the `q`-exterior and preserves the `p`-exterior from stage one.
  have hr : 0 < dist p q / 2 := div_pos (dist_pos.mpr hpq) zero_lt_two
  have hqpdist : dist q p = 2 * (dist p q / 2) := by
    rw [dist_comm]
    ring
  let y := firstExpansionPoint p q hpq 1 z
  have hyp : dist p q / 2 ≤ dist (y : ℂ) p :=
    radius_le_dist_radialPushValue_one p z.property.1
  change dist p q / 2 ≤ dist (radialPushValue q (dist p q / 2) 1 y) p ∧
    dist p q / 2 ≤ dist (radialPushValue q (dist p q / 2) 1 y) q
  constructor
  · exact radius_le_dist_radialPushValue_other q p hr hqpdist 1 y.property.2 hyp
  · exact radius_le_dist_radialPushValue_one q y.property.2

/-- Helper for Example 58.2: the two puncture-disk expansions concatenate to one
relative homotopy. -/
private def punctureDiskExpansionHomotopyRel (p q : ℂ) (hpq : p ≠ q) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (TwoPuncturePlane p q))
      (punctureDiskExpansionMap p q hpq) (inComplement p q) :=
  (firstExpansionHomotopyRel p q hpq).trans (secondExpansionHomotopyRel p q hpq)

/-- Helper for Example 58.2: the subtype consisting of points outside both open
puncture disks. -/
private abbrev DiskExterior (p q : ℂ) :=
  outsidePunctureDisks p q

/-- Helper for Example 58.2: the expanded endpoint as a point of the common disk exterior. -/
private def expansionExteriorPoint (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) : DiskExterior p q :=
  ⟨punctureDiskExpansionMap p q hpq z,
    punctureDiskExpansionMap_mem_outside p q hpq z⟩

/-- Helper for Example 58.2: the expanded endpoint map into the disk exterior is continuous. -/
private lemma continuous_expansionExteriorPoint (p q : ℂ) (hpq : p ≠ q) :
    Continuous (expansionExteriorPoint p q hpq) := by
  -- The ambient endpoint is continuous, and its exterior membership was proved separately.
  exact ((punctureDiskExpansionMap p q hpq).continuous.subtype_val).subtype_mk _

/-- Helper for Example 58.2: midpoint-radial scaling changes squared radial norm
quadratically. -/
private lemma radialNormSq_midpoint_smul (p q z : ℂ) (s : ℝ) :
    radialNormSq p q (midpoint p q + s • (z - midpoint p q)) =
      s ^ 2 * radialNormSq p q z := by
  -- Translation cancels and the complex norm is homogeneous under real scaling.
  unfold radialNormSq
  rw [add_sub_cancel_left, Complex.normSq_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, ← Complex.normSq_eq_norm_sq]

/-- Helper for Example 58.2: nonnegative midpoint-radial scaling changes radial
width linearly. -/
private lemma radialWidth_midpoint_smul (p q z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    radialWidth p q (midpoint p q + s • (z - midpoint p q)) =
      s * radialWidth p q z := by
  -- Real scaling passes through the real part, and nonnegativity removes its absolute value.
  unfold radialWidth
  rw [add_sub_cancel_left, smul_mul_assoc, Complex.smul_re, smul_eq_mul, abs_mul,
    abs_of_nonneg hs]

/-- Helper for Example 58.2: the scalar used to collapse an exterior point onto
the figure eight along its midpoint ray. -/
private def radialProjectionScale (p q z : ℂ) : ℝ :=
  radialWidth p q z / radialNormSq p q z

/-- Helper for Example 58.2: an exterior point has a nonnegative radial projection scale. -/
private lemma radialProjectionScale_nonneg (p q : ℂ) (z : DiskExterior p q) :
    0 ≤ radialProjectionScale p q z := by
  -- Both radial invariants are nonnegative.
  exact div_nonneg (abs_nonneg _) (Complex.normSq_nonneg _)

/-- Helper for Example 58.2: an exterior point has radial projection scale at most one. -/
private lemma radialProjectionScale_le_one (p q : ℂ) (z : DiskExterior p q) :
    radialProjectionScale p q z ≤ 1 := by
  -- The exterior bridge gives `radialWidth ≤ radialNormSq`; handle the zero denominator separately.
  have hle := (mem_outsidePunctureDisks_iff_radialWidth_le p q z).mp z.property
  by_cases hzero : radialNormSq p q z = 0
  · simp [radialProjectionScale, hzero]
  · exact (div_le_one (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hzero))).2 hle

/-- Helper for Example 58.2: the ambient midpoint-radial projection value. -/
private def radialProjectionValue (p q z : ℂ) : ℂ :=
  midpoint p q + radialProjectionScale p q z • (z - midpoint p q)

/-- Helper for Example 58.2: radial projection does not increase distance from
the midpoint on the disk exterior. -/
private lemma dist_radialProjectionValue_midpoint_le (p q : ℂ) (z : DiskExterior p q) :
    dist (radialProjectionValue p q z) (midpoint p q) ≤ dist (z : ℂ) (midpoint p q) := by
  -- Its distance is the original distance multiplied by a scalar in `[0,1]`.
  rw [Complex.dist_eq, Complex.dist_eq]
  simp only [radialProjectionValue, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (radialProjectionScale_nonneg p q z)]
  exact mul_le_of_le_one_left (norm_nonneg _) (radialProjectionScale_le_one p q z)

/-- Helper for Example 58.2: the midpoint itself is fixed by radial projection. -/
private lemma radialProjectionValue_midpoint (p q : ℂ) :
    radialProjectionValue p q (midpoint p q) = midpoint p q := by
  -- The displacement vector from the midpoint is zero.
  simp [radialProjectionValue]

/-- Helper for Example 58.2: midpoint-radial projection is continuous on the
common exterior of the two puncture disks. -/
private lemma continuous_radialProjectionValue (p q : ℂ) :
    Continuous fun z : DiskExterior p q ↦ radialProjectionValue p q z := by
  -- Away from the midpoint this is a quotient of continuous functions; at the midpoint
  -- the exterior inequality makes the projected distance no larger than the input distance.
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : (z : ℂ) = midpoint p q
  · rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have hzproj : radialProjectionValue p q z = midpoint p q := by
      rw [hz, radialProjectionValue_midpoint]
    have hy' : dist (y : ℂ) (z : ℂ) < ε := hy
    calc
      dist (radialProjectionValue p q y) (radialProjectionValue p q z) =
          dist (radialProjectionValue p q y) (midpoint p q) := by rw [hzproj]
      _ ≤ dist (y : ℂ) (midpoint p q) := dist_radialProjectionValue_midpoint_le p q y
      _ = dist (y : ℂ) (z : ℂ) := by rw [hz]
      _ < ε := hy'
  · have hnorm : radialNormSq p q z ≠ 0 := by
      intro hzero
      have hsub : (z : ℂ) - midpoint p q = 0 := Complex.normSq_eq_zero.mp hzero
      exact hz (sub_eq_zero.mp hsub)
    have hambient : ContinuousAt (radialProjectionValue p q) (z : ℂ) := by
      have hsub : ContinuousAt (fun w : ℂ ↦ w - midpoint p q) (z : ℂ) :=
        continuousAt_id.sub continuousAt_const
      have hnormSq : ContinuousAt (fun w : ℂ ↦ radialNormSq p q w) (z : ℂ) :=
        Complex.continuous_normSq.continuousAt.comp hsub
      have hproduct : ContinuousAt
          (fun w : ℂ ↦ (w - midpoint p q) * conj (q - p)) (z : ℂ) :=
        hsub.mul continuousAt_const
      have hwidth : ContinuousAt (fun w : ℂ ↦ radialWidth p q w) (z : ℂ) :=
        (Complex.continuous_re.continuousAt.comp hproduct).abs
      have hscale : ContinuousAt (fun w : ℂ ↦ radialProjectionScale p q w) (z : ℂ) :=
        hwidth.div hnormSq hnorm
      exact continuousAt_const.add (hscale.smul hsub)
    exact hambient.comp continuousAt_subtype_val

/-- Helper for Example 58.2: radial projection of an exterior point lands on the
figure-eight carrier. -/
private lemma radialProjectionValue_mem_carrier (p q : ℂ) (z : DiskExterior p q) :
    radialProjectionValue p q z ∈ carrier p q := by
  -- The chosen scale makes the quadratic radial norm equal the linear radial width.
  rw [mem_carrier_iff_radialEquation, radialProjectionValue,
    radialNormSq_midpoint_smul,
    radialWidth_midpoint_smul p q z (radialProjectionScale_nonneg p q z)]
  by_cases hzero : radialNormSq p q z = 0
  · simp [radialProjectionScale, hzero]
  · unfold radialProjectionScale
    field_simp [hzero]

/-- Helper for Example 58.2: radial projection fixes every point already on the
figure-eight carrier. -/
private lemma radialProjectionValue_fixed (p q : ℂ) {z : ℂ} (hz : z ∈ carrier p q) :
    radialProjectionValue p q z = z := by
  -- On the carrier the two radial invariants agree, so the projection scale is one,
  -- except at the midpoint where the displacement itself is zero.
  have heq := (mem_carrier_iff_radialEquation p q z).mp hz
  by_cases hzero : radialNormSq p q z = 0
  · have hsub : z - midpoint p q = 0 := Complex.normSq_eq_zero.mp hzero
    have hzmid : z = midpoint p q := sub_eq_zero.mp hsub
    rw [hzmid, radialProjectionValue_midpoint]
  · unfold radialProjectionValue radialProjectionScale
    rw [← heq, div_self hzero]
    simp

/-- Helper for Example 58.2: the affine coefficient used during midpoint-radial collapse. -/
private def radialCollapseCoefficient (p q : ℂ) (t : unitInterval) (z : ℂ) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) * radialProjectionScale p q z

/-- Helper for Example 58.2: the midpoint-radial collapse coefficient stays
between the endpoint scale and one on the disk exterior. -/
private lemma radialCollapseCoefficient_bounds (p q : ℂ) (t : unitInterval)
    (z : DiskExterior p q) :
    radialProjectionScale p q z ≤ radialCollapseCoefficient p q t z ∧
      radialCollapseCoefficient p q t z ≤ 1 := by
  -- It is the affine interpolation from `1` to the endpoint scale in `[0,1]`.
  have hs0 := radialProjectionScale_nonneg p q z
  have hs1 := radialProjectionScale_le_one p q z
  unfold radialCollapseCoefficient
  constructor
  · nlinarith [t.2.2]
  · nlinarith [t.2.1]

/-- Helper for Example 58.2: the ambient radial-collapse path on the disk exterior. -/
private def radialCollapseValue (p q : ℂ) (t : unitInterval) (z : DiskExterior p q) : ℂ :=
  (1 - (t : ℝ)) • (z : ℂ) + (t : ℝ) • radialProjectionValue p q z

/-- Helper for Example 58.2: the affine radial-collapse path has its midpoint-ray
normal form. -/
private lemma radialCollapseValue_eq_midpoint_smul (p q : ℂ) (t : unitInterval)
    (z : DiskExterior p q) :
    radialCollapseValue p q t z = midpoint p q +
      radialCollapseCoefficient p q t z • ((z : ℂ) - midpoint p q) := by
  -- Substitute the endpoint projection and collect the two scalar coefficients.
  unfold radialCollapseValue radialProjectionValue radialCollapseCoefficient
  module

/-- Helper for Example 58.2: every point of the radial-collapse path remains in
the common disk exterior. -/
private lemma radialCollapseValue_mem_outside (p q : ℂ) (t : unitInterval)
    (z : DiskExterior p q) : radialCollapseValue p q t z ∈ outsidePunctureDisks p q := by
  -- Along a midpoint ray, the exterior inequality is preserved for all coefficients
  -- between the projection scale and one.
  rw [mem_outsidePunctureDisks_iff_radialWidth_le,
    radialCollapseValue_eq_midpoint_smul, radialNormSq_midpoint_smul]
  have hk0 : 0 ≤ radialCollapseCoefficient p q t z :=
    (radialProjectionScale_nonneg p q z).trans
      (radialCollapseCoefficient_bounds p q t z).1
  rw [radialWidth_midpoint_smul p q z hk0]
  have hWN := (mem_outsidePunctureDisks_iff_radialWidth_le p q z).mp z.property
  have hN0 : 0 ≤ radialNormSq p q z := Complex.normSq_nonneg _
  have hkScale := (radialCollapseCoefficient_bounds p q t z).1
  by_cases hzero : radialNormSq p q z = 0
  · have hwidth : radialWidth p q z = 0 := by
      have hwidth0 : 0 ≤ radialWidth p q z := abs_nonneg _
      nlinarith
    simp [hzero, hwidth]
  · have hscale : radialWidth p q z =
        radialProjectionScale p q z * radialNormSq p q z := by
      unfold radialProjectionScale
      field_simp [hzero]
    calc
      radialCollapseCoefficient p q t z * radialWidth p q z =
          radialCollapseCoefficient p q t z *
            (radialProjectionScale p q z * radialNormSq p q z) := by rw [hscale]
      _ ≤ radialCollapseCoefficient p q t z *
          (radialCollapseCoefficient p q t z * radialNormSq p q z) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hkScale hN0) hk0
      _ = radialCollapseCoefficient p q t z ^ 2 * radialNormSq p q z := by ring

/-- Helper for Example 58.2: the radial-collapse path is continuous on the disk exterior. -/
private lemma continuous_radialCollapseValue (p q : ℂ) :
    Continuous fun x : unitInterval × DiskExterior p q ↦
      radialCollapseValue p q x.1 x.2 := by
  -- Use the affine form between the identity and the already continuous projection.
  unfold radialCollapseValue
  have ht : Continuous fun x : unitInterval × DiskExterior p q ↦ (x.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun x : unitInterval × DiskExterior p q ↦ (x.2 : ℂ) :=
    continuous_subtype_val.comp continuous_snd
  have hprojection : Continuous fun x : unitInterval × DiskExterior p q ↦
      radialProjectionValue p q x.2 :=
    (continuous_radialProjectionValue p q).comp continuous_snd
  exact (continuous_const.sub ht).smul hz |>.add (ht.smul hprojection)

/-- Helper for Example 58.2: the radial collapse starts at its exterior input. -/
private lemma radialCollapseValue_zero (p q : ℂ) (z : DiskExterior p q) :
    radialCollapseValue p q 0 z = z := by
  -- At time zero only the identity endpoint has nonzero weight.
  simp [radialCollapseValue]

/-- Helper for Example 58.2: the radial collapse ends at radial projection. -/
private lemma radialCollapseValue_one (p q : ℂ) (z : DiskExterior p q) :
    radialCollapseValue p q 1 z = radialProjectionValue p q z := by
  -- At time one only the projection endpoint has nonzero weight.
  simp [radialCollapseValue]

/-- Helper for Example 58.2: the radial-collapse path fixes carrier points. -/
private lemma radialCollapseValue_fixed (p q : ℂ) (t : unitInterval)
    {z : DiskExterior p q} (hz : (z : ℂ) ∈ carrier p q) :
    radialCollapseValue p q t z = z := by
  -- Radial projection fixes the carrier, so its affine interpolation does as well.
  unfold radialCollapseValue
  rw [radialProjectionValue_fixed p q hz]
  module

/-- Helper for Example 58.2: when the punctures are distinct, every point in the
common disk exterior avoids both punctures. -/
private lemma mem_twoPuncturePlane_of_mem_outside (p q z : ℂ) (hpq : p ≠ q)
    (hz : z ∈ outsidePunctureDisks p q) : z ≠ p ∧ z ≠ q := by
  -- Exterior distances are bounded below by the positive half-distance of the punctures.
  have hr : 0 < dist p q / 2 := div_pos (dist_pos.mpr hpq) zero_lt_two
  change dist p q / 2 ≤ dist z p ∧ dist p q / 2 ≤ dist z q at hz
  constructor
  · intro hzp
    rw [hzp, dist_self] at hz
    nlinarith [hz.1]
  · intro hzq
    rw [hzq, dist_self] at hz
    nlinarith [hz.2]

/-- Helper for Example 58.2: the subtype-valued radial-collapse path on the disk exterior. -/
private def radialCollapsePoint (p q : ℂ) (hpq : p ≠ q) (t : unitInterval)
    (z : DiskExterior p q) : TwoPuncturePlane p q :=
  ⟨radialCollapseValue p q t z,
    mem_twoPuncturePlane_of_mem_outside p q _ hpq (radialCollapseValue_mem_outside p q t z)⟩

/-- Helper for Example 58.2: the subtype-valued radial-collapse path is continuous. -/
private lemma continuous_radialCollapsePoint (p q : ℂ) (hpq : p ≠ q) :
    Continuous fun x : unitInterval × DiskExterior p q ↦
      radialCollapsePoint p q hpq x.1 x.2 := by
  -- Lift the continuous ambient path through its puncture-avoidance specification.
  exact (continuous_radialCollapseValue p q).subtype_mk _

/-- Helper for Example 58.2: expanding both disks fixes points of the carrier. -/
private lemma punctureDiskExpansionMap_fixed (p q : ℂ) (hpq : p ≠ q)
    {z : TwoPuncturePlane p q} (hz : z ∈ inComplement p q) :
    punctureDiskExpansionMap p q hpq z = z := by
  -- Each of the two radial-push stages is fixed on the carrier.
  calc
    punctureDiskExpansionMap p q hpq z = firstExpansionMap p q hpq z :=
      secondExpansion_fixed p q hpq 1 hz
    _ = z := firstExpansion_fixed p q hpq 1 hz

/-- Helper for Example 58.2: the ambient endpoint value of the full retraction. -/
private def figureEightProjectionValue (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) : ℂ :=
  radialProjectionValue p q (expansionExteriorPoint p q hpq z)

/-- Helper for Example 58.2: the full endpoint value belongs to the carrier. -/
private lemma figureEightProjectionValue_mem_carrier (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) : figureEightProjectionValue p q hpq z ∈ carrier p q := by
  -- The expansion supplies an exterior point, and radial projection lands on the carrier.
  exact radialProjectionValue_mem_carrier p q (expansionExteriorPoint p q hpq z)

/-- Helper for Example 58.2: the full endpoint value avoids both punctures. -/
private lemma figureEightProjectionValue_mem_twoPuncture (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) :
    figureEightProjectionValue p q hpq z ≠ p ∧ figureEightProjectionValue p q hpq z ≠ q := by
  -- Carrier points lie in the disk exterior, whose positive radius excludes the centers.
  exact mem_twoPuncturePlane_of_mem_outside p q _ hpq
    (mem_outsidePunctureDisks_of_mem_carrier p q _
      (figureEightProjectionValue_mem_carrier p q hpq z))

/-- Helper for Example 58.2: the full endpoint as a point of the doubly punctured plane. -/
private def figureEightProjectionPoint (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) : TwoPuncturePlane p q :=
  ⟨figureEightProjectionValue p q hpq z,
    figureEightProjectionValue_mem_twoPuncture p q hpq z⟩

/-- Helper for Example 58.2: the endpoint map takes values in the relative figure eight. -/
private def figureEightProjection (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) : inComplement p q :=
  ⟨figureEightProjectionPoint p q hpq z,
    (mem_inComplement_iff p q _).mpr (figureEightProjectionValue_mem_carrier p q hpq z)⟩

/-- Helper for Example 58.2: the endpoint projection into the relative figure
eight is continuous. -/
private lemma continuous_figureEightProjection (p q : ℂ) (hpq : p ≠ q) :
    Continuous (figureEightProjection p q hpq) := by
  -- Compose exterior expansion with radial projection, then lift through the two subtype layers.
  have hambient : Continuous (figureEightProjectionValue p q hpq) :=
    (continuous_radialProjectionValue p q).comp
      (continuous_expansionExteriorPoint p q hpq)
  exact (hambient.subtype_mk _).subtype_mk _

/-- Helper for Example 58.2: the endpoint projection is a left inverse to carrier inclusion. -/
private lemma figureEightProjection_leftInverse (p q : ℂ) (hpq : p ≠ q) :
    Function.LeftInverse (figureEightProjection p q hpq) Subtype.val := by
  -- Expansion and radial projection both fix a point already on the carrier.
  intro z
  have hexpand := punctureDiskExpansionMap_fixed p q hpq z.property
  have hcarrier : ((z : inComplement p q) : TwoPuncturePlane p q) ∈ inComplement p q := z.property
  have hradial := radialProjectionValue_fixed p q
    ((mem_inComplement_iff p q _).mp hcarrier)
  apply Subtype.ext
  apply Subtype.ext
  calc
    figureEightProjectionValue p q hpq z =
        radialProjectionValue p q (punctureDiskExpansionMap p q hpq z) := rfl
    _ = radialProjectionValue p q z := congrArg _ (congrArg Subtype.val hexpand)
    _ = z := hradial

/-- Helper for Example 58.2: the endpoint projection as a retraction onto the figure eight. -/
private def figureEightRetraction (p q : ℂ) (hpq : p ≠ q) :
    Set.Retraction (inComplement p q) :=
  { toContinuousMap := ⟨figureEightProjection p q hpq,
      continuous_figureEightProjection p q hpq⟩
    leftInverse := figureEightProjection_leftInverse p q hpq }

/-- Helper for Example 58.2: the radial collapse after the two disk expansions. -/
private def radialCollapseAfterExpansionPoint (p q : ℂ) (hpq : p ≠ q)
    (t : unitInterval) (z : TwoPuncturePlane p q) : TwoPuncturePlane p q :=
  radialCollapsePoint p q hpq t (expansionExteriorPoint p q hpq z)

/-- Helper for Example 58.2: radial collapse after expansion is continuous. -/
private lemma continuous_radialCollapseAfterExpansionPoint (p q : ℂ) (hpq : p ≠ q) :
    Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      radialCollapseAfterExpansionPoint p q hpq x.1 x.2 := by
  -- Pair the time coordinate with the continuous expansion endpoint, then compose.
  have hinput : Continuous fun x : unitInterval × TwoPuncturePlane p q ↦
      (x.1, expansionExteriorPoint p q hpq x.2) :=
    continuous_fst.prodMk ((continuous_expansionExteriorPoint p q hpq).comp continuous_snd)
  exact (continuous_radialCollapsePoint p q hpq).comp hinput

/-- Helper for Example 58.2: radial collapse after expansion as a continuous homotopy map. -/
private def radialCollapseAfterExpansion (p q : ℂ) (hpq : p ≠ q) :
    C(unitInterval × TwoPuncturePlane p q, TwoPuncturePlane p q) :=
  ⟨fun x ↦ radialCollapseAfterExpansionPoint p q hpq x.1 x.2,
    continuous_radialCollapseAfterExpansionPoint p q hpq⟩

/-- Helper for Example 58.2: the post-expansion collapse starts at the expansion endpoint. -/
private lemma radialCollapseAfterExpansion_zero (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) :
    radialCollapseAfterExpansion p q hpq (0, z) = punctureDiskExpansionMap p q hpq z := by
  -- The exterior radial collapse is the identity at time zero.
  apply Subtype.ext
  exact radialCollapseValue_zero p q (expansionExteriorPoint p q hpq z)

/-- Helper for Example 58.2: the post-expansion collapse ends at the retraction map. -/
private lemma radialCollapseAfterExpansion_one (p q : ℂ) (hpq : p ≠ q)
    (z : TwoPuncturePlane p q) :
    radialCollapseAfterExpansion p q hpq (1, z) =
      (figureEightRetraction p q hpq).toAmbient z := by
  -- At time one its ambient value is the radial projection used by the retraction.
  apply Subtype.ext
  exact radialCollapseValue_one p q (expansionExteriorPoint p q hpq z)

/-- Helper for Example 58.2: the post-expansion radial collapse is fixed on the carrier. -/
private lemma radialCollapseAfterExpansion_fixed (p q : ℂ) (hpq : p ≠ q)
    (t : unitInterval) {z : TwoPuncturePlane p q} (hz : z ∈ inComplement p q) :
    radialCollapseAfterExpansion p q hpq (t, z) = punctureDiskExpansionMap p q hpq z := by
  -- Expansion fixes `z`, so its exterior endpoint is a carrier point fixed by radial collapse.
  have hexpand := punctureDiskExpansionMap_fixed p q hpq hz
  have hexpandVal : ((expansionExteriorPoint p q hpq z : DiskExterior p q) : ℂ) = z :=
    congrArg Subtype.val hexpand
  have hcarrier : ((expansionExteriorPoint p q hpq z : DiskExterior p q) : ℂ) ∈
      carrier p q := by
    rw [hexpandVal]
    exact (mem_inComplement_iff p q z).mp hz
  apply Subtype.ext
  calc
    ((radialCollapseAfterExpansion p q hpq (t, z) : TwoPuncturePlane p q) : ℂ) =
        radialCollapseValue p q t (expansionExteriorPoint p q hpq z) := rfl
    _ = (expansionExteriorPoint p q hpq z : ℂ) :=
      radialCollapseValue_fixed p q t hcarrier
    _ = z := hexpandVal
    _ = ((punctureDiskExpansionMap p q hpq z : TwoPuncturePlane p q) : ℂ) :=
      (congrArg Subtype.val hexpand).symm

/-- Helper for Example 58.2: the radial-collapse stage after expansion is a
homotopy relative to the figure eight. -/
private def radialCollapseAfterExpansionHomotopyRel (p q : ℂ) (hpq : p ≠ q) :
    ContinuousMap.HomotopyRel (punctureDiskExpansionMap p q hpq)
      (figureEightRetraction p q hpq).toAmbient (inComplement p q) :=
  { toHomotopy :=
      { toContinuousMap := radialCollapseAfterExpansion p q hpq
        map_zero_left := radialCollapseAfterExpansion_zero p q hpq
        map_one_left := radialCollapseAfterExpansion_one p q hpq }
    prop' := radialCollapseAfterExpansion_fixed p q hpq }

/-- Helper for Example 58.2: the explicit three-stage deformation retraction onto
the planar figure eight. -/
private def deformationRetraction (p q : ℂ) (hpq : p ≠ q) :
    Set.DeformationRetraction (inComplement p q) :=
  { toRetraction := figureEightRetraction p q hpq
    toHomotopyRel := (punctureDiskExpansionHomotopyRel p q hpq).trans
      (radialCollapseAfterExpansionHomotopyRel p q hpq) }

/-- Example 58.2: for distinct points `p` and `q`, the planar figure eight formed by the
two equal-radius circles centered at the punctures is a deformation retract of the doubly
punctured plane. -/
theorem isDeformationRetract (p q : ℂ) (hpq : p ≠ q) :
    Set.IsDeformationRetract (inComplement p q) := by
  -- The packaged retraction and concatenated relative homotopy supply the witness.
  apply (Set.isDeformationRetract_iff (inComplement p q)).2
  exact ⟨(deformationRetraction p q hpq).toRetraction,
    ⟨(deformationRetraction p q hpq).toHomotopyRel⟩⟩

end
end PlanarFigureEight
