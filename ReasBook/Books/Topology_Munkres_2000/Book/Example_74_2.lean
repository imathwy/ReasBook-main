module

public import Topology_Munkres_2000.Book.Example_74_2.Presentation
public import Topology_Munkres_2000.Book.Example_74_2.UnitSquare
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import all Topology_Munkres_2000.Book.Example_74_2.Presentation
import all Topology_Munkres_2000.Book.Example_74_2.UnitSquare
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Homeomorph.Quotient

public section

namespace SphereSquare

open scoped Topology

/-- Helper for Example 74.2: every occurrence in the singleton scheme is `region`. -/
private lemma occurrence_eq_region (r : LabellingScheme.Occurrence scheme) : r = region := by
  -- The remainder of the cons-occurrence equivalence has no elements.
  unfold region
  apply (LabellingScheme.consOccurrenceEquiv boundaryWord 0).injective
  rw [Equiv.apply_symm_apply]
  cases h : LabellingScheme.consOccurrenceEquiv boundaryWord 0 r with
  | none => rfl
  | some remaining =>
      exact (Nat.not_lt_zero remaining.2 remaining.2.isLt).elim

/-- Helper for Example 74.2: the unique occurrence carries the displayed boundary word. -/
private lemma region_word : region.1 = boundaryWord := by
  -- The inverse occurrence equivalence selects the head word.
  rfl

/-- Helper for Example 74.2: every occurrence in the square scheme has four edges. -/
private lemma occurrence_length (r : LabellingScheme.Occurrence scheme) :
    r.1.1.length = 4 := by
  -- Normalize to the unique occurrence and compute the concrete word length.
  rw [occurrence_eq_region r, region_word]
  decide

/-- Helper for Example 74.2: projection from the singleton source region to the square is a
homeomorphism. -/
private lemma sourceProjectionIsHomeomorph :
    IsHomeomorph (fun x : regions.Source ↦ x.2) := by
  -- Exhibit insertion into the unique summand as the continuous inverse.
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · rw [continuous_iSup_dom]
    intro r
    rw [continuous_coinduced_dom]
    letI : TopologicalSpace (regions.Point r) := regions.topology r
    exact continuous_id
  · have hinclusion : Continuous[regions.topology region, regions.sourceTopology]
        (Sigma.mk region : regions.Point region → regions.Source) :=
      continuous_iSup_rng (i := region) (f := Sigma.mk region)
        (continuous_coinduced_rng (f := Sigma.mk region))
    refine ⟨fun p ↦ (⟨region, p⟩ : regions.Source), ?_, ?_, ?_⟩
    · rintro ⟨r, p⟩
      rw [occurrence_eq_region r]
    · intro p
      rfl
    · unfold regions at hinclusion ⊢
      exact hinclusion

/-- Helper for Example 74.2: the explicit equivalence relation generated on the square
boundary. -/
private def squareBoundaryRel (p q : unitInterval × unitInterval) : Prop :=
  p = q ∨
    (∃ t : unitInterval, p = (t, 0) ∧ q = (1, unitInterval.symm t)) ∨
    (∃ t : unitInterval, p = (1, unitInterval.symm t) ∧ q = (t, 0)) ∨
    (∃ t : unitInterval, p = (unitInterval.symm t, 1) ∧ q = (0, t)) ∨
    (∃ t : unitInterval, p = (0, t) ∧ q = (unitInterval.symm t, 1))

/-- Helper for Example 74.2: the first barycentric coordinate on either triangular half of
the square. -/
private def outerCoordinate (p : unitInterval × unitInterval) : ℝ :=
  1 - max (p.1 : ℝ) (p.2 : ℝ)

/-- Helper for Example 74.2: the unsigned distance from the diagonal of the square. -/
private def diagonalCoordinate (p : unitInterval × unitInterval) : ℝ :=
  |(p.2 : ℝ) - (p.1 : ℝ)|

/-- Helper for Example 74.2: the third barycentric coordinate on either triangular half of
the square. -/
private def innerCoordinate (p : unitInterval × unitInterval) : ℝ :=
  min (p.1 : ℝ) (p.2 : ℝ)

/-- Helper for Example 74.2: the closed-first-quadrant complex coordinate of a square point. -/
private def sectorCoordinate (p : unitInterval × unitInterval) : ℂ :=
  Complex.ofReal (outerCoordinate p) + Complex.ofReal (innerCoordinate p) * Complex.I

/-- Helper for Example 74.2: the odd homogeneous fourth power of a real number. -/
private def signedFourth (x : ℝ) : ℝ :=
  x * |x| ^ 3

/-- Helper for Example 74.2: homogeneous coordinates for the square-to-sphere quotient map. -/
private noncomputable def rawSphereVector (p : unitInterval × unitInterval) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[(sectorCoordinate p ^ 4).re, (sectorCoordinate p ^ 4).im,
    signedFourth ((p.2 : ℝ) - (p.1 : ℝ))]

/-- Helper for Example 74.2: the three barycentric coordinates of a square point sum to one. -/
private lemma barycentricCoordinate_sum (p : unitInterval × unitInterval) :
    outerCoordinate p + diagonalCoordinate p + innerCoordinate p = 1 := by
  -- Split at the diagonal, where `max`, `min`, and absolute value have fixed formulas.
  rcases le_total (p.1 : ℝ) (p.2 : ℝ) with h | h
  · rw [outerCoordinate, diagonalCoordinate, innerCoordinate, max_eq_right h,
      min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring
  · rw [outerCoordinate, diagonalCoordinate, innerCoordinate, max_eq_left h,
      min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring

/-- Helper for Example 74.2: the homogeneous square-to-sphere coordinate vector never
vanishes. -/
private lemma rawSphereVector_ne_zero (p : unitInterval × unitInterval) :
    rawSphereVector p ≠ 0 := by
  -- Vanishing of the signed height first places the point on the diagonal.
  intro hzero
  have hheight := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) hzero
  have hdiag : (p.2 : ℝ) - (p.1 : ℝ) = 0 := by
    simpa [rawSphereVector, signedFourth] using hheight
  have hxy : (p.1 : ℝ) = (p.2 : ℝ) := (sub_eq_zero.mp hdiag).symm
  -- The first two zero coordinates say that the complex sector coordinate has fourth power
  -- zero, hence both remaining barycentric coordinates vanish.
  have hre := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) hzero
  have him := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) hzero
  have hpow : sectorCoordinate p ^ 4 = 0 := by
    apply Complex.ext
    · simpa [rawSphereVector] using hre
    · simpa [rawSphereVector] using him
  have hsector : sectorCoordinate p = 0 := eq_zero_of_pow_eq_zero hpow
  have houter : outerCoordinate p = 0 := by
    simpa [sectorCoordinate] using congrArg Complex.re hsector
  have hinner : innerCoordinate p = 0 := by
    simpa [sectorCoordinate] using congrArg Complex.im hsector
  have hsum := barycentricCoordinate_sum p
  simp only [houter, diagonalCoordinate, hdiag, abs_zero, hinner, add_zero] at hsum
  norm_num at hsum

/-- Helper for Example 74.2: normalization of the raw coordinates lies on the unit sphere. -/
private lemma normalizedRawSphereVector_mem_sphere (p : unitInterval × unitInterval) :
    NormedSpace.normalize (rawSphereVector p) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- A nonzero vector has normalized norm one.
  rw [Metric.mem_sphere, dist_zero_right]
  exact NormedSpace.norm_normalize (rawSphereVector_ne_zero p)

/-- Helper for Example 74.2: the normalized homogeneous coordinates packaged as a sphere
point. -/
private noncomputable def spherePoint (p : unitInterval × unitInterval) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨NormedSpace.normalize (rawSphereVector p), normalizedRawSphereVector_mem_sphere p⟩

/-- Helper for Example 74.2: the explicit square-to-sphere map is continuous. -/
private lemma continuous_spherePoint : Continuous spherePoint := by
  -- Check continuity after forgetting the sphere subtype, keeping the nonvanishing side
  -- condition explicit for inversion of the norm.
  have hraw : Continuous rawSphereVector := by
    unfold rawSphereVector sectorCoordinate outerCoordinate innerCoordinate signedFourth
    fun_prop
  have hnormNe (p : unitInterval × unitInterval) : ‖rawSphereVector p‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (rawSphereVector_ne_zero p)
  apply continuous_induced_rng.mpr
  unfold spherePoint NormedSpace.normalize
  exact (hraw.norm.inv₀ hnormNe).smul hraw

/-- Helper for Example 74.2: the raw coordinates agree on the paired bottom and right
edges. -/
private lemma rawSphereVector_bottom_right (t : unitInterval) :
    rawSphereVector (t, 0) = rawSphereVector (1, unitInterval.symm t) := by
  -- On the two edges the complex coordinates lie on the two axes, whose fourth powers
  -- agree, while the signed diagonal coordinate is unchanged.
  have ht₀ : 0 ≤ (t : ℝ) := unitInterval.nonneg t
  ext i
  fin_cases i
  all_goals
    simp [rawSphereVector, sectorCoordinate, outerCoordinate, innerCoordinate, signedFourth,
      unitInterval.coe_symm_eq, max_eq_left ht₀, min_eq_right ht₀,
      max_eq_left (unitInterval.one_minus_le_one t),
      min_eq_right (unitInterval.one_minus_le_one t), mul_pow]

/-- Helper for Example 74.2: the raw coordinates agree on the paired top and left edges. -/
private lemma rawSphereVector_top_left (t : unitInterval) :
    rawSphereVector (unitInterval.symm t, 1) = rawSphereVector (0, t) := by
  -- This is the analogous fourth-power identification on the other two boundary axes.
  have ht₀ : 0 ≤ (t : ℝ) := unitInterval.nonneg t
  have hsymm₁ : 1 - (t : ℝ) ≤ 1 := unitInterval.one_minus_le_one t
  ext i
  fin_cases i
  all_goals
    simp [rawSphereVector, sectorCoordinate, outerCoordinate, innerCoordinate, signedFourth,
      unitInterval.coe_symm_eq, max_eq_right hsymm₁, min_eq_left hsymm₁,
      max_eq_right ht₀, min_eq_left ht₀, mul_pow]

/-- Helper for Example 74.2: every prescribed square-boundary identification has the same
sphere image. -/
private lemma spherePoint_eq_of_squareBoundaryRel {p q : unitInterval × unitInterval}
    (hpq : squareBoundaryRel p q) : spherePoint p = spherePoint q := by
  -- Each nontrivial case is one of the two raw-coordinate identities or its reverse.
  rcases hpq with rfl | hpq | hpq | hpq | hpq
  · rfl
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Subtype.ext (congrArg NormedSpace.normalize (rawSphereVector_bottom_right t))
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Subtype.ext (congrArg NormedSpace.normalize (rawSphereVector_bottom_right t).symm)
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Subtype.ext (congrArg NormedSpace.normalize (rawSphereVector_top_left t))
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Subtype.ext (congrArg NormedSpace.normalize (rawSphereVector_top_left t).symm)

/-- Helper for Example 74.2: every complex number has a fourth root in the closed first
quadrant. -/
private lemma exists_firstQuadrant_fourthRoot (w : ℂ) :
    ∃ z : ℂ, 0 ≤ z.re ∧ 0 ≤ z.im ∧ z ^ 4 = w := by
  -- Rotate an arbitrary fourth root by a fourth root of unity into the chosen quadrant.
  obtain ⟨z, hz⟩ := (Complex.isOpenQuotientMap_pow 4).surjective w
  by_cases hre : 0 ≤ z.re
  · by_cases him : 0 ≤ z.im
    · exact ⟨z, hre, him, hz⟩
    · refine ⟨Complex.I * z, ?_, ?_, ?_⟩
      · simpa using le_of_not_ge him
      · simpa using hre
      · calc
          (Complex.I * z) ^ 4 = Complex.I ^ 4 * z ^ 4 := mul_pow _ _ _
          _ = z ^ 4 := by norm_num [pow_succ]
          _ = w := hz
  · by_cases him : 0 ≤ z.im
    · refine ⟨-Complex.I * z, ?_, ?_, ?_⟩
      · simpa using him
      · simpa using le_of_not_ge hre
      · calc
          (-Complex.I * z) ^ 4 = (-Complex.I) ^ 4 * z ^ 4 := mul_pow _ _ _
          _ = z ^ 4 := by norm_num [pow_succ]
          _ = w := hz
    · refine ⟨-z, ?_, ?_, ?_⟩
      · simpa using le_of_not_ge hre
      · simpa using le_of_not_ge him
      · calc
          (-z) ^ 4 = z ^ 4 := by norm_num [pow_succ]
          _ = w := hz

/-- Helper for Example 74.2: the iterated square root is a nonnegative fourth root. -/
private lemma sqrtSqrt_fourthPower (x : ℝ) (hx : 0 ≤ x) :
    (√√x) ^ 4 = x := by
  -- Apply the square-root square identity twice.
  calc
    (√√x) ^ 4 = ((√√x) ^ 2) ^ 2 := by ring
    _ = (√x) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg x)]
    _ = x := Real.sq_sqrt hx

/-- Helper for Example 74.2: construct a square point from a first-quadrant sector
coordinate, a nonnegative height, and their common scale. -/
private noncomputable def squarePointFromSector (z : ℂ) (b s : ℝ) (upper : Bool)
    (hc : z.im / s ∈ unitInterval) (hcb : (z.im + b) / s ∈ unitInterval) :
    unitInterval × unitInterval :=
  if upper then (⟨z.im / s, hc⟩, ⟨(z.im + b) / s, hcb⟩)
  else (⟨(z.im + b) / s, hcb⟩, ⟨z.im / s, hc⟩)

/-- Helper for Example 74.2: the outer, inner, and signed diagonal coordinates of a
sector-built square point have their expected scaled values. -/
private lemma squarePointFromSector_coordinates (z : ℂ) (b s : ℝ) (upper : Bool)
    (hc : z.im / s ∈ unitInterval) (hcb : (z.im + b) / s ∈ unitInterval)
    (hb : 0 ≤ b) (hs : s = z.re + b + z.im) (hspos : 0 < s) :
    outerCoordinate (squarePointFromSector z b s upper hc hcb) = z.re / s ∧
      innerCoordinate (squarePointFromSector z b s upper hc hcb) = z.im / s ∧
      ((squarePointFromSector z b s upper hc hcb).2 : ℝ) -
          ((squarePointFromSector z b s upper hc hcb).1 : ℝ) =
        if upper then b / s else -(b / s) := by
  -- The two hemisphere choices only exchange the ordered coordinates.
  have hordered : z.im / s ≤ (z.im + b) / s := by
    exact (div_le_div_iff_of_pos_right hspos).mpr (by linarith)
  cases upper
  · dsimp [squarePointFromSector]
    constructor
    · rw [outerCoordinate, max_eq_left hordered]
      field_simp
      linarith
    · constructor
      · exact min_eq_right hordered
      · ring
  · dsimp [squarePointFromSector]
    constructor
    · rw [outerCoordinate, max_eq_right hordered]
      field_simp
      linarith
    · constructor
      · exact min_eq_left hordered
      · ring

/-- Helper for Example 74.2: the complex sector coordinate of a sector-built square point
is the original coordinate divided by its scale. -/
private lemma sectorCoordinate_squarePointFromSector (z : ℂ) (b s : ℝ) (upper : Bool)
    (hc : z.im / s ∈ unitInterval) (hcb : (z.im + b) / s ∈ unitInterval)
    (hb : 0 ≤ b) (hs : s = z.re + b + z.im) (hspos : 0 < s) :
    sectorCoordinate (squarePointFromSector z b s upper hc hcb) = z / s := by
  -- The coordinate formulas identify the real and imaginary parts separately.
  have hcoords := squarePointFromSector_coordinates z b s upper hc hcb hb hs hspos
  apply Complex.ext
  · simpa [sectorCoordinate] using hcoords.1
  · simpa [sectorCoordinate] using hcoords.2.1

/-- Helper for Example 74.2: the raw vector of a sector-built square point is the
corresponding fourth-power vector divided by the fourth power of the scale. -/
private lemma rawSphereVector_squarePointFromSector (z : ℂ) (b s : ℝ) (upper : Bool)
    (hc : z.im / s ∈ unitInterval) (hcb : (z.im + b) / s ∈ unitInterval)
    (hb : 0 ≤ b) (hs : s = z.re + b + z.im) (hspos : 0 < s) :
    rawSphereVector (squarePointFromSector z b s upper hc hcb) =
      !₂[(z ^ 4).re / s ^ 4, (z ^ 4).im / s ^ 4,
        if upper then b ^ 4 / s ^ 4 else -(b ^ 4 / s ^ 4)] := by
  -- Consume only the projection interface, then calculate one raw coordinate at a time.
  have hcoords := squarePointFromSector_coordinates z b s upper hc hcb hb hs hspos
  have hsector := sectorCoordinate_squarePointFromSector z b s upper hc hcb hb hs hspos
  ext i
  fin_cases i
  · change (sectorCoordinate (squarePointFromSector z b s upper hc hcb) ^ 4).re =
        (z ^ 4).re / s ^ 4
    rw [hsector, div_pow]
    simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re]
  · change (sectorCoordinate (squarePointFromSector z b s upper hc hcb) ^ 4).im =
        (z ^ 4).im / s ^ 4
    rw [hsector, div_pow]
    simpa only [← Complex.ofReal_pow, Complex.div_ofReal_im]
  · change signedFourth
        (((squarePointFromSector z b s upper hc hcb).2 : ℝ) -
          ((squarePointFromSector z b s upper hc hcb).1 : ℝ)) = _
    rw [hcoords.2.2]
    cases upper
    · change signedFourth (-(b / s)) = -(b ^ 4 / s ^ 4)
      rw [signedFourth]
      rw [abs_of_nonpos (neg_nonpos.mpr (div_nonneg hb hspos.le))]
      ring
    · change signedFourth (b / s) = b ^ 4 / s ^ 4
      rw [signedFourth]
      rw [abs_of_nonneg (div_nonneg hb hspos.le)]
      ring

/-- Helper for Example 74.2: the explicit normalized coordinate map covers the unit
two-sphere. -/
private lemma spherePoint_surjective : Function.Surjective spherePoint := by
  intro q
  -- Choose the planar fourth root in the fundamental quadrant and the nonnegative
  -- fourth root of the absolute height.
  let w : ℂ := ⟨q.1 0, q.1 1⟩
  obtain ⟨z, hzreal, hzimag, hzpow⟩ := exists_firstQuadrant_fourthRoot w
  let b : ℝ := √√|q.1 2|
  let s : ℝ := z.re + b + z.im
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hbpow : b ^ 4 = |q.1 2| := sqrtSqrt_fourthPower _ (abs_nonneg _)
  have hs : s = z.re + b + z.im := rfl
  have hqnorm : ‖q.1‖ = 1 := mem_sphere_zero_iff_norm.mp q.2
  have hqne : q.1 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hqnorm
    norm_num at hqnorm
  have hspos : 0 < s := by
    -- If the scale vanished, every coordinate of the sphere point would vanish.
    by_contra hnot
    have hsle : s ≤ 0 := le_of_not_gt hnot
    have hzreal0 : z.re = 0 := by dsimp [s] at hsle; nlinarith
    have hzimag0 : z.im = 0 := by dsimp [s] at hsle; nlinarith
    have hb0 : b = 0 := by dsimp [s] at hsle; nlinarith
    have hz0 : z = 0 := by
      apply Complex.ext
      · simpa using hzreal0
      · simpa using hzimag0
    have hzpow0 : z ^ 4 = 0 := by rw [hz0]; norm_num
    have hwzero : w = 0 := hzpow.symm.trans hzpow0
    have hq0 : q.1 0 = 0 := by
      simpa [w] using congrArg Complex.re hwzero
    have hq1 : q.1 1 = 0 := by
      simpa [w] using congrArg Complex.im hwzero
    have hq2 : q.1 2 = 0 := by
      apply abs_eq_zero.mp
      rw [← hbpow, hb0]
      norm_num
    apply hqne
    ext i
    fin_cases i
    · exact hq0
    · exact hq1
    · exact hq2
  have hc : z.im / s ∈ unitInterval := by
    apply unitInterval.div_mem hzimag hspos.le
    dsimp [s]
    linarith
  have hcb : (z.im + b) / s ∈ unitInterval := by
    apply unitInterval.div_mem (add_nonneg hzimag hb) hspos.le
    dsimp [s]
    linarith
  have hpowreal : (z ^ 4).re = q.1 0 := by
    simpa [w] using congrArg Complex.re hzpow
  have hpowimag : (z ^ 4).im = q.1 1 := by
    simpa [w] using congrArg Complex.im hzpow
  have hscale : 0 < (s ^ 4)⁻¹ := inv_pos.mpr (pow_pos hspos 4)
  -- Select the hemisphere from the sign of the third sphere coordinate.
  by_cases hupper : 0 ≤ q.1 2
  · let p := squarePointFromSector z b s true hc hcb
    have hbpow' : b ^ 4 = q.1 2 := by simpa [abs_of_nonneg hupper] using hbpow
    have hraw : rawSphereVector p = (s ^ 4)⁻¹ • q.1 := by
      rw [rawSphereVector_squarePointFromSector z b s true hc hcb hb hs hspos]
      ext i
      fin_cases i
      all_goals simp [hpowreal, hpowimag, hbpow', div_eq_inv_mul, mul_comm]
    refine ⟨p, ?_⟩
    -- Positive rescaling disappears under normalization, and a sphere point is already
    -- normalized.
    have hnormalized : NormedSpace.normalize (rawSphereVector p) = q.1 := by
      rw [hraw, NormedSpace.normalize_smul_of_pos hscale,
        NormedSpace.normalize_eq_self_of_norm_eq_one hqnorm]
    exact Subtype.ext hnormalized
  · let p := squarePointFromSector z b s false hc hcb
    have hneg : q.1 2 < 0 := lt_of_not_ge hupper
    have hbpow' : b ^ 4 = -(q.1 2) := by simpa [abs_of_neg hneg] using hbpow
    have hraw : rawSphereVector p = (s ^ 4)⁻¹ • q.1 := by
      rw [rawSphereVector_squarePointFromSector z b s false hc hcb hb hs hspos]
      ext i
      fin_cases i
      all_goals simp [hpowreal, hpowimag, hbpow', div_eq_inv_mul, mul_comm]
    refine ⟨p, ?_⟩
    -- The same positive normalization argument handles the lower hemisphere.
    have hnormalized : NormedSpace.normalize (rawSphereVector p) = q.1 := by
      rw [hraw, NormedSpace.normalize_smul_of_pos hscale,
        NormedSpace.normalize_eq_self_of_norm_eq_one hqnorm]
    exact Subtype.ext hnormalized

/-- Helper for Example 74.2: equal fourth powers in the closed first quadrant differ only
by equality or by exchanging the two coordinate axes. -/
private lemma firstQuadrantFourthPower_eq_iff (z w : ℂ)
    (hzreal : 0 ≤ z.re) (hzimag : 0 ≤ z.im)
    (hwreal : 0 ≤ w.re) (hwimag : 0 ≤ w.im) :
    z ^ 4 = w ^ 4 ↔
      z = w ∨
        (z.re = 0 ∧ w.im = 0 ∧ z.im = w.re) ∨
        (z.im = 0 ∧ w.re = 0 ∧ z.re = w.im) := by
  constructor
  · intro hpow
    -- Factor the difference of fourth powers and analyze the four roots of unity.
    have hfactor : (z - w) * (z + w) * (z - Complex.I * w) *
        (z + Complex.I * w) = 0 := by
      have hsub : z ^ 4 - w ^ 4 = 0 := sub_eq_zero.mpr hpow
      calc
        (z - w) * (z + w) * (z - Complex.I * w) * (z + Complex.I * w) =
            z ^ 4 - w ^ 4 := by
          ring_nf
          norm_num [pow_succ]
          exact (sub_eq_add_neg _ _).symm
        _ = 0 := hsub
    rcases mul_eq_zero.mp hfactor with hleft | hplusI
    · rcases mul_eq_zero.mp hleft with hleft | hminusI
      · rcases mul_eq_zero.mp hleft with hminus | hplus
        · exact Or.inl (sub_eq_zero.mp hminus)
        · have hre := congrArg Complex.re hplus
          have him := congrArg Complex.im hplus
          simp only [Complex.add_re, Complex.add_im, Complex.zero_re,
            Complex.zero_im] at hre him
          have hzreal0 : z.re = 0 := by nlinarith
          have hzimag0 : z.im = 0 := by nlinarith
          have hwreal0 : w.re = 0 := by nlinarith
          have hwimag0 : w.im = 0 := by nlinarith
          apply Or.inl
          apply Complex.ext
          · rw [hzreal0, hwreal0]
          · rw [hzimag0, hwimag0]
      · have heq : z = Complex.I * w := sub_eq_zero.mp hminusI
        have hre := congrArg Complex.re heq
        have him := congrArg Complex.im heq
        simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          zero_mul, one_mul, zero_sub, zero_add] at hre him
        have hzreal0 : z.re = 0 := by nlinarith
        have hwimag0 : w.im = 0 := by nlinarith
        exact Or.inr (Or.inl ⟨hzreal0, hwimag0, him⟩)
    · have heq : z = -(Complex.I * w) := add_eq_zero_iff_eq_neg.mp hplusI
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add,
        neg_neg] at hre him
      have hzimag0 : z.im = 0 := by nlinarith
      have hwreal0 : w.re = 0 := by nlinarith
      exact Or.inr (Or.inr ⟨hzimag0, hwreal0, hre⟩)
  · rintro (rfl | haxes | haxes)
    · rfl
    · rcases haxes with ⟨hzreal0, hwimag0, hcross⟩
      apply Complex.ext
      · simp [hzreal0, hwimag0, hcross, pow_succ]
      · simp [hzreal0, hwimag0, hcross, pow_succ]
    · rcases haxes with ⟨hzimag0, hwreal0, hcross⟩
      apply Complex.ext
      · simp [hzimag0, hwreal0, hcross, pow_succ]
      · simp [hzimag0, hwreal0, hcross, pow_succ]

/-- Helper for Example 74.2: the sector coordinates of every square point are
nonnegative. -/
private lemma sectorCoordinate_nonnegative (p : unitInterval × unitInterval) :
    0 ≤ (sectorCoordinate p).re ∧ 0 ≤ (sectorCoordinate p).im := by
  -- `max` is at most one and `min` is nonnegative on the unit square.
  constructor
  · simp only [sectorCoordinate, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
      outerCoordinate]
    simpa using sub_nonneg.mpr (max_le (unitInterval.le_one p.1) (unitInterval.le_one p.2))
  · simp only [sectorCoordinate, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.ofReal_re, Complex.I_im, mul_zero, mul_one, zero_add,
      innerCoordinate]
    simpa using le_min (unitInterval.nonneg p.1) (unitInterval.nonneg p.2)

/-- Helper for Example 74.2: signed fourth power commutes with multiplication by a
nonnegative scalar, with fourth-power scaling. -/
private lemma signedFourth_mul_nonnegative (k x : ℝ) (hk : 0 ≤ k) :
    signedFourth (k * x) = k ^ 4 * signedFourth x := by
  -- Absolute values are multiplicative, and the scalar absolute value is itself.
  rw [signedFourth, signedFourth, abs_mul, abs_of_nonneg hk]
  ring

/-- Helper for Example 74.2: signed fourth power is injective on the real line. -/
private lemma signedFourth_injective : Function.Injective signedFourth := by
  have hfour : (4 : ℕ) ≠ 0 := by norm_num
  intro x y hxy
  rcases le_total 0 x with hx | hx
  · rcases le_total 0 y with hy | hy
    · have hpow : x ^ 4 = y ^ 4 := by
        simp [signedFourth, abs_of_nonneg hx, abs_of_nonneg hy] at hxy
        ring_nf at hxy ⊢
        exact hxy
      exact (pow_left_inj₀ hx hy hfour).mp hpow
    · have hxpow : x ^ 4 = 0 := by
        have hxnonneg : 0 ≤ x ^ 4 := by positivity
        have hynonneg : 0 ≤ y ^ 4 := by positivity
        simp [signedFourth, abs_of_nonneg hx, abs_of_nonpos hy] at hxy
        ring_nf at hxy
        nlinarith
      have hypow : y ^ 4 = 0 := by
        have hxnonneg : 0 ≤ x ^ 4 := by positivity
        have hynonneg : 0 ≤ y ^ 4 := by positivity
        simp [signedFourth, abs_of_nonneg hx, abs_of_nonpos hy] at hxy
        ring_nf at hxy
        nlinarith
      rw [eq_zero_of_pow_eq_zero hxpow, eq_zero_of_pow_eq_zero hypow]
  · rcases le_total 0 y with hy | hy
    · have hxpow : x ^ 4 = 0 := by
        have hxnonneg : 0 ≤ x ^ 4 := by positivity
        have hynonneg : 0 ≤ y ^ 4 := by positivity
        simp [signedFourth, abs_of_nonpos hx, abs_of_nonneg hy] at hxy
        ring_nf at hxy
        nlinarith
      have hypow : y ^ 4 = 0 := by
        have hxnonneg : 0 ≤ x ^ 4 := by positivity
        have hynonneg : 0 ≤ y ^ 4 := by positivity
        simp [signedFourth, abs_of_nonpos hx, abs_of_nonneg hy] at hxy
        ring_nf at hxy
        nlinarith
      rw [eq_zero_of_pow_eq_zero hxpow, eq_zero_of_pow_eq_zero hypow]
    · have hpow : x ^ 4 = y ^ 4 := by
        simp [signedFourth, abs_of_nonpos hx, abs_of_nonpos hy] at hxy
        ring_nf at hxy ⊢
        linarith
      have hnegpow : (-x) ^ 4 = (-y) ^ 4 := by
        ring_nf
        exact hpow
      have hneg : -x = -y :=
        (pow_left_inj₀ (neg_nonneg.mpr hx) (neg_nonneg.mpr hy) hfour).mp hnegpow
      exact neg_injective hneg

/-- Helper for Example 74.2: equal normalizations of two nonzero vectors make the first a
positive scalar multiple of the second. -/
private lemma eq_positive_smul_of_normalize_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {u v : V} (hu : u ≠ 0) (hv : v ≠ 0)
    (hnormalize : NormedSpace.normalize u = NormedSpace.normalize v) :
    ∃ r : ℝ, 0 < r ∧ u = r • v := by
  -- Rescale the common unit vector by the quotient of the two positive norms.
  have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r : ℝ := ‖u‖ / ‖v‖
  have hr : 0 < r := div_pos hunorm hvnorm
  have huformula : ‖u‖ • NormedSpace.normalize u = u :=
    NormedSpace.norm_smul_normalize u
  have hvnormalize : NormedSpace.normalize v = ‖v‖⁻¹ • v := rfl
  have hscaled : ‖u‖ • NormedSpace.normalize v = r • v := by
    rw [hvnormalize, smul_smul]
    dsimp [r]
    rw [div_eq_mul_inv]
  refine ⟨r, hr, ?_⟩
  exact huformula.symm.trans ((congrArg (‖u‖ • ·) hnormalize).trans hscaled)

/-- Helper for Example 74.2: a point of the square is determined by its inner coordinate
and its signed displacement from the diagonal. -/
private lemma squarePoint_eq_of_inner_difference_eq (p q : unitInterval × unitInterval)
    (hinner : innerCoordinate p = innerCoordinate q)
    (hdiff : (p.2 : ℝ) - (p.1 : ℝ) = (q.2 : ℝ) - (q.1 : ℝ)) :
    p = q := by
  -- On each side of the diagonal, `min` selects the endpoint from which the displacement
  -- reconstructs both coordinates.
  rcases le_total (p.1 : ℝ) (p.2 : ℝ) with hp | hp
  · rcases le_total (q.1 : ℝ) (q.2 : ℝ) with hq | hq
    · simp only [innerCoordinate, min_eq_left hp, min_eq_left hq] at hinner
      apply Prod.ext
      · exact Subtype.ext hinner
      · apply Subtype.ext
        linarith
    · simp only [innerCoordinate, min_eq_left hp, min_eq_right hq] at hinner
      have hpEq : (p.1 : ℝ) = (p.2 : ℝ) := by nlinarith
      have hqEq : (q.1 : ℝ) = (q.2 : ℝ) := by nlinarith
      apply Prod.ext
      · apply Subtype.ext
        linarith
      · apply Subtype.ext
        linarith
  · rcases le_total (q.1 : ℝ) (q.2 : ℝ) with hq | hq
    · simp only [innerCoordinate, min_eq_right hp, min_eq_left hq] at hinner
      have hpEq : (p.1 : ℝ) = (p.2 : ℝ) := by nlinarith
      have hqEq : (q.1 : ℝ) = (q.2 : ℝ) := by nlinarith
      apply Prod.ext
      · apply Subtype.ext
        linarith
      · apply Subtype.ext
        linarith
    · simp only [innerCoordinate, min_eq_right hp, min_eq_right hq] at hinner
      apply Prod.ext
      · apply Subtype.ext
        linarith
      · exact Subtype.ext hinner

/-- Helper for Example 74.2: two square points have the same sphere image exactly when
they are equal or form one of the two prescribed boundary pairs. -/
private lemma spherePoint_eq_iff_squareBoundaryRel (p q : unitInterval × unitInterval) :
    spherePoint p = spherePoint q ↔ squareBoundaryRel p q := by
  constructor
  · intro hpq
    -- Equal normalized vectors are positively proportional before normalization.
    have hnormalize : NormedSpace.normalize (rawSphereVector p) =
        NormedSpace.normalize (rawSphereVector q) := congrArg Subtype.val hpq
    obtain ⟨r, hr, hraw⟩ := eq_positive_smul_of_normalize_eq
      (rawSphereVector_ne_zero p) (rawSphereVector_ne_zero q) hnormalize
    let k : ℝ := √√r
    have hk : 0 ≤ k := Real.sqrt_nonneg _
    have hkpow : k ^ 4 = r := sqrtSqrt_fourthPower r hr.le
    have hkne : k ≠ 0 := by
      intro hkzero
      rw [hkzero] at hkpow
      norm_num at hkpow
      linarith
    have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hkne)
    have hrawreal := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) hraw
    have hrawimag := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) hraw
    have hrawheight := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) hraw
    simp only [rawSphereVector, Matrix.cons_val_zero] at hrawreal
    simp only [rawSphereVector, Matrix.cons_val_one, Matrix.cons_val_zero] at hrawimag
    simp only [rawSphereVector, Matrix.cons_val_two] at hrawheight
    have hcomplexScalar : sectorCoordinate p ^ 4 =
        (r : ℂ) * sectorCoordinate q ^ 4 := by
      apply Complex.ext
      · simpa using hrawreal
      · simpa using hrawimag
    have hkpowComplex : (k : ℂ) ^ 4 = (r : ℂ) := by
      simpa using congrArg Complex.ofReal hkpow
    have hscaledPower : ((k : ℂ) * sectorCoordinate q) ^ 4 =
        (r : ℂ) * sectorCoordinate q ^ 4 := by
      rw [mul_pow, hkpowComplex]
    have hcomplex : sectorCoordinate p ^ 4 =
        ((k : ℂ) * sectorCoordinate q) ^ 4 :=
      hcomplexScalar.trans hscaledPower.symm
    have hdiffscale : (p.2 : ℝ) - (p.1 : ℝ) =
        k * ((q.2 : ℝ) - (q.1 : ℝ)) := by
      apply signedFourth_injective
      rw [signedFourth_mul_nonnegative k _ hk, hkpow]
      exact hrawheight
    have hdiagscale : diagonalCoordinate p = k * diagonalCoordinate q := by
      rw [diagonalCoordinate, diagonalCoordinate, hdiffscale, abs_mul, abs_of_nonneg hk]
    have hpsector := sectorCoordinate_nonnegative p
    have hqsector := sectorCoordinate_nonnegative q
    have hscaledreal : 0 ≤ ((k : ℂ) * sectorCoordinate q).re := by
      simpa using mul_nonneg hk hqsector.1
    have hscaledimag : 0 ≤ ((k : ℂ) * sectorCoordinate q).im := by
      simpa using mul_nonneg hk hqsector.2
    rcases (firstQuadrantFourthPower_eq_iff (sectorCoordinate p)
      ((k : ℂ) * sectorCoordinate q) hpsector.1 hpsector.2
      hscaledreal hscaledimag).mp hcomplex with hequal | haxis | haxis
    · -- Away from the coordinate axes, equality of the quadrant roots forces equality
      -- of all barycentric coordinates.
      have houter : outerCoordinate p = k * outerCoordinate q := by
        simpa [sectorCoordinate] using congrArg Complex.re hequal
      have hinner : innerCoordinate p = k * innerCoordinate q := by
        simpa [sectorCoordinate] using congrArg Complex.im hequal
      have hpsum := barycentricCoordinate_sum p
      have hqsum := barycentricCoordinate_sum q
      rw [houter, hdiagscale, hinner] at hpsum
      have hkone : k = 1 := by nlinarith
      have hinnerEq : innerCoordinate p = innerCoordinate q := by
        simpa [hkone] using hinner
      have hdiffEq : (p.2 : ℝ) - (p.1 : ℝ) =
          (q.2 : ℝ) - (q.1 : ℝ) := by simpa [hkone] using hdiffscale
      exact Or.inl (squarePoint_eq_of_inner_difference_eq p q hinnerEq hdiffEq)
    · -- The first axis exchange puts `p` on the top/right pair and `q` on the
      -- bottom/left pair.
      rcases haxis with ⟨hpouter0, hqinnerScaled0, hcross⟩
      have hpouter : outerCoordinate p = 0 := by
        simpa [sectorCoordinate] using hpouter0
      have hqinner : innerCoordinate q = 0 := by
        have hmul : k * innerCoordinate q = 0 := by
          simpa [sectorCoordinate] using hqinnerScaled0
        exact (mul_eq_zero.mp hmul).resolve_left hkne
      have hinnerOuter : innerCoordinate p = k * outerCoordinate q := by
        simpa [sectorCoordinate] using hcross
      have hpsum := barycentricCoordinate_sum p
      have hqsum := barycentricCoordinate_sum q
      rw [hpouter, zero_add, hdiagscale, hinnerOuter] at hpsum
      rw [hqinner, add_zero] at hqsum
      have hkone : k = 1 := by nlinarith
      have hdiffEq : (p.2 : ℝ) - (p.1 : ℝ) =
          (q.2 : ℝ) - (q.1 : ℝ) := by simpa [hkone] using hdiffscale
      have hpmax : max (p.1 : ℝ) (p.2 : ℝ) = 1 := by
        unfold outerCoordinate at hpouter
        linarith
      have hqmin : min (q.1 : ℝ) (q.2 : ℝ) = 0 := hqinner
      by_cases hnegative : (p.2 : ℝ) - (p.1 : ℝ) < 0
      · have hporder : (p.2 : ℝ) ≤ (p.1 : ℝ) := by linarith
        have hqorder : (q.2 : ℝ) ≤ (q.1 : ℝ) := by linarith
        have hpone : (p.1 : ℝ) = 1 := by rwa [max_eq_left hporder] at hpmax
        have hqzero : (q.2 : ℝ) = 0 := by rwa [min_eq_right hqorder] at hqmin
        have hpsecond : (p.2 : ℝ) = 1 - (q.1 : ℝ) := by linarith
        have hpform : p = (1, unitInterval.symm q.1) := by
          apply Prod.ext
          · exact Subtype.ext hpone
          · exact Subtype.ext hpsecond
        have hqform : q = (q.1, 0) := by
          apply Prod.ext
          · rfl
          · exact Subtype.ext hqzero
        exact Or.inr (Or.inr (Or.inl ⟨q.1, hpform, hqform⟩))
      · have hporder : (p.1 : ℝ) ≤ (p.2 : ℝ) := by linarith
        have hqorder : (q.1 : ℝ) ≤ (q.2 : ℝ) := by linarith
        have hpone : (p.2 : ℝ) = 1 := by rwa [max_eq_right hporder] at hpmax
        have hqzero : (q.1 : ℝ) = 0 := by rwa [min_eq_left hqorder] at hqmin
        have hpfirst : (p.1 : ℝ) = 1 - (q.2 : ℝ) := by linarith
        have hpform : p = (unitInterval.symm q.2, 1) := by
          apply Prod.ext
          · exact Subtype.ext hpfirst
          · exact Subtype.ext hpone
        have hqform : q = (0, q.2) := by
          apply Prod.ext
          · exact Subtype.ext hqzero
          · rfl
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q.2, hpform, hqform⟩)))
    · -- The other axis exchange reverses the roles of the two boundary pairs.
      rcases haxis with ⟨hpinner0, hqouterScaled0, hcross⟩
      have hpinner : innerCoordinate p = 0 := by
        simpa [sectorCoordinate] using hpinner0
      have hqouter : outerCoordinate q = 0 := by
        have hmul : k * outerCoordinate q = 0 := by
          simpa [sectorCoordinate] using hqouterScaled0
        exact (mul_eq_zero.mp hmul).resolve_left hkne
      have houterInner : outerCoordinate p = k * innerCoordinate q := by
        simpa [sectorCoordinate] using hcross
      have hpsum := barycentricCoordinate_sum p
      have hqsum := barycentricCoordinate_sum q
      rw [hpinner, add_zero, houterInner, hdiagscale] at hpsum
      rw [hqouter, zero_add] at hqsum
      have hkone : k = 1 := by nlinarith
      have hdiffEq : (p.2 : ℝ) - (p.1 : ℝ) =
          (q.2 : ℝ) - (q.1 : ℝ) := by simpa [hkone] using hdiffscale
      have hpmin : min (p.1 : ℝ) (p.2 : ℝ) = 0 := hpinner
      have hqmax : max (q.1 : ℝ) (q.2 : ℝ) = 1 := by
        unfold outerCoordinate at hqouter
        linarith
      by_cases hnegative : (p.2 : ℝ) - (p.1 : ℝ) < 0
      · have hporder : (p.2 : ℝ) ≤ (p.1 : ℝ) := by linarith
        have hqorder : (q.2 : ℝ) ≤ (q.1 : ℝ) := by linarith
        have hpzero : (p.2 : ℝ) = 0 := by rwa [min_eq_right hporder] at hpmin
        have hqone : (q.1 : ℝ) = 1 := by rwa [max_eq_left hqorder] at hqmax
        have hqsecond : (q.2 : ℝ) = 1 - (p.1 : ℝ) := by linarith
        have hpform : p = (p.1, 0) := by
          apply Prod.ext
          · rfl
          · exact Subtype.ext hpzero
        have hqform : q = (1, unitInterval.symm p.1) := by
          apply Prod.ext
          · exact Subtype.ext hqone
          · exact Subtype.ext hqsecond
        exact Or.inr (Or.inl ⟨p.1, hpform, hqform⟩)
      · have hporder : (p.1 : ℝ) ≤ (p.2 : ℝ) := by linarith
        have hqorder : (q.1 : ℝ) ≤ (q.2 : ℝ) := by linarith
        have hpzero : (p.1 : ℝ) = 0 := by rwa [min_eq_left hporder] at hpmin
        have hqone : (q.2 : ℝ) = 1 := by rwa [max_eq_right hqorder] at hqmax
        have hqfirst : (q.1 : ℝ) = 1 - (p.2 : ℝ) := by linarith
        have hpform : p = (0, p.2) := by
          apply Prod.ext
          · exact Subtype.ext hpzero
          · rfl
        have hqform : q = (unitInterval.symm p.2, 1) := by
          apply Prod.ext
          · exact Subtype.ext hqfirst
          · exact Subtype.ext hqone
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p.2, hpform, hqform⟩)))
  · exact spherePoint_eq_of_squareBoundaryRel

/-- Helper for Example 74.2: every direct labelled-edge pairing projects to one of the
explicit square-boundary pairs. -/
private lemma squareBoundaryRel_of_edgeRelated {x y : regions.Source}
    (hxy : regions.EdgeRelated x y) : squareBoundaryRel x.2 y.2 := by
  -- Normalize the unique occurrence, then enumerate the sixteen ordered edge pairs.
  unfold LabellingScheme.PolygonalRegions.EdgeRelated at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  have hregion₁ := occurrence_eq_region region₁
  have hregion₂ := occurrence_eq_region region₂
  subst region₁
  subst region₂
  fin_cases edge₁
  all_goals fin_cases edge₂
  all_goals
    simp [regions, region_word, boundaryWord, boundaryLetters, UnitSquare.edge,
      squareBoundaryRel] at hlabel ⊢

/-- Helper for Example 74.2: the bottom and right edges with opposite orientations are a
direct labelled-edge pair. -/
private lemma bottomRightEdgesRelated (t : unitInterval) :
    regions.EdgeRelated (⟨region, (t, 0)⟩ : regions.Source)
      ⟨region, (1, unitInterval.symm t)⟩ := by
  -- Select the two occurrences of the first label; their unequal signs reverse `t`.
  refine ⟨region, region,
    Fin.cast (occurrence_length region).symm (0 : Fin 4),
    Fin.cast (occurrence_length region).symm (1 : Fin 4), t, ?_⟩
  simp [regions, region_word, boundaryWord, boundaryLetters, UnitSquare.edge]

/-- Helper for Example 74.2: the top and left edges with opposite orientations are a direct
labelled-edge pair. -/
private lemma topLeftEdgesRelated (t : unitInterval) :
    regions.EdgeRelated (⟨region, (unitInterval.symm t, 1)⟩ : regions.Source)
      ⟨region, (0, t)⟩ := by
  -- Select the two occurrences of the second label; the edge parametrization cancels the
  -- sign-induced reversal on the left edge.
  refine ⟨region, region,
    Fin.cast (occurrence_length region).symm (2 : Fin 4),
    Fin.cast (occurrence_length region).symm (3 : Fin 4), t, ?_⟩
  simp [regions, region_word, boundaryWord, boundaryLetters, UnitSquare.edge]

/-- Helper for Example 74.2: every explicit square-boundary pair belongs to the generated
labelled-edge relation. -/
private lemma eqvGen_of_squareBoundaryRel {p q : unitInterval × unitInterval}
    (hpq : squareBoundaryRel p q) :
    Relation.EqvGen regions.EdgeRelated
      (⟨region, p⟩ : regions.Source) ⟨region, q⟩ := by
  -- Equality is reflexivity; the other four cases use the two edge generators and their
  -- reverses.
  rcases hpq with rfl | hpq | hpq | hpq | hpq
  · exact Relation.EqvGen.refl _
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Relation.EqvGen.rel _ _ (bottomRightEdgesRelated t)
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (bottomRightEdgesRelated t))
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Relation.EqvGen.rel _ _ (topLeftEdgesRelated t)
  · rcases hpq with ⟨t, rfl, rfl⟩
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (topLeftEdgesRelated t))

/-- Helper for Example 74.2: every source point can be written in the unique square
occurrence. -/
private lemma source_eq_region_mk (x : regions.Source) : x = ⟨region, x.2⟩ := by
  -- Replace the sigma index by the unique occurrence.
  rcases x with ⟨r, p⟩
  rw [occurrence_eq_region r]

/-- Helper for Example 74.2: the generated presentation relation is exactly the kernel of
the explicit sphere map after source projection. -/
private lemma identified_projection_iff (x y : regions.Source) :
    regions.Identified.r x y ↔ spherePoint x.2 = spherePoint y.2 := by
  constructor
  · intro hxy
    -- Extend the generator calculation through the equivalence closure.
    induction hxy with
    | rel _ _ h =>
        exact spherePoint_eq_of_squareBoundaryRel (squareBoundaryRel_of_edgeRelated h)
    | refl _ => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ hab hbc => exact hab.trans hbc
  · intro hxy
    -- The fiber classification supplies a generator path between the canonical copies;
    -- uniqueness of the occurrence transports it back to the original source points.
    have hpq : squareBoundaryRel x.2 y.2 :=
      (spherePoint_eq_iff_squareBoundaryRel x.2 y.2).mp hxy
    have hcanonical := eqvGen_of_squareBoundaryRel hpq
    rw [source_eq_region_mk x, source_eq_region_mk y]
    exact hcanonical

/-- Helper for Example 74.2: the explicit square-to-sphere map bundled with its continuity
proof. -/
private noncomputable def sphereMap :
    C(unitInterval × unitInterval, Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨spherePoint, continuous_spherePoint⟩

/-- Helper for Example 74.2: the bundled square-to-sphere map is a quotient map. -/
private lemma sphereMap_isQuotientMap : Topology.IsQuotientMap sphereMap := by
  -- A continuous surjection from the compact square to the Hausdorff sphere is quotient.
  exact Topology.IsQuotientMap.of_surjective_continuous
    spherePoint_surjective continuous_spherePoint

/-- Example 74.2: Pasting the oriented edges of the square according to the scheme
`a a⁻¹ b b⁻¹` gives a space homeomorphic to `S²`. -/
theorem homeomorphicTwoSphere :
    Nonempty (Realization ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  -- Replace the singleton disjoint union by its square, identify the presentation relation
  -- with the analytic kernel, and then use the quotient map's canonical homeomorphism.
  let projectionHomeomorph : regions.Source ≃ₜ unitInterval × unitInterval :=
    sourceProjectionIsHomeomorph.homeomorph
  have hkernel : ∀ x y : regions.Source,
      regions.Identified.r x y ↔
        Setoid.ker sphereMap (projectionHomeomorph x) (projectionHomeomorph y) := by
    intro x y
    exact identified_projection_iff x y
  exact ⟨(Homeomorph.Quotient.congr projectionHomeomorph hkernel).trans
    sphereMap_isQuotientMap.homeomorph⟩

end SphereSquare
