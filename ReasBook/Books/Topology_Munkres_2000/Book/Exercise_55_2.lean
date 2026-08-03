module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homotopy.Contractible
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup

public section

noncomputable section

/-- Helper for Exercise 55.2: nullhomotopy is preserved when the map is replaced by a
homotopic map. -/
theorem ContinuousMap.Nullhomotopic.of_homotopic {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (hf : f.Nullhomotopic) (hfg : f.Homotopic g) : g.Nullhomotopic := by
  -- Reverse the given homotopy and concatenate it with the nullhomotopy of `f`.
  obtain ⟨y, hfy⟩ := hf
  exact ⟨y, hfg.symm.trans hfy⟩

/-- Helper for Exercise 55.2: the antipodal self-map of the circle. -/
def circleAntipodal : C(Circle, Circle) :=
  ⟨fun x ↦ -x, continuous_neg⟩

/-- Helper for Exercise 55.2: the segment joining distinct unit vectors `y` and `-x`
does not pass through the origin. -/
theorem circleUnitSegmentToNeg_ne_zero (x y : Circle) (hyx : y ≠ x)
    (t : unitInterval) :
    (1 - (t : ℝ)) • (y : ℂ) - (t : ℝ) • (x : ℂ) ≠ 0 := by
  -- Equality with zero would force the two scalar coefficients to have equal norms.
  intro hzero
  have hscaled : (1 - (t : ℝ)) • (y : ℂ) = (t : ℝ) • (x : ℂ) :=
    sub_eq_zero.mp hzero
  have hnorm := congrArg norm hscaled
  have ht_nonneg : 0 ≤ (t : ℝ) := t.property.1
  have ht_le_one : (t : ℝ) ≤ 1 := t.property.2
  have hcoeff : 1 - (t : ℝ) = (t : ℝ) := by
    rw [norm_smul, norm_smul, Circle.norm_coe, Circle.norm_coe, mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht_nonneg,
      abs_of_nonneg (sub_nonneg.mpr ht_le_one)] at hnorm
    exact hnorm
  have ht_half : (t : ℝ) = 1 / 2 := by
    linarith
  -- At the midpoint, cancellation of the nonzero scalar gives `y = x`.
  apply hyx
  apply Circle.ext
  have hscaled_half : (1 / 2 : ℝ) • (y : ℂ) = (1 / 2 : ℝ) • (x : ℂ) := by
    rw [ht_half] at hscaled
    norm_num at hscaled ⊢
    exact hscaled
  have hrescaled := congrArg (fun z : ℂ ↦ (2 : ℝ) • z) hscaled_half
  simpa [smul_smul] using hrescaled

/-- Helper for Exercise 55.2: normalization of the fixed-point-free segment has unit norm. -/
theorem circleFixedPointHomotopyValue_mem (h : C(Circle, Circle))
    (hfree : ∀ x, h x ≠ x) (t : unitInterval) (x : Circle) :
    NormedSpace.normalize
      ((1 - (t : ℝ)) • (h x : ℂ) - (t : ℝ) • (x : ℂ)) ∈
      Metric.sphere (0 : ℂ) 1 := by
  -- The segment is nonzero, so its normalization has norm one.
  rw [mem_sphere_zero_iff_norm]
  exact NormedSpace.norm_normalize (circleUnitSegmentToNeg_ne_zero x (h x) (hfree x) t)

/-- Helper for Exercise 55.2: the normalized segment from `h x` to `-x`, regarded as a
point of the circle. -/
def circleFixedPointHomotopyValue (h : C(Circle, Circle))
    (hfree : ∀ x, h x ≠ x) (t : unitInterval) (x : Circle) : Circle :=
  ⟨NormedSpace.normalize
      ((1 - (t : ℝ)) • (h x : ℂ) - (t : ℝ) • (x : ℂ)),
    circleFixedPointHomotopyValue_mem h hfree t x⟩

/-- Helper for Exercise 55.2: the normalized fixed-point-free segment varies continuously. -/
theorem continuous_circleFixedPointHomotopyValue (h : C(Circle, Circle))
    (hfree : ∀ x, h x ≠ x) :
    Continuous (fun p : unitInterval × Circle ↦
      circleFixedPointHomotopyValue h hfree p.1 p.2) := by
  -- Work in the ambient complex plane, where normalization is inverse norm times the vector.
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  unfold NormedSpace.normalize
  have hsegment : ContinuousAt
      (fun q : unitInterval × Circle ↦
        (1 - (q.1 : ℝ)) • (h q.2 : ℂ) - (q.1 : ℝ) • (q.2 : ℂ)) p := by
    fun_prop
  have hnorm_ne : ‖(1 - (p.1 : ℝ)) • (h p.2 : ℂ) - (p.1 : ℝ) • (p.2 : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (circleUnitSegmentToNeg_ne_zero p.2 (h p.2) (hfree p.2) p.1)
  exact (hsegment.norm.inv₀ hnorm_ne).smul hsegment

/-- Helper for Exercise 55.2: the normalized segment starts at `h`. -/
theorem circleFixedPointHomotopyValue_zero (h : C(Circle, Circle))
    (hfree : ∀ x, h x ≠ x) (x : Circle) :
    circleFixedPointHomotopyValue h hfree 0 x = h x := by
  -- At time zero, normalization fixes the unit vector `h x`.
  apply Circle.ext
  simp [circleFixedPointHomotopyValue, NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Exercise 55.2: the normalized segment ends at the antipode of `x`. -/
theorem circleFixedPointHomotopyValue_one (h : C(Circle, Circle))
    (hfree : ∀ x, h x ≠ x) (x : Circle) :
    circleFixedPointHomotopyValue h hfree 1 x = circleAntipodal x := by
  -- At time one, normalization fixes the unit vector `-x`.
  apply Circle.ext
  simp [circleFixedPointHomotopyValue, circleAntipodal,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Exercise 55.2: a fixed-point-free circle map is homotopic to the
antipodal map. -/
theorem circleMap_homotopic_antipodal_of_fixedPoint_free (h : C(Circle, Circle))
    (hfree : ∀ x, h x ≠ x) : h.Homotopic circleAntipodal := by
  -- Assemble the homotopy only from the normalized-segment interface lemmas.
  exact ⟨{
    toFun := fun p ↦ circleFixedPointHomotopyValue h hfree p.1 p.2
    continuous_toFun := continuous_circleFixedPointHomotopyValue h hfree
    map_zero_left := circleFixedPointHomotopyValue_zero h hfree
    map_one_left := circleFixedPointHomotopyValue_one h hfree
  }⟩

/-- Helper for Exercise 55.2: a circle map that never hits an antipode is homotopic to
the identity. -/
theorem circleMap_homotopic_id_of_avoidsAntipodes (h : C(Circle, Circle))
    (havoid : ∀ x, h x ≠ -x) : h.Homotopic (ContinuousMap.id Circle) := by
  -- Negating `h` converts antipode avoidance into fixed-point avoidance.
  let negH : C(Circle, Circle) := circleAntipodal.comp h
  have negH_free : ∀ x, negH x ≠ x := by
    intro x hneg
    apply havoid x
    apply Circle.ext
    have hcoe := congrArg Subtype.val hneg
    simpa [negH, circleAntipodal] using congrArg Neg.neg hcoe
  have hneg := circleMap_homotopic_antipodal_of_fixedPoint_free negH negH_free
  -- Postcomposition by the antipodal involution turns the endpoints into `h` and `id`.
  have hcomposed :=
    ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl circleAntipodal) hneg
  have hleft : circleAntipodal.comp negH = h := by
    apply ContinuousMap.ext
    intro x
    simp [negH, circleAntipodal]
  have hright : circleAntipodal.comp circleAntipodal = ContinuousMap.id Circle := by
    apply ContinuousMap.ext
    intro x
    simp [circleAntipodal]
  rwa [hleft, hright] at hcomposed

/-- Helper for Exercise 55.2: the identity map of the circle is not nullhomotopic. -/
theorem circle_id_not_nullhomotopic :
    ¬ (ContinuousMap.id Circle).Nullhomotopic := by
  -- A nullhomotopic identity would make the circle contractible and hence simply connected.
  intro hid
  letI : ContractibleSpace Circle := (contractible_iff_id_nullhomotopic Circle).mpr hid
  have hsub : Subsingleton (FundamentalGroup Circle 1) := inferInstance
  have hsub_int : Subsingleton (Multiplicative ℤ) :=
    Circle.fundamentalGroupEquivInt.toEquiv.subsingleton_congr.mp hsub
  -- The multiplicative copy of `ℤ` is nontrivial, contradicting subsingletonness.
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub_int

/-- Helper for Exercise 55.2: a nullhomotopic continuous self-map of `Circle` has a fixed point. -/
theorem nullhomotopicCircleMap_exists_fixedPoint
    (h : C(Circle, Circle)) (h_null : h.Nullhomotopic) :
    ∃ x, Function.IsFixedPt h x := by
  -- If there were no fixed point, `h` would be homotopic to the antipodal map.
  by_contra hnone
  have hfree : ∀ x, h x ≠ x := by
    simpa only [not_exists, Function.IsFixedPt] using hnone
  have hantipodal_null :=
    h_null.of_homotopic (circleMap_homotopic_antipodal_of_fixedPoint_free h hfree)
  -- Composing with the antipodal involution would then nullhomotope the identity.
  have hid_null := hantipodal_null.comp_right circleAntipodal
  apply circle_id_not_nullhomotopic
  have hcomp : circleAntipodal.comp circleAntipodal = ContinuousMap.id Circle := by
    apply ContinuousMap.ext
    intro x
    simp [circleAntipodal]
  rwa [hcomp] at hid_null

/-- Helper for Exercise 55.2: a nullhomotopic continuous self-map of `Circle` maps some point
to its antipode. -/
theorem nullhomotopicCircleMap_exists_mapsToAntipode
    (h : C(Circle, Circle)) (h_null : h.Nullhomotopic) :
    ∃ x, h x = -x := by
  -- Avoiding every antipode would make `h` homotopic to the identity.
  by_contra hnone
  have havoid : ∀ x, h x ≠ -x := by
    simpa only [not_exists] using hnone
  have hid_null := h_null.of_homotopic (circleMap_homotopic_id_of_avoidsAntipodes h havoid)
  -- This contradicts the non-nullhomotopy of the circle identity.
  exact circle_id_not_nullhomotopic hid_null

/-- Exercise 55.2: A nullhomotopic continuous self-map of `Circle` has a fixed point
and maps some point to its antipode. -/
theorem nullhomotopicCircleMap_exists_fixedPoint_and_mapsToAntipode
    (h : C(Circle, Circle)) (h_null : h.Nullhomotopic) :
    (∃ x, Function.IsFixedPt h x) ∧ ∃ x, h x = -x :=
  ⟨nullhomotopicCircleMap_exists_fixedPoint h h_null,
    nullhomotopicCircleMap_exists_mapsToAntipode h h_null⟩
