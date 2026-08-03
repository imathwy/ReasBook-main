module

public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal

import Topology_Munkres_2000.Book.Corollary_58_6
import Topology_Munkres_2000.Book.Exercise_57_3
import Topology_Munkres_2000.Book.Exercise_57_4
import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
import Mathlib.Topology.ContinuousMap.Algebra

public section

noncomputable section

/-- Helper for Exercise 57.1: complex coordinates preserve the unit-sphere predicate. -/
private lemma euclideanPlaneComplex_mem_unitSphere (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both sphere predicates reduce to the norm-one equation preserved by the isometry.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Exercise 57.1: complex coordinates identify `StandardSphere 1` with `Circle`. -/
private noncomputable def standardSphereOneHomeomorphCircle : StandardSphere 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneComplex_mem_unitSphere

/-- Helper for Exercise 57.1: the sphere-circle coordinate map intertwines antipodes. -/
private lemma standardSphereOneHomeomorphCircle_neg (x : StandardSphere 1) :
    standardSphereOneHomeomorphCircle (-x) = -standardSphereOneHomeomorphCircle x := by
  -- Equality in the circle follows from linearity of the ambient complex coordinate.
  apply Circle.ext
  exact map_neg Complex.orthonormalBasisOneI.repr.symm x.1

/-- Helper for Exercise 57.1: left translation normalizes a circle map at `1`. -/
private def normalizeCircleMapAtOne (g : C(Circle, Circle)) : C(Circle, Circle) :=
  ContinuousMap.const Circle (g 1)⁻¹ * g

/-- Helper for Exercise 57.1: a normalized circle map fixes `1`. -/
private lemma normalizeCircleMapAtOne_one (g : C(Circle, Circle)) :
    normalizeCircleMapAtOne g 1 = 1 := by
  -- The normalizing factor cancels the value of the map at the basepoint.
  exact inv_mul_cancel (g 1)

/-- Helper for Exercise 57.1: normalization preserves antipode compatibility. -/
private lemma normalizeCircleMapAtOne_odd (g : C(Circle, Circle))
    (hodd : Function.Odd g) : Function.Odd (normalizeCircleMapAtOne g) := by
  -- Pull the sign through the fixed left-translation factor.
  intro z
  apply Circle.ext
  simp only [normalizeCircleMapAtOne, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  rw [hodd z]
  exact mul_neg _ _

/-- Helper for Exercise 57.1: normalization preserves nullhomotopy. -/
private lemma normalizeCircleMapAtOne_nullhomotopic (g : C(Circle, Circle))
    (hnull : g.Nullhomotopic) : (normalizeCircleMapAtOne g).Nullhomotopic := by
  -- Realize normalization as postcomposition by a fixed circle translation.
  let translation : C(Circle, Circle) :=
    ContinuousMap.const Circle (g 1)⁻¹ * ContinuousMap.id Circle
  have hcomp : translation.comp g = normalizeCircleMapAtOne g := by
    ext z
    rfl
  rw [← hcomp]
  exact hnull.comp_right translation

/-- Helper for Exercise 57.1: a chosen integer-coordinate generator generates
the circle fundamental group. -/
private lemma circleFundamentalGenerator_zpowers_eq_top :
    Subgroup.zpowers
        ((Circle.fundamentalGroupEquivInt).symm (Multiplicative.ofAdd 1)) = ⊤ := by
  -- Integer coordinates express every loop as a power of the chosen generator.
  rw [Subgroup.eq_top_iff']
  intro x
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(Circle.fundamentalGroupEquivInt x).toAdd, ?_⟩
  apply Circle.fundamentalGroupEquivInt.injective
  rw [map_zpow, MulEquiv.apply_symm_apply, ← ofAdd_zsmul, zsmul_eq_mul,
    Int.cast_id, mul_one, ofAdd_toAdd]

/-- Helper for Exercise 57.1: casting the constant loop along equal endpoints
again gives the constant loop. -/
private lemma quotientCast_refl_eq_refl {X : Type*} [TopologicalSpace X]
    {x y : X} (h : y = x) :
    (Path.Homotopic.Quotient.refl x).cast h h =
      Path.Homotopic.Quotient.refl y := by
  -- Endpoint substitution reduces the cast to a reflexive cast.
  subst x
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- Helper for Exercise 57.1: a nullhomotopic based circle map induces the
trivial endomorphism of the fundamental group. -/
private lemma circleMap_induced_eq_one_of_nullhomotopic (g : C(Circle, Circle))
    (hg1 : g 1 = 1) (hnull : g.Nullhomotopic) :
    FundamentalGroup.mapOfEq g hg1 = 1 := by
  -- The unbased induced map is trivial by homotopy invariance; endpoint casting
  -- then preserves the constant loop.
  have hmap := fundamentalGroupMap_eq_one_of_nullhomotopic g 1 hnull
  ext loop
  have hvalue := congrArg
    (fun f : π₁(Circle, 1) →* π₁(Circle, g 1) ↦ f (MulOpposite.op loop)) hmap
  have hraw : FundamentalGroup.map g 1 loop = 1 := by
    simpa using congrArg MulOpposite.unop hvalue
  rw [FundamentalGroup.mapOfEq_apply]
  have hmapped : Path.Homotopic.Quotient.map loop g =
      Path.Homotopic.Quotient.refl (g 1) := by
    rw [FundamentalGroup.map_apply, FundamentalGroup.one_def] at hraw
    exact hraw
  rw [hmapped, quotientCast_refl_eq_refl]
  exact FundamentalGroup.one_def.symm

/-- Helper for Exercise 57.1: an odd based circle map induces a nontrivial
endomorphism of the fundamental group. -/
private lemma oddBasedCircleMap_induced_ne_one (g : C(Circle, Circle))
    (hodd : Function.Odd g) (hg1 : g 1 = 1) :
    FundamentalGroup.mapOfEq g hg1 ≠ 1 := by
  -- The odd-power theorem sends a generator to a nonzero odd power.
  let generator : FundamentalGroup Circle 1 :=
    (Circle.fundamentalGroupEquivInt).symm (Multiplicative.ofAdd 1)
  obtain ⟨n, hnodd, hgenerator⟩ := oddPowerOfFundamentalGroupGenerator g hodd hg1
    generator circleFundamentalGenerator_zpowers_eq_top
  have hnzero : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hnodd
  have hpower : generator ^ n ≠ 1 := by
    intro htrivial
    apply hnzero
    have hcoordinates := congrArg
      (fun x : FundamentalGroup Circle 1 ↦ (Circle.fundamentalGroupEquivInt x).toAdd)
      htrivial
    simpa only [generator, map_zpow, MulEquiv.apply_symm_apply,
      toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, Int.cast_id, one_mul,
      map_one, toAdd_one, mul_one] using hcoordinates
  intro htrivial
  apply hpower
  calc
    generator ^ n = FundamentalGroup.mapOfEq g hg1 generator := hgenerator.symm
    _ = 1 := by
      have heval := DFunLike.congr_fun htrivial generator
      simpa only [MonoidHom.one_apply] using heval

/-- Helper for Exercise 57.1: every odd continuous self-map of the complex circle
is not nullhomotopic. -/
private lemma oddComplexCircleMap_not_nullhomotopic (g : C(Circle, Circle))
    (hodd : Function.Odd g) : ¬ g.Nullhomotopic := by
  -- Normalize at the basepoint and compare the induced fundamental-group map.
  intro hnull
  let normalized := normalizeCircleMapAtOne g
  have hnormalizedOdd : Function.Odd normalized := normalizeCircleMapAtOne_odd g hodd
  have hnormalizedOne : normalized 1 = 1 := normalizeCircleMapAtOne_one g
  have hnormalizedNull : normalized.Nullhomotopic :=
    normalizeCircleMapAtOne_nullhomotopic g hnull
  exact oddBasedCircleMap_induced_ne_one normalized hnormalizedOdd hnormalizedOne
    (circleMap_induced_eq_one_of_nullhomotopic normalized hnormalizedOne hnormalizedNull)

/-- Helper for Exercise 57.1: every odd self-map of `StandardSphere 1` is not
nullhomotopic. -/
private lemma oddStandardSphereOneMap_not_nullhomotopic
    (h : C(StandardSphere 1, StandardSphere 1))
    (hodd : Function.Odd h) : ¬ h.Nullhomotopic := by
  -- Conjugate by the antipode-compatible complex coordinate homeomorphism.
  let e := standardSphereOneHomeomorphCircle
  let g : C(Circle, Circle) :=
    (e : C(StandardSphere 1, Circle)).comp
      (h.comp (e.symm : C(Circle, StandardSphere 1)))
  have hinverseNeg (z : Circle) : e.symm (-z) = -e.symm z := by
    apply e.injective
    rw [e.apply_symm_apply, standardSphereOneHomeomorphCircle_neg,
      e.apply_symm_apply]
  have hgOdd : Function.Odd g := by
    intro z
    calc
      g (-z) = e (h (e.symm (-z))) := rfl
      _ = e (h (-e.symm z)) := congrArg (fun x ↦ e (h x)) (hinverseNeg z)
      _ = e (-h (e.symm z)) := congrArg e (hodd (e.symm z))
      _ = -e (h (e.symm z)) := standardSphereOneHomeomorphCircle_neg _
      _ = -g z := rfl
  intro hnull
  have hgNull : g.Nullhomotopic :=
    (hnull.comp_left (e.symm : C(Circle, StandardSphere 1))).comp_right
      (e : C(StandardSphere 1, Circle))
  exact oddComplexCircleMap_not_nullhomotopic g hgOdd hgNull

/-- Helper for Exercise 57.1: packaging two continuous real fields as a `PiLp`
field preserves continuity. -/
private lemma continuous_pairedWeatherField
    (temperature pressure : C(StandardSphere 2, ℝ)) :
    Continuous (fun x ↦ WithLp.toLp 2 (fun i ↦ ![temperature, pressure] i x)) := by
  -- Compose the continuous finite product field with the canonical `PiLp` inclusion.
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    (ContinuousMap.pi ![temperature, pressure]).continuous

/-- Helper for Exercise 57.1: the continuous field whose coordinates are temperature
and barometric pressure. -/
private def pairedWeatherField
    (temperature pressure : C(StandardSphere 2, ℝ)) :
    C(StandardSphere 2, EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun x ↦ WithLp.toLp 2 (fun i ↦ ![temperature, pressure] i x),
    continuous_pairedWeatherField temperature pressure⟩

/-- Helper for Exercise 57.1: each coordinate of `pairedWeatherField` is the
corresponding weather measurement. -/
private lemma pairedWeatherField_apply
    (temperature pressure : C(StandardSphere 2, ℝ)) (x : StandardSphere 2) (i : Fin 2) :
    pairedWeatherField temperature pressure x i = ![temperature x, pressure x] i := by
  -- Unpack the `PiLp` inclusion, then check the two finite coordinates.
  rw [pairedWeatherField, PiLp.toLp_apply]
  fin_cases i
  · rfl
  · rfl

/-- Exercise 57.1. At any fixed time, continuous temperature and barometric-pressure
fields on the earth's surface agree simultaneously at some antipodal pair. -/
theorem existsAntipodalTemperaturePressure
    (temperature pressure : C(StandardSphere 2, ℝ)) :
    ∃ x, temperature x = temperature (-x) ∧ pressure x = pressure (-x) := by
  -- Apply Borsuk--Ulam to the paired field, obtaining one common antipodal pair.
  obtain ⟨x, hx⟩ := existsAntipodalEq 1
    (StandardSphere.OddSelfMapsNotNullhomotopic.of_forall 1
      oddStandardSphereOneMap_not_nullhomotopic)
    (pairedWeatherField temperature pressure)
  refine ⟨x, ?_, ?_⟩
  -- Project the paired equality to the temperature coordinate.
  · calc
      temperature x = pairedWeatherField temperature pressure x 0 := by
        rw [pairedWeatherField_apply, Matrix.cons_val_zero]
      _ = pairedWeatherField temperature pressure (-x) 0 :=
        congrArg (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0) hx
      _ = temperature (-x) := by
        rw [pairedWeatherField_apply, Matrix.cons_val_zero]
  -- Project the same equality to the pressure coordinate.
  · calc
      pressure x = pairedWeatherField temperature pressure x 1 := by
        rw [pairedWeatherField_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      _ = pairedWeatherField temperature pressure (-x) 1 :=
        congrArg (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 1) hx
      _ = pressure (-x) := by
        rw [pairedWeatherField_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
