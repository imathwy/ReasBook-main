module

public import Topology_Munkres_2000.Book.Theorem_44_1
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Path

public section

open Complex Set unitInterval

/-- Helper for Exercise 59.2: the Euclidean vector given by the standard latitude
parametrization of the two-sphere. -/
private noncomputable def circleLatitudeVector (p : Circle × unitInterval) :
    EuclideanSpace ℝ (Fin 3) :=
  -- Use the circle point as longitude and the interval coordinate as latitude.
  !₂[Real.sin (Real.pi * p.2) * (p.1 : ℂ).re,
    Real.sin (Real.pi * p.2) * (p.1 : ℂ).im,
    Real.cos (Real.pi * p.2)]

/-- Helper for Exercise 59.2: every standard latitude vector has Euclidean norm one. -/
private lemma circleLatitudeVector_mem_sphere (p : Circle × unitInterval) :
    circleLatitudeVector p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- The circle equation and the Pythagorean trigonometric identity give the sphere equation.
  have hcircle : (p.1 : ℂ).re ^ 2 + (p.1 : ℂ).im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two] using Circle.normSq_coe p.1
  rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]
  simp only [Set.mem_setOf_eq, circleLatitudeVector, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, one_pow]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (p.2 : ℝ))]

/-- Helper for Exercise 59.2: the standard latitude parametrization, packaged as a
point of the two-sphere. -/
private noncomputable def circleLatitudePoint (p : Circle × unitInterval) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  -- Package the named vector with its norm-one certificate.
  ⟨circleLatitudeVector p, circleLatitudeVector_mem_sphere p⟩

/-- Helper for Exercise 59.2: the standard latitude parametrization is continuous. -/
private lemma continuous_circleLatitudePoint : Continuous circleLatitudePoint := by
  -- After forgetting the sphere subtype, continuity is coordinatewise.
  apply continuous_induced_rng.mpr
  unfold circleLatitudePoint circleLatitudeVector
  fun_prop

/-- Helper for Exercise 59.2: the first coordinate of the latitude parametrization has
the expected trigonometric formula. -/
private lemma circleLatitudePoint_apply_zero (p : Circle × unitInterval) :
    (circleLatitudePoint p).1 0 =
      Real.sin (Real.pi * p.2) * (p.1 : ℂ).re := by
  -- This is the first projection of the named latitude vector.
  rfl

/-- Helper for Exercise 59.2: the second coordinate of the latitude parametrization has
the expected trigonometric formula. -/
private lemma circleLatitudePoint_apply_one (p : Circle × unitInterval) :
    (circleLatitudePoint p).1 1 =
      Real.sin (Real.pi * p.2) * (p.1 : ℂ).im := by
  -- This is the second projection of the named latitude vector.
  rfl

/-- Helper for Exercise 59.2: the height of the latitude parametrization is the cosine
of its latitude angle. -/
private lemma circleLatitudePoint_apply_two (p : Circle × unitInterval) :
    (circleLatitudePoint p).1 2 = Real.cos (Real.pi * p.2) := by
  -- This is the final projection of the named latitude vector.
  rfl

/-- Helper for Exercise 59.2: two three-dimensional Euclidean vectors are equal when
their three coordinates agree. -/
private lemma euclideanFinThree_ext
    {x y : EuclideanSpace ℝ (Fin 3)}
    (hzero : x 0 = y 0) (hone : x 1 = y 1) (htwo : x 2 = y 2) : x = y := by
  -- Exhausting `Fin 3` turns vector equality into the three supplied equations.
  ext i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo

/-- Helper for Exercise 59.2: the standard latitude parametrization covers the entire
two-sphere. -/
private lemma surjective_circleLatitudePoint : Function.Surjective circleLatitudePoint := by
  intro x
  -- The sphere equation controls the height and the norm of the horizontal complex coordinate.
  have hsphere : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
    have hmem : x.1 ∈ {y : EuclideanSpace ℝ (Fin 3) | ∑ i, y i ^ 2 = 1 ^ 2} :=
      (Set.ext_iff.mp (EuclideanSpace.sphere_zero_eq 1 zero_le_one) x.1).mp x.property
    simpa only [Set.mem_setOf_eq, Fin.sum_univ_three, one_pow] using hmem
  have hheightBounds : -1 ≤ x.1 2 ∧ x.1 2 ≤ 1 := by
    constructor
    · nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1), sq_nonneg (x.1 2)]
    · nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1), sq_nonneg (x.1 2)]
  let z : ℂ := ⟨x.1 0, x.1 1⟩
  have hnormSq : ‖z‖ ^ 2 = 1 - x.1 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp only [z]
    nlinarith
  have hradicand : 0 ≤ 1 - x.1 2 ^ 2 := by
    nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
  have hhorizontal : ‖z‖ = Real.sin (Real.arccos (x.1 2)) := by
    rw [Real.sin_arccos]
    exact (sq_eq_sq₀ (norm_nonneg z) (Real.sqrt_nonneg _)).mp
      (hnormSq.trans (Real.sq_sqrt hradicand).symm)
  have hlatitude : Real.arccos (x.1 2) / Real.pi ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
    · exact (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)
  let t : unitInterval := Set.projIcc 0 1 zero_le_one
    (Real.arccos (x.1 2) / Real.pi)
  have hangle : Real.pi * (Real.arccos (x.1 2) / Real.pi) =
      Real.arccos (x.1 2) := by
    field_simp
  refine ⟨(Circle.exp (Complex.arg z), t), ?_⟩
  -- Projection recovers the chosen latitude, while argument recovers both horizontal coordinates.
  apply Subtype.ext
  apply euclideanFinThree_ext
  · rw [circleLatitudePoint_apply_zero]
    dsimp only [t]
    rw [Set.projIcc_of_mem zero_le_one hlatitude]
    simp only [hangle, Circle.coe_exp, Complex.exp_mul_I]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    rw [← hhorizontal, Complex.norm_mul_cos_arg]
  · rw [circleLatitudePoint_apply_one]
    dsimp only [t]
    rw [Set.projIcc_of_mem zero_le_one hlatitude]
    simp only [hangle, Circle.coe_exp, Complex.exp_mul_I]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, mul_zero, mul_one, zero_add, add_zero]
    rw [← hhorizontal, Complex.norm_mul_sin_arg]
  · rw [circleLatitudePoint_apply_two]
    dsimp only [t]
    rw [Set.projIcc_of_mem zero_le_one hlatitude]
    simp only [hangle]
    exact Real.cos_arccos hheightBounds.1 hheightBounds.2

/-- Helper for Exercise 59.2: traversing the two complementary semicircles gives a
surjective closed path on `Circle`. -/
private noncomputable def circleSurjection : Path (1 : Circle) 1 :=
  -- Concatenate the two oriented semicircles at their common endpoint.
  (Circle.path 1 (-1)).trans (Circle.path (-1) 1)

/-- Helper for Exercise 59.2: the closed circle path reaches every point of `Circle`. -/
private lemma surjective_circleSurjection : Function.Surjective circleSurjection := by
  -- The range of a concatenation is the union of the two semicircle ranges.
  have hRange : Set.range circleSurjection = Set.univ := by
    unfold circleSurjection
    rw [Path.trans_range,
      Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm]
  exact Set.range_eq_univ.mp hRange

/-- Helper for Exercise 59.2: a continuous interval surjection can be closed up to a
surjective loop by following it and then reversing it. -/
private lemma existsSurjectiveLoopOfContinuousSurjection
    {X : Type*} [TopologicalSpace X] (f : C(unitInterval, X))
    (hf : Function.Surjective f) :
    ∃ x : X, ∃ γ : Path x x, Function.Surjective γ := by
  let γ : Path (f 0) (f 1) := Path.id.map f.continuous
  refine ⟨f 0, γ.trans γ.symm, ?_⟩
  -- Reversal adds no new range, so the closed path retains the range of `f`.
  have hRange : Set.range (γ.trans γ.symm) = Set.range f := by
    rw [Path.trans_range, Path.symm_range, Set.union_self]
    rfl
  rw [← Set.range_eq_univ, hRange]
  exact hf.range_eq

/-- Exercise 59.2: The proposed proof fails because a loop on the standard two-sphere
can be surjective, so there need not be a point outside its image. -/
theorem existsSurjectiveLoopTwoSphere :
    ∃ x₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∃ f : Path x₀ x₀, Function.Surjective f := by
  -- First fill the square by the earlier Peano curve.
  obtain ⟨squareMap, hSquareMap⟩ := existsContinuousSurjectiveUnitSquare
  let cylinderMap : C(unitInterval × unitInterval, Circle × unitInterval) :=
    ContinuousMap.prodMap circleSurjection.toContinuousMap (ContinuousMap.id unitInterval)
  have hCylinderMap : Function.Surjective cylinderMap :=
    surjective_circleSurjection.prodMap Function.surjective_id
  let latitudeMap :
      C(Circle × unitInterval, Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ⟨circleLatitudePoint, continuous_circleLatitudePoint⟩
  let sphereCurve :
      C(unitInterval, Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    latitudeMap.comp (cylinderMap.comp squareMap)
  have hSphereCurve : Function.Surjective sphereCurve :=
    surjective_circleLatitudePoint.comp (hCylinderMap.comp hSquareMap)
  -- Closing the space-filling path gives the required surjective loop.
  exact existsSurjectiveLoopOfContinuousSurjection sphereCurve hSphereCurve
