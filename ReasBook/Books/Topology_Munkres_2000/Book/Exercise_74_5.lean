module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Topology_Munkres_2000.Book.Example_74_5.MobiusBand
import all Topology_Munkres_2000.Book.Example_74_5.MobiusBand
import Topology_Munkres_2000.Book.Theorem_60_3
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homeomorph.Quotient

public section

noncomputable section

open scoped unitInterval

/-- Helper for Exercise 74.5: the generating Möbius relation has its boundary-coordinate form. -/
private lemma mobiusBandGlue_iff (p q : UnitSquare) :
    mobiusBandGlue p q ↔
      p.1 = 0 ∧ q.1 = 1 ∧ p.2 = unitInterval.symm q.2 := by
  -- This is the defining relation on the two vertical edges of the square.
  rfl

/-- Helper for Exercise 74.5: equality or one generating Möbius gluing step in either
direction is an equivalence relation. -/
private lemma mobiusBandGlueNormalForm_equivalence :
    Equivalence (fun p q : UnitSquare ↦
      p = q ∨ mobiusBandGlue p q ∨ mobiusBandGlue q p) := by
  -- Reflexivity and symmetry only select or reverse one of the three alternatives.
  refine ⟨fun p ↦ Or.inl rfl, ?_, ?_⟩
  · intro p q hpq
    rcases hpq with hpq | hpq | hqp
    · exact Or.inl hpq.symm
    · exact Or.inr (Or.inr hpq)
    · exact Or.inr (Or.inl hqp)
  · intro p q r hpq hqr
    -- Nontrivial composable cases either collapse by endpoint uniqueness or are impossible.
    rcases hpq with rfl | hpq | hqp
    · exact hqr
    · rcases hqr with rfl | hqr | hrq
      · exact Or.inr (Or.inl hpq)
      · rw [mobiusBandGlue_iff] at hpq hqr
        have h : (1 : unitInterval) = 0 := hpq.2.1.symm.trans hqr.1
        norm_num at h
      · left
        rw [mobiusBandGlue_iff] at hpq hrq
        apply Prod.ext
        · exact hpq.1.trans hrq.1.symm
        · exact hpq.2.2.trans hrq.2.2.symm
    · rcases hqr with rfl | hqr | hrq
      · exact Or.inr (Or.inr hqp)
      · left
        rw [mobiusBandGlue_iff] at hqp hqr
        apply Prod.ext
        · exact hqp.2.1.trans hqr.2.1.symm
        · apply unitInterval.symm_bijective.injective
          exact hqp.2.2.symm.trans hqr.2.2
      · rw [mobiusBandGlue_iff] at hrq hqp
        have h : (1 : unitInterval) = 0 := hrq.2.1.symm.trans hqp.1
        norm_num at h

/-- Helper for Exercise 74.5: the generated Möbius setoid has a three-case normal form. -/
private lemma mobiusBandSetoid_rel_iff (p q : UnitSquare) :
    Relation.EqvGen.setoid mobiusBandGlue p q ↔
      p = q ∨ mobiusBandGlue p q ∨ mobiusBandGlue q p := by
  -- Compare the generated closure with the explicit equivalence relation above.
  change Relation.EqvGen mobiusBandGlue p q ↔ _
  constructor
  · intro hpq
    apply mobiusBandGlueNormalForm_equivalence.eqvGen_iff.mp
    exact Relation.EqvGen.mono (fun _ _ h ↦ Or.inr (Or.inl h)) p q hpq
  · rintro (rfl | hpq | hqp)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ hpq
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hqp)

/-- Helper for Exercise 74.5: the unit sphere in Euclidean three-space. -/
private abbrev ProjectiveSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Helper for Exercise 74.5: adjoining a leading coordinate to a Euclidean plane vector. -/
private def prependCoordinate (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (Fin.cons c (EuclideanSpace.equiv (Fin 2) ℝ v))

/-- Helper for Exercise 74.5: the leading coordinate of a Euclidean three-space vector. -/
private def leadingCoordinate (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  EuclideanSpace.equiv (Fin 3) ℝ z 0

/-- Helper for Exercise 74.5: the two coordinates after the leading coordinate. -/
private def tailCoordinates (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (Fin.tail (EuclideanSpace.equiv (Fin 3) ℝ z))

/-- Helper for Exercise 74.5: adjoining a head and tail splits the squared Euclidean norm. -/
private lemma prependCoordinate_norm_sq (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖prependCoordinate c v‖ ^ 2 = c ^ 2 + ‖v‖ ^ 2 := by
  -- Expand the Euclidean norm as a finite sum and split off its first coordinate.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp [prependCoordinate]

/-- Helper for Exercise 74.5: extracting the coordinates after adjoining them recovers the head. -/
private lemma leadingCoordinate_prependCoordinate
    (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    leadingCoordinate (prependCoordinate c v) = c := by
  -- The zeroth coordinate of `Fin.cons c v` is `c`.
  simp [leadingCoordinate, prependCoordinate]

/-- Helper for Exercise 74.5: extracting the coordinates after adjoining them recovers the tail. -/
private lemma tailCoordinates_prependCoordinate
    (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    tailCoordinates (prependCoordinate c v) = v := by
  -- Apply the plane coordinate equivalence and cancel both coordinate equivalences.
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  rw [tailCoordinates, prependCoordinate, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Helper for Exercise 74.5: adjoining the extracted head and tail reconstructs a vector. -/
private lemma prependCoordinate_leading_tail (z : EuclideanSpace ℝ (Fin 3)) :
    prependCoordinate (leadingCoordinate z) (tailCoordinates z) = z := by
  -- Compare coordinates, treating the head and the two tail entries separately.
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  rw [prependCoordinate, ContinuousLinearEquiv.apply_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · change (EuclideanSpace.equiv (Fin 3) ℝ z) j.succ = _
    rfl

/-- Helper for Exercise 74.5: adjoining coordinates commutes with negation. -/
private lemma prependCoordinate_neg (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    prependCoordinate (-c) (-v) = -prependCoordinate c v := by
  -- Compare ordinary coordinates, where both the head and tail negate pointwise.
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simp only [prependCoordinate, ContinuousLinearEquiv.apply_symm_apply, map_neg]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

/-- Helper for Exercise 74.5: the leading coordinate changes sign under negation. -/
private lemma leadingCoordinate_neg (z : EuclideanSpace ℝ (Fin 3)) :
    leadingCoordinate (-z) = -leadingCoordinate z := by
  -- The Euclidean coordinate equivalence is linear.
  simp [leadingCoordinate]

/-- Helper for Exercise 74.5: the tail coordinates change sign under negation. -/
private lemma tailCoordinates_neg (z : EuclideanSpace ℝ (Fin 3)) :
    tailCoordinates (-z) = -tailCoordinates z := by
  -- Compare ordinary tail coordinates after applying the plane equivalence.
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  simp only [tailCoordinates, ContinuousLinearEquiv.apply_symm_apply, map_neg]
  rfl

/-- Helper for Exercise 74.5: adjoining a varying head to a varying tail is continuous. -/
private lemma continuous_prependCoordinate :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      prependCoordinate p.1 p.2) := by
  -- Check continuity coordinatewise after applying the Euclidean equivalence.
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp
      ((EuclideanSpace.equiv (Fin 2) ℝ).continuous.comp continuous_snd)

/-- Helper for Exercise 74.5: a sphere point satisfies the head-tail norm equation. -/
private lemma leading_sq_add_tail_norm_sq (z : ProjectiveSphere) :
    leadingCoordinate z ^ 2 + ‖tailCoordinates z‖ ^ 2 = 1 := by
  -- Reconstruct the ambient vector, split its norm, and use sphere membership.
  calc
    leadingCoordinate z ^ 2 + ‖tailCoordinates z‖ ^ 2 =
        ‖prependCoordinate (leadingCoordinate z) (tailCoordinates z)‖ ^ 2 :=
      (prependCoordinate_norm_sq _ _).symm
    _ = ‖(z : EuclideanSpace ℝ (Fin 3))‖ ^ 2 := by
      rw [prependCoordinate_leading_tail]
    _ = 1 := by
      rw [mem_sphere_zero_iff_norm.mp z.property]
      norm_num

/-- Helper for Exercise 74.5: the standard real-linear isometry from the Euclidean plane
to the complex plane. -/
private def planeComplexIsometry : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- Helper for Exercise 74.5: the selected closed semicircle direction at a unit parameter. -/
private def halfCircleDirection (u : unitInterval) : EuclideanSpace ℝ (Fin 2) :=
  planeComplexIsometry.symm (Circle.exp (Real.pi * (u : ℝ)) : ℂ)

/-- Helper for Exercise 74.5: every selected semicircle direction has unit norm. -/
private lemma halfCircleDirection_norm (u : unitInterval) :
    ‖halfCircleDirection u‖ = 1 := by
  -- The plane-complex isometry preserves the norm of a point of `Circle`.
  rw [halfCircleDirection, planeComplexIsometry.symm.norm_map]
  exact Circle.norm_coe _

/-- Helper for Exercise 74.5: the selected semicircle direction varies continuously. -/
private lemma continuous_halfCircleDirection : Continuous halfCircleDirection := by
  -- Compose the interval coordinate, circle exponential, and inverse linear isometry.
  unfold halfCircleDirection
  fun_prop

/-- Helper for Exercise 74.5: shifting a circle angle by `π` gives the antipodal point. -/
private lemma circleExp_add_pi (theta : ℝ) :
    Circle.exp (theta + Real.pi) = -Circle.exp theta := by
  -- On complex representatives this is the exponential identity `exp (π I) = -1`.
  apply Circle.ext
  rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_exp]
  have hexponent : ((theta + Real.pi : ℝ) : ℂ) * Complex.I =
      (theta : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexponent, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Helper for Exercise 74.5: the selected closed semicircle has no repeated directions. -/
private lemma halfCircleDirection_injective : Function.Injective halfCircleDirection := by
  -- Pull equality through the isometry and use injectivity of `Circle.exp` on `[0, π]`.
  intro u v huv
  have hcomplex :
      (Circle.exp (Real.pi * (u : ℝ)) : ℂ) =
        Circle.exp (Real.pi * (v : ℝ)) := by
    apply planeComplexIsometry.symm.injective
    exact huv
  have hcircle :
      Circle.exp (Real.pi * (u : ℝ)) =
        Circle.exp (Real.pi * (v : ℝ)) := Subtype.ext hcomplex
  have huAngle : Real.pi * (u : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg Real.pi_pos.le u.property.1
    · nlinarith [u.property.2, Real.pi_pos]
  have hvAngle : Real.pi * (v : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg Real.pi_pos.le v.property.1
    · nlinarith [v.property.2, Real.pi_pos]
  have hpiSpan : Real.pi - 0 < 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hangle := Circle.exp_injOn_Icc hpiSpan huAngle hvAngle hcircle
  apply Subtype.ext
  nlinarith [Real.pi_pos]

/-- Helper for Exercise 74.5: antipodal selected directions occur only at opposite endpoints. -/
private lemma halfCircleDirection_eq_neg_iff (u v : unitInterval) :
    halfCircleDirection v = -halfCircleDirection u ↔
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  -- Convert an antipodal equality to equality of circle angles modulo `2π`.
  constructor
  · intro huv
    have hcomplex :
        (Circle.exp (Real.pi * (v : ℝ)) : ℂ) =
          -(Circle.exp (Real.pi * (u : ℝ)) : ℂ) := by
      have himage := congrArg planeComplexIsometry huv
      simpa only [halfCircleDirection, LinearIsometryEquiv.apply_symm_apply,
        map_neg] using himage
    have hcircle : Circle.exp (Real.pi * (v : ℝ)) =
        -Circle.exp (Real.pi * (u : ℝ)) := Subtype.ext hcomplex
    rw [← circleExp_add_pi] at hcircle
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircle
    have hnormalized : (v : ℝ) = (u : ℝ) + 1 + 2 * (m : ℝ) := by
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      apply (mul_left_cancel₀ hpi)
      linear_combination hm
    have hmLower : (-1 : ℝ) ≤ (m : ℝ) := by
      linarith [u.property.2, v.property.1]
    have hmUpper : (m : ℝ) ≤ 0 := by
      linarith [u.property.1, v.property.2]
    have hmLowerInt : (-1 : ℤ) ≤ m := by exact_mod_cast hmLower
    have hmUpperInt : m ≤ (0 : ℤ) := by exact_mod_cast hmUpper
    have hmCases : m = -1 ∨ m = 0 := by omega
    rcases hmCases with rfl | rfl
    · right
      norm_num at hnormalized
      have huValue : (u : ℝ) = 1 := by
        linarith [u.property.2, v.property.1]
      have hvValue : (v : ℝ) = 0 := by
        linarith [u.property.2, v.property.1]
      exact ⟨Subtype.ext huValue, Subtype.ext hvValue⟩
    · left
      norm_num at hnormalized
      have huValue : (u : ℝ) = 0 := by
        linarith [u.property.1, v.property.2]
      have hvValue : (v : ℝ) = 1 := by
        linarith [u.property.1, v.property.2]
      exact ⟨Subtype.ext huValue, Subtype.ext hvValue⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · apply planeComplexIsometry.injective
      simp only [halfCircleDirection, LinearIsometryEquiv.apply_symm_apply, map_neg]
      norm_num
    · apply planeComplexIsometry.injective
      simp only [halfCircleDirection, LinearIsometryEquiv.apply_symm_apply, map_neg]
      norm_num

/-- Helper for Exercise 74.5: every unit plane direction has a selected semicircle
representative, possibly after negation. -/
private lemma exists_halfCircleDirection_eq_or_eq_neg
    (d : EuclideanSpace ℝ (Fin 2)) (hd : ‖d‖ = 1) :
    ∃ u : unitInterval,
      halfCircleDirection u = d ∨ halfCircleDirection u = -d := by
  -- Regard the direction as a circle point and orient its principal argument into `[0, π]`.
  have hcircleMem : planeComplexIsometry d ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, planeComplexIsometry.norm_map, hd]
  let c : Circle := ⟨planeComplexIsometry d, hcircleMem⟩
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  by_cases harg : 0 ≤ Complex.arg (c : ℂ)
  · have huMem : Complex.arg (c : ℂ) / Real.pi ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg harg Real.pi_pos.le
      · exact (div_le_one Real.pi_pos).mpr (Complex.arg_le_pi c)
    let u : unitInterval := ⟨Complex.arg (c : ℂ) / Real.pi, huMem⟩
    refine ⟨u, Or.inl ?_⟩
    apply planeComplexIsometry.injective
    rw [halfCircleDirection, LinearIsometryEquiv.apply_symm_apply]
    change (Circle.exp (Real.pi * (Complex.arg (c : ℂ) / Real.pi)) : ℂ) =
      planeComplexIsometry d
    rw [mul_div_cancel₀ _ hpi]
    exact congrArg Subtype.val (Circle.exp_arg c)
  · have hargNeg : Complex.arg (c : ℂ) < 0 := lt_of_not_ge harg
    have huMem : (Complex.arg (c : ℂ) + Real.pi) / Real.pi ∈
        Set.Icc (0 : ℝ) 1 := by
      constructor
      · have hsum : 0 ≤ Complex.arg (c : ℂ) + Real.pi := by
          linarith [Complex.neg_pi_lt_arg (c : ℂ)]
        exact div_nonneg hsum Real.pi_pos.le
      · have hsum : Complex.arg (c : ℂ) + Real.pi ≤ Real.pi := by
          linarith
        exact (div_le_one Real.pi_pos).mpr hsum
    let u : unitInterval :=
      ⟨(Complex.arg (c : ℂ) + Real.pi) / Real.pi, huMem⟩
    refine ⟨u, Or.inr ?_⟩
    apply planeComplexIsometry.injective
    rw [halfCircleDirection, LinearIsometryEquiv.apply_symm_apply, map_neg]
    change (Circle.exp
        (Real.pi * ((Complex.arg (c : ℂ) + Real.pi) / Real.pi)) : ℂ) =
      -planeComplexIsometry d
    rw [mul_div_cancel₀ _ hpi]
    exact congrArg Subtype.val
      ((circleExp_add_pi (Complex.arg (c : ℂ))).trans
        (congrArg Neg.neg (Circle.exp_arg c)))

/-- Helper for Exercise 74.5: the leading-coordinate projection is continuous. -/
private lemma continuous_leadingCoordinate : Continuous leadingCoordinate := by
  -- It is coordinate evaluation after the Euclidean coordinate equivalence.
  exact (continuous_apply 0).comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous

/-- Helper for Exercise 74.5: the tail-coordinate projection is continuous. -/
private lemma continuous_tailCoordinates : Continuous tailCoordinates := by
  -- Check the two tail coordinates after applying the plane coordinate equivalence.
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous

/-- Helper for Exercise 74.5: the open northern spherical cap used as the deleted disk. -/
private def projectiveCap : Set ProjectiveSphere :=
  {z | (3 : ℝ) / 5 < leadingCoordinate z}

/-- Helper for Exercise 74.5: the image of the northern cap in the projective plane. -/
private def projectiveDisk : Set RealProjectivePlane :=
  RealProjectivePlane.quotientMap '' projectiveCap

/-- Helper for Exercise 74.5: the selected northern spherical cap is open. -/
private lemma projectiveCap_isOpen : IsOpen projectiveCap := by
  -- Pull the open ray `(3/5, ∞)` back along the leading-coordinate projection.
  exact isOpen_lt continuous_const
    (continuous_leadingCoordinate.comp continuous_subtype_val)

/-- Helper for Exercise 74.5: the selected projective disk is open. -/
private lemma projectiveDisk_isOpen : IsOpen projectiveDisk := by
  -- The sphere quotient is an open covering map, so it sends the open cap to an open set.
  exact RealProjectivePlane.quotientMap_isCoveringMap.isOpenMap
    projectiveCap projectiveCap_isOpen

/-- Helper for Exercise 74.5: the tail of a cap point lies in the radius-`4/5` open ball. -/
private lemma capTail_mem_smallBall (z : projectiveCap) :
    tailCoordinates z ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) := by
  -- The unit-sphere equation turns the strict lower bound on the head into a tail bound.
  rw [Metric.mem_ball, dist_zero_right]
  have hsphere := leading_sq_add_tail_norm_sq z
  have hhead : (3 : ℝ) / 5 < leadingCoordinate z := z.property
  nlinarith [norm_nonneg (tailCoordinates z)]

/-- Helper for Exercise 74.5: tail coordinates identify the cap with a small open ball. -/
private def capTail (z : projectiveCap) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) :=
  ⟨tailCoordinates z, capTail_mem_smallBall z⟩

/-- Helper for Exercise 74.5: a point of the small ball gives a nonnegative sphere radicand. -/
private lemma upperCap_radicand_nonneg
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5)) :
    0 ≤ 1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
  -- Its norm is strictly below `4/5`, hence in particular below one.
  have hy : ‖(y : EuclideanSpace ℝ (Fin 2))‖ < (4 : ℝ) / 5 := by
    simpa only [Metric.mem_ball, dist_zero_right] using y.property
  nlinarith [norm_nonneg (y : EuclideanSpace ℝ (Fin 2))]

/-- Helper for Exercise 74.5: the upper-cap coordinate formula lies on the unit sphere. -/
private lemma upperCapAmbient_mem_sphere
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5)) :
    prependCoordinate (Real.sqrt
        (1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) y ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- The square-root head supplies the missing part of the unit norm.
  rw [mem_sphere_zero_iff_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [prependCoordinate_norm_sq, Real.sq_sqrt (upperCap_radicand_nonneg y)]
  ring

/-- Helper for Exercise 74.5: the upper-cap sphere point over a small-ball vector. -/
private def upperCapSpherePoint
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5)) :
    ProjectiveSphere :=
  ⟨prependCoordinate (Real.sqrt
      (1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) y,
    upperCapAmbient_mem_sphere y⟩

/-- Helper for Exercise 74.5: the upper-cap sphere point has head greater than `3/5`. -/
private lemma upperCapSpherePoint_mem_cap
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5)) :
    upperCapSpherePoint y ∈ projectiveCap := by
  -- Compare squares, using the strict `4/5` tail bound and nonnegativity of the square root.
  have hy : ‖(y : EuclideanSpace ℝ (Fin 2))‖ < (4 : ℝ) / 5 := by
    simpa only [Metric.mem_ball, dist_zero_right] using y.property
  have hsq := Real.sq_sqrt (upperCap_radicand_nonneg y)
  have hsqrt := Real.sqrt_nonneg
    (1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2)
  rw [projectiveCap, Set.mem_setOf_eq, upperCapSpherePoint,
    leadingCoordinate_prependCoordinate]
  nlinarith [norm_nonneg (y : EuclideanSpace ℝ (Fin 2))]

/-- Helper for Exercise 74.5: the inverse cap coordinate associated to a small-ball vector. -/
private def upperCapPoint
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5)) :
    projectiveCap :=
  ⟨upperCapSpherePoint y, upperCapSpherePoint_mem_cap y⟩

/-- Helper for Exercise 74.5: the cap tail-coordinate map is continuous. -/
private lemma continuous_capTail : Continuous capTail := by
  -- Restrict the continuous ambient tail projection to the two subtypes.
  exact Continuous.subtype_mk
    (continuous_tailCoordinates.comp (continuous_subtype_val.comp continuous_subtype_val)) _

/-- Helper for Exercise 74.5: the inverse upper-cap coordinate map is continuous. -/
private lemma continuous_upperCapPoint : Continuous upperCapPoint := by
  -- The square-root height and the unchanged tail vary continuously.
  have hheight : Continuous (fun y :
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) ↦
        Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) := by
    fun_prop
  have htail : Continuous (fun y :
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) ↦
        (y : EuclideanSpace ℝ (Fin 2))) := continuous_subtype_val
  exact Continuous.subtype_mk
    (Continuous.subtype_mk
      (continuous_prependCoordinate.comp (hheight.prodMk htail)) _) _

/-- Helper for Exercise 74.5: extracting the tail of the reconstructed cap point is the identity. -/
private lemma capTail_upperCapPoint
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5)) :
    capTail (upperCapPoint y) = y := by
  -- Tail extraction cancels coordinate adjoining.
  apply Subtype.ext
  exact tailCoordinates_prependCoordinate _ _

/-- Helper for Exercise 74.5: reconstructing a cap point from its tail is the identity. -/
private lemma upperCapPoint_capTail (z : projectiveCap) :
    upperCapPoint (capTail z) = z := by
  -- The positive head is the square root determined by the sphere equation.
  have hrad : 1 - ‖tailCoordinates (z : ProjectiveSphere)‖ ^ 2 =
      leadingCoordinate (z : ProjectiveSphere) ^ 2 := by
    nlinarith [leading_sq_add_tail_norm_sq (z : ProjectiveSphere)]
  have hheadPos : 0 < leadingCoordinate (z : ProjectiveSphere) := by
    exact (show (3 : ℝ) / 5 < leadingCoordinate (z : ProjectiveSphere) from z.property).trans'
      (by norm_num)
  have hheight : Real.sqrt (1 - ‖tailCoordinates (z : ProjectiveSphere)‖ ^ 2) =
      leadingCoordinate (z : ProjectiveSphere) := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hheadPos]
  apply Subtype.ext
  apply Subtype.ext
  calc
    (upperCapPoint (capTail z) : EuclideanSpace ℝ (Fin 3)) =
        prependCoordinate
          (Real.sqrt (1 - ‖tailCoordinates (z : ProjectiveSphere)‖ ^ 2))
          (tailCoordinates (z : ProjectiveSphere)) := rfl
    _ = prependCoordinate (leadingCoordinate (z : ProjectiveSphere))
        (tailCoordinates (z : ProjectiveSphere)) := by rw [hheight]
    _ = z := prependCoordinate_leading_tail z

/-- Helper for Exercise 74.5: tail coordinates give a bijection from the cap to the small ball. -/
private lemma capTail_bijective : Function.Bijective capTail := by
  -- The explicit upper-cap construction is simultaneously a left and right inverse.
  exact ⟨Function.LeftInverse.injective upperCapPoint_capTail,
    Function.RightInverse.surjective capTail_upperCapPoint⟩

/-- Helper for Exercise 74.5: the underlying cap-to-small-ball equivalence. -/
private def capTailEquiv : projectiveCap ≃
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) :=
  Equiv.ofBijective capTail capTail_bijective

/-- Helper for Exercise 74.5: the inverse of the cap-tail equivalence is the explicit cap point. -/
private lemma capTailEquiv_symm_apply
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5)) :
    capTailEquiv.symm y = upperCapPoint y := by
  -- Injectivity of `capTail` reduces the claim to the right-inverse calculation.
  apply capTail_bijective.injective
  calc
    capTail (capTailEquiv.symm y) = y := capTailEquiv.apply_symm_apply y
    _ = capTail (upperCapPoint y) := (capTail_upperCapPoint y).symm

/-- Helper for Exercise 74.5: the cap-tail equivalence is a homeomorphism. -/
private lemma capTail_isHomeomorph : IsHomeomorph capTail := by
  -- Both directions are continuous by the stable coordinate interface.
  change IsHomeomorph (capTailEquiv : projectiveCap →
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5))
  rw [capTailEquiv.isHomeomorph_iff]
  constructor
  · exact continuous_capTail
  · have heq : (capTailEquiv.symm :
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) →
          projectiveCap) = upperCapPoint := by
      funext y
      exact capTailEquiv_symm_apply y
    rw [heq]
    exact continuous_upperCapPoint

/-- Helper for Exercise 74.5: the cap is homeomorphic to the radius-`4/5` ball. -/
private def capTailHomeomorph : projectiveCap ≃ₜ
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) :=
  capTail_isHomeomorph.homeomorph capTail

/-- Helper for Exercise 74.5: the quotient map restricted to the cap lands in its image. -/
private def capQuotient (z : projectiveCap) : projectiveDisk :=
  ⟨RealProjectivePlane.quotientMap z, ⟨z, z.property, rfl⟩⟩

/-- Helper for Exercise 74.5: the restricted cap quotient is injective. -/
private lemma capQuotient_injective : Function.Injective capQuotient := by
  -- The antipodal fiber alternative contradicts positivity of both cap heads.
  intro z w hzw
  have hquotient : RealProjectivePlane.quotientMap (z : ProjectiveSphere) =
      RealProjectivePlane.quotientMap (w : ProjectiveSphere) := congrArg Subtype.val hzw
  rcases (RealProjectivePlane.quotientMap_eq_iff z w).mp hquotient with h | h
  · exact Subtype.ext h.symm
  · have hhead := congrArg
        (fun x : ProjectiveSphere ↦ leadingCoordinate (x : EuclideanSpace ℝ (Fin 3))) h
    have hz : (3 : ℝ) / 5 < leadingCoordinate (z : ProjectiveSphere) := z.property
    have hw : (3 : ℝ) / 5 < leadingCoordinate (w : ProjectiveSphere) := w.property
    simp only [coe_neg_sphere, leadingCoordinate_neg] at hhead
    nlinarith

/-- Helper for Exercise 74.5: the restricted cap quotient is surjective onto its image. -/
private lemma capQuotient_surjective : Function.Surjective capQuotient := by
  -- Unpack the image witness carried by the codomain subtype.
  rintro ⟨q, z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

/-- Helper for Exercise 74.5: the restricted cap quotient is continuous. -/
private lemma continuous_capQuotient : Continuous capQuotient := by
  -- Restrict the continuous sphere quotient to the domain and image subtypes.
  exact Continuous.subtype_mk
    (RealProjectivePlane.quotientMap_isQuotientMap.continuous.comp
      continuous_subtype_val) _

/-- Helper for Exercise 74.5: the restricted cap quotient is an open map. -/
private lemma capQuotient_isOpenMap : IsOpenMap capQuotient := by
  -- Restrict the open sphere quotient to the open cap and then corestrict to its image.
  exact (RealProjectivePlane.quotientMap_isCoveringMap.isOpenMap.restrict
    projectiveCap_isOpen).subtype_mk _

/-- Helper for Exercise 74.5: the restricted cap quotient is a homeomorphism. -/
private lemma capQuotient_isHomeomorph : IsHomeomorph capQuotient := by
  -- Combine continuity, openness, and the explicit bijection onto the image.
  exact ⟨continuous_capQuotient, capQuotient_isOpenMap,
    capQuotient_injective, capQuotient_surjective⟩

/-- Helper for Exercise 74.5: the northern cap maps homeomorphically onto the projective disk. -/
private def capQuotientHomeomorph : projectiveCap ≃ₜ projectiveDisk :=
  capQuotient_isHomeomorph.homeomorph capQuotient

/-- Helper for Exercise 74.5: the radius `4/5` is positive. -/
private lemma fourFifths_pos : (0 : ℝ) < 4 / 5 := by
  -- This is the elementary positivity side condition for ball rescaling.
  norm_num

/-- Helper for Exercise 74.5: radial scaling identifies the unit ball with the small ball. -/
private def unitBallSmallBallHomeomorph :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) :=
  (OpenPartialHomeomorph.unitBallBall
    (0 : EuclideanSpace ℝ (Fin 2)) ((4 : ℝ) / 5) fourFifths_pos).toHomeomorphSourceTarget

/-- Helper for Exercise 74.5: the Euclidean unit ball is homeomorphic to the chosen
projective disk. -/
private def unitBallProjectiveDiskHomeomorph :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ projectiveDisk :=
  unitBallSmallBallHomeomorph.trans
    (capTailHomeomorph.symm.trans capQuotientHomeomorph)

/-- Helper for Exercise 74.5: membership in the projective disk is detected by the
absolute leading coordinate of a sphere representative. -/
private lemma quotientMap_mem_projectiveDisk_iff (z : ProjectiveSphere) :
    RealProjectivePlane.quotientMap z ∈ projectiveDisk ↔
      (3 : ℝ) / 5 < |leadingCoordinate z| := by
  -- An image witness is either the given representative or its antipode.
  constructor
  · rintro ⟨w, hw, hquotient⟩
    change (3 : ℝ) / 5 < leadingCoordinate w at hw
    have hwPos : 0 < leadingCoordinate w := lt_trans (by norm_num) hw
    rcases (RealProjectivePlane.quotientMap_eq_iff w z).mp hquotient with h | h
    · rw [h]
      rwa [abs_of_pos hwPos]
    · have hhead := congrArg
          (fun x : ProjectiveSphere ↦ leadingCoordinate (x : EuclideanSpace ℝ (Fin 3))) h
      simp only [coe_neg_sphere, leadingCoordinate_neg] at hhead
      rw [hhead, abs_neg, abs_of_pos hwPos]
      exact hw
  · intro hz
    by_cases hpositive : (3 : ℝ) / 5 < leadingCoordinate z
    · exact ⟨z, hpositive, rfl⟩
    · have hnegative : leadingCoordinate z < -((3 : ℝ) / 5) := by
        by_cases hnonneg : 0 ≤ leadingCoordinate z
        · rw [abs_of_nonneg hnonneg] at hz
          exact (hpositive hz).elim
        · rw [abs_of_neg (lt_of_not_ge hnonneg)] at hz
          linarith
      have hnegCap : -z ∈ projectiveCap := by
        rw [projectiveCap, Set.mem_setOf_eq]
        simp only [coe_neg_sphere, leadingCoordinate_neg]
        linarith
      exact ⟨-z, hnegCap, RealProjectivePlane.quotientMap_neg z⟩

/-- Helper for Exercise 74.5: the complement of the projective disk is the closed
equatorial band `|x₀| ≤ 3/5`. -/
private lemma quotientMap_not_mem_projectiveDisk_iff (z : ProjectiveSphere) :
    RealProjectivePlane.quotientMap z ∉ projectiveDisk ↔
      |leadingCoordinate z| ≤ (3 : ℝ) / 5 := by
  -- Negate the strict membership characterization.
  rw [quotientMap_mem_projectiveDisk_iff, not_lt]

/-- Helper for Exercise 74.5: the latitude assigned to a point of the parameter square. -/
private def bandLatitude (p : UnitSquare) : ℝ :=
  ((3 : ℝ) / 5) * (2 * (p.2 : ℝ) - 1)

/-- Helper for Exercise 74.5: all square latitudes lie between `-3/5` and `3/5`. -/
private lemma bandLatitude_bounds (p : UnitSquare) :
    -((3 : ℝ) / 5) ≤ bandLatitude p ∧
      bandLatitude p ≤ (3 : ℝ) / 5 := by
  -- Rescale the defining bounds `0 ≤ p.2 ≤ 1` affinely.
  constructor <;> unfold bandLatitude <;> nlinarith [p.2.property.1, p.2.property.2]

/-- Helper for Exercise 74.5: interval reflection negates the associated latitude. -/
private lemma bandLatitude_symm (u v : unitInterval) :
    bandLatitude (u, unitInterval.symm v) = -bandLatitude (u, v) := by
  -- Reflection replaces the transverse real coordinate `v` by `1 - v`.
  unfold bandLatitude
  rw [unitInterval.coe_symm_eq]
  ring

/-- Helper for Exercise 74.5: the positive tail radius at a square parameter. -/
private def bandRadius (p : UnitSquare) : ℝ :=
  Real.sqrt (1 - bandLatitude p ^ 2)

/-- Helper for Exercise 74.5: the band-radius radicand is strictly positive. -/
private lemma bandRadius_radicand_pos (p : UnitSquare) :
    0 < 1 - bandLatitude p ^ 2 := by
  -- The latitude bound is strictly smaller than one in absolute value.
  obtain ⟨hlower, hupper⟩ := bandLatitude_bounds p
  nlinarith

/-- Helper for Exercise 74.5: the band tail radius is strictly positive. -/
private lemma bandRadius_pos (p : UnitSquare) : 0 < bandRadius p := by
  -- Apply positivity of the real square root to the radicand estimate.
  exact Real.sqrt_pos.2 (bandRadius_radicand_pos p)

/-- Helper for Exercise 74.5: the square of the band tail radius has its defining value. -/
private lemma bandRadius_sq (p : UnitSquare) :
    bandRadius p ^ 2 = 1 - bandLatitude p ^ 2 := by
  -- Square the positive square root in the definition.
  exact Real.sq_sqrt (bandRadius_radicand_pos p).le

/-- Helper for Exercise 74.5: opposite transverse parameters have the same tail radius. -/
private lemma bandRadius_symm (u v : unitInterval) :
    bandRadius (u, unitInterval.symm v) = bandRadius (u, v) := by
  -- The defining radicand is unchanged when latitude changes sign.
  rw [bandRadius, bandRadius, bandLatitude_symm]
  ring_nf

/-- Helper for Exercise 74.5: the latitude function is continuous. -/
private lemma continuous_bandLatitude : Continuous bandLatitude := by
  -- It is an affine expression in the second square coordinate.
  unfold bandLatitude
  fun_prop

/-- Helper for Exercise 74.5: the positive tail-radius function is continuous. -/
private lemma continuous_bandRadius : Continuous bandRadius := by
  -- Compose the latitude polynomial with the continuous real square root.
  unfold bandRadius
  exact Real.continuous_sqrt.comp
    (continuous_const.sub (continuous_bandLatitude.pow 2))

/-- Helper for Exercise 74.5: the ambient equatorial-band coordinate has unit norm. -/
private lemma projectiveBandAmbient_norm (p : UnitSquare) :
    ‖prependCoordinate (bandLatitude p)
      (bandRadius p • halfCircleDirection p.1)‖ = 1 := by
  -- Split head and tail norms and use the radius and direction specifications.
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [prependCoordinate_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (bandRadius_pos p), halfCircleDirection_norm, mul_one,
    bandRadius_sq]
  ring

/-- Helper for Exercise 74.5: the equatorial-band coordinate lies on the unit sphere. -/
private lemma projectiveBandAmbient_mem_sphere (p : UnitSquare) :
    prependCoordinate (bandLatitude p)
        (bandRadius p • halfCircleDirection p.1) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- Rewrite sphere membership using the unit-norm calculation.
  exact mem_sphere_zero_iff_norm.2 (projectiveBandAmbient_norm p)

/-- Helper for Exercise 74.5: the square parametrization of the closed spherical band. -/
private def projectiveBandSpherePoint (p : UnitSquare) : ProjectiveSphere :=
  ⟨prependCoordinate (bandLatitude p)
      (bandRadius p • halfCircleDirection p.1),
    projectiveBandAmbient_mem_sphere p⟩

/-- Helper for Exercise 74.5: the band point has the prescribed leading coordinate. -/
private lemma projectiveBandSpherePoint_leading (p : UnitSquare) :
    leadingCoordinate (projectiveBandSpherePoint p) = bandLatitude p := by
  -- Extract the head of the adjoined coordinate vector.
  exact leadingCoordinate_prependCoordinate _ _

/-- Helper for Exercise 74.5: the band point has the prescribed tail vector. -/
private lemma projectiveBandSpherePoint_tail (p : UnitSquare) :
    tailCoordinates (projectiveBandSpherePoint p) =
      bandRadius p • halfCircleDirection p.1 := by
  -- Extract the tail of the adjoined coordinate vector.
  exact tailCoordinates_prependCoordinate _ _

/-- Helper for Exercise 74.5: the spherical-band parametrization is continuous. -/
private lemma continuous_projectiveBandSpherePoint :
    Continuous projectiveBandSpherePoint := by
  -- Combine the continuous latitude, radius, and half-circle direction.
  have htail : Continuous (fun p : UnitSquare ↦
      bandRadius p • halfCircleDirection p.1) := by
    exact continuous_bandRadius.smul
      (continuous_halfCircleDirection.comp continuous_fst)
  exact Continuous.subtype_mk
    (continuous_prependCoordinate.comp (continuous_bandLatitude.prodMk htail)) _

/-- Helper for Exercise 74.5: every spherical band point maps outside the projective disk. -/
private lemma projectiveBandSpherePoint_not_mem_disk (p : UnitSquare) :
    RealProjectivePlane.quotientMap (projectiveBandSpherePoint p) ∉ projectiveDisk := by
  -- Apply the complement characterization to the latitude bound.
  rw [quotientMap_not_mem_projectiveDisk_iff,
    projectiveBandSpherePoint_leading, abs_le]
  exact bandLatitude_bounds p

/-- Helper for Exercise 74.5: the square-to-projective-band map. -/
private def projectiveBandMap (p : UnitSquare) : Set.compl projectiveDisk :=
  ⟨RealProjectivePlane.quotientMap (projectiveBandSpherePoint p),
    projectiveBandSpherePoint_not_mem_disk p⟩

/-- Helper for Exercise 74.5: the square-to-projective-band map is continuous. -/
private lemma continuous_projectiveBandMap : Continuous projectiveBandMap := by
  -- Compose the spherical parametrization with the quotient and corestrict to the complement.
  exact Continuous.subtype_mk
    (RealProjectivePlane.quotientMap_isQuotientMap.continuous.comp
      continuous_projectiveBandSpherePoint) _

/-- Helper for Exercise 74.5: a latitude in the closed band determines a transverse
unit-interval parameter. -/
private lemma bandTransverseValue_mem_unitInterval (c : ℝ)
    (hc : -((3 : ℝ) / 5) ≤ c ∧ c ≤ (3 : ℝ) / 5) :
    (5 * c / 3 + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  -- Solve the affine inequalities using the prescribed latitude bounds.
  constructor <;> nlinarith [hc.1, hc.2]

/-- Helper for Exercise 74.5: the inverse affine coordinate from band latitudes to
the transverse interval. -/
private def bandTransverse (c : ℝ)
    (hc : -((3 : ℝ) / 5) ≤ c ∧ c ≤ (3 : ℝ) / 5) : unitInterval :=
  ⟨(5 * c / 3 + 1) / 2, bandTransverseValue_mem_unitInterval c hc⟩

/-- Helper for Exercise 74.5: the inverse transverse coordinate recovers its latitude. -/
private lemma bandLatitude_bandTransverse (u : unitInterval) (c : ℝ)
    (hc : -((3 : ℝ) / 5) ≤ c ∧ c ≤ (3 : ℝ) / 5) :
    bandLatitude (u, bandTransverse c hc) = c := by
  -- Substitute the inverse affine formula and normalize.
  unfold bandLatitude bandTransverse
  ring

/-- Helper for Exercise 74.5: a sphere point in the closed band has nonzero tail. -/
private lemma tailCoordinates_norm_pos_of_abs_le (z : ProjectiveSphere)
    (hz : |leadingCoordinate z| ≤ (3 : ℝ) / 5) :
    0 < ‖tailCoordinates z‖ := by
  -- The sphere equation and `|x₀| ≤ 3/5` leave positive squared norm in the tail.
  rw [abs_le] at hz
  nlinarith [leading_sq_add_tail_norm_sq z, norm_nonneg (tailCoordinates z)]

/-- Helper for Exercise 74.5: the normalized tail direction of a band point. -/
private def normalizedTailDirection (z : ProjectiveSphere) :
    EuclideanSpace ℝ (Fin 2) :=
  (‖tailCoordinates z‖)⁻¹ • tailCoordinates z

/-- Helper for Exercise 74.5: a nonzero normalized tail has unit norm. -/
private lemma normalizedTailDirection_norm (z : ProjectiveSphere)
    (hz : 0 < ‖tailCoordinates z‖) :
    ‖normalizedTailDirection z‖ = 1 := by
  -- Pull the positive inverse scalar out of the norm and cancel it.
  simp only [normalizedTailDirection, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hz), inv_mul_cancel₀ hz.ne']

/-- Helper for Exercise 74.5: normalizing the antipodal tail negates the direction. -/
private lemma normalizedTailDirection_neg (z : ProjectiveSphere) :
    normalizedTailDirection (-z) = -normalizedTailDirection z := by
  -- Tail extraction, its norm, and scalar multiplication all commute with negation.
  unfold normalizedTailDirection
  rw [coe_neg_sphere, tailCoordinates_neg, norm_neg, smul_neg]

/-- Helper for Exercise 74.5: matching latitude makes the constructed radius equal the
tail norm of a sphere point. -/
private lemma bandRadius_eq_tailCoordinates_norm (p : UnitSquare) (z : ProjectiveSphere)
    (hlatitude : bandLatitude p = leadingCoordinate z) :
    bandRadius p = ‖tailCoordinates z‖ := by
  -- Both nonnegative quantities have the same square by the sphere equation.
  have hradius := bandRadius_sq p
  rw [hlatitude] at hradius
  nlinarith [leading_sq_add_tail_norm_sq z, bandRadius_pos p,
    norm_nonneg (tailCoordinates z)]

/-- Helper for Exercise 74.5: matching latitude and normalized direction reconstructs
the original sphere point. -/
private lemma projectiveBandSpherePoint_eq_of_coordinates
    (p : UnitSquare) (z : ProjectiveSphere)
    (htail : 0 < ‖tailCoordinates z‖)
    (hlatitude : bandLatitude p = leadingCoordinate z)
    (hdirection : halfCircleDirection p.1 = normalizedTailDirection z) :
    projectiveBandSpherePoint p = z := by
  -- Replace radius and direction by the coordinates of `z`, then cancel normalization.
  apply Subtype.ext
  calc
    (projectiveBandSpherePoint p : EuclideanSpace ℝ (Fin 3)) =
        prependCoordinate (bandLatitude p)
          (bandRadius p • halfCircleDirection p.1) := rfl
    _ = prependCoordinate (leadingCoordinate z)
        (‖tailCoordinates z‖ • normalizedTailDirection z) := by
      rw [hlatitude, hdirection, bandRadius_eq_tailCoordinates_norm p z hlatitude]
    _ = prependCoordinate (leadingCoordinate z) (tailCoordinates z) := by
      rw [normalizedTailDirection, smul_smul,
        mul_inv_cancel₀ htail.ne', one_smul]
    _ = z := prependCoordinate_leading_tail z

/-- Helper for Exercise 74.5: the square parametrization covers the complement of the
chosen projective disk. -/
private lemma projectiveBandMap_surjective : Function.Surjective projectiveBandMap := by
  -- Choose a spherical representative and use the disk-complement criterion to bound it.
  rintro ⟨q, hq⟩
  obtain ⟨z, hz⟩ := RealProjectivePlane.quotientMap_surjective q
  have hzOutside : RealProjectivePlane.quotientMap z ∉ projectiveDisk := by
    rwa [hz]
  have hzBounds : -((3 : ℝ) / 5) ≤ leadingCoordinate z ∧
      leadingCoordinate z ≤ (3 : ℝ) / 5 := by
    rw [quotientMap_not_mem_projectiveDisk_iff, abs_le] at hzOutside
    exact hzOutside
  have htail : 0 < ‖tailCoordinates z‖ :=
    tailCoordinates_norm_pos_of_abs_le z (abs_le.mpr hzBounds)
  obtain ⟨u, hu | hu⟩ := exists_halfCircleDirection_eq_or_eq_neg
    (normalizedTailDirection z) (normalizedTailDirection_norm z htail)
  · -- If the selected semicircle contains the tail direction, retain the representative.
    let p : UnitSquare := (u, bandTransverse (leadingCoordinate z) hzBounds)
    have hlatitude : bandLatitude p = leadingCoordinate z := by
      simpa only [p] using
        bandLatitude_bandTransverse u (leadingCoordinate z) hzBounds
    have hpoint : projectiveBandSpherePoint p = z :=
      projectiveBandSpherePoint_eq_of_coordinates p z htail hlatitude hu
    refine ⟨p, Subtype.ext ?_⟩
    calc
      RealProjectivePlane.quotientMap (projectiveBandSpherePoint p) =
          RealProjectivePlane.quotientMap z := congrArg _ hpoint
      _ = q := hz
  · -- Otherwise negate the representative; projective space identifies the antipodal pair.
    have hzNegBounds : -((3 : ℝ) / 5) ≤ -leadingCoordinate z ∧
        -leadingCoordinate z ≤ (3 : ℝ) / 5 := by
      constructor <;> nlinarith [hzBounds.1, hzBounds.2]
    let p : UnitSquare := (u, bandTransverse (-leadingCoordinate z) hzNegBounds)
    have htailNeg : 0 < ‖tailCoordinates (-z)‖ := by
      simpa only [coe_neg_sphere, tailCoordinates_neg, norm_neg] using htail
    have hlatitude : bandLatitude p = leadingCoordinate (-z) := by
      calc
        bandLatitude p = -leadingCoordinate z := by
          simpa only [p] using
            bandLatitude_bandTransverse u (-leadingCoordinate z) hzNegBounds
        _ = leadingCoordinate (-z) := (leadingCoordinate_neg z).symm
    have hdirection : halfCircleDirection p.1 = normalizedTailDirection (-z) := by
      rw [normalizedTailDirection_neg]
      exact hu
    have hpoint : projectiveBandSpherePoint p = -z :=
      projectiveBandSpherePoint_eq_of_coordinates p (-z) htailNeg hlatitude hdirection
    refine ⟨p, Subtype.ext ?_⟩
    calc
      RealProjectivePlane.quotientMap (projectiveBandSpherePoint p) =
          RealProjectivePlane.quotientMap (-z) := congrArg _ hpoint
      _ = RealProjectivePlane.quotientMap z := RealProjectivePlane.quotientMap_neg z
      _ = q := hz

/-- Helper for Exercise 74.5: the spherical band parametrization is injective before
passing to antipodal projective classes. -/
private lemma projectiveBandSpherePoint_injective :
    Function.Injective projectiveBandSpherePoint := by
  -- The leading coordinate recovers the transverse parameter.
  intro p q hpq
  have hlatitude : bandLatitude p = bandLatitude q := by
    calc
      bandLatitude p = leadingCoordinate (projectiveBandSpherePoint p) :=
        (projectiveBandSpherePoint_leading p).symm
      _ = leadingCoordinate (projectiveBandSpherePoint q) :=
        congrArg (fun z : ProjectiveSphere ↦ leadingCoordinate z) hpq
      _ = bandLatitude q := projectiveBandSpherePoint_leading q
  have hsecond : p.2 = q.2 := by
    apply Subtype.ext
    unfold bandLatitude at hlatitude
    nlinarith
  -- Equal positive radii can be cancelled from the tail-coordinate equality.
  have hradius : bandRadius p = bandRadius q := by
    unfold bandRadius
    rw [hlatitude]
  have htail := congrArg
    (fun z : ProjectiveSphere ↦ tailCoordinates z) hpq
  rw [projectiveBandSpherePoint_tail p,
    projectiveBandSpherePoint_tail q, hradius] at htail
  have hdirection : halfCircleDirection p.1 = halfCircleDirection q.1 :=
    smul_right_injective _ (bandRadius_pos q).ne' htail
  exact Prod.ext (halfCircleDirection_injective hdirection) hsecond

/-- Helper for Exercise 74.5: one directed Möbius edge gluing produces antipodal
spherical band points. -/
private lemma projectiveBandSpherePoint_eq_neg_of_glue {p q : UnitSquare}
    (hpq : mobiusBandGlue p q) :
    projectiveBandSpherePoint q = -projectiveBandSpherePoint p := by
  -- Convert the directed gluing into endpoint and reflected-transverse coordinates.
  rw [mobiusBandGlue_iff] at hpq
  have hqSecond : q.2 = unitInterval.symm p.2 := by
    apply unitInterval.symm_bijective.injective
    rw [unitInterval.symm_symm]
    exact hpq.2.2.symm
  have hlatitude : bandLatitude q = -bandLatitude p := by
    calc
      bandLatitude q = bandLatitude (p.1, q.2) := rfl
      _ = bandLatitude (p.1, unitInterval.symm p.2) := by rw [hqSecond]
      _ = -bandLatitude p := bandLatitude_symm p.1 p.2
  have hradius : bandRadius q = bandRadius p := by
    unfold bandRadius
    rw [hlatitude]
    ring_nf
  have hdirection : halfCircleDirection q.1 = -halfCircleDirection p.1 :=
    (halfCircleDirection_eq_neg_iff p.1 q.1).mpr
      (Or.inl ⟨hpq.1, hpq.2.1⟩)
  -- Reassemble the negated head and tail into the antipodal ambient vector.
  apply Subtype.ext
  calc
    (projectiveBandSpherePoint q : EuclideanSpace ℝ (Fin 3)) =
        prependCoordinate (bandLatitude q)
          (bandRadius q • halfCircleDirection q.1) := rfl
    _ = prependCoordinate (-bandLatitude p)
        (-(bandRadius p • halfCircleDirection p.1)) := by
      rw [hlatitude, hradius, hdirection, smul_neg]
    _ = -prependCoordinate (bandLatitude p)
        (bandRadius p • halfCircleDirection p.1) :=
      prependCoordinate_neg _ _
    _ = -(projectiveBandSpherePoint p : EuclideanSpace ℝ (Fin 3)) := rfl

/-- Helper for Exercise 74.5: antipodal spherical band points are exactly the two
orientations of the Möbius edge gluing. -/
private lemma projectiveBandSpherePoint_eq_neg_iff (p q : UnitSquare) :
    projectiveBandSpherePoint q = -projectiveBandSpherePoint p ↔
      mobiusBandGlue p q ∨ mobiusBandGlue q p := by
  constructor
  · intro hpq
    -- Compare head coordinates to recover reflection in the transverse interval.
    have hambient := congrArg Subtype.val hpq
    have hlatitude : bandLatitude q = -bandLatitude p := by
      have hleading := congrArg leadingCoordinate hambient
      simpa only [projectiveBandSpherePoint_leading, coe_neg_sphere,
        leadingCoordinate_neg] using hleading
    have hsecond : q.2 = unitInterval.symm p.2 := by
      apply Subtype.ext
      rw [unitInterval.coe_symm_eq]
      unfold bandLatitude at hlatitude
      nlinarith
    -- Equal radii let the antipodal tail equation reduce to the semicircle endpoint rule.
    have hradius : bandRadius q = bandRadius p := by
      unfold bandRadius
      rw [hlatitude]
      ring_nf
    have htail : bandRadius q • halfCircleDirection q.1 =
        -(bandRadius p • halfCircleDirection p.1) := by
      have htailCoordinates := congrArg tailCoordinates hambient
      simpa only [projectiveBandSpherePoint_tail, coe_neg_sphere,
        tailCoordinates_neg] using htailCoordinates
    have hscaled : bandRadius p • halfCircleDirection q.1 =
        bandRadius p • (-halfCircleDirection p.1) := by
      rw [smul_neg]
      simpa only [hradius] using htail
    have hdirection : halfCircleDirection q.1 = -halfCircleDirection p.1 :=
      smul_right_injective _ (bandRadius_pos p).ne' hscaled
    rcases (halfCircleDirection_eq_neg_iff p.1 q.1).mp hdirection with
      ⟨hpZero, hqOne⟩ | ⟨hpOne, hqZero⟩
    · left
      rw [mobiusBandGlue_iff]
      refine ⟨hpZero, hqOne, ?_⟩
      rw [hsecond, unitInterval.symm_symm]
    · right
      rw [mobiusBandGlue_iff]
      exact ⟨hqZero, hpOne, hsecond⟩
  · rintro (hpq | hqp)
    · exact projectiveBandSpherePoint_eq_neg_of_glue hpq
    · have hreverse := projectiveBandSpherePoint_eq_neg_of_glue hqp
      simpa only [neg_neg] using (congrArg Neg.neg hreverse).symm

/-- Helper for Exercise 74.5: two square parameters have the same projective-band image
exactly in the three Möbius normal-form cases. -/
private lemma projectiveBandMap_fiber_iff (p q : UnitSquare) :
    projectiveBandMap p = projectiveBandMap q ↔
      p = q ∨ mobiusBandGlue p q ∨ mobiusBandGlue q p := by
  constructor
  · intro hpq
    -- Projective equality says that the two selected sphere representatives are equal
    -- or antipodal.
    have hquotient :
        RealProjectivePlane.quotientMap (projectiveBandSpherePoint p) =
          RealProjectivePlane.quotientMap (projectiveBandSpherePoint q) :=
      congrArg Subtype.val hpq
    rcases (RealProjectivePlane.quotientMap_eq_iff
      (projectiveBandSpherePoint p) (projectiveBandSpherePoint q)).mp hquotient with
      hequal | hantipodal
    · exact Or.inl (projectiveBandSpherePoint_injective hequal.symm)
    · exact Or.inr
        ((projectiveBandSpherePoint_eq_neg_iff p q).mp hantipodal)
  · rintro (rfl | hpq | hqp)
    · rfl
    · apply Subtype.ext
      exact (RealProjectivePlane.quotientMap_eq_iff
        (projectiveBandSpherePoint p) (projectiveBandSpherePoint q)).mpr
          (Or.inr ((projectiveBandSpherePoint_eq_neg_iff p q).mpr (Or.inl hpq)))
    · apply Subtype.ext
      exact (RealProjectivePlane.quotientMap_eq_iff
        (projectiveBandSpherePoint p) (projectiveBandSpherePoint q)).mpr
          (Or.inr ((projectiveBandSpherePoint_eq_neg_iff p q).mpr (Or.inr hqp)))

/-- Helper for Exercise 74.5: the square-to-projective-band map is a quotient map. -/
private lemma projectiveBandMap_isQuotientMap :
    Topology.IsQuotientMap projectiveBandMap := by
  -- A continuous surjection from the compact square to the Hausdorff complement is quotient.
  exact Topology.IsQuotientMap.of_surjective_continuous
    projectiveBandMap_surjective continuous_projectiveBandMap

/-- Helper for Exercise 74.5: the projective-band parametrization bundled as a
continuous map. -/
private def projectiveBandMapContinuous :
    C(UnitSquare, Set.compl projectiveDisk) :=
  ⟨projectiveBandMap, continuous_projectiveBandMap⟩

/-- Helper for Exercise 74.5: the Möbius setoid is the kernel of the projective-band
parametrization. -/
private lemma mobiusBandSetoid_iff_projectiveBandMapKernel (p q : UnitSquare) :
    Relation.EqvGen.setoid mobiusBandGlue p q ↔
      Setoid.ker projectiveBandMapContinuous p q := by
  -- Both relations have the same equality/gluing/reverse-gluing normal form.
  change Relation.EqvGen.setoid mobiusBandGlue p q ↔
    projectiveBandMap p = projectiveBandMap q
  rw [mobiusBandSetoid_rel_iff, projectiveBandMap_fiber_iff]

/-- Helper for Exercise 74.5: the Möbius quotient is homeomorphic to the complement
of the chosen projective disk. -/
private def mobiusBandProjectiveDiskComplHomeomorph :
    MobiusBand ≃ₜ Set.compl projectiveDisk :=
  (Homeomorph.Quotient.congrRight
    mobiusBandSetoid_iff_projectiveBandMapKernel).trans
      projectiveBandMap_isQuotientMap.homeomorph

/-- Exercise 74.5: The Möbius band is homeomorphic to the complement of an open
topological disk in the real projective plane. -/
theorem mobiusBand_homeomorphic_projectivePlaneMinusDisk :
    ∃ U : Set RealProjectivePlane,
      IsOpen U ∧
        Nonempty (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ U) ∧
        Nonempty (MobiusBand ≃ₜ Set.compl U) := by
  -- Choose the cap image, then supply the disk chart and quotient comparison homeomorphisms.
  exact ⟨projectiveDisk, projectiveDisk_isOpen,
    ⟨unitBallProjectiveDiskHomeomorph⟩,
    ⟨mobiusBandProjectiveDiskComplHomeomorph⟩⟩
