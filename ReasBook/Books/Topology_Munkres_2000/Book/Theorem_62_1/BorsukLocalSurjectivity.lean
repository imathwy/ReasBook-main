module

public import Topology_Munkres_2000.Book.Exercise_55_2
public import Topology_Munkres_2000.Book.Definition_55_2.Nonvanishing
public import Topology_Munkres_2000.Book.Theorem_57_6
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Compact

noncomputable section

public section

open scoped unitInterval

namespace InvarianceOfDomainSupport

/-- Helper for Theorem 62.1: evaluate a continuous homotopy-shaped map at time zero. -/
private def homotopyAtZero {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(unitInterval × X, Y)) : C(X, Y) :=
  ⟨fun x ↦ F (0, x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Helper for Theorem 62.1: evaluate a continuous homotopy-shaped map at time one. -/
private def homotopyAtOne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(unitInterval × X, Y)) : C(X, Y) :=
  ⟨fun x ↦ F (1, x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Helper for Theorem 62.1: nonvanishing values lie in the punctured space. -/
private lemma nonvanishing_mem_compl {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : C(X, E)) (hF : F.IsNonvanishing) (x : X) :
    F x ∈ ({0}ᶜ : Set E) := by
  -- Complement membership is the same as inequality with zero.
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hF x

/-- Helper for Theorem 62.1: radial normalization of a nonvanishing map is continuous. -/
private lemma continuous_radialDirection {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : F.IsNonvanishing) :
    Continuous (fun x ↦
      ((homeomorphUnitSphereProd E) ⟨F x, nonvanishing_mem_compl F hF x⟩).1) := by
  -- Lift through the punctured space before taking the polar direction coordinate.
  exact continuous_fst.comp ((homeomorphUnitSphereProd E).continuous.comp
    (Continuous.subtype_mk F.continuous (nonvanishing_mem_compl F hF)))

/-- Helper for Theorem 62.1: radial normalization of a nonvanishing continuous map. -/
private def radialDirection {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : C(X, E)) (hF : F.IsNonvanishing) :
    C(X, Metric.sphere (0 : E) 1) :=
  ⟨fun x ↦
      ((homeomorphUnitSphereProd E) ⟨F x, nonvanishing_mem_compl F hF x⟩).1,
    continuous_radialDirection F hF⟩

/-- Helper for Theorem 62.1: radial direction is ambient normalization by the norm. -/
private lemma radialDirection_coe {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : C(X, E)) (hF : F.IsNonvanishing) (x : X) :
    (radialDirection F hF x : E) = ‖F x‖⁻¹ • F x := by
  -- Read the direction-coordinate formula from polar coordinates.
  exact homeomorphUnitSphereProd_apply_fst_coe E
    ⟨F x, nonvanishing_mem_compl F hF x⟩

/-- Helper for Theorem 62.1: radial normalization carries a nonvanishing vector
homotopy to a homotopy of its endpoint directions. -/
private lemma radialDirection_homotopy {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(unitInterval × X, E))
    (hF : F.IsNonvanishing) :
    (radialDirection (homotopyAtZero F) (fun x ↦ hF (0, x))).Homotopic
      (radialDirection (homotopyAtOne F) (fun x ↦ hF (1, x))) := by
  -- The normalized map itself supplies the homotopy; both endpoint laws are pointwise.
  refine ⟨{
    toFun := radialDirection F hF
    continuous_toFun := (radialDirection F hF).continuous
    map_zero_left := ?_
    map_one_left := ?_
  }⟩
  · intro x
    rfl
  · intro x
    rfl

/-- Helper for Theorem 62.1: radial normalization preserves oddness. -/
private lemma radialDirection_odd {X E : Type*} [TopologicalSpace X] [Neg X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : F.IsNonvanishing) (hOdd : Function.Odd F) :
    Function.Odd (radialDirection F hF) := by
  -- Compare normalized sphere points through their ambient vectors.
  intro x
  have normalizedNeg :
      ‖F (-x)‖⁻¹ • F (-x) = -(‖F x‖⁻¹ • F x) := by
    rw [hOdd x, norm_neg, smul_neg]
  apply Subtype.ext
  calc
    (radialDirection F hF (-x) : E) = ‖F (-x)‖⁻¹ • F (-x) :=
      radialDirection_coe F hF (-x)
    _ = -(‖F x‖⁻¹ • F x) := normalizedNeg
    _ = -(radialDirection F hF x : E) :=
      congrArg Neg.neg (radialDirection_coe F hF x).symm
    _ = ((-(radialDirection F hF x) : Metric.sphere (0 : E) 1) : E) := rfl

/-- Helper for Theorem 62.1: an inward antipodal multiple of a unit vector lies
in the closed unit ball. -/
private lemma inwardAntipode_mem {d : ℕ} (p : unitInterval × StandardSphere d) :
    -(p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (d + 1))) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by
  -- Its norm is the interval parameter, hence at most one.
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg p.1.property.1,
    mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
  exact p.1.property.2

/-- Helper for Theorem 62.1: the inward antipodal radial point in the closed ball. -/
private def inwardAntipode {d : ℕ}
    (p : unitInterval × StandardSphere d) : ClosedUnitBall d :=
  ⟨-(p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (d + 1))), inwardAntipode_mem p⟩

/-- Helper for Theorem 62.1: inward antipodal radial motion is continuous. -/
private lemma continuous_inwardAntipode {d : ℕ} :
    Continuous (inwardAntipode : unitInterval × StandardSphere d → ClosedUnitBall d) := by
  -- Continuity is checked in the ambient Euclidean space.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Theorem 62.1: displacement of an embedded boundary from the
image of the center. -/
private lemma continuous_boundaryDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1)))) :
    Continuous (fun x : StandardSphere d ↦ F (StandardSphere.toBall d x) - F 0) := by
  -- Compose with the boundary inclusion and subtract the constant center value.
  exact (F.continuous.comp (StandardSphere.toBall d).continuous).sub continuous_const

/-- Helper for Theorem 62.1: displacement of an embedded boundary from the
image of the center. -/
private def boundaryDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1)))) :
    C(StandardSphere d, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun x ↦ F (StandardSphere.toBall d x) - F 0,
    continuous_boundaryDisplacement F⟩

/-- Helper for Theorem 62.1: antipodal boundary displacement of an embedded ball. -/
private lemma continuous_antipodalDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1)))) :
    Continuous (fun x : StandardSphere d ↦
      F (StandardSphere.toBall d x) - F (StandardSphere.toBall d (-x))) := by
  -- Both boundary evaluations are continuous, including after antipodal reflection.
  exact (F.continuous.comp (StandardSphere.toBall d).continuous).sub
    (F.continuous.comp ((StandardSphere.toBall d).continuous.comp continuous_neg))

/-- Helper for Theorem 62.1: antipodal boundary displacement of an embedded ball. -/
private def antipodalDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1)))) :
  C(StandardSphere d, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun x ↦ F (StandardSphere.toBall d x) - F (StandardSphere.toBall d (-x)),
    continuous_antipodalDisplacement F⟩

/-- Helper for Theorem 62.1: the boundary-to-inward-antipode displacement homotopy. -/
private lemma continuous_boundaryDisplacementHomotopy {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1)))) :
    Continuous (fun p : unitInterval × StandardSphere d ↦
      F (StandardSphere.toBall d p.2) - F (inwardAntipode p)) := by
  -- Compose the two continuous ball-valued motions with `F` and subtract.
  exact (F.continuous.comp ((StandardSphere.toBall d).continuous.comp continuous_snd)).sub
    (F.continuous.comp continuous_inwardAntipode)

/-- Helper for Theorem 62.1: the boundary-to-inward-antipode displacement homotopy. -/
private def boundaryDisplacementHomotopy {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1)))) :
  C(unitInterval × StandardSphere d, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun p ↦ F (StandardSphere.toBall d p.2) - F (inwardAntipode p),
    continuous_boundaryDisplacementHomotopy F⟩

/-- Helper for Theorem 62.1: a boundary point differs from every inward
antipodal radial point. -/
private lemma sphere_ne_inwardAntipode {d : ℕ}
    (p : unitInterval × StandardSphere d) :
    StandardSphere.toBall d p.2 ≠ inwardAntipode p := by
  -- Equality would force a unit norm to equal a nonpositive scalar multiple.
  intro h
  have hAmbient := congrArg
    (fun z : ClosedUnitBall d ↦ (z : EuclideanSpace ℝ (Fin (d + 1)))) h
  have hInner := congrArg
    (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦
      inner ℝ z (p.2 : EuclideanSpace ℝ (Fin (d + 1)))) hAmbient
  simp only [StandardSphere.toBall_apply, inwardAntipode, Subtype.coe_mk,
    real_inner_smul_left, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp p.2.property, one_pow, mul_one] at hInner
  have htNonneg : 0 ≤ (p.1 : ℝ) := p.1.property.1
  linarith

/-- Helper for Theorem 62.1: injectivity makes every vector in the inward
boundary-displacement homotopy nonzero. -/
private lemma boundaryDisplacementHomotopy_isNonvanishing {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (hF : Function.Injective F) : (boundaryDisplacementHomotopy F).IsNonvanishing := by
  -- A zero displacement would identify the two distinct ball points.
  intro p hp
  apply sphere_ne_inwardAntipode p
  apply hF
  exact sub_eq_zero.mp hp

/-- Helper for Theorem 62.1: injectivity makes the center displacement nonzero. -/
private lemma boundaryDisplacement_isNonvanishing {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (hF : Function.Injective F) : (boundaryDisplacement F).IsNonvanishing := by
  -- A zero displacement would identify a nonzero boundary point with the center.
  intro x hx
  have hBall := hF (sub_eq_zero.mp hx)
  apply StandardSphere.ne_zero x
  exact congrArg Subtype.val hBall

/-- Helper for Theorem 62.1: injectivity makes the antipodal displacement nonzero. -/
private lemma antipodalDisplacement_isNonvanishing {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (hF : Function.Injective F) : (antipodalDisplacement F).IsNonvanishing := by
  -- A zero displacement would identify the two antipodal boundary points.
  intro x hx
  apply sphere_ne_inwardAntipode (1, x)
  apply hF
  calc
    F (StandardSphere.toBall d x) = F (StandardSphere.toBall d (-x)) :=
      sub_eq_zero.mp hx
    _ = F (inwardAntipode (1, x)) := by
      apply congrArg F
      apply Subtype.ext
      simp [inwardAntipode, StandardSphere.toBall_apply]

/-- Helper for Theorem 62.1: the normalized antipodal displacement is odd. -/
private lemma antipodalDirection_odd {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (hF : Function.Injective F) :
    Function.Odd
      (radialDirection (antipodalDisplacement F)
        (antipodalDisplacement_isNonvanishing F hF)) := by
  -- Swapping an antipodal pair negates its displacement.
  apply radialDirection_odd
  intro x
  simp only [antipodalDisplacement, ContinuousMap.coe_mk, neg_neg, neg_sub]

/-- Helper for Theorem 62.1: the normalized displacement of an embedded unit-ball
boundary from the image of its center is not nullhomotopic. -/
private lemma closedUnitBall_boundaryDirection_not_nullhomotopic {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (hF : Function.Injective F) :
    ¬ (radialDirection (boundaryDisplacement F)
      (boundaryDisplacement_isNonvanishing F hF)).Nullhomotopic := by
  -- Normalize the inward radial homotopy, then identify its two endpoint maps.
  have hHomotopy := radialDirection_homotopy (boundaryDisplacementHomotopy F)
    (boundaryDisplacementHomotopy_isNonvanishing F hF)
  have hZero : homotopyAtZero (boundaryDisplacementHomotopy F) =
      boundaryDisplacement F := by
    apply ContinuousMap.ext
    intro x
    have hInwardZero : inwardAntipode (0, x) = (0 : ClosedUnitBall d) := by
      apply Subtype.ext
      norm_num [inwardAntipode]
    simp only [homotopyAtZero, boundaryDisplacementHomotopy, boundaryDisplacement,
      ContinuousMap.coe_mk, hInwardZero]
  have hOne : homotopyAtOne (boundaryDisplacementHomotopy F) =
      antipodalDisplacement F := by
    apply ContinuousMap.ext
    intro x
    have hInwardOne : inwardAntipode (1, x) = StandardSphere.toBall d (-x) := by
      apply Subtype.ext
      simp [inwardAntipode, StandardSphere.toBall_apply]
    simp only [homotopyAtOne, boundaryDisplacementHomotopy, antipodalDisplacement,
      ContinuousMap.coe_mk, hInwardOne]
  have hZeroDirection :
      radialDirection (homotopyAtZero (boundaryDisplacementHomotopy F))
          (fun x ↦ boundaryDisplacementHomotopy_isNonvanishing F hF (0, x)) =
        radialDirection (boundaryDisplacement F)
          (boundaryDisplacement_isNonvanishing F hF) := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rw [radialDirection_coe, radialDirection_coe,
      congrArg (fun G : C(StandardSphere d, EuclideanSpace ℝ (Fin (d + 1))) ↦ G x) hZero]
  have hOneDirection :
      radialDirection (homotopyAtOne (boundaryDisplacementHomotopy F))
          (fun x ↦ boundaryDisplacementHomotopy_isNonvanishing F hF (1, x)) =
        radialDirection (antipodalDisplacement F)
          (antipodalDisplacement_isNonvanishing F hF) := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rw [radialDirection_coe, radialDirection_coe,
      congrArg (fun G : C(StandardSphere d, EuclideanSpace ℝ (Fin (d + 1))) ↦ G x) hOne]
  rw [hZeroDirection, hOneDirection] at hHomotopy
  -- A nullhomotopy at the center endpoint would transfer to the forbidden odd endpoint.
  intro hNull
  exact StandardSphere.oddSelfMap_not_nullhomotopic d _
    (antipodalDirection_odd F hF) (hNull.of_homotopic hHomotopy)

/-- Helper for Theorem 62.1: displacement from a fixed target point on the closed ball. -/
private lemma continuous_closedBallDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    Continuous (fun x ↦ F x - y) := by
  -- Subtracting a fixed target point preserves continuity.
  exact F.continuous.sub continuous_const

/-- Helper for Theorem 62.1: displacement from a fixed target point on the closed ball. -/
private def closedBallDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun x ↦ F x - y, continuous_closedBallDisplacement F y⟩

/-- Helper for Theorem 62.1: omission of a point makes its closed-ball displacement
nonvanishing. -/
private lemma closedBallDisplacement_isNonvanishing {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (y : EuclideanSpace ℝ (Fin (d + 1))) (hy : y ∉ Set.range F) :
    (closedBallDisplacement F y).IsNonvanishing := by
  -- A zero displacement is exactly a preimage of the omitted point.
  intro x hx
  exact hy ⟨x, sub_eq_zero.mp hx⟩

/-- Helper for Theorem 62.1: boundary displacement while the target point moves
linearly to the image of the center. -/
private lemma continuous_movingCenterDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    Continuous (fun p : unitInterval × StandardSphere d ↦
      F (StandardSphere.toBall d p.2) -
        AffineMap.lineMap y (F 0) (p.1 : ℝ)) := by
  -- Boundary evaluation and the affine motion of the target point are continuous.
  fun_prop (disch := assumption)

/-- Helper for Theorem 62.1: boundary displacement while the target point moves
linearly to the image of the center. -/
private def movingCenterDisplacement {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
  C(unitInterval × StandardSphere d, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun p ↦ F (StandardSphere.toBall d p.2) -
      AffineMap.lineMap y (F 0) (p.1 : ℝ), continuous_movingCenterDisplacement F y⟩

/-- Helper for Theorem 62.1: a boundary image avoids every point on a segment
contained in a boundary-avoiding convex set. -/
private lemma movingCenterDisplacement_isNonvanishing {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (y : EuclideanSpace ℝ (Fin (d + 1))) {V : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hV : Convex ℝ V) (hy : y ∈ V) (hcenter : F 0 ∈ V)
    (havoid : V ⊆ (Set.range (F.comp (StandardSphere.toBall d)))ᶜ) :
    (movingCenterDisplacement F y).IsNonvanishing := by
  -- A zero displacement would put a boundary value on the protected segment.
  intro p hp
  have hsegment : AffineMap.lineMap y (F 0) (p.1 : ℝ) ∈ V :=
    hV.lineMap_mem hy hcenter p.1.property
  apply havoid hsegment
  refine ⟨p.2, ?_⟩
  exact sub_eq_zero.mp hp

/-- Helper for Theorem 62.1: an injective map of a closed unit ball sends its
interior onto a neighborhood of the image of the center. -/
lemma closedUnitBall_center_imageNeighborhood {d : ℕ}
    (F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))))
    (hF : Function.Injective F) :
    ∃ ε > 0, Metric.ball (F 0) ε ⊆
      F '' {x : ClosedUnitBall d |
        (x : EuclideanSpace ℝ (Fin (d + 1))) ∈
          Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1} := by
  let boundaryMap := F.comp (StandardSphere.toBall d)
  have hBoundaryClosed : IsClosed (Set.range boundaryMap) := by
    -- The continuous image of the compact sphere is compact, hence closed.
    exact (isCompact_range boundaryMap.continuous).isClosed
  have hCenterAvoidsBoundary : F 0 ∈ (Set.range boundaryMap)ᶜ := by
    intro hRange
    obtain ⟨x, hx⟩ := hRange
    have hBallEq : (0 : ClosedUnitBall d) = StandardSphere.toBall d x := by
      apply hF
      exact hx.symm
    have hAmbient := congrArg
      (fun z : ClosedUnitBall d ↦ (z : EuclideanSpace ℝ (Fin (d + 1)))) hBallEq
    apply StandardSphere.ne_zero x
    exact hAmbient.symm
  obtain ⟨ε, hε, hAvoid⟩ :=
    Metric.isOpen_iff.mp hBoundaryClosed.isOpen_compl (F 0) hCenterAvoidsBoundary
  refine ⟨ε, hε, ?_⟩
  intro y hy
  -- If a nearby point were omitted by the interior, boundary avoidance would
  -- make it omitted by the whole closed ball.
  by_contra hyInterior
  have hyNotRange : y ∉ Set.range F := by
    rintro ⟨x, rfl⟩
    have hxUnion : (x : EuclideanSpace ℝ (Fin (d + 1))) ∈
        Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 ∪
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by
      rw [Metric.ball_union_sphere]
      exact x.property
    rcases hxUnion with hxInterior | hxBoundary
    · exact hyInterior ⟨x, hxInterior, rfl⟩
    · apply hAvoid hy
      exact ⟨⟨x, hxBoundary⟩, rfl⟩
  let closedDirection := radialDirection (closedBallDisplacement F y)
    (closedBallDisplacement_isNonvanishing F y hyNotRange)
  have hClosedNull : closedDirection.Nullhomotopic := by
    letI : ContractibleSpace (ClosedUnitBall d) :=
      Metric.contractibleSpace_closedBall zero_le_one
    exact (id_nullhomotopic (ClosedUnitBall d)).comp_right closedDirection
  have hBoundaryAtYNull :
      (radialDirection (homotopyAtZero (movingCenterDisplacement F y))
        (fun x ↦ movingCenterDisplacement_isNonvanishing F y (convex_ball (F 0) ε)
          hy (Metric.mem_ball_self hε) hAvoid (0, x))).Nullhomotopic := by
    -- Restrict the nullhomotopy over the ball to its boundary and identify values.
    have hRestricted := hClosedNull.comp_left (StandardSphere.toBall d)
    have hMaps : closedDirection.comp (StandardSphere.toBall d) =
        radialDirection (homotopyAtZero (movingCenterDisplacement F y))
          (fun x ↦ movingCenterDisplacement_isNonvanishing F y (convex_ball (F 0) ε)
            hy (Metric.mem_ball_self hε) hAvoid (0, x)) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      rw [ContinuousMap.comp_apply, radialDirection_coe, radialDirection_coe]
      have hVector :
          closedBallDisplacement F y (StandardSphere.toBall d x) =
            homotopyAtZero (movingCenterDisplacement F y) x := by
        simp [closedBallDisplacement, homotopyAtZero, movingCenterDisplacement,
          AffineMap.lineMap_apply]
      rw [hVector]
    rwa [hMaps] at hRestricted
  have hMoving := radialDirection_homotopy (movingCenterDisplacement F y)
    (movingCenterDisplacement_isNonvanishing F y (convex_ball (F 0) ε)
      hy (Metric.mem_ball_self hε) hAvoid)
  have hOne : homotopyAtOne (movingCenterDisplacement F y) =
      boundaryDisplacement F := by
    ext x
    simp [homotopyAtOne, movingCenterDisplacement, boundaryDisplacement,
      AffineMap.lineMap_apply]
  have hBoundaryMoving :
      (radialDirection (homotopyAtZero (movingCenterDisplacement F y))
        (fun x ↦ movingCenterDisplacement_isNonvanishing F y (convex_ball (F 0) ε)
          hy (Metric.mem_ball_self hε) hAvoid (0, x))).Homotopic
        (radialDirection (boundaryDisplacement F)
          (boundaryDisplacement_isNonvanishing F hF)) := by
    simpa only [hOne] using hMoving
  -- Moving the omitted point to the center transfers nullhomotopy to the
  -- forbidden normalized center displacement.
  exact closedUnitBall_boundaryDirection_not_nullhomotopic F hF
    (hBoundaryAtYNull.of_homotopic hBoundaryMoving)

/-- Helper for Theorem 62.1: affine rescaling carries the closed unit ball into
a closed ball of nonnegative radius. -/
private lemma affineClosedUnitBall_mem_closedBall {d : ℕ}
    (c : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (hr : 0 ≤ r)
    (z : ClosedUnitBall d) :
    c + r • (z : EuclideanSpace ℝ (Fin (d + 1))) ∈ Metric.closedBall c r := by
  -- The distance from the center is `r * ‖z‖`, bounded by `r` on the unit ball.
  have hzNorm : ‖(z : EuclideanSpace ℝ (Fin (d + 1)))‖ ≤ 1 := by
    simpa only [mem_closedBall_zero_iff] using z.property
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hr]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hzNorm hr

/-- Helper for Theorem 62.1: affine rescaling carries the open unit ball into
the corresponding positive-radius open ball. -/
private lemma affineClosedUnitBall_mem_ball {d : ℕ}
    (c : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (hr : 0 < r)
    (z : ClosedUnitBall d)
    (hz : (z : EuclideanSpace ℝ (Fin (d + 1))) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) :
    c + r • (z : EuclideanSpace ℝ (Fin (d + 1))) ∈ Metric.ball c r := by
  -- Strict norm control is preserved by multiplication by the positive radius.
  have hzNorm : ‖(z : EuclideanSpace ℝ (Fin (d + 1)))‖ < 1 := by
    simpa only [mem_ball_zero_iff] using hz
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hzNorm hr

/-- Helper for Theorem 62.1: affine rescaling lands in every ambient domain
that contains the corresponding closed ball. -/
private lemma affineClosedUnitBall_mem_domain {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (x : U) (r : ℝ) (hr : 0 ≤ r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U)
    (z : ClosedUnitBall d) :
    (x : EuclideanSpace ℝ (Fin (d + 1))) + r •
      (z : EuclideanSpace ℝ (Fin (d + 1))) ∈ U := by
  -- First enter the closed ball, then use the supplied domain inclusion.
  apply hclosed
  exact affineClosedUnitBall_mem_closedBall (d := d)
    (x : EuclideanSpace ℝ (Fin (d + 1))) r hr z

/-- Helper for Theorem 62.1: affine rescaling of the closed unit ball into an
ambient domain containing the target closed ball. -/
private def affineClosedUnitBallInto {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (x : U) (r : ℝ) (hr : 0 ≤ r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U) :
    ClosedUnitBall d → U :=
  fun z ↦ ⟨(x : EuclideanSpace ℝ (Fin (d + 1))) + r •
      (z : EuclideanSpace ℝ (Fin (d + 1))),
    affineClosedUnitBall_mem_domain x r hr hclosed z⟩

/-- Helper for Theorem 62.1: the ambient value of affine closed-unit-ball
rescaling is its defining affine formula. -/
private lemma affineClosedUnitBallInto_coe {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (x : U) (r : ℝ) (hr : 0 ≤ r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U)
    (z : ClosedUnitBall d) :
    ((affineClosedUnitBallInto x r hr hclosed z : U) :
      EuclideanSpace ℝ (Fin (d + 1))) =
        (x : EuclideanSpace ℝ (Fin (d + 1))) + r •
          (z : EuclideanSpace ℝ (Fin (d + 1))) := rfl

/-- Helper for Theorem 62.1: affine closed-unit-ball rescaling is continuous. -/
private lemma continuous_affineClosedUnitBallInto {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (x : U) (r : ℝ) (hr : 0 ≤ r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U) :
    Continuous (affineClosedUnitBallInto x r hr hclosed) := by
  -- Continuity is checked on the ambient affine formula.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Theorem 62.1: positive-radius affine closed-unit-ball rescaling is injective. -/
private lemma affineClosedUnitBallInto_injective {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (x : U) (r : ℝ) (hr : 0 < r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U) :
    Function.Injective (affineClosedUnitBallInto x r hr.le hclosed) := by
  -- Cancel the translation and then the nonzero scalar factor.
  intro a b hab
  apply Subtype.ext
  apply smul_right_injective (EuclideanSpace ℝ (Fin (d + 1))) hr.ne'
  have hAmbient := congrArg Subtype.val hab
  exact add_left_cancel hAmbient

/-- Helper for Theorem 62.1: affine closed-unit-ball rescaling sends zero to its center. -/
private lemma affineClosedUnitBallInto_zero {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (x : U) (r : ℝ) (hr : 0 ≤ r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U) :
    affineClosedUnitBallInto x r hr hclosed 0 = x := by
  -- The scalar multiple of the zero vector vanishes.
  have hZeroCoe :
      ((0 : ClosedUnitBall d) : EuclideanSpace ℝ (Fin (d + 1))) = 0 := rfl
  apply Subtype.ext
  rw [affineClosedUnitBallInto_coe, hZeroCoe, smul_zero, add_zero]

/-- Helper for Theorem 62.1: interior points remain interior under affine
closed-unit-ball rescaling. -/
private lemma affineClosedUnitBallInto_mem_ball {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (x : U) (r : ℝ) (hr : 0 < r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U)
    (z : ClosedUnitBall d)
    (hz : (z : EuclideanSpace ℝ (Fin (d + 1))) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) :
    ((affineClosedUnitBallInto x r hr.le hclosed z : U) :
      EuclideanSpace ℝ (Fin (d + 1))) ∈
        Metric.ball (x : EuclideanSpace ℝ (Fin (d + 1))) r := by
  -- Expose the affine formula once, then use the ambient strict-ball calculation.
  rw [affineClosedUnitBallInto_coe]
  exact affineClosedUnitBall_mem_ball (d := d)
    (x : EuclideanSpace ℝ (Fin (d + 1))) r hr z hz

/-- Helper for Theorem 62.1: the image of the center of a closed ball has a
neighborhood covered by the image of the ball interior. -/
private lemma closedBall_center_imageNeighborhood {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (f : U → EuclideanSpace ℝ (Fin (d + 1)))
    (hf_continuous : Continuous f) (hf_injective : Function.Injective f)
    (x : U) (r : ℝ) (hr : 0 < r)
    (hclosed : Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) r ⊆ U) :
    ∃ ε > 0, Metric.ball (f x) ε ⊆
      f '' {y : U | (y : EuclideanSpace ℝ (Fin (d + 1))) ∈
        Metric.ball (x : EuclideanSpace ℝ (Fin (d + 1))) r} := by
  let A := affineClosedUnitBallInto x r hr.le hclosed
  have hAContinuous : Continuous A :=
    continuous_affineClosedUnitBallInto x r hr.le hclosed
  have hFContinuous : Continuous (fun z ↦ f (A z)) :=
    hf_continuous.comp hAContinuous
  let F : C(ClosedUnitBall d, EuclideanSpace ℝ (Fin (d + 1))) :=
    ⟨fun z ↦ f (A z), hFContinuous⟩
  have hFInjective : Function.Injective F :=
    hf_injective.comp (affineClosedUnitBallInto_injective x r hr hclosed)
  have hFZero : F 0 = f x := by
    -- The affine center computation identifies the center used by local surjectivity.
    calc
      F 0 = f (A 0) := rfl
      _ = f x := congrArg f (affineClosedUnitBallInto_zero x r hr.le hclosed)
  obtain ⟨ε, hε, hNeighborhood⟩ :=
    closedUnitBall_center_imageNeighborhood F hFInjective
  refine ⟨ε, hε, ?_⟩
  intro w hw
  have hwF : w ∈ Metric.ball (F 0) ε := by
    rwa [hFZero]
  obtain ⟨z, hz, rfl⟩ := hNeighborhood hwF
  exact ⟨A z, affineClosedUnitBallInto_mem_ball x r hr hclosed z hz, rfl⟩

/-- Helper for Theorem 62.1: every point in a restricted Euclidean ball image
has an open neighborhood contained in that image. -/
private lemma exists_open_imageNeighborhood_restrictedBall {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (f : U → EuclideanSpace ℝ (Fin (d + 1)))
    (hf_continuous : Continuous f) (hf_injective : Function.Injective f)
    (c : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ)
    (hclosed : Metric.closedBall c r ⊆ U) (x : U)
    (hx : (x : EuclideanSpace ℝ (Fin (d + 1))) ∈ Metric.ball c r) :
    ∃ V, V ⊆ f '' {z : U | (z : EuclideanSpace ℝ (Fin (d + 1))) ∈
        Metric.ball c r} ∧ IsOpen V ∧ f x ∈ V := by
  obtain ⟨s, hs, hsmall⟩ := Metric.exists_ball_subset_ball hx
  let ρ := s / 2
  have hρ : 0 < ρ := half_pos hs
  have hInnerClosed :
      Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) ρ ⊆ Metric.ball c r := by
    intro z hz
    exact hsmall (Metric.closedBall_subset_ball (half_lt_self hs) hz)
  have hInnerDomain :
      Metric.closedBall (x : EuclideanSpace ℝ (Fin (d + 1))) ρ ⊆ U := by
    intro z hz
    exact hclosed (Metric.ball_subset_closedBall (hInnerClosed hz))
  obtain ⟨ε, hε, hNeighborhood⟩ :=
    closedBall_center_imageNeighborhood f hf_continuous hf_injective x ρ hρ hInnerDomain
  refine ⟨Metric.ball (f x) ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε⟩
  intro w hw
  obtain ⟨z, hz, hzw⟩ := hNeighborhood hw
  exact ⟨z, hInnerClosed (Metric.ball_subset_closedBall hz), hzw⟩

/-- Helper for Theorem 62.1: a continuous injective Euclidean map sends a restricted
positive-dimensional ball to an open set when its closure stays in the domain. -/
lemma isOpen_image_restricted_euclidean_ball {n : ℕ} (hn : 0 < n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (f : U → EuclideanSpace ℝ (Fin n))
    (hf_continuous : Continuous f) (hf_injective : Function.Injective f)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) (_hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ U) :
    IsOpen (f '' {x : U | (x : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball c r}) := by
  -- Write the positive dimension as a successor, then cover each image point
  -- by the center-neighborhood theorem on a smaller closed ball.
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact exists_open_imageNeighborhood_restrictedBall f hf_continuous hf_injective
    c r hclosed x hx

end InvarianceOfDomainSupport

end
