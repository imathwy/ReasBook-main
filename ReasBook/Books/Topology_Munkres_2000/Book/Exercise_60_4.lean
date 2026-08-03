module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

/-- Helper for Exercise 60.4: the canonical real-linear isometry identifies the
Euclidean plane with the complex plane. -/
private noncomputable def euclideanPlaneHomeomorphComplex :
    EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Exercise 60.4: the canonical Euclidean-complex homeomorphism
preserves the unit-sphere predicate. -/
private lemma euclideanPlaneHomeomorphComplex_mem_sphere
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      euclideanPlaneHomeomorphComplex x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- The underlying linear isometry preserves both zero and norms.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Exercise 60.4: the Euclidean unit circle is canonically
homeomorphic to the complex unit circle. -/
private noncomputable def euclideanSphereHomeomorphCircle :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  (euclideanPlaneHomeomorphComplex.subtype
    euclideanPlaneHomeomorphComplex_mem_sphere)

/-- Helper for Exercise 60.4: the canonical sphere homeomorphism commutes with
the antipodal involution. -/
private lemma euclideanSphereHomeomorphCircle_neg
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    euclideanSphereHomeomorphCircle (-x) = -euclideanSphereHomeomorphCircle x := by
  -- Coercing to `ℂ` reduces the claim to linearity of the coordinate isometry.
  apply Circle.ext
  change Complex.orthonormalBasisOneI.repr.symm (-x.1) =
    -Complex.orthonormalBasisOneI.repr.symm x.1
  exact map_neg Complex.orthonormalBasisOneI.repr.symm x.1

/-- Helper for Exercise 60.4: squaring on the complex circle is constant on
antipodal classes of the Euclidean unit circle. -/
private lemma circleSquare_respectsAntipodal
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hxy : RealProjectiveSpace.antipodalSetoid 1 x y) :
    euclideanSphereHomeomorphCircle x ^ 2 =
      euclideanSphereHomeomorphCircle y ^ 2 := by
  -- Equal representatives are immediate; antipodes have the same square.
  rcases (RealProjectiveSpace.setoid_rel_iff 1 x y).1 hxy with rfl | rfl
  · rfl
  · rw [euclideanSphereHomeomorphCircle_neg]
    exact (neg_sq (euclideanSphereHomeomorphCircle x)).symm

/-- Helper for Exercise 60.4: choose a sphere representative of each projective
line using the surjective canonical quotient map. -/
private noncomputable def projectiveLineRepresentative :
    RealProjectiveSpace 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  Function.surjInv (RealProjectiveSpace.quotientMap_isQuotientMap 1).surjective

/-- Helper for Exercise 60.4: squaring a chosen sphere representative defines
the circle-valued map on projective lines. -/
private noncomputable def projectiveLineSquare : RealProjectiveSpace 1 → Circle :=
  fun q ↦ euclideanSphereHomeomorphCircle (projectiveLineRepresentative q) ^ 2

/-- Helper for Exercise 60.4: the descended squaring map computes by squaring
on every sphere representative. -/
private lemma projectiveLineSquare_apply
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    projectiveLineSquare (RealProjectiveSpace.quotientMap 1 x) =
      euclideanSphereHomeomorphCircle x ^ 2 := by
  -- A chosen representative lies in the same antipodal class as the given one.
  have hRepresentative :
      RealProjectiveSpace.quotientMap 1
          (projectiveLineRepresentative (RealProjectiveSpace.quotientMap 1 x)) =
        RealProjectiveSpace.quotientMap 1 x :=
    Function.surjInv_eq
      (RealProjectiveSpace.quotientMap_isQuotientMap 1).surjective
      (RealProjectiveSpace.quotientMap 1 x)
  have hAntipodal :
      RealProjectiveSpace.antipodalSetoid 1
        (projectiveLineRepresentative (RealProjectiveSpace.quotientMap 1 x)) x := by
    exact (RealProjectiveSpace.setoid_rel_iff 1 _ _).2
      ((RealProjectiveSpace.quotientMap_eq_iff 1 _ _).1 hRepresentative)
  exact circleSquare_respectsAntipodal _ _ hAntipodal

/-- Helper for Exercise 60.4: the descended squaring map is bijective. -/
private lemma projectiveLineSquare_bijective :
    Function.Bijective projectiveLineSquare := by
  constructor
  · -- Equality of squares identifies precisely equal or antipodal representatives.
    intro a b hab
    obtain ⟨x, rfl⟩ := (RealProjectiveSpace.quotientMap_isQuotientMap 1).surjective a
    obtain ⟨y, rfl⟩ := (RealProjectiveSpace.quotientMap_isQuotientMap 1).surjective b
    rw [RealProjectiveSpace.quotientMap_eq_iff]
    rw [projectiveLineSquare_apply, projectiveLineSquare_apply] at hab
    have hSquares :
        (euclideanSphereHomeomorphCircle x : ℂ) ^ 2 =
          (euclideanSphereHomeomorphCircle y : ℂ) ^ 2 := by
      exact congrArg ((↑) : Circle → ℂ) hab
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hSquares with hEqual | hNeg
    · left
      apply euclideanSphereHomeomorphCircle.injective
      exact Circle.coe_injective hEqual.symm
    · right
      have hCircle :
          euclideanSphereHomeomorphCircle x =
            -euclideanSphereHomeomorphCircle y := by
        exact Circle.coe_injective hNeg
      have hSphere : x = -y := by
        apply euclideanSphereHomeomorphCircle.injective
        rw [euclideanSphereHomeomorphCircle_neg]
        exact hCircle
      calc
        y = -(-y) := (neg_neg y).symm
        _ = -x := congrArg Neg.neg hSphere.symm
  · -- Every circle point has a square root and hence a sphere representative.
    intro z
    obtain ⟨w, hw⟩ := (Circle.isQuotientCoveringMap_npow 2).surjective z
    obtain ⟨x, rfl⟩ := euclideanSphereHomeomorphCircle.surjective w
    refine ⟨RealProjectiveSpace.quotientMap 1 x, ?_⟩
    exact (projectiveLineSquare_apply x).trans hw

/-- Helper for Exercise 60.4: the descended squaring map is continuous. -/
private lemma continuous_projectiveLineSquare : Continuous projectiveLineSquare := by
  -- Continuity is checked after precomposition with the defining quotient map.
  apply (RealProjectiveSpace.quotientMap_isQuotientMap 1).continuous_iff.mpr
  have hcomp :
      projectiveLineSquare ∘ RealProjectiveSpace.quotientMap 1 =
        fun x ↦ euclideanSphereHomeomorphCircle x ^ 2 := by
    funext x
    exact projectiveLineSquare_apply x
  rw [hcomp]
  exact euclideanSphereHomeomorphCircle.continuous.pow 2

/-- Exercise 60.4: Real projective `1`-space is a circle, and under a homeomorphic
identification of `S¹` with `Circle`, its canonical quotient map is `z ↦ z ^ 2`. -/
theorem realProjectiveLineHomeomorphicCircle :
    ∃ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle,
      ∃ e : RealProjectiveSpace 1 ≃ₜ Circle,
        ∀ x, e (RealProjectiveSpace.quotientMap 1 x) = s x ^ 2 := by
  -- Upgrade the continuous bijection to a homeomorphism using compactness and Hausdorffness.
  let projectiveLineEquiv : RealProjectiveSpace 1 ≃ Circle :=
    Equiv.ofBijective projectiveLineSquare projectiveLineSquare_bijective
  let projectiveLineHomeomorphCircle : RealProjectiveSpace 1 ≃ₜ Circle :=
    Continuous.homeoOfEquivCompactToT2
      (f := projectiveLineEquiv) continuous_projectiveLineSquare
  refine ⟨euclideanSphereHomeomorphCircle, projectiveLineHomeomorphCircle, ?_⟩
  -- The quotient-lift computation rule is exactly the required covering-map formula.
  intro x
  exact projectiveLineSquare_apply x
