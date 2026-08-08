import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp ofLp)
open scoped BigOperators
open InnerProductSpace (toDualMap)

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Proposition 3.23 is `source-facing`: the textbook formula is a vector-side description of the
extendedRealSubdifferential of the coordinatewise maximum on `ℝ^n`. The chapter owner bridge for that
vector-side view is already `euclideanSubdifferentialAt` from Theorem 3.4, so the main
declarations below use that owner directly. The continuous-dual image equalities are kept only as
thin companion reformulations. -/

/-- The max function on a finite coordinate space, specializing to `x ↦ max_i x i` on `ℝ^n`. -/
noncomputable def coordinatewiseMax (x : ι → ℝ) : ℝ :=
  ⨆ i : ι, x i

/-- The face of the standard simplex supported on the active coordinates of `x`, namely the
indices `i` with `coordinatewiseMax x = x i`. -/
def activeCoordinateFace (x : ι → ℝ) : Set (ι → ℝ) :=
  {l | l ∈ stdSimplex ℝ ι ∧ ∀ i, coordinatewiseMax x ≠ x i → l i = 0}

-- Proof sketch: unfold `activeCoordinateFace`; membership is exactly the conjunction that `λ`
-- lies in the standard simplex and vanishes on every inactive coordinate.
/-- Membership in `activeCoordinateFace x` means belonging to the standard simplex and being
supported on the active coordinates of `x`. -/
@[simp] theorem mem_activeCoordinateFace_iff {x l : ι → ℝ} :
    l ∈ activeCoordinateFace x ↔
      l ∈ stdSimplex ℝ ι ∧ ∀ i, coordinatewiseMax x ≠ x i → l i = 0 :=
  Iff.rfl

-- Proof sketch: apply the max rule for subdifferentials to the coordinate projections
-- `x ↦ x i`. Each coordinate map has singleton Euclidean extendedRealSubdifferential given by the
-- corresponding standard basis vector, so the extendedRealSubdifferential of
-- the maximum is the convex hull of the active basis vectors, equivalently the active face of the
-- standard simplex.
section

variable [Nonempty ι]

/-- Proposition 3.23: the Euclidean/vector-side extendedRealSubdifferential of the coordinatewise maximum on
`ℝ^n` is exactly the face of the standard simplex supported on the active coordinates. -/
theorem euclidean_subdifferentialAt_coordinatewiseMax_eq_activeCoordinateFace
    (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) x =
      toLp 2 '' activeCoordinateFace (ofLp x) := sorry

/-- Continuous-dual reformulation of Proposition 3.23 obtained by applying the canonical Riesz
map to the vector-side active face. -/
theorem subdifferentialAt_coordinatewiseMax_eq_image_activeCoordinateFace
    (x : E) :
    subdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) x =
      toDualMap ℝ E '' (toLp 2 '' activeCoordinateFace (ofLp x)) := sorry

-- Proof sketch: if `x = fun _ ↦ α`, then every coordinate is active, so
-- `activeCoordinateFace x` is the whole standard simplex. Substitute this into the preceding
-- proposition.
/-- At a constant vector `α e`, every coordinate is active, so the vector-side extendedRealSubdifferential of
the max function is the whole standard simplex. -/
theorem euclidean_subdifferentialAt_coordinatewiseMax_const_eq_stdSimplex
    (α : ℝ) :
    euclideanSubdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) (toLp 2 fun _ : ι ↦ α) =
      toLp 2 '' (stdSimplex ℝ ι : Set (ι → ℝ)) := sorry

/-- Continuous-dual reformulation of the constant-vector case of Proposition 3.23. -/
theorem subdifferentialAt_coordinatewiseMax_const_eq_image_stdSimplex
    (α : ℝ) :
    subdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) (toLp 2 fun _ : ι ↦ α) =
      toDualMap ℝ E '' (toLp 2 '' (stdSimplex ℝ ι : Set (ι → ℝ))) := sorry

end

end
