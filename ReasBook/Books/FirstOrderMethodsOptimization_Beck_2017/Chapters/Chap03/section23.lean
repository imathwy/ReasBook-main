

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_23 (from Chap03) -/
open WithLp (toLp ofLp)
open scoped BigOperators
open InnerProductSpace (toDualMap)

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Proposition 3.23 is `source-facing`: the textbook formula is a vector-side description of the
subdifferential of the coordinatewise maximum on `ℝ^n`. The chapter owner bridge for that
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
-- `x ↦ x i`. Each coordinate map has singleton Euclidean subdifferential given by the
-- corresponding standard basis vector, so the subdifferential of
-- the maximum is the convex hull of the active basis vectors, equivalently the active face of the
-- standard simplex.
section

variable [Nonempty ι]

/-- Proposition 3.23: the Euclidean/vector-side subdifferential of the coordinatewise maximum on
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
/-- At a constant vector `α e`, every coordinate is active, so the vector-side subdifferential of
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

/-! ### Theorem_3_23 (from Chap03) -/
universe u v

section

variable {E : Type u} {ι : Type v}
variable [AddCommGroup E] [Module ℝ E]

/-
Theorem 3.23 is `source-facing` at the Chapter 3 owner `subdifferential`. Domain sampling for the
weak max-rule API points to the following declarations:

* `is_subgradient_at` in `Definition_3_1` as the primitive predicate.
* `subdifferential` in `Definition_3_2` as the owner set-valued map.
* `convex_subdifferential` in `Definition_3_2` as the owner-level derived convexity needed to pass
  from the active union to its convex hull.
* `directional_derivative_iSup_eq_iSup_active_indices` in `Theorem_3_9` as the matching canonical
  active-index subtype for pointwise suprema.

The primitive data here is only the ambient subdifferential of the supremum; the active-index
collection at `x` is derived data, so the public statement keeps it inline as the subtype
`{i // f i x = iSup fun j ↦ f j x}` instead of introducing a parallel `activeIndices` wrapper. The
theorem stays directly on the owner declaration from `Definition_3_2` rather than depending on the
later strong-dual bridge/view files: the weak inclusion itself is purely algebraic and needs no
topological dual packaging. The textbook properness and convexity hypotheses are ambient for the
convex-calculus context, but this weak inclusion already holds for the owner `subdifferential`
without additional assumptions, so the API stays on that minimal canonical statement.
-/
recall subdifferential
recall convex_subdifferential

-- Proof sketch: if `g ∈ ∂ fᵢ(x)` and `f i x = ⨆ j, f j x`, then for every `y` we have
-- `⨆ j, f j y ≥ f i y ≥ f i x + g (y - x) = (⨆ j, f j x) + g (y - x)`, so
-- `g ∈ ∂ (fun y ↦ ⨆ j, f j y) x`. Hence the union of the active subdifferentials is contained in
-- the ambient subdifferential. Since every subdifferential is convex, the convex hull of that
-- union is contained there as well.
/-- Theorem 3.23: weak maximum rule of subdifferential calculus. For the pointwise supremum of an
arbitrary family of extended-real-valued functions, the convex hull of the active branch
subdifferentials at `x` is contained in the subdifferential of the supremum at `x`. -/
theorem convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup
    (f : ι → E → EReal) (x : E) :
    convexHull ℝ (⋃ i : {i : ι // f i x = ⨆ j : ι, f j x}, subdifferential (f i) x) ⊆
      subdifferential (fun y ↦ ⨆ i : ι, f i y) x := sorry

end
