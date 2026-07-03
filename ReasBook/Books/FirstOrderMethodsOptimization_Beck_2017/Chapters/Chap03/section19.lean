

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_19 (from Chap03) -/
open InnerProductSpace (toDual)
open WithLp (toLp)
open scoped BigOperators Gradient Pointwise

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "l1Norm" => (fun y : E ↦ ‖toLp 1 fun i ↦ y i‖)
local notation "l1Regularizer" => (fun lam : ℝ ↦ fun y : E ↦ ((lam * l1Norm y : ℝ) : EReal))

/- Definition 3.19 is `source-facing`: it defines the stationary-point predicate for the
`ℓ₁`-regularized problem. The owner abstractions in this domain are the chapter/project
`is_differentiable_at`, `subdifferentialAt`, and the composite stationary predicate
`is_stationary_point`, so this file keeps only the specialized `ℓ₁` subdifferential term on top
of the chapter differentiability owner. -/

recall is_stationary_point
recall is_differentiable_at
recall subdifferentialAt

/-- Definition 3.19: a point `x` is stationary for the `ℓ₁`-regularized problem
`min_y f y + λ ‖y‖₁` when `f` is differentiable at `x` in the sense of Definition 3.10 and the
negative gradient belongs to `λ ∂ ‖·‖₁ (x)`. -/
def is_l1_regularized_stationary_point (f : E → EReal) (lam : ℝ) (x : E) : Prop :=
  is_differentiable_at f x ∧
    -toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) ∈
      lam • subdifferentialAt l1Norm x

/-- Unfolding `is_l1_regularized_stationary_point` gives the chapter differentiability condition
and the scaled `ℓ₁`-subdifferential condition. -/
@[simp] theorem is_l1_regularized_stationary_point_iff
    {f : E → EReal} {lam : ℝ} {x : E} :
    is_l1_regularized_stationary_point f lam x ↔
      is_differentiable_at f x ∧
        -toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) ∈
          lam • subdifferentialAt l1Norm x :=
  Iff.rfl

-- Proof sketch: under `0 ≤ λ`, Definition 3.19 is the same stationary condition as in
-- Definition 3.17 for the composite objective with nonsmooth term `y ↦ λ * ‖y‖₁`. The
-- identification of the subdifferential of `y ↦ λ * ‖y‖₁` with `λ ∂ ‖·‖₁` is the standard scalar
-- chain rule from Theorem 3.21.
/-- Under the standard nonnegativity hypothesis on the regularization parameter, Definition 3.19 is
exactly the owner stationary predicate from Definition 3.17 for the composite objective
`f + λ ‖·‖₁`. -/
theorem is_l1_regularized_stationary_point_iff_is_stationary_point
    {f : E → EReal} {lam : ℝ} {x : E}
    (hlam : 0 ≤ lam) :
    is_l1_regularized_stationary_point f lam x ↔
      is_stationary_point f (l1Regularizer lam) x := sorry

-- Proof sketch: rewrite stationarity with `is_l1_regularized_stationary_point_iff`, then apply the
-- coordinatewise description of `∂ ‖·‖₁(x)` from Proposition 3.17 and scale each coordinate by
-- `λ`. The three cases `x i > 0`, `x i < 0`, and `x i = 0` yield the displayed piecewise gradient
-- conditions.
/-- The stationarity condition for `f + λ ‖·‖₁` is equivalent to the coordinatewise relations
`∂ᵢ f(x) = -λ` on positive coordinates, `∂ᵢ f(x) = λ` on negative coordinates, and
`∂ᵢ f(x)` lying between `-λ` and `λ` on zero coordinates. -/
theorem is_l1_regularized_stationary_point_iff_coordinatewise
    (f : E → EReal) (lam : ℝ) (x : E) :
    is_l1_regularized_stationary_point f lam x ↔
      is_differentiable_at f x ∧
        ∀ i : Fin n,
          (0 < x i → (∇ (fun y ↦ (f y).toReal) x) i = -lam) ∧
            (x i < 0 → (∇ (fun y ↦ (f y).toReal) x) i = lam) ∧
              (x i = 0 → (∇ (fun y ↦ (f y).toReal) x) i ∈ Set.uIcc (-lam) lam) := sorry

end

/-! ### Proposition_3_19 (from Chap03) -/
open scoped BigOperators
open WithLp (toLp)

section

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.19 is a `bridge/view` item in the chapter real-valued subdifferential API. The
core owner abstraction is `subdifferentialAt`, and the canonical vector-side bridge owner is
`euclideanSubdifferentialAt`. The affine pullback is already owned upstream by
`subdifferential_precompose_affineMap_eq`, while the source-facing `ℓ₁` subgradient set is
already packaged by `l1CoordinateSubgradientVectors` together with
`subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. This file keeps only the affine
matrix specialization of that owner stack rather than a parallel rowwise decomposition API. -/

recall euclideanSubdifferentialAt
recall l1CoordinateSubgradientVectors
recall subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints
recall sign_vector_mem_subdifferentialAt_l1_norm
recall subdifferential_precompose_affineMap_eq
recall sgn

-- Proof sketch: apply the affine chain rule from Theorem 3.19 to the `ℓ₁` norm
-- `z ↦ ∑ i, |z i|`, then transport the resulting pullback through the Euclidean bridge
-- `euclideanSubdifferentialAt`. Proposition 3.17 already identifies the target-side
-- subdifferential with `l1CoordinateSubgradientVectors`, so the affine formula is exactly the
-- transpose image of that canonical source-facing set.
/-- Proposition 3.19 (1): for the affine `ℓ¹` objective
`x ↦ ∑ i, |(A.toEuclideanLin x + b) i|`, the Euclidean/vector-side subdifferential is the
transpose image of the canonical coordinatewise `ℓ₁` subgradient set at the residual
`A.toEuclideanLin x + b`. -/
theorem euclidean_subdifferentialAt_affine_l1_eq_transpose_image_l1CoordinateSubgradientVectors
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x =
      A.transpose.toEuclideanLin ''
        l1CoordinateSubgradientVectors (A.toEuclideanLin x + b) := sorry

-- Proof sketch: Proposition 3.18 provides the canonical sign vector
-- `toLp 2 (sgn (fun i ↦ (A.toEuclideanLin x + b) i))` as an element of the `ℓ₁` subdifferential
-- at the residual `A.toEuclideanLin x + b`. Pull that vector back through the affine chain rule
-- above; in Euclidean coordinates the pullback is represented by `A.transpose.toEuclideanLin`.
/-- Proposition 3.19 (2): taking the coordinatewise sign vector from Definition 1.27, which uses
`sgn 0 = 1`, yields a concrete element of the Euclidean/vector-side subdifferential of the affine
`ℓ¹` objective, namely `Aᵀ *ᵥ sgn (fun i ↦ (A.toEuclideanLin x + b) i)`. -/
theorem transpose_sgn_mem_subdifferentialAt_affine_l1
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    A.transpose.toEuclideanLin
        (toLp 2 (sgn (fun i ↦ (A.toEuclideanLin x + b) i))) ∈
      euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x := sorry

end

/-! ### Theorem_3_19 (from Chap03) -/
universe u v

section

variable {V : Type u} {E : Type v}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup E] [Module ℝ E]

/- Theorem 3.19 is `source-facing` at the chapter owner
`subdifferential : Set (Module.Dual ℝ E)`, while the ambient affine geometry already has the
canonical owner abstraction `AffineMap`. The pullback acts on subgradients through the linear part
`φ.linear.dualMap`, so the public theorem stays at the algebraic-dual owner level and downstream
`StrongDual` and Euclidean files should reuse it through the chapter bridge/view APIs rather than
repackaging the affine map as primitive data `(A, b)`. -/

recall subdifferential

-- Proof sketch: if `g ∈ ∂ f (φ x)`, then `φ x ∈ effective_domain f` and the defining
-- subgradient inequality for `g` applied to `φ y` gives
-- `f (φ y) ≥ f (φ x) + g (φ.linear (y - x))`. Rewrite the last term as
-- `(φ.linear.dualMap g) (y - x)` using `φ.linearMap_vsub` to obtain the subgradient inequality
-- for `φ.linear.dualMap g` at `x`.
/-- Theorem 3.19 (1): weak affine transformation rule of subdifferential calculus. For
`h = f ∘ φ`, every subgradient of `f` at `φ x` pulls back along the linear part of `φ` to a
subgradient of `h` at `x`. Specializing to `φ y = A y + b` recovers the textbook notation
`Aᵀ (∂ f (A x + b))`. -/
theorem subdifferential_precompose_affineMap_subset
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x : V) :
    φ.linear.dualMap '' subdifferential f (φ x) ⊆
      subdifferential (fun y ↦ f (φ y)) x := sorry

end

section

variable {V : Type u} {E : Type v}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall finite_domain

-- Proof sketch: combine the weak inclusion with the max formula for directional derivatives at
-- interior finite-domain points. For every direction `d`, compare the support functions of the
-- two convex sets `∂ (fun y ↦ f (φ y)) x` and `φ.linear.dualMap '' ∂ f (φ x)` via the identity
-- `h' (x; d) = f' (φ x; φ.linear d)`. The hypothesis `φ x ∈ interior (finite_domain f)` is the
-- canonical owner-side condition ensuring the point is finite-valued, so the directional
-- derivative formula applies without any false `effective_domain`-only shortcut. Then use compact
-- convexity of both subdifferentials and the equality criterion from support functions to conclude
-- equality of the sets.
/-- Theorem 3.19 (2): affine transformation rule of subdifferential calculus. If
`φ x ∈ interior (finite_domain f)` for `h = f ∘ φ`, then the subdifferential of `h` at `x` is
exactly the pullback of the subdifferential of `f` at `φ x` along the linear part of `φ`.
Specializing to `φ y = A y + b` recovers the textbook notation `Aᵀ (∂ f (A x + b))`. -/
theorem subdifferential_precompose_affineMap_eq
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x : V)
    (hconvex : is_convex_function f)
    (hφx : φ x ∈ interior (finite_domain f)) :
    subdifferential (fun y ↦ f (φ y)) x =
      φ.linear.dualMap '' subdifferential f (φ x) := sorry

end
