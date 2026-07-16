import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

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
