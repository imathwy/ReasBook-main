import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_4_17
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Proposition_6_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Remark 6.1.1 lies in the accelerated-prefix-convexity / Euclidean prox-function domain.

Sampled owner-style declarations:
- `bounded_union_of_prefix_convex_hull_sequences` in `Proposition_6_8`, the chapter owner of the
  boundedness conclusion once prefix convex-hull membership is known;
- `bounded_union_of_prefix_convex_hull_sequences_of_isBounded` in `Proposition_6_8`, the same
  owner factored through boundedness of `Set.range v`;
- `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical owner of the
  centered quadratic penalty;
- `quadraticallyRegularizedObjective_apply` in `Chap01/Definition_1_4_17`, the companion bridge
  back to the textbook formula.

Best owner abstractions:
- source-facing: the update-rule consequences placing `x_k` and `y_k` in the convex hull of the
  prefix `v₀, …, v_k`, and the Euclidean-prox radius estimate used in the remark;
- core/canonical: `bounded_union_of_prefix_convex_hull_sequences` for boundedness and
  `quadraticallyRegularizedObjective` for the quadratic penalty;
- bridge/view: the source-facing shorthand `quadraticDistanceTo` and the prefix-membership lemmas
  that feed Proposition 6.8.

Primitive data:
- the iterate families `v`, `x`, `y` together with the source update identities;
- the seminorm owner `p` and center `x0` for the generic quadratic prox term;
- the Euclidean prox center `x0` and comparison point `xStar`.

Derived API:
- the generic seminorm-centered quadratic prox owner `Seminorm.quadraticDistanceTo`;
- prefix convex-hull membership of `x_k` and `y_k`;
- boundedness of the union of the three ranges via Proposition 6.8;
- the Euclidean radius estimate derived from the chapter's quadratic-regularization owner.

The Euclidean prox formula is now routed through the generic seminorm-centered quadratic owner
`Seminorm.quadraticDistanceTo`. The source-facing shorthand `quadraticDistanceTo` is retained
because it materially shortens the Euclidean theorem surface, but it is only the
`normSeminorm` specialization of that owner. -/

section PrefixConvexHull

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: argue by induction on `k`. The base case is `x₀ = v₀`, so `x₀` belongs to the
-- convex hull of the singleton prefix. For the step, use `x_succ_eq` to write `x_{k+1}` as a
-- convex combination of `x_k` and `v_{k+1}`, then enlarge the prefix from `v₀, ..., v_k` to
-- `v₀, ..., v_{k+1}`.
/-- The iterates `x_k` of the composite fast gradient method lie in the convex hull of the prefix
`v₀, ..., v_k` once the initialization satisfies `x₀ = v₀`. -/
theorem x_mem_prefix_convexHull_of_update
    (x v : ℕ → E) (hx0 : x 0 = v 0)
    (hxsucc : ∀ k : ℕ,
      x (k + 1) =
        (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v (k + 1)) :
    ∀ k : ℕ, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)) := sorry

-- Proof sketch: use `y_eq` to write `y_k` as a convex combination of `x_k` and `v_k`, then apply
-- `x_mem_prefix_convexHull` and the fact that `v_k` itself belongs to the same finite prefix hull.
/-- Every interpolation point `y_k` lies in the convex hull of the prefix `v₀, ..., v_k`. -/
theorem y_mem_prefix_convexHull_of_update
    (x y v : ℕ → E) (hx0 : x 0 = v 0)
    (hxsucc : ∀ k : ℕ,
      x (k + 1) =
        (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v (k + 1))
    (hy : ∀ k : ℕ,
      y k = (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v k) :
    ∀ k : ℕ, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)) := sorry

-- Proof sketch: derive the prefix convex-hull membership of `x_k` and `y_k` from the update
-- rules, then apply Proposition 6.8 to the resulting source-facing hypotheses.
/-- Remark 6.1.1: if method `(6.1.19)` starts from `x₀ = v₀`, then the update relations place
`x_k` and `y_k` in the convex hull of `v₀, ..., v_k`; if moreover
`‖v_k - x^*‖² ≤ 2 D` for all `k ≥ 0`, where `D` is the source scalar `d(x^*)`, then the iterates
`v_k`, `x_k`, and `y_k` form a bounded family. -/
theorem bounded_iterates_of_sqDist_bound
    (D : ℝ) (x y v : ℕ → E) (xStar : E) (hx0 : x 0 = v 0)
    (hxsucc : ∀ k : ℕ,
      x (k + 1) =
        (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v (k + 1))
    (hy : ∀ k : ℕ,
      y k = (1 - (2 / ((k : ℝ) + 2))) • x k + (2 / ((k : ℝ) + 2)) • v k)
    (hv : ∀ k : ℕ, ‖v k - xStar‖ ^ (2 : ℕ) ≤ 2 * D) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := by
  refine bounded_union_of_prefix_convex_hull_sequences xStar D v x y ?_ ?_ ?_
  · exact x_mem_prefix_convexHull_of_update x v hx0 hxsucc
  · exact y_mem_prefix_convexHull_of_update x y v hx0 hxsucc hy
  · simpa using hv

end PrefixConvexHull

namespace Seminorm

section QuadraticDistance

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The quadratic prox function centered at `x₀` attached to the seminorm `p`. -/
def quadraticDistanceTo (p : Seminorm ℝ E) (x0 : E) : E → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * p (x - x0) ^ (2 : ℕ)

/-- Evaluating `p.quadraticDistanceTo x₀` recovers the centered quadratic formula
`(1 / 2) p(x - x₀)^2`. -/
@[simp] theorem quadraticDistanceTo_apply
    (p : Seminorm ℝ E) (x0 x : E) :
    p.quadraticDistanceTo x0 x = (1 / 2 : ℝ) * p (x - x0) ^ (2 : ℕ) :=
  rfl

end QuadraticDistance

end Seminorm

section QuadraticDistance

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euclidean prox function centered at `x₀`, realized as the zero-objective specialization
of the seminorm-centered quadratic prox owner for the ambient norm. -/
abbrev quadraticDistanceTo (x0 : E) : E → ℝ :=
  (normSeminorm ℝ E).quadraticDistanceTo x0

/-- Evaluating `quadraticDistanceTo x₀` recovers the textbook formula
`(1 / 2) ‖x - x₀‖²`. -/
@[simp] theorem quadraticDistanceTo_apply (x0 x : E) :
    quadraticDistanceTo x0 x = (1 / 2 : ℝ) * ‖x - x0‖ ^ (2 : ℕ) := by
  simp [quadraticDistanceTo, Seminorm.quadraticDistanceTo]

-- Proof sketch: rewrite the prox function using `hprox`, then apply
-- `two_mul_quadraticDistanceTo`, identify `‖xStar - x0‖` with `‖x0 - xStar‖`, and then take
-- square roots on both sides of the resulting nonnegative inequality.
/-- Doubling `quadraticDistanceTo x₀ x` recovers the squared Euclidean distance `‖x - x₀‖²`. -/
theorem two_mul_quadraticDistanceTo (x0 x : E) :
    2 * quadraticDistanceTo x0 x = ‖x - x0‖ ^ (2 : ℕ) := sorry

-- Proof sketch: rewrite `2 * quadraticDistanceTo x0 xStar` as `‖xStar - x0‖²`, use symmetry of
-- the norm, and pass from the squared-distance bound to the norm bound.
/-- In the Euclidean prox choice `d(x) = (1 / 2) ‖x - x₀‖²`, the estimate
`‖v_k - x^*‖² ≤ 2 d(x^*)` yields the explicit radius bound `‖v_k - x^*‖ ≤ ‖x₀ - x^*‖`. -/
theorem euclidean_prox_radius_bound
    (x0 xStar : E) (v : ℕ → E)
    (hv : ∀ k : ℕ, ‖v k - xStar‖ ^ (2 : ℕ) ≤ 2 * quadraticDistanceTo x0 xStar) (k : ℕ) :
    ‖v k - xStar‖ ≤ ‖x0 - xStar‖ := sorry

end QuadraticDistance

end
