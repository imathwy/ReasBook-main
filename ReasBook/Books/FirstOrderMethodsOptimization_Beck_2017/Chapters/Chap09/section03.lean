import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_3 (from Chap09) -/
universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 9.3 is `source-facing`: the textbook specifies a recursive first-order procedure
through explicit iterates `x^k`, chosen positive stepsizes `t_k`, chosen Euclidean subgradients
`f'(x^k)`, and an argmin update over the feasible set `C`. The owner abstractions already present
in the project for these ingredients are the Euclidean subgradient bridge
`euclideanSubdifferentialAt`, the source-facing subdifferential domain `subdifferential_domain`
for the mirror map `ω.toEReal`, Chapter 9's Bregman-distance owner `B[ω]`, and mathlib's
minimizer predicate `IsMinOn` for the argmin step. Since no canonical minimizer has been chosen,
the public object here is a trajectory predicate on the iterate, stepsize, and
selected-subgradient sequences, together with the explicit one-step mirror-descent objective. -/

/-- The one-step mirror-descent objective obtained by linearizing `f` with the chosen
subgradient `g` at the current iterate `x` and keeping the mirror map `ω` explicit. -/
def mirror_descent_update_objective (ω : E → ℝ) (x g : E) (t : ℝ) : E → ℝ :=
  fun y ↦ inner ℝ (t • g) y + B[ω] y x + ω x - inner ℝ (∇ ω x) x

-- Proof sketch: unfold `mirror_descent_update_objective`; the displayed formula is exactly its
-- defining lambda expression.
/-- Evaluating `mirror_descent_update_objective ω x g t` at `y` gives the linearized term
`⟪t • g - ∇ ω x, y⟫` plus the mirror map value `ω y`. -/
@[simp] theorem mirror_descent_update_objective_apply
    (ω : E → ℝ) (x g y : E) (t : ℝ) :
    mirror_descent_update_objective ω x g t y =
      inner ℝ (t • g - ∇ ω x) y + ω y := by
  rw [mirror_descent_update_objective, bregmanDistance]
  have hω : (fun z : E ↦ (Function.toEReal ω z).toReal) = ω := by
    funext z
    simp
  rw [hω]
  simp only [Function.comp_apply, EReal.toReal_coe]
  rw [inner_sub_right, inner_sub_left]
  ring

/-- Definition 9.3: sequences of iterates `x`, stepsizes `t`, and chosen Euclidean subgradients
`g` follow the Mirror Descent Method for objective `f`, mirror map `ω`, and feasible set `C` when
for every iteration `k`, the current iterate lies in `C ∩ dom(∂ ω)`, the chosen vector `g k`
belongs to `∂ f(x^k)`, the stepsize `t k` is positive, and the next iterate `x^(k+1)` minimizes
the mirror-descent update objective
`y ↦ ⟪t_k g_k - ∇ ω(x^k), y⟫ + ω(y)` over `C`. -/
def is_mirror_descent_trajectory
    (f ω : E → ℝ) (C : Set E) (x g : ℕ → E) (t : ℕ → ℝ) : Prop :=
  ∀ k,
    x k ∈ C ∩ subdifferential_domain ω.toEReal ∧
      g k ∈ euclideanSubdifferentialAt f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_descent_update_objective ω (x k) (g k) (t k)) C (x (k + 1))

-- Proof sketch: specialize the defining universal clause in
-- `is_mirror_descent_trajectory f ω C x g t` at the iteration index `k`.
/-- A mirror-descent trajectory satisfies the feasible-domain, subgradient, positive-stepsize, and
one-step minimization conditions at each iteration. -/
theorem is_mirror_descent_trajectory_step
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    x k ∈ C ∩ subdifferential_domain ω.toEReal ∧
      g k ∈ euclideanSubdifferentialAt f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_descent_update_objective ω (x k) (g k) (t k)) C (x (k + 1)) := sorry

end

/-! ### Lemma_9_3 (from Chap09) -/
noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ω : E → EReal} {a b c : E}

/- Lemma 9.3 is `source-facing`: it records the standard three-point identity for the Chapter 9
owner `bregmanDistance` on the mathematically meaningful differentiable domain of the two anchor
points. The Chapter 9 owner on the right is still `bregmanDistance`, while the gradient data on
the left should be supplied through the canonical mathlib owner `HasGradientAt` rather than through
the global totalized surface `∇`. -/

-- Proof sketch: expand the three owner-level Bregman terms `B[ω] c a`, `B[ω] a b`, and
-- `B[ω] c b`, cancel the function values, and use `c - b = (c - a) + (a - b)` to collect the
-- remaining inner products into the canonical gradient difference.
/-- Lemma 9.3: if `ω.toReal` has gradients `ωa` at `a` and `ωb` at `b`, then the associated
three-point identity for the Chapter 9 Bregman distance is
`⟪ωb - ωa, c - a⟫ = B_ω(c, a) + B_ω(a, b) - B_ω(c, b)`. -/
theorem bregman_three_point_identity
    {ωa ωb : E}
    (ha : HasGradientAt (fun x ↦ (ω x).toReal) ωa a)
    (hb : HasGradientAt (fun x ↦ (ω x).toReal) ωb b) :
    inner ℝ (ωb - ωa) (c - a) =
      B[ω] c a + B[ω] a b - B[ω] c b := by
  rw [bregmanDistance_def, bregmanDistance_def, bregmanDistance_def, ha.gradient, hb.gradient]
  have hcb : c - b = (c - a) + (a - b) := by
    abel
  rw [hcb, inner_add_right, inner_sub_left]
  ring

end

/-! ### Text_9_3 (from Chap09) -/
/- Text 9.3 is `source-facing`: it asserts the existence of a strictly convex real-valued
generator together with positive points witnessing triangle-inequality failure. The core owner is
the Chapter 9 Bregman distance `bregmanDistance`; the one-dimensional bridge to real-valued
generators is already supplied upstream in `Text_9_2`, so this file keeps the witness data itself
rather than repackaging it as an auxiliary set. -/

/-- The cubic generator used to witness failure of the triangle inequality for Bregman distance. -/
def cubic_bregmanGenerator : ℝ → ℝ :=
  fun x ↦ x ^ (3 : ℕ)

/-- Evaluating the cubic Bregman generator. -/
@[simp] theorem cubic_bregmanGenerator_apply (x : ℝ) :
    cubic_bregmanGenerator x = x ^ (3 : ℕ) :=
  rfl

-- Proof sketch: apply the one-variable strict-convexity criterion on `(0, ∞)` to `x ↦ x^3`,
-- using that its second derivative is positive there.
/-- The cubic generator is strictly convex on the positive real line. -/
theorem strictConvexOn_cubic_bregmanGenerator :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) cubic_bregmanGenerator := sorry

-- Proof sketch: compute the three Bregman distances for `ω(x) = x^3` at `x = 3`, `y = 2`,
-- and `z = 1`; the values are `20`, `7`, and `4`, so the direct distance exceeds the broken path.
/-- The cubic generator violates the triangle inequality at the points `3`, `2`, and `1`. -/
theorem cubic_bregman_triangle_counterexample :
    B[cubic_bregmanGenerator] 3 1 >
      B[cubic_bregmanGenerator] 3 2 + B[cubic_bregmanGenerator] 2 1 := sorry

-- Proof sketch: witness the existential statement with `ω(x) = x^3` on `(0, ∞)` and the points
-- `x = 3`, `y = 2`, `z = 1`, combining strict convexity with the explicit counterexample above.
/-- Text 9.3: the Bregman distance need not satisfy the triangle inequality; a strictly convex
generator on the positive reals already gives a counterexample. -/
theorem exists_strictly_convex_bregman_triangle_counterexample :
    ∃ ω : ℝ → ℝ,
      StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) ω ∧
        ∃ x y z : ℝ,
          0 < x ∧
            0 < y ∧
              0 < z ∧
                B[ω] x z > B[ω] x y + B[ω] y z := sorry
