import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m p : ℕ}

local notation "InequalitySpace" => EuclideanSpace ℝ (Fin m)
local notation "EqualitySpace" => EuclideanSpace ℝ (Fin p)
local notation "PerturbationSpace" =>
  InequalitySpace × EqualitySpace

/- Lemma 3.4 is `source-facing` in the perturbation-value-function API. Its
`core/canonical` owner declarations are the Chapter 2 convexity predicate
`is_convex_function` and the partial-minimization theorem
`partial_infimum_is_convex_function`. This file keeps only the source-facing
feasible-set and value-function constructions, with the membership/evaluation
facts exposed as derived simp lemmas. -/
recall is_convex_function
recall partial_infimum_is_convex_function

/-- The feasible set for the perturbation parameter `(u, t)` consists of the points of `X`
satisfying the coordinatewise inequality constraints `g i x ≤ u i` and the affine equality
constraint `A x + b = t`. -/
def value_function_feasible_set (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (u : InequalitySpace) (t : EqualitySpace) : Set E :=
  {x | x ∈ X ∧ (∀ i : Fin m, g i x ≤ (u i : EReal)) ∧ A x + b = t}

-- Proof sketch: unfold `value_function_feasible_set`; membership is exactly the conjunction of
-- belonging to `X`, satisfying each scalar inequality constraint, and solving the affine equality
-- constraint.
/-- A point lies in the perturbation feasible set exactly when it belongs to `X`, satisfies every
inequality constraint, and meets the affine equality constraint. -/
@[simp] theorem mem_value_function_feasible_set (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (u : InequalitySpace) (t : EqualitySpace) (x : E) :
    x ∈ value_function_feasible_set X g A b u t ↔
      x ∈ X ∧ (∀ i : Fin m, g i x ≤ (u i : EReal)) ∧ A x + b = t :=
  Iff.rfl

/-- The perturbation value function assigns to `(u, t)` the infimum of `f` over the feasible set
cut out by the perturbation constraints. -/
def value_function (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace) :
    PerturbationSpace → EReal :=
  Function.uncurry fun u t ↦ sInf (f '' value_function_feasible_set X g A b u t)

-- Proof sketch: unfold `value_function`; evaluation at `(u, t)` is definitionally the infimum of
-- the image of `f` on `value_function_feasible_set X g A b u t`.
/-- Evaluating the perturbation value function at `(u, t)` gives the infimum of `f` over the
corresponding feasible set. -/
@[simp] theorem value_function_apply (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (u : InequalitySpace) (t : EqualitySpace) :
    value_function X f g A b (u, t) =
      sInf (f '' value_function_feasible_set X g A b u t) :=
  rfl

-- Proof sketch: if `∀ i, u i ≤ w i`, every point feasible for `u` is also feasible for `w`,
-- because the only changing conditions are the coordinatewise bounds `g i x ≤ u i`. Membership in
-- `X` and the affine equality constraint are unchanged.
/-- Relaxing the inequality perturbation coordinates enlarges the perturbation feasible set. -/
theorem value_function_feasible_set_mono_u (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    {u w : InequalitySpace} {t : EqualitySpace} (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function_feasible_set X g A b u t ⊆ value_function_feasible_set X g A b w t := sorry

-- Proof sketch: `value_function_feasible_set_mono_u` shows the feasible set for `u` sits inside
-- the feasible set for `w` whenever `∀ i, u i ≤ w i`. Taking infima of `f` over these nested
-- feasible sets yields antitonicity in the inequality perturbation parameter.
/-- For fixed equality perturbation `t`, the perturbation value function is antitone in the
inequality perturbation parameter. -/
theorem value_function_antitone_u (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    {u w : InequalitySpace} {t : EqualitySpace} (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function X f g A b (u, t) ≥ value_function X f g A b (w, t) := sorry

-- Proof sketch: view `value_function X f g A b` as the partial infimum in the `E`-variable of the
-- jointly convex constrained objective on `E × (ℝ^m × ℝ^p)` that equals `f x` on the convex set of
-- triples `(x, u, t)` with `x ∈ X`, `g i x ≤ u i`, and `A x + b = t`, and equals `⊤` outside that
-- set. Convexity of `X`, of `f`, and of each `g i`, together with linearity of `A`, gives
-- convexity of that owner objective, so `partial_infimum_is_convex_function` yields convexity of
-- the value function directly, with no properness hypothesis.
/-- Lemma 3.4: if `f` and all constraint functions `g i` are convex and `X` is convex, then the
perturbation value function is convex on `ℝ^m × ℝ^p`. -/
theorem value_function_is_convex (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (hf_convex : is_convex_function f) (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hX_convex : Convex ℝ X) :
    is_convex_function (value_function X f g A b) := sorry

end
