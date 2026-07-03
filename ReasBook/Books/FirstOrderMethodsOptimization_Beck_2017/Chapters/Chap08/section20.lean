import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_20 (from Chap08) -/
universe u

section

variable {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- Definition 8.20 is `source-facing`: the textbook introduces the dual optimization problem for
the Chapter 8 inequality-constrained primal problem. Domain sampling against mathlib shows that
the canonical owner for the optimization viewpoint is `IsMaxOn`; the only genuinely new local
object is the nonnegative multiplier region `ℝ_+^m`, written here as the explicit coordinatewise
orthant in `EuclideanSpace ℝ (Fin m)`. As in Definition 8.17, the source-facing API is therefore
a feasible-set owner together with a companion `IsMaxOn` characterization, rather than a
surrogate package or an existential wrapper for optimal multipliers. -/

/-- Definition 8.20: the feasible multiplier region of the dual problem is the nonnegative
orthant `ℝ_+^m`. The dual problem maximizes the dual function `q` over this set. -/
def dual_problem_feasible_set (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {lam | ∀ i : Fin m, 0 ≤ lam i}

-- Proof sketch: unfold `dual_problem_feasible_set`; membership is definitionally the
-- coordinatewise nonnegativity condition `∀ i, 0 ≤ λ i`.
/-- Helper for Definition 8.20: membership in `dual_problem_feasible_set m` means that every
coordinate of the multiplier vector is nonnegative. -/
@[simp] theorem mem_dual_problem_feasible_set {lam : Λ} :
    lam ∈ dual_problem_feasible_set m ↔ ∀ i : Fin m, 0 ≤ lam i := by
  -- Unfolding the set-builder exposes exactly the coordinatewise nonnegativity condition.
  rfl

section

variable {α : Type u} [Preorder α]

-- Proof sketch: rewrite `IsMaxOn q (dual_problem_feasible_set m) lam` using the canonical
-- characterization `isMaxOn_iff`, then keep the maximizer's feasibility explicit so the result
-- matches the textbook constrained maximization statement over `ℝ_+^m`.
/-- Helper for Definition 8.20: a feasible multiplier `lam` maximizes `q` on
`dual_problem_feasible_set m` exactly when it dominates every feasible comparison multiplier. -/
theorem isMaxOn_dual_problem_feasible_set_iff
    {q : Λ → α} {lam : Λ} :
    lam ∈ dual_problem_feasible_set m ∧
      IsMaxOn q (dual_problem_feasible_set m) lam ↔
      lam ∈ dual_problem_feasible_set m ∧
        ∀ μ, μ ∈ dual_problem_feasible_set m → q μ ≤ q lam := by
  -- Route correction: mathlib's `IsMaxOn` only gives comparison inequalities on feasible points,
  -- so the maximizer's own feasibility must be recorded explicitly on the left-hand side.
  constructor
  · rintro ⟨hlam, hmax⟩
    rw [isMaxOn_iff] at hmax
    refine ⟨hlam, ?_⟩
    -- Every feasible comparison multiplier lies in the same feasible set, so `IsMaxOn` applies.
    intro μ hμ
    exact hmax μ hμ
  · rintro ⟨hlam, hmax⟩
    refine ⟨hlam, ?_⟩
    rw [isMaxOn_iff]
    -- Rewriting the comparison premise to feasible-set membership reduces the goal to `hmax`.
    intro μ hμ
    exact hmax μ hμ

end

end

/-! ### Lemma_8_20 (from Chap08) -/
universe u v

section

open Metric

variable {α : Type u} [PseudoMetricSpace α]
variable {ι : Type v} [Finite ι] [Nonempty ι]

/- Lemma 8.20 is `source-facing`: the textbook function is the maximum of finitely many
distance-to-set functions. The canonical owner for each summand is `Metric.infDist`, and the
clean finite-family owner is their pointwise supremum over a finite nonempty index type. -/

/-- The function `x ↦ max_i d_{S_i}(x)` associated with a finite nonempty family of sets. -/
noncomputable def max_distance_to_sets (S : ι → Set α) : α → ℝ :=
  fun x ↦ ⨆ i, Metric.infDist x (S i)

-- Proof sketch: unfold `max_distance_to_sets`; the statement is the defining equation written in
-- the source-facing `d_{S_i}` notation.
omit [Finite ι] [Nonempty ι] in
/-- The owner `max_distance_to_sets` is the pointwise supremum of the individual distance
functions `x ↦ d_{S_i}(x)`. -/
theorem max_distance_to_sets_eq_iSup (S : ι → Set α) (x : α) :
    max_distance_to_sets S x = ⨆ i, Metric.infDist x (S i) := by
  -- Unfold the source-facing definition of the maximum distance objective.
  rfl

omit [Finite ι] in
/-- Helper for Lemma 8.20: on a finite nonempty index type, the supremum defining
`max_distance_to_sets` is the finite maximum over `Finset.univ`. -/
lemma max_distance_to_sets_eq_sup'_univ (S : ι → Set α) [Fintype ι] (x : α) :
    max_distance_to_sets S x =
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i)) := by
  classical
  -- Rewrite the conditionally complete supremum as the concrete finite supremum on `univ`.
  rw [max_distance_to_sets_eq_iSup]
  symm
  exact Finset.sup'_univ_eq_ciSup (f := fun i ↦ Metric.infDist x (S i))

/-- Helper for Lemma 8.20: the finite maximum of distance-to-set functions satisfies the same
one-sided triangle inequality as each coordinate distance. -/
lemma max_distance_to_sets_le_add_dist (S : ι → Set α) (x y : α) :
    max_distance_to_sets S x ≤ max_distance_to_sets S y + dist x y := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- Pass from the abstract supremum to a finite maximum so each coordinate can be bounded.
  rw [max_distance_to_sets_eq_sup'_univ, max_distance_to_sets_eq_sup'_univ]
  refine
    Finset.sup'_le (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
      (f := fun i ↦ Metric.infDist x (S i)) ?_
  intro i hi
  -- Apply the triangle inequality to one coordinate and then compare with the outer maximum.
  calc
    Metric.infDist x (S i) ≤ Metric.infDist y (S i) + dist x y :=
      Metric.infDist_le_infDist_add_dist
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun j ↦ Metric.infDist y (S j)) + dist x y := by
      exact add_le_add_left
        (Finset.le_sup' (s := (Finset.univ : Finset ι))
          (f := fun j ↦ Metric.infDist y (S j)) (Finset.mem_univ i)) _

-- Proof sketch: each coordinate function `x ↦ Metric.infDist x (S i)` is `1`-Lipschitz by
-- `Metric.lipschitz_infDist_pt`. Since the index type is finite, the pointwise supremum is an
-- iterated binary `max`, and `LipschitzWith.max` preserves the `1`-Lipschitz constant.
/-- Lemma 8.20: for a finite nonempty family of sets, the function `x ↦ max_i d_{S_i}(x)` is
globally Lipschitz continuous with constant `1`; in particular this applies to the nonempty closed
convex sets of the convex feasibility setting. -/
theorem lipschitzWith_max_distance_to_sets (S : ι → Set α) :
    LipschitzWith 1 (max_distance_to_sets S) := by
  -- The textbook argument is the one-sided triangle inequality followed by the generic
  -- `LipschitzWith.of_le_add` wrapper.
  exact
    LipschitzWith.of_le_add (f := max_distance_to_sets S)
      (fun x y ↦ max_distance_to_sets_le_add_dist (S := S) (x := x) (y := y))

end

/-! ### Theorem_8_20 (from Chap08) -/
universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m : ℕ}
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt : ℝ}

/-- The standing Chapter 8 assumptions for the convex inequality-constrained problem: `X` is
convex, `f` and each `g i` are convex, `XStar` is the nonempty primal solution set with optimal
value `fOpt`, there is a strict feasible point in `X`, and every nonnegative-multiplier
Lagrangian minimization over `X` attains a minimizer. -/
class IsDualProjectedSubgradientProblem
    (X XStar : Set E) (f : E → ℝ) (g : Fin m → E → ℝ) (fOpt : ℝ) : Prop where
  feasible_convex : Convex ℝ X
  objective_convex : ConvexOn ℝ Set.univ f
  constraint_convex (i : Fin m) : ConvexOn ℝ Set.univ (g i)
  optimal_set_eq :
    XStar = {x | IsMinOn f {y | y ∈ X ∧ ∀ i : Fin m, g i y ≤ 0} x}
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (f '' {x | x ∈ X ∧ ∀ i : Fin m, g i x ≤ 0}) fOpt
  slater_condition_on_X :
    ∃ x ∈ X, ∀ i : Fin m, g i x < 0
  lagrangian_has_minimizer (lam : Fin m → NNReal) :
    ∃ x,
      IsMinOn
        (fun y ↦
          f y +
            dotProduct (fun i : Fin m ↦ (lam i : ℝ)) (fun i ↦ g i y))
        X x

/-- The feasible set of the Chapter 8 dual problem is the nonnegative orthant in multiplier
space. -/
def dual_problem_feasible_set (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {lam | ∀ i : Fin m, 0 ≤ lam i}

-- Proof sketch: unfold `dual_problem_feasible_set`; membership is exactly coordinatewise
-- nonnegativity of the multiplier vector.
/-- Membership in `dual_problem_feasible_set m` means that every multiplier coordinate is
nonnegative. -/
@[simp] theorem mem_dual_problem_feasible_set
    {lam : EuclideanSpace ℝ (Fin m)} :
    lam ∈ dual_problem_feasible_set m ↔ ∀ i : Fin m, 0 ≤ lam i := sorry

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "q" =>
  fun lam : Λ ↦
    sInf ((fun x : E ↦ ((f x + dotProduct lam (fun i ↦ g i x) : ℝ) : EReal)) '' X)

-- Proof sketch: apply the strong-duality theorem for convex inequality-constrained problems under
-- the Slater-type assumptions packaged by `h_problem`. This identifies the least upper bound of
-- the dual objective values with the primal optimal value.
/-- Theorem 8.20 (1): under Assumption 8.41, if `qOpt` is the optimal value of the dual problem
`max {q(λ) : λ ∈ ℝ_+^m}`, then `qOpt = fOpt`. -/
theorem dual_projected_subgradient_problem_strong_duality
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {qOpt : EReal}
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) qOpt) :
    qOpt = (fOpt : EReal) := sorry

-- Proof sketch: apply the dual-attainment part of the strong-duality theorem for convex
-- inequality-constrained problems under the Slater-type assumptions packaged by `h_problem` to
-- obtain a maximizer of `q` on the nonnegative orthant whose value is `qOpt`.
/-- Theorem 8.20 (2): under Assumption 8.41, the dual problem attains the optimal value `qOpt`
at some nonnegative multiplier. -/
theorem dual_projected_subgradient_problem_dual_attainment
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {qOpt : EReal}
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) qOpt) :
    ∃ lamStar : Λ,
      IsMaxOn q (dual_problem_feasible_set m) lamStar ∧
        q lamStar = qOpt := sorry

end
