import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_2 (from Chap08) -/
universe u v

section

variable {E : Type u} {α : Type v} [Preorder α]

/- Definition 8.2 is `source-facing`: it introduces the unconstrained minimization problem for an
objective `f` on the whole ambient space. The canonical mathlib owner for a global minimizer is
`IsMinOn f Set.univ x`, so this file exposes the corresponding solution-set view instead of adding
a bundled optimization-problem structure or a redundant alias for `f` itself. The Euclidean-space
setup from Definition 8.1 is not semantically active for this owner and is therefore omitted. -/

/-- Definition 8.2: the unconstrained problem `(P)` for an objective `f` is represented by the set
of points that globally minimize `f` on the whole ambient space. -/
def unconstrained_problem_solutions (f : E → α) : Set E :=
  {x | IsMinOn f Set.univ x}

-- Proof sketch: unfold `unconstrained_problem_solutions`; membership in the set is definitionally
-- the statement that the point is a global minimizer of `f`.
/-- A point belongs to the solution set of the unconstrained problem exactly when it globally
minimizes `f`. -/
theorem mem_unconstrained_problem_solutions_iff {f : E → α} {x : E} :
    x ∈ unconstrained_problem_solutions f ↔ IsMinOn f Set.univ x := by
  -- Unfold the source-facing owner so membership becomes the canonical mathlib minimizer predicate.
  rfl

-- Proof sketch: combine `mem_unconstrained_problem_solutions_iff` with mathlib's
-- `isMinOn_univ_iff` to rewrite global minimality as pointwise comparison with every objective
-- value.
/-- A point solves the unconstrained problem exactly when its objective value is less than or equal
to the value at every other point. -/
theorem mem_unconstrained_problem_solutions_iff_forall_le {f : E → α} {x : E} :
    x ∈ unconstrained_problem_solutions f ↔ ∀ y, f x ≤ f y := by
  -- First pass from the solution-set view to the global minimizer predicate on `Set.univ`.
  rw [mem_unconstrained_problem_solutions_iff]
  -- Then use mathlib's characterization of `IsMinOn` over the whole ambient space.
  simpa using (isMinOn_univ_iff (f := f) (a := x))

end

/-! ### Lemma_8_2 (from Chap08) -/
universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: choose `α > 0` with the lower directional derivative at `x` along `d` bounded
-- above by `-2 α`. The liminf hypothesis then yields `ε₁ > 0` such that
-- `(f (x + t • d) - f x) / t ≤ -α` for all `t ∈ (0, ε₁]`, hence
-- `f (x + t • d) ≤ f x - α t < f x`. Since `x ∈ interior (effective_domain f)`, some ball around
-- `x` lies in `effective_domain f`; because `d ≠ 0`, choosing `ε₂` so that `t • d` stays in that
-- ball for `t ∈ (0, ε₂]` gives the domain membership. Taking `ε = min ε₁ ε₂` yields the claim.
/-- Lemma 8.2: if `f : E → (-∞, ∞]` is represented by an `EReal`-valued function with no `⊥`
values, `x` lies in the interior of `dom(f)`, and the lower directional derivative of `f` at `x`
along a nonzero direction `d` is negative, then `f` strictly decreases along the ray
`x + t • d` for all sufficiently small `t > 0`, and those nearby points remain in `dom(f)`. -/
theorem exists_strict_decrease_along_descent_direction
    (f : E → EReal) (x d : E) (h_ne_bot : ∀ y, f y ≠ ⊥)
    (hx : x ∈ interior (effective_domain f)) (hd : d ≠ 0)
    (hdescent :
      Filter.liminf
          (fun t : ℝ ↦ (f (x + t • d) - f x) / (t : EReal))
          (𝓝[>] (0 : ℝ)) < 0) :
    ∃ ε > 0, ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) ε →
      x + t • d ∈ effective_domain f ∧ f (x + t • d) < f x := sorry

end
