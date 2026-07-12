import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_5_feasible_set
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} {m : ℕ}

/- Lemma 3.5 is `source-facing` in the chapter's finite-family inequality-constrained
optimization API. The relevant owner abstractions are:
1. mathlib's `IsMinOn` for minimizers on a set;
2. Chapter 3's `coordinatewiseMax` for the maximum of finitely many real quantities.
The primitive source-facing data are therefore only:
1. the feasible set cut out by the inequality family `g`;
2. the `(m + 1)`-tuple consisting of the objective gap and the constraint values.
The residual objective itself is derived from that tuple through the owner `coordinatewiseMax`,
so the file no longer keeps a parallel ad hoc finite-maximum encoding. -/
recall inequality_feasible_set
recall mem_inequality_feasible_set
recall coordinatewiseMax

variable {g : Fin m → E → ℝ}

/-- The coordinate vector whose last entry is the objective gap `f x - fbar` and whose first `m`
entries are the inequality values `g i x`. -/
def optimality_residual_coordinates
    (f : E → ℝ) (fbar : ℝ) (g : Fin m → E → ℝ) (x : E) : Fin (m + 1) → ℝ :=
  Fin.snoc (fun i ↦ g i x) (f x - fbar)

/-- The residual objective obtained by taking the coordinatewise maximum of the objective gap
`f x - fbar` and all inequality values `g i x`. -/
noncomputable def optimality_residual (f : E → ℝ) (fbar : ℝ) (g : Fin m → E → ℝ) : E → ℝ :=
  fun x ↦ coordinatewiseMax (optimality_residual_coordinates f fbar g x)

variable {f : E → ℝ} {fbar : ℝ}

/-- On the first `m` coordinates, `optimality_residual_coordinates` records the constraint
values. -/
@[simp] theorem optimality_residual_coordinates_castSucc
    (x : E) (i : Fin m) :
    optimality_residual_coordinates f fbar g x i.castSucc = g i x := by
  simp [optimality_residual_coordinates]

/-- On the last coordinate, `optimality_residual_coordinates` records the objective gap. -/
@[simp] theorem optimality_residual_coordinates_last
    (x : E) :
    optimality_residual_coordinates f fbar g x (Fin.last m) = f x - fbar := by
  simp [optimality_residual_coordinates]

-- Proof sketch: unfold `optimality_residual`; the fold starts at `f x - fbar`, and every later
-- coordinate of `optimality_residual_coordinates` is bounded above by its supremum, so the
-- objective-gap entry is bounded above by the resulting coordinatewise maximum.
/-- The objective gap `f x - fbar` is bounded above by the residual objective. -/
theorem objective_gap_le_optimality_residual
    (x : E) :
    f x - fbar ≤ optimality_residual f fbar g x := by
  simpa [optimality_residual, coordinatewiseMax] using
    le_ciSup (Finite.bddAbove_range (optimality_residual_coordinates f fbar g x)) (Fin.last m)

-- Proof sketch: each coordinate of `optimality_residual_coordinates` is bounded above by its
-- supremum, so every constraint entry is bounded above by the resulting coordinatewise maximum.
/-- Every individual constraint value is bounded above by the residual objective. -/
theorem constraint_le_optimality_residual
    (x : E) (i : Fin m) :
    g i x ≤ optimality_residual f fbar g x := by
  simpa [optimality_residual, coordinatewiseMax] using
    le_ciSup (Finite.bddAbove_range (optimality_residual_coordinates f fbar g x)) i.castSucc

-- Proof sketch: let `S = inequality_feasible_set g`. The hypothesis `hfbar` says precisely that
-- `fbar` is the least feasible objective value. If `x ∈ S` and `x` minimizes `f` on `S`, then
-- `f x = fbar`, so every entry in the finite max defining
-- `optimality_residual f fbar g x` is at most `0`, while the objective-gap term is exactly `0`;
-- hence `x` globally minimizes the residual. Conversely, if `x` globally minimizes the residual,
-- compare against a feasible point attaining `fbar` from `hfbar` to deduce the minimum residual
-- value is `0`; then `objective_gap_le_optimality_residual` and
-- `constraint_le_optimality_residual` force `f x ≤ fbar` and all constraints `g i x ≤ 0`. Using
-- the lower-bound part of `hfbar`, conclude `f x = fbar`, so `x` is a feasible minimizer of `f`.
/-- Lemma 3.5: if `fbar` is the minimum value of `f` on the inequality-feasible set determined by
`g`, then the optimal set of the constrained problem coincides with the global minimizer set of
the residual objective `x ↦ max {f x - fbar, g 0 x, …, g (m - 1) x}`. -/
theorem inequality_constrained_optimal_set_eq_global_minimizers_optimality_residual
    (hfbar : IsLeast (f '' inequality_feasible_set g) fbar) :
    {x | x ∈ inequality_feasible_set g ∧ IsMinOn f (inequality_feasible_set g) x} =
      {x | IsMinOn (optimality_residual f fbar g) Set.univ x} := sorry

end
