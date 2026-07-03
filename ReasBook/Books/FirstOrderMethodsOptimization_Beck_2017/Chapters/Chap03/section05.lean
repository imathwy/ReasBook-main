import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_5_1 (from Chap03) -/
/-
Theorem 3.5.1 is a `core/canonical` recall item in convex geometry. The owner notion is
`intrinsicInterior ℝ`, and the exact owner theorem for the source statement is
`Set.Nonempty.intrinsicInterior`.
-/
recall Set.Nonempty.intrinsicInterior

/-! ### Definition_3_5 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x : E}

/- Definition 3.5 is a `bridge/view` item in the chapter convex-analysis API: the owner object is
`subdifferential f x`, and the textbook phrase "f is subdifferentiable at x" is exactly the
nonemptiness proposition on that owner set. The downstream owner set `subdifferential_domain`
introduced in Definition 3.6 is derived from this same proposition, so this file only recalls it. -/
#check (subdifferential f x).Nonempty

end

/-! ### Lemma_3_5 (from Chap03) -/
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

/-! ### Lemma_3_5_feasible_set (from Chap03) -/
universe u

section

variable {E : Type u} {m : ℕ}

/- This file isolates the primitive feasible-set owner from Lemma 3.5. The owner abstraction is
the set cut out by a finite family of scalar inequalities; later residual-objective results are
derived API that should import this owner, not own it. -/

/-- The feasible set of the inequality-constrained problem cut out by the family `g`. -/
def inequality_feasible_set (g : Fin m → E → ℝ) : Set E :=
  {x | ∀ i, g i x ≤ 0}

variable {g : Fin m → E → ℝ}

/-- Membership in `inequality_feasible_set g` means satisfying every inequality constraint
`g i x ≤ 0`. -/
@[simp] theorem mem_inequality_feasible_set {x : E} :
    x ∈ inequality_feasible_set g ↔ ∀ i, g i x ≤ 0 :=
  Iff.rfl

end

/-! ### Proposition_3_5 (from Chap03) -/
/- Proposition 3.5 is recall-only in the chapter subdifferential API. The primitive owner data is
`subdifferential : Set (Module.Dual ℝ E)`. Convexity belongs to that owner abstraction itself,
while closedness is a topological bridge statement on `strongDualSubdifferential`; this file
therefore reuses those upstream declarations directly and introduces no parallel local wrapper. -/
recall isClosed_subdifferential
recall convex_subdifferential

/-! ### Theorem_3_5 (from Chap03) -/
universe u

open Bornology
open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (f : E → EReal) (X : Set E)

/- Theorem 3.5 is `source-facing` in the Chapter 3 convex-analysis API. Its owner declarations are
already the project primitives `effective_domain`, `is_convex_function`, and the continuous-dual
bridge `strongDualSubdifferential`; this file keeps the textbook compact-union boundedness
statement directly on that owner API instead of introducing any parallel wrapper. The ambient
properness of `f` is derived here from the source-relevant hypotheses `∀ y, f y ≠ ⊥`,
`X.Nonempty`, and `X ⊆ interior (effective_domain f)`, so it does not remain a primitive public
binder. -/
recall effective_domain
recall is_convex_function
recall strongDualSubdifferential

local notation "Y" => ⋃ x ∈ X, strongDualSubdifferential f x

-- Proof sketch: nonemptiness follows by choosing `x ∈ X` and applying the interior-point
-- existence theorem to the continuous-dual bridge `strongDualSubdifferential`. For boundedness,
-- argue by contradiction: choose `x_k ∈ X` and `g_k ∈ ∂f(x_k)` with unbounded dual norm, use
-- compactness of `X` and a positive distance from `X` to the complement of
-- `interior (effective_domain f)`, and combine the subgradient inequality with continuity of `f`
-- on the interior of its effective domain to obtain a uniform contradiction.
/-- Theorem 3.5: if `f` is a convex extended-real-valued function that never takes the value
`⊥`, and `X` is a nonempty compact subset of `interior (dom(f))`, then the union of the
continuous-dual subdifferentials `Y = ⋃ x ∈ X, strongDualSubdifferential f x` is nonempty and
bounded in the dual norm. Under the stated hypotheses, `effective_domain f` is automatically
nonempty, so this is equivalent here to the textbook properness assumption. -/
theorem subdifferential_biUnion_nonempty_and_isBounded_of_isCompact_subset_interior
    (h_ne_bot : ∀ y, f y ≠ ⊥) (hconvex : is_convex_function f) (hX_nonempty : X.Nonempty)
    (hX_compact : IsCompact X) (hX_subset : X ⊆ interior (effective_domain f)) :
    Set.Nonempty Y ∧ IsBounded Y := sorry

end
