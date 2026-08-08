import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_36
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.37 is a `bridge/view` item in the same inequality-constrained convex-optimality
domain as Theorem 3.36. Its owner abstractions are the chapter `slaters_condition` from
Definition 3.20, the strict/weak feasible-set owners
`strict_inequality_feasible_set` and `inequality_feasible_set`, and the source-facing Fritz-John
multiplier predicate from Theorem 3.36. This file therefore keeps the textbook KKT wording only
as a thin specialization of `IsFritzJohnMultiplier f g xstar 1 lambda`, instead of
reintroducing parallel existential wrappers for strict feasibility or KKT data. -/
recall subdifferentialAt
recall strict_inequality_feasible_set
recall strict_inequality_feasible_set_subset_inequality_feasible_set
recall inequality_feasible_set
recall slaters_condition
recall IsFritzJohnMultiplier
recall exists_fritz_john_multipliers_of_isMinOn

section KKTContext

variable {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}

-- Proof sketch: in one direction, specialize the Fritz-John fields at `lambda0 = 1`, rewrite
-- `1 • subdifferentialAt f xstar` as `subdifferentialAt f xstar`, and discard the automatic
-- clauses `0 ≤ 1` and `1 ≠ 0`. In the other direction, assemble the KKT nonnegativity,
-- stationarity, and complementary-slackness data into the Fritz-John predicate at `lambda0 = 1`.
/-- A normalized Fritz-John multiplier is exactly a KKT multiplier: componentwise nonnegativity,
the extendedRealSubdifferential stationarity condition, and complementary slackness. -/
@[simp] theorem isFritzJohnMultiplier_one_iff {lambda : Fin m → ℝ} :
    IsFritzJohnMultiplier f g xstar 1 lambda ↔
      (∀ i : Fin m, 0 ≤ lambda i) ∧
        (0 : StrongDual ℝ E) ∈
            subdifferentialAt f xstar + ∑ i : Fin m, lambda i • subdifferentialAt (g i) xstar ∧
          ∀ i : Fin m, lambda i * g i xstar = 0 := sorry

end KKTContext

section ConvexProblemContext

variable {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
variable (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i : Fin m, ConvexOn ℝ Set.univ (g i))

-- Proof sketch: apply the Fritz-John necessary condition theorem to obtain multipliers
-- `(lambda0, lambda)`. Use the strict feasible point supplied by `hslater` and the subset
-- `strict_inequality_feasible_set g ⊆ inequality_feasible_set g` to rule out `lambda0 = 0`,
-- exactly as in the textbook contradiction argument. Normalize by dividing through by `lambda0`,
-- then package the resulting nonnegative multiplier vector as a normalized Fritz-John multiplier,
-- which is exactly the KKT condition.
/-- Theorem 3.37 (1): if `xstar` is feasible, minimizes the convex objective `f` on the
inequality-feasible set cut out by `g`, and Slater's condition holds, then there exists a KKT
multiplier vector at `xstar`. -/
theorem exists_kkt_multiplier_of_isMinOn_of_slaters_condition
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hmin : IsMinOn f (inequality_feasible_set g) xstar)
    (hslater : slaters_condition g) :
    ∃ lambda : Fin m → ℝ, IsFritzJohnMultiplier f g xstar 1 lambda := sorry

-- Proof sketch: form the convex Lagrangian objective
-- `h x = f x + ∑ i, lambda i * g i x`. The KKT stationarity assumption says
-- `0 ∈ ∂ h(xstar)` after the finite-dimensional sum rule for subdifferentials, so Fermat's rule
-- yields that `xstar` globally minimizes `h`. For any feasible `x`, the nonnegativity of
-- `lambda` and the inequalities `g i x ≤ 0` show `h x ≤ f x`, while complementary slackness gives
-- `h xstar = f xstar`; hence `f xstar ≤ f x` on the feasible set. The separate feasibility
-- hypothesis `hxstar` records the primal-feasibility part of the KKT conclusion.
/-- Theorem 3.37 (2): a feasible point `xstar` satisfying the KKT conditions for some multiplier
vector `lambda` is an optimal solution of the convex inequality-constrained problem. -/
theorem isMinOn_of_mem_inequality_feasible_set_of_isFritzJohnMultiplier_one
    (lambda : Fin m → ℝ)
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hlambda : IsFritzJohnMultiplier f g xstar 1 lambda) :
    IsMinOn f (inequality_feasible_set g) xstar := sorry

end ConvexProblemContext

end
