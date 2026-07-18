import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Lemma_3_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.36 is `source-facing` in the chapter's inequality-constrained convex-optimality API.
Its `core/canonical` owner notions already exist upstream:
1. `subdifferentialAt` from Theorem 3.4 for real-valued subgradients;
2. `inequality_feasible_set` from Lemma 3.5 for the feasible set;
3. `optimality_residual` from Lemma 3.5 for the canonical finite-maximum residual objective.
The primitive source-facing data here are only the scalar/vector multipliers together with the
textbook Fritz-John conditions they satisfy, so this file keeps those conditions as a plain
predicate and reuses the owner declarations directly. -/
recall subdifferentialAt
recall inequality_feasible_set
recall optimality_residual

/-- A scalar `lambda0` together with inequality multipliers `lambda` satisfies the Fritz-John
conditions for the convex problem with objective `f`, constraints `g`, and candidate optimizer
`xstar` when the multipliers are nonnegative, not all zero, satisfy the extendedRealSubdifferential
stationarity condition, and obey complementary slackness. -/
def IsFritzJohnMultiplier
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
    (lambda0 : ℝ) (lambda : Fin m → ℝ) : Prop :=
    0 ≤ lambda0 ∧
      (∀ i, 0 ≤ lambda i) ∧
      (lambda0 ≠ 0 ∨ ∃ i : Fin m, lambda i ≠ 0) ∧
      (0 : StrongDual ℝ E) ∈
          lambda0 • subdifferentialAt f xstar + ∑ i, lambda i • subdifferentialAt (g i) xstar ∧
        ∀ i, lambda i * g i xstar = 0

/-- Unfolding `IsFritzJohnMultiplier` gives exactly the textbook Fritz-John multiplier
conditions. -/
@[simp] theorem isFritzJohnMultiplier_iff
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda0 : ℝ} {lambda : Fin m → ℝ} :
    IsFritzJohnMultiplier f g xstar lambda0 lambda ↔
      0 ≤ lambda0 ∧
        (∀ i, 0 ≤ lambda i) ∧
        (lambda0 ≠ 0 ∨ ∃ i : Fin m, lambda i ≠ 0) ∧
        (0 : StrongDual ℝ E) ∈
            lambda0 • subdifferentialAt f xstar + ∑ i, lambda i • subdifferentialAt (g i) xstar ∧
          ∀ i, lambda i * g i xstar = 0 :=
  Iff.rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: set `F := optimality_residual f (f xstar) g`. By Lemma 3.5, the feasible
-- minimality of `xstar` for `f` is equivalent to global minimality of `F`, and `F xstar = 0`.
-- Apply Fermat's rule to obtain `0 ∈ ∂F(xstar)`, then use the finite max-rule for
-- subdifferentials in the owner coordinate presentation of `optimality_residual` to write `0` as
-- a convex combination of active subgradients. Separate the last coordinate, corresponding to
-- `f - f xstar`, from the constraint coordinates and extend inactive multipliers by `0` to obtain
-- the Fritz-John coefficients and complementary slackness.
/-- Theorem 3.36: Fritz-John necessary optimality conditions. If `xstar` is a feasible optimal
solution of the convex problem `min f x` subject to `g i x ≤ 0` for all `i`, then there exist
nonnegative multipliers `lambda0` and `lambda` that are not all zero and satisfy the
extendedRealSubdifferential stationarity condition together with complementary slackness at `xstar`. -/
theorem exists_fritz_john_multipliers_of_isMinOn
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i : Fin m, ConvexOn ℝ Set.univ (g i))
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hmin : IsMinOn f (inequality_feasible_set g) xstar) :
    ∃ (lambda0 : ℝ) (lambda : Fin m → ℝ),
      IsFritzJohnMultiplier f g xstar lambda0 lambda := sorry

end
