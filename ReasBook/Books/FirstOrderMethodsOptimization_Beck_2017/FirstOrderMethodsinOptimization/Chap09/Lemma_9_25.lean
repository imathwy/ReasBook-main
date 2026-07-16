import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt σ : ℝ}
variable {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}

/- Domain sampling for Lemma 9.25.
- Primary domain: composite mirror descent in Bregman geometry.
- Inspected owner declarations:
  `IsCompositeConvexMinimizationProblem f g XStar FOpt` and
  `IsCompositeMirrorDescentProblem f g XStar FOpt Lf` from Definition 9.4,
  `IsBregmanPotentialOn ω (effective_domain g) σ` from Definitions 9.2 and 9.5,
  `is_mirror_c_trajectory f g ω x s t` from Definition 9.6,
  `existsUnique_mirror_c_problem_minimizer_mem_domains` from Theorem 9.24, and
  `mirror_descent_best_value_gap_le` from Lemma 9.14.

Lemma 9.25 is `source-facing`: it states the weighted running-best Mirror-C objective-gap estimate
for a concrete trajectory with nonincreasing stepsizes. The best owner abstraction for the
iterative side is therefore `is_mirror_c_trajectory`, while the composite-objective assumptions
should use the smaller chapter owner `IsCompositeConvexMinimizationProblem`; the stronger
`IsCompositeMirrorDescentProblem` is only the `Lf`-augmented extension used by later rate theorems.
The primitive data are the composite convex problem package, the Bregman owner `B[ω]`, the
nonnegativity of `g` on `dom(g)`, and the concrete trajectory/stepsize hypotheses. -/

-- Proof sketch: start from the one-step Mirror-C inequality obtained by combining the non-Euclidean
-- second prox theorem with the three-point identity for the Bregman distance, then sum from
-- `n = 0` to `k`. Use `h_stepsize_antitone` together with the nonnegativity of `g` to convert the
-- shifted `g(x^{n+1})` terms into the weighted sum of objective gaps, and finish by comparing that
-- weighted sum with the prefix minimum encoded by `best_achieved_function_value`.
/-- Lemma 9.25: under the composite convex minimization assumptions extracted from Definition 9.4,
together with the mirror-map assumptions of Definition 9.5 and the Mirror-C trajectory data of
Definition 9.6, if `g` is nonnegative on `dom(g)` and the Mirror-C stepsizes are nonincreasing,
then for every optimal point `xStar ∈ XStar = X^*` and every iteration index `k`, the
running-best composite objective gap up to time `k` is bounded by the weighted ratio
`(t₀ g(x⁰) + B_ω(xStar, x⁰) + (1 / (2σ)) * ∑_{n=0}^k t_n^2 ‖f'(x^n)‖^2) / ∑_{n=0}^k t_n`. -/
theorem mirror_c_best_value_gap_le_of_antitone_stepsizes
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (h_stepsize_antitone : Antitone t)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt ≤
      ((t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) /
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := sorry

end
