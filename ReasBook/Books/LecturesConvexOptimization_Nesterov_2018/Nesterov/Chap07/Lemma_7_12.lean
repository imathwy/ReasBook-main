import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_57
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [AddCommGroup U] [Module ℝ U]

/- Lemma 7.12 lies in the barrier-subgradient / saddle-representation / Jensen-averaging domain.

Mandatory domain-style sampling:
- `Finset.centerMass` in mathlib, the canonical owner for normalized finite weighted averages;
- `ConcaveOn.le_map_centerMass` and `ConvexOn.map_centerMass_le` in mathlib, the canonical Jensen
  inequalities for passing between averaged points and averaged values;
- `SaddlePointRepresentation` in `Definition_7_59`, the Chapter 7 owner of the saddle data
  `(f, Ψ)`;
- `maximalValueOn` in `Definition_7_56`, the Chapter 7 `EReal` owner for maximization over a
  feasible set;
- `barrierSubgradientWeightSum` and `barrierSubgradientMaximalGap` in `Definition_7_57`, the
  Chapter 7 owners for `S_k` and `ℓ_k⋆`.

Best owner abstraction:
- source-facing: the averaged duality-gap estimate of Lemma 7.12;
- core/canonical: `SaddlePointRepresentation`, `Finset.centerMass`, `maximalValueOn`,
  `barrierSubgradientWeightSum`, and `barrierSubgradientMaximalGap`;
- bridge/view: the textbook symbols `\bar x_k`, `\bar w_k`, and `η`, which here are only views of
  those owners, not separate public declarations.

Primitive data:
- the feasible set `P`, an ambient objective extension `f`, the saddle representation owner
  `representation`, and a minimizing branch `w`;
- the iterate family `x`, chosen subgradients, weights `λ`, and index `k`.

Derived API:
- the primal and dual averages as direct `Finset.centerMass` expressions;
- the dual value as direct use of `maximalValueOn`.

The previous file exposed raw parameters `f`, `Ψ`, and `w` even though Definition 7.59 already
introduced the chapter owner surface for the saddle data. This refinement keeps only the ambient
objective extension `f : E → ℝ` needed to state concavity on the feasible set `P ⊆ E`, moves the
saddle data itself to `SaddlePointRepresentation`, removes the redundant standalone convexity
hypothesis because `ConcaveOn ℝ P f` already contains that convexity, and removes the redundant
owner-level minimizer-selection hypothesis because this averaged-gap estimate uses `w` only
through the assumed model inequality and the resulting weighted averages.
-/

-- Proof sketch: for each iterate `x_i`, use the assumed linearization inequality
-- `Ψ(y, w(x_i)) - f(x_i) ≤ ⟪g_i, y - x_i⟫`, weight by `λ_i`, sum over `i = 0, …, k`,
-- and divide by `S_k`. Then use convexity of the slices `Ψ(y, ·)` to pass from the weighted
-- average of the values `Ψ(y, w(x_i))` to `Ψ(y, \bar w_k)`, identify the resulting supremum with
-- `η(\bar w_k)`, and finally apply concavity of `f` on `P` to bound the weighted average of the
-- primal values by `f(\bar x_k)`.
/-- Lemma 7.12: with the canonical weighted averages
`\bar w_k = (1 / S_k) ∑_{i=0}^k λ_i w(x_i)` and
`\bar x_k = (1 / S_k) ∑_{i=0}^k λ_i x_i`, one has
`η(\bar w_k) - f(\bar x_k) ≤ (1 / S_k) ℓ_k^⋆`. -/
theorem barrierSubgradientAverageDualityGap_le_maximalGap
    {P : Set E} {f : E → ℝ} {representation : SaddlePointRepresentation ↥P U} {w : P → U}
    (hobjective_eq : ∀ y : P, representation y = f y)
    (hf_concave : ConcaveOn ℝ P f)
    (hsaddle_convex : ∀ y : P, ConvexOn ℝ Set.univ (representation.saddleFunction y))
    (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ)
    (hlam_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ lam i)
    (hlam_sum_pos : 0 < barrierSubgradientWeightSum lam k)
    (hsubgradient_model :
      ∀ i ∈ Finset.range (k + 1), ∀ y : P,
        representation.saddleFunction y (w (x i)) - representation (x i) ≤
          inner ℝ (subgradient i) ((y : E) - (x i : E))) :
    maximalValueOn (Set.univ : Set ↥P)
        (fun y ↦
          representation.saddleFunction y
            ((Finset.range (k + 1)).centerMass lam fun i ↦ w (x i))) -
        f ((Finset.range (k + 1)).centerMass lam fun i ↦ (x i : E)) ≤
      barrierSubgradientMaximalGap x subgradient lam k / barrierSubgradientWeightSum lam k := sorry

end
