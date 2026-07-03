import Mathlib
import Nesterov.Chap05.Definition_5_4_3_2
import Nesterov.Chap05.Definition_5_4_6_2
import Nesterov.Chap05.Definition_5_4_7_16
import Nesterov.Chap05.Definition_5_4_7_17
import Nesterov.Chap05.Theorem_5_4_6_2
import Nesterov.Chap05.Theorem_5_4_7_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.14 lies in the Chapter 5 posynomial / positive-orthant barrier-compatibility
domain.

Sampled owner declarations:
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the ambient/source-facing owners for
  simplex monomials;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for barrier compatibility;
* `IsBetaCompatibleWith.smul` and `IsBetaCompatibleWith.add` from `Theorem_5_4_6_2`, the canonical
  closure API for positive combinations;
* `monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier` from `Theorem_5_4_7_13`, the
  monomial compatibility owner theorem.

Best owner abstraction:
* source-facing: `posynomialXi` on the strict positive orthant;
* core/canonical: `IsBetaCompatibleWith` applied to the ambient finite sum of monomial terms;
* bridge/view: evaluation of that ambient finite sum on `positiveOrthant n`.

Primitive data:
* the positive coefficients `α : Fin m → Set.Ioi (0 : ℝ)`;
* the simplex exponents `a : Fin m → Δ[n]`.

Derived API:
* the source-facing owner `posynomialXi`;
* its evaluation lemma `posynomialXi_apply`;
* the bridge lemma identifying the corresponding ambient finite sum with `posynomialXi` on
  `positiveOrthant n`;
* the compatibility theorem for that ambient finite sum.

The previous version introduced a second public owner `ambientPosynomialXi` whose only role was to
repackage the ambient finite combination already determined by the monomial owners and the
`IsBetaCompatibleWith` closure API. This refinement keeps `posynomialXi` as the public owner,
adds a named bridge from the canonical ambient finite sum to `posynomialXi`, and uses that bridge
to keep the source-facing posynomial connected to the ambient compatibility surface without
preserving a parallel wrapper.
-/

/-- The posynomial `ξ(x) = \sum_{k=1}^m α_k x^{a_k}` on the strict positive orthant. -/
def posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    positiveOrthant n → ℝ :=
  ∑ k : Fin m, (α k : ℝ) • ξ_[(a k)]

/-- Evaluating `posynomialXi n m α a` at a positive vector gives the textbook sum formula. -/
@[simp] theorem posynomialXi_apply
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    posynomialXi n m α a x =
      ∑ k : Fin m, (α k : ℝ) * ξ_[(a k)] x := by
  simp [posynomialXi, smul_eq_mul]

/-- Restricting the canonical ambient finite sum of monomial terms to the strict positive orthant
recovers the source-facing posynomial `posynomialXi n m α a`. -/
@[simp] theorem sum_smul_ambientMonomialXi_eq_posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    (∑ k : Fin m, (α k : ℝ) • ambientMonomialXi (a k)) x = posynomialXi n m α a x := by
  simp [posynomialXi, smul_eq_mul]

private theorem zero_isOneCompatibleWith_positiveOrthantLogarithmicBarrier :
    IsBetaCompatibleWith
      (positiveOrthant n)
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (0 : Eₙ → ℝ) := by
  sorry

/-- Theorem 5.4.7.14: the posynomial
`ξ(x) = \sum_{k=1}^m α_k x^{a_k}` with positive coefficients and simplex exponents is
`1`-compatible with the logarithmic barrier
`F(x) = -\sum_{i=1}^n \log x^{(i)}` on the positive orthant `\mathbb{R}^n_{++}`. -/
theorem posynomialXi_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
    (m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    IsBetaCompatibleWith
      (positiveOrthant n)
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (∑ k : Fin m, (α k : ℝ) • ambientMonomialXi (a k)) := by
  -- The ambient function in the compatibility statement restricts to `posynomialXi n m α a`
  -- by `sum_smul_ambientMonomialXi_eq_posynomialXi`.
  induction m with
  | zero =>
      simpa using zero_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
  | succ m ih =>
      have hhead :
          IsBetaCompatibleWith
            (positiveOrthant n)
            (ConvexCone.positive ℝ ℝ)
            (standardLogarithmicBarrierAmbient n)
            (1 : NNReal)
            ((α 0 : ℝ) • ambientMonomialXi (a 0)) := by
        simpa using
          IsBetaCompatibleWith.smul
            (monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier (a 0))
            ⟨α 0, (α 0).2.le⟩
      have htail :
          IsBetaCompatibleWith
            (positiveOrthant n)
            (ConvexCone.positive ℝ ℝ)
            (standardLogarithmicBarrierAmbient n)
            (1 : NNReal)
            (∑ k : Fin m, ((α k.succ : Set.Ioi (0 : ℝ)) : ℝ) • ambientMonomialXi (a k.succ)) :=
        ih (fun k ↦ α k.succ) (fun k ↦ a k.succ)
      simpa [Fin.sum_univ_succ] using IsBetaCompatibleWith.add hhead htail

end
