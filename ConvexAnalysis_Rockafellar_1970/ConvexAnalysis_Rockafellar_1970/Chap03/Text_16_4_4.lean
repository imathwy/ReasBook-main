import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

attribute [local instance] Classical.propDecidable

section

variable {ι : Type*} [Fintype ι]

local notation "E" => ι → ℝ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.4.4 computes the Fenchel conjugate of the negative entropy
  `∑ i ξᵢ log ξᵢ` on the simplex `{ξ | ξᵢ ≥ 0, ∑ i ξᵢ = 1}`, extended by `+∞` outside that
  simplex.
- `core/canonical`: the owner abstraction is the chapter Fenchel conjugate `convexConjugate` on
  `WithBotTop ℝ`-valued functions on a finite coordinate owner.
- `bridge/view`: the simplex constraint is represented by the canonical mathlib owner
  `stdSimplex ℝ ι`, and the conjugate value is stated directly by the canonical log-sum-exp
  formula `log (∑ i exp x⋆ᵢ)`.

Domain-style sampling used here:
- `convexConjugate` from Defn. 12.2;
- `stdSimplex`;
- `δ[ℝ](· | ·)` from Defintion 4.8.1 as the canonical `+∞`-outside restriction owner;
- the concrete conjugate-computation pattern of Text 12.2.4;
- the closure-free sum-conjugate owner theorem
  `convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior`
  from Theorem 16.4.3.

Primitive data vs derived API:
- primitive source-facing data: the coordinate entropy sum `∑ i, ξᵢ log ξᵢ`;
- owner-derived restriction data: `δ[ℝ](· | stdSimplex ℝ ι)`;
- derived API: its pointwise Fenchel-conjugate formula.

Layer target: `source-facing`, expressed directly through `convexConjugate` and the existing
simplex owner, without introducing a surrogate package.
-/

/-- The function `ξ ↦ ∑ i ξᵢ log ξᵢ` on the standard simplex, extended by `+∞` outside the
simplex. Because `Real.log 0 = 0`, this agrees with the convention `0 log 0 = 0`. -/
def standardSimplexNegativeEntropyFunction : E → WithBotTop ℝ :=
  fun x ↦
    (((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ) : WithBotTop ℝ) +
      δ[ℝ](x | stdSimplex ℝ ι)

-- Proof sketch: unfold `standardSimplexNegativeEntropyFunction` as the entropy sum plus the
-- canonical indicator `δ[ℝ](· | stdSimplex ℝ ι)`, then split on membership in the
-- simplex. On the simplex the indicator term is `0`; off the simplex it is `⊤`.
/-- Evaluating `standardSimplexNegativeEntropyFunction` gives the entropy sum on the simplex and
`+∞` away from the simplex. -/
theorem standardSimplexNegativeEntropyFunction_apply (x : E) :
    standardSimplexNegativeEntropyFunction x =
      if _hx : x ∈ stdSimplex ℝ ι then
        (((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ) : WithBotTop ℝ)
      else
        ⊤ := by
  by_cases hx : x ∈ stdSimplex ℝ ι
  · simp [standardSimplexNegativeEntropyFunction, hx]
  · have htop :
      (((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ) : WithBotTop ℝ) + ⊤ = (⊤ : WithBotTop ℝ) :=
      WithBotTop.coe_add_top ((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ)
    simpa [standardSimplexNegativeEntropyFunction, hx] using htop

section

variable [Nonempty ι]

-- Proof sketch: write the source function as the sum of the separable scalar function
-- `k(t) = t log t` on `t ≥ 0` with the indicator of the affine simplex constraint
-- `∑ i ξᵢ = 1`, then apply Theorem 16.4.3 to remove the closure in the conjugate-of-sum formula.
-- The scalar conjugate is `k⋆(s) = exp (s - 1)`, while the simplex indicator contributes a single
-- Lagrange multiplier `λ`; minimizing `λ + ∑ i exp (x⋆ᵢ - λ - 1)` in `λ` gives
-- `log (∑ i exp x⋆ᵢ)`.
/-- Text 16.4.4: if `f(ξ) = ∑ i ξᵢ log ξᵢ` on the standard simplex
`{ξ | ξᵢ ≥ 0, ∑ i ξᵢ = 1}` and `f(ξ) = +∞` off that simplex, then the Fenchel conjugate of `f`
is the log-sum-exp function `x⋆ ↦ log (∑ i exp x⋆ᵢ)`. -/
theorem convexConjugate_standardSimplexNegativeEntropyFunction_eq_logSumExp
    (xStar : E) :
    (standardSimplexNegativeEntropyFunction (ι := ι))⋆ xStar =
      ((Real.log (∑ i, Real.exp (xStar i)) : ℝ) : WithBotTop ℝ) := sorry

end

end
