import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_20
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_21
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_57

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped BigOperators Gradient HessianDualLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 7.14 lies in the Chapter 7 barrier-subgradient / self-concordant remainder domain.

Mandatory domain-style sampling:
- `HessianDualLocalNorm.ofDetNeZero F x hPos hH g` from `Chap05/Definition_5_0_20`, the owner
  surface for the determinant-based Hessian dual local norm;
- `ω_*` from `Chap05/Definition_5_0_21`, the Chapter 5 owner of the self-concordant upper
  remainder term;
- `IsSelfConcordantBarrierOnWith` from `Chap05/Definition_5_3_2`, the Chapter 5 owner that ties
  the barrier parameter `ν` to the actual barrier term `F`;
- `DualBarrierSubgradientMethod` from `Chap07/Algorithm_7_12`, the Chapter 7 source-facing owner
  of the iterates, step sizes, barrier parameters, and barrier data behind `Uβ`;
- `DualBarrierSubgradientMethod.maximalGap` and `barrierSubgradientWeightSum` from
  `Chap07/Definition_7_57`, the Chapter 7 owners of `ℓ_k⋆` and `S_k`.

Best owner abstraction:
- source-facing: Theorem 7.14's upper bound for the maximal gap of a
  `DualBarrierSubgradientMethod`;
- core/canonical: `method.maximalGap k`, `barrierSubgradientWeightSum`, `ω_*`,
  `IsSelfConcordantBarrierOnWith P ν method.F`, and the determinant-based dual-local-norm bridge;
- bridge/view: the accumulated self-concordant error term `A_k`.

Primitive data:
- the method owner `method : DualBarrierSubgradientMethod P f`;
- the barrier owner `[IsSelfConcordantBarrierOnWith P ν method.F]`, which makes `ν` the actual
  barrier complexity of `method.F`;
- the Hessian nondegeneracy data along the method iterates.

Derived API:
- the maximal gap `ℓ_k⋆` via `method.maximalGap`;
- the step sum `S_k` via `barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ))`;
- the accumulated self-concordant error `A_k` via `method.accumulatedOmegaStarError`.

The previous revision still stated the main theorem over free iterate, step-size, and smoothing
sequences together with a disconnected parameter `x₀`. This refinement keeps the auxiliary error
term, but moves the public theorem surface onto the actual Chapter 7 method owner so the initial
point is the method iterate `method 0` and the maximal gap is the established owner
`method.maximalGap`. The barrier parameter is now also tied to the actual barrier term by the
canonical Chapter 5 owner `[IsSelfConcordantBarrierOnWith P ν method.F]` instead of being a free
scalar.
-/

namespace DualBarrierSubgradientMethod

section

variable {P : Set E} {f : E → ℝ}
variable (method : DualBarrierSubgradientMethod P f)

/-- The barrier owner supplies Hessian positivity at every iterate of the method. -/
theorem iterate_hessian_isPositive
    [IsStandardSelfConcordantOn P method.F] (i : ℕ) :
    (hessian method.F (method i : E)).IsPositive :=
  (inferInstance : IsStandardSelfConcordantOn P method.F).hessian_isPositive (method i).2

/-- The accumulated barrier error term
`A_k = ∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))` for the actual Chapter 7 method data, where
`g_i` is the chosen subgradient at the iterate `x_i = method i`. The hypothesis `hω` records the
domain condition needed to evaluate `ω_*` at each stage. -/
def accumulatedOmegaStarError
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun i ↦
    let δi :=
      HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
        (method.iterate_hessian_isPositive i) (hH i)
        (method.dualSubgradient (method i))
    let τi : Set.Iio (1 : ℝ) := ⟨
      (method.stepSize i : ℝ) * δi / method.beta i,
      by
        have hlt : (method.stepSize i : ℝ) * δi < (method.beta i : ℝ) := by
          simpa [δi] using hω i
        exact (div_lt_iff₀ (method.beta i).2).2 (by simpa using hlt)⟩
    (method.beta i : ℝ) * ω_* τi

/-- Evaluating `method.accumulatedOmegaStarError hH hω k` gives the finite sum
`∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))` attached to the actual method data. -/
theorem accumulatedOmegaStarError_def
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (k : ℕ) :
    method.accumulatedOmegaStarError hH hω k =
      Finset.sum (Finset.range (k + 1)) fun i ↦
        let δi :=
          HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
            (method.iterate_hessian_isPositive i) (hH i)
            (method.dualSubgradient (method i))
        let τi : Set.Iio (1 : ℝ) := ⟨
          (method.stepSize i : ℝ) * δi / method.beta i,
          by
            exact
              (div_lt_iff₀ (method.beta i).2).2 (by
                simpa [δi] using hω i)⟩
        (method.beta i : ℝ) * ω_* τi :=
  rfl

-- Proof sketch: sum the one-step upper model for the smoothed support functions along the
-- barrier-subgradient iterates to control the accumulated `ω_*`-error by `A_k`, bound the
-- linearized value at the initial iterate `x₀ = method 0` by
-- `-3 ν S_k ‖g₀‖*_(x₀)`, and insert these estimates into the
-- logarithmic comparison bound coming from inequality `(7.3.12)`.
/-- Theorem 7.14: if the barrier-subgradient iterates `x_k ∈ P` have local ratios
`(λ_k / β_k) ‖g_k‖*_(x_k) < 1` and the smoothing parameters satisfy `β_k ≤ β_{k+1}`, then
for every `k ≥ 0` the maximal-gap owner `method.maximalGap k` is bounded by
`A_k + β_{k+1} ν [1 + 2 log (1 + sqrt (A_k / (β_{k+1} ν)) + 3 (S_k / β_{k+1}) ‖g₀‖*_(x₀))]`,
where `x₀ = method 0`, `g₀` is the chosen subgradient at `x₀`,
`S_k = ∑_{i=0}^k λ_i`, and
`A_k = ∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))`. -/
theorem maximalGap_upper_bound
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (hβ_mono : ∀ i : ℕ, (method.beta i : ℝ) ≤ method.beta (i + 1))
    (k : ℕ) :
    let A := method.accumulatedOmegaStarError hH hω k;
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k;
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0));
    method.maximalGap k ≤
      A +
        (method.beta (k + 1) : ℝ) * (ν : ℝ) *
          (1 +
            2 * Real.log
              (1 +
                Real.sqrt (A / ((method.beta (k + 1) : ℝ) * (ν : ℝ))) +
                3 * ((S / (method.beta (k + 1) : ℝ)) * δ0))) :=
  sorry

end

end DualBarrierSubgradientMethod

end
