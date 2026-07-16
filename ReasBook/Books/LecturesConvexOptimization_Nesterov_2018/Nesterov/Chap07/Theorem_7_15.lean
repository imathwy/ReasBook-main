import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_57
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Theorem_7_14
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_58

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient HessianDualLocalNorm WithTopConvexAnalysis

universe u

/- Theorem 7.15 lies in Chapter 7's barrier-subgradient explicit-rate domain.

Mandatory domain-style sampling:
- `DualBarrierSubgradientMethod.maximalGap_upper_bound` in `Chap07/Theorem_7_14`, the upstream
  maximal-gap owner theorem that still carries the source error term `A_k`;
- `DualBarrierSubgradientMethod.maximalGap` and `barrierSubgradientWeightSum` in
  `Chap07/Definition_7_57`, the Chapter 7 owners of `ℓ_k⋆` and `S_k`;
- `HessianDualLocalNorm.ofPosDefMem` in `Chap05/Definition_5_0_20`, the canonical owner of the
  barrier Hessian dual norm attached to the actual chosen subgradient field of the method;
- `barrierSubgradientLambda` and `barrierSubgradientBeta` in `Chap07/Definition_7_58`, the
  chapter owners of the parameter choice `(7.3.19)`.

Best owner abstraction:
- source-facing: Theorem 7.15's explicit rate for the normalized maximal gap of a
  `DualBarrierSubgradientMethod`;
- core/canonical: `method.maximalGap_upper_bound`, `method.maximalGap`,
  `barrierSubgradientWeightSum`, `HessianDualLocalNorm.ofPosDefMem`,
  `barrierSubgradientLambda`, and `barrierSubgradientBeta`;
- bridge/view: the generic algebraic simplification theorem
  `barrierSubgradient_rate_le_explicit_rate_of_preliminary_bound` and the parameter-choice
  preliminary estimate below.

Primitive data:
- the Chapter 7 method owner `method : DualBarrierSubgradientMethod P f`;
- the barrier complexity parameter `ν` and subgradient bound `M`;
- the canonical Chapter 5 Hessian-dual local-norm bound on the actual selected field of `method`,
  namely
  `HessianDualLocalNorm.ofPosDefMem method.F x.2 (method.dualSubgradient x) ≤ M`;
- the parameter-choice identities `λ_k = barrierSubgradientLambda k` and
  `β_k = barrierSubgradientBeta M ν k`.

Derived API:
- the owner-level barrier-subgradient-class membership of `-f`, reconstructed internally from the
  actual selected field and the canonical Hessian-dual bound;
- the local ratio hypothesis `hω`, derived in the bridge layer from the owner-level bounded
  subgradient data and the parameter choice `(7.3.19)`;
- the accumulated error term `method.accumulatedOmegaStarError ... k` from Theorem 7.14;
- the preliminary normalized maximal-gap estimate obtained from Theorem 7.14 under the parameter
  choice `(7.3.19)`;
- the closed-form explicit rate obtained by the generic algebraic bridge theorem.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply the assumed pre-simplified barrier-subgradient gap estimate, then use the
-- two elementary inequalities from the textbook proof to bound the algebraic prefactor by
-- `sqrt (ν / (k + 1)) + ν / (k + 1)` and the logarithmic factor by
-- `2 * (1 + log (2 + (3 / 2) * sqrt (ν (k + 1))))`.
/-- If a pre-simplified scalar bound for the normalized maximal-gap rate is already available,
then the two scalar inequalities used in the textbook proof convert it into the closed-form
explicit rate. This is the bridge/view algebraic step behind Theorem 7.15. -/
theorem barrierSubgradient_rate_le_explicit_rate_of_preliminary_bound
    (rate : ℕ → ℝ) (M : NNReal) (ν : {ν : ℝ // 0 < ν})
    (hpreliminary :
      ∀ k : ℕ,
        rate k ≤
          (((M : ℝ) *
              ((Real.sqrt (ν : ℝ) / ((k : ℝ) + 1)) * ((1 / 2 : ℝ) + Real.sqrt (k : ℝ)) +
                (((ν : ℝ) + Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))) / ((k : ℝ) + 1)) *
                  (1 + 2 * Real.log
                    (1 + Real.sqrt (1 + 3 * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))))))) : ℝ))
    (k : ℕ) :
    rate k ≤
      ((2 * (M : ℝ) *
          (Real.sqrt ((ν : ℝ) / ((k : ℝ) + 1)) + (ν : ℝ) / ((k : ℝ) + 1)) *
            (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1)))) : ℝ)) :=
  sorry

namespace DualBarrierSubgradientMethod

variable {P : Set E} {f : E → ℝ}

-- Proof sketch: use Theorem 7.14 for `method.maximalGap`, specialize the Chapter 7 parameter
-- choice `λ_k = 1` and `β_k = M (1 + sqrt (max k 1 / ν))`, divide by `S_k`, and insert the two
-- component estimates supplied by the textbook derivation of `(7.3.19)` to obtain the
-- pre-simplified normalized bound.
/-- Under the Chapter 7 parameter choice `(7.3.19)`, Theorem 7.14 and the two component bounds
produced in the textbook proof yield the pre-simplified estimate for `(1 / S_k) ℓ_k⋆` used in
Theorem 7.15. This is the source-to-bridge step; unlike the generic algebraic lemma above, it
still works directly with the actual method owner and the Chapter 7 data `A_k`, `S_k`, `λ_k`,
and `β_k`. -/
theorem maximalGap_le_preliminary_rate_of_parameter_choice
    (method : DualBarrierSubgradientMethod P f)
    [IsStandardSelfConcordantOn P method.F]
    (M : NNReal) (ν : {ν : ℝ // 0 < ν})
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hstep : ∀ i : ℕ, (method.stepSize i : ℝ) = barrierSubgradientLambda i)
    (hbeta : ∀ i : ℕ, (method.beta i : ℝ) = barrierSubgradientBeta M ν i)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (herror :
      ∀ k : ℕ,
        method.accumulatedOmegaStarError hH hω k /
            barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
          (M : ℝ) *
            (Real.sqrt (ν : ℝ) / ((k : ℝ) + 1)) *
              ((1 / 2 : ℝ) + Real.sqrt (k : ℝ)))
    (hlog :
      ∀ k : ℕ,
        let A := method.accumulatedOmegaStarError hH hω k;
        let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k;
        Real.sqrt (A / ((method.beta (k + 1) : ℝ) * (ν : ℝ))) +
            3 *
              ((S / (method.beta (k + 1) : ℝ)) *
                HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
                  (method.iterate_hessian_isPositive 0) (hH 0)
                  (method.dualSubgradient (method 0))) ≤
          Real.sqrt (1 + 3 * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))))
    (k : ℕ) :
    method.maximalGap k /
        barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
      (M : ℝ) *
        ((Real.sqrt (ν : ℝ) / ((k : ℝ) + 1)) * ((1 / 2 : ℝ) + Real.sqrt (k : ℝ)) +
          (((ν : ℝ) + Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))) / ((k : ℝ) + 1)) *
            (1 + 2 * Real.log
              (1 + Real.sqrt (1 + 3 * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1)))))) :=
  sorry

-- Proof sketch: `method.subgradient_spec x` is the Chapter 7 concave-subgradient owner for `f`
-- at `x`; by the sign-flip bridge from Definition 7.50 and the constrained-subdifferential owner
-- from Chapter 3, the negated chosen vector belongs to the constrained subdifferential of `-f`
-- over `P` at `x`.
/-- The actual chosen field of a `DualBarrierSubgradientMethod` supplies a constrained subgradient
of `-f` over `P` at each iterate point, after the canonical sign flip from concave to convex
subgradients. This is the bridge/view connecting Algorithm 7.12's chosen witnesses to the
source-facing owner `barrierSubgradientClass`. -/
theorem neg_subgradient_mem_subdifferentialWithin
    (method : DualBarrierSubgradientMethod P f) (x : P) :
    -method.subgradient x ∈ ∂[P] (fun y ↦ ((-f y : ℝ) : WithTop ℝ)) ((x : E)) :=
  sorry

/-- If the actual chosen field of a `DualBarrierSubgradientMethod` satisfies the pointwise owner
dual-norm bound `‖-method.subgradient x‖ₓ* ≤ M`, then the negated objective belongs to the
Chapter 7 barrier-subgradient class with the same bound. This is the canonical bridge from the
selected-witness layer to the owner-level class `𝓑_M(P)`. -/
private theorem neg_mem_barrierSubgradientClass_of_selected_dualNorm_le
    (method : DualBarrierSubgradientMethod P f)
    {pointNorm : P → Seminorm ℝ E}
    (hpointNorm : ∀ x : P, Seminorm.IsNorm (pointNorm x))
    (M : NNReal)
    (hselected :
      ∀ x : P,
        let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
        (pointNorm x).dualNorm (-method.subgradient x) ≤ (M : ℝ)) :
    (fun y ↦ -f y) ∈ barrierSubgradientClass P P pointNorm hpointNorm M := by
  rw [mem_barrierSubgradientClass_iff]
  intro x
  refine ⟨-method.subgradient x, ?_⟩
  let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
  exact ⟨method.neg_subgradient_mem_subdifferentialWithin x, hselected x⟩

-- Proof sketch: first apply the parameter-choice preliminary theorem above to recover the
-- normalized maximal-gap estimate supplied by the Chapter 7 maximal-gap machinery; then invoke the
-- generic algebraic bridge theorem to put that estimate into the closed-form rate displayed in the
-- textbook.
/-- Theorem 7.15: if a dual barrier subgradient method uses the Chapter 7 parameter choice
`λ_k = barrierSubgradientLambda k = 1` and
`β_k = barrierSubgradientBeta M ⟨ν, hν⟩ k = M (1 + √(max k 1 / ν))`, where `ν` is the actual
barrier parameter of `method.F` and `M` bounds the actual chosen field of `method` through the
canonical Chapter 5 Hessian dual local norm
`HessianDualLocalNorm.ofPosDefMem method.F x.2 (method.dualSubgradient x)`. The corresponding
owner-level class membership `-f ∈ 𝓑_M(P)` and the local ratio condition remain internal bridge
data, so the public theorem stays on the method owner together with the canonical Hessian-dual
bound. Then for every `k ≥ 0` the normalized maximal gap of the actual method satisfies the
displayed explicit rate. -/
theorem maximalGap_le_explicit_rate
    (method : DualBarrierSubgradientMethod P f)
    (M ν : NNReal) [IsSelfConcordantBarrierOnWith P ν method.F]
    [HasPositiveDefiniteHessianOn P method.F]
    (hν : 0 < (ν : ℝ))
    (hdual :
      ∀ x : P,
        HessianDualLocalNorm.ofPosDefMem method.F x.2 (method.dualSubgradient x) ≤ (M : ℝ))
    (hstep : ∀ i : ℕ, (method.stepSize i : ℝ) = barrierSubgradientLambda i)
    (hbeta : ∀ i : ℕ, (method.beta i : ℝ) = barrierSubgradientBeta M ⟨(ν : ℝ), hν⟩ i)
    (k : ℕ) :
    method.maximalGap k /
      barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
      ((2 * (M : ℝ) *
          (Real.sqrt ((ν : ℝ) / ((k : ℝ) + 1)) + (ν : ℝ) / ((k : ℝ) + 1)) *
            (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1)))) : ℝ)) :=
  sorry

end DualBarrierSubgradientMethod
