import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

open scoped Rockafellar

section KernelCondition

variable {ι : Type u}
variable {E : Type*} [AddCommGroup E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLattice α]

namespace Function

/-- Finite-operational recession-kernel condition over a finite index set `s`: no family `z` with
`∑ i ∈ s, (f i)₀⁺ (z i) ≤ 0 < ∑ i ∈ s, (f i)₀⁺ (-z i)` has zero total sum over `s`. -/
def NoZeroSumAsymmetricRecessionOn (s : Finset ι) (f : ι → E → WithTopBot α) : Prop :=
  ∀ z : ι → E,
    (∑ i ∈ s, (f i)₀⁺ (z i)) ≤ 0 →
    (0 : WithTopBot α) < ∑ i ∈ s, (f i)₀⁺ (-z i) →
    (∑ i ∈ s, z i) ≠ 0

section FintypeFamily

variable [Fintype ι]

/-- Family-level recession-kernel condition used in Corollary 9.2.1: this is the
`Finset.univ` specialization of `NoZeroSumAsymmetricRecessionOn`. -/
def NoZeroSumAsymmetricRecession (f : ι → E → WithTopBot α) : Prop :=
  NoZeroSumAsymmetricRecessionOn (s := (Finset.univ : Finset ι)) f

end FintypeFamily

end Function

namespace Rockafellar

/-- Scoped notation for the family-level asymmetric recession-kernel owner in Corollary 9.2.1. -/
scoped notation "noZeroSumAsymmetricRecession[" f "]" =>
  Function.NoZeroSumAsymmetricRecession f

end Rockafellar

end KernelCondition

section

variable {ι : Type u} [Fintype ι]
variable
  {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
  [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable
  {α : Type*} [AddCommGroup α] [SMul 𝕜 α]
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 9.2.1 treats the infimal convolution of a finite family of closed
  proper convex functions and gives closedness, properness, convexity, attainment of the defining
  infimum, and the recession formula. The source nonemptiness assumption is mathematically active
  only in the attainment clause, because for an empty index type the canonical decomposition
  condition `∑ i, xs i = x` is solvable only at `x = 0`, while the lower-semicontinuity,
  properness, convexity, and recession statements still make sense for the owner
  `finiteInfimalConvolution`.
- `core/canonical`: the project owners are `finiteInfimalConvolution`,
  `Function.recessionFunction`, `LowerSemicontinuous`, `Function.IsProper`, and
  `Function.IsConvex`.
- `bridge/view`: Rockafellar's proof packages the family into a sum function on the product space
  and applies Theorem 9.2 to the addition map. The public API here keeps the source-facing owner
  `finiteInfimalConvolution` rather than introducing a second linear-image wrapper.
- ambient-space refinement: neither the owner `finiteInfimalConvolution` nor the specialization of
  Theorems 9.2 and 9.3 uses coordinates, so the public statements live on an arbitrary
  finite-dimensional Hausdorff topological vector space over the ordered scalar field `𝕜` rather
  than the concrete model `EuclideanSpace ℝ (Fin n)`.

Domain-style sampling used here:
- `finiteInfimalConvolution` and `finiteInfimalConvolution_eq_sInf_decompositions`;
- `recessionFunction`;
- `Function.linearImage` and the statement pattern of Theorem 9.2;
- `Function.isConvex_finiteInfimalConvolution`;
- `Function.NoZeroSumAsymmetricRecessionOn` with the `Fintype` specialization
  `Function.NoZeroSumAsymmetricRecession`.

Primitive data vs derived API:
- primitive inputs: the finite family `f : ι → E → WithTopBot α`, convexity and closedness of its
  members, the source-visible recession-kernel hypothesis, and for the clauses that only need
  exclusion of `-∞`, the pointwise hypothesis `∀ i x, ⊥ < f i x`; the properness and recession
  clauses additionally use the somewhere-finite data packaged by `Function.IsProper`, while
  `[Nonempty ι]` is needed only for the attainment clause;
- derived API: lower semicontinuity, properness, convexity, pointwise attainment, and the
  recession identity for `finiteInfimalConvolution f`.

Layer target: this item stays `source-facing`, stated directly for the chapter owner
`finiteInfimalConvolution`.
-/

variable (f : ι → E → WithTopBot α)

-- Proof sketch: form the sum function `h(xs) = ∑ i, f i (xs i)` on the product space `ι → E`.
-- Theorem 9.3 gives lower semicontinuity of `h`, while
-- `Function.isConvex_sum_of_bot_lt` gives convexity from `hf_convex` and the pointwise
-- `⊥`-avoidance hypothesis `hf_bot`. The addition map `A(xs) = ∑ i, xs i` turns
-- `finiteInfimalConvolution f` into the linear image function `Ah`, and the displayed hypothesis
-- is exactly Theorem 9.2's asymmetric recession-kernel condition for this addition map.
section

/-- Corollary 9.2.1 (1): under the stated zero-sum recession hypothesis, the infimal convolution
of a finite family of convex closed functions that are everywhere strictly above `⊥` is closed,
expressed by lower semicontinuity of `finiteInfimalConvolution f`. -/
theorem finiteInfimalConvolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_bot : ∀ i x, ⊥ < f i x)
    : LowerSemicontinuous (finiteInfimalConvolution f) := sorry

end

section

-- Proof sketch: use the same sum-function and addition-map reduction as in part (1). Theorem 9.2
-- then gives properness of the linear image, and the linear image is exactly
-- `finiteInfimalConvolution f`.
/-- Corollary 9.2.1 (2): under the same hypothesis, the finite infimal convolution is proper. -/
theorem finiteInfimalConvolution_isProper_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_proper : ∀ i, (f i).IsProper)
    : (finiteInfimalConvolution f).IsProper := sorry

end

/- The convexity clause is exactly the existing finite-family owner theorem for
`finiteInfimalConvolution`. -/
recall Function.isConvex_finiteInfimalConvolution

section

-- Proof sketch: apply the attainment clause of Theorem 9.2 to the sum function on the product
-- space and the addition map. Translating the resulting point of the fiber `∑ i, xs i = x` back
-- through the definition of `finiteInfimalConvolution` gives an optimizing decomposition whenever
-- the value is finite, while in the case `finiteInfimalConvolution f x = ⊤` any decomposition of
-- `x` suffices.
variable [Nonempty ι]

/-- Corollary 9.2.1 (3): for each `x`, the infimum defining `finiteInfimalConvolution f x` is
attained by some decomposition `x = ∑ i, xs i`, assuming the finite index type is nonempty and
each summand is everywhere strictly above `⊥`. -/
theorem exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_bot : ∀ i x, ⊥ < f i x)
    (x : E) :
    ∃ xs : ι → E,
      (∑ i, xs i) = x ∧ finiteInfimalConvolution f x = ∑ i, f i (xs i) := sorry

end

section

-- Proof sketch: first identify `finiteInfimalConvolution f` with the linear image under the
-- addition map of the finite sum function on the product space. Theorem 9.3 computes the recession
-- function of that finite sum as the finite sum of the recession functions, and Theorem 9.2 then
-- transports recession functions across the addition map under the same kernel hypothesis.
/-- Corollary 9.2.1 (4): the recession function of the finite infimal convolution is the finite
infimal convolution of the recession functions,
`(f₁ □ ⋯ □ f_m)₀⁺ = f₁0⁺ □ ⋯ □ f_m0⁺`. -/
theorem
    recessionFunction_finiteInfimalConvolution_eq_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_proper : ∀ i, (f i).IsProper)
    : (finiteInfimalConvolution f)₀⁺ =
        finiteInfimalConvolution (fun i ↦ (f i)₀⁺) := sorry

end

end
