import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section KernelBridge

variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable {E : Type*} [AddCommGroup E]
variable (f₁ f₂ : E → WithTopBot α)

/-- Binary bridge from Rockafellar's positivity hypothesis to the canonical family owner
`noZeroSumAsymmetricRecession[![f₁, f₂]]`. -/
theorem noZeroSumAsymmetricRecession_two_of_positive_recession_sum
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z)) :
    noZeroSumAsymmetricRecession[![f₁, f₂]] := by
  intro z hz_nonpos hz_pos
  rw [Fin.sum_univ_two]
  intro hsum
  have hz1 : z 1 = -z 0 := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hsum
  by_cases hz0 : z 0 = 0
  · have hz1_zero : z 1 = 0 := by simpa [hz0] using hz1
    have hz_nonpos' : ((f₁)₀⁺) 0 + ((f₂)₀⁺) 0 ≤ 0 := by
      simpa [Fin.sum_univ_two, hz0, hz1_zero] using hz_nonpos
    have hz_pos' : (0 : WithTopBot α) < ((f₁)₀⁺) 0 + ((f₂)₀⁺) 0 := by
      simpa [Fin.sum_univ_two, hz0, hz1_zero] using hz_pos
    exact (not_lt_of_ge hz_nonpos') hz_pos'
  · have hz_nonpos' : ((f₁)₀⁺) (z 0) + ((f₂)₀⁺) (-z 0) ≤ 0 := by
      simpa [Fin.sum_univ_two, hz1] using hz_nonpos
    exact (not_lt_of_ge hz_nonpos') (hrecession (z 0) hz0)

end KernelBridge

section

variable
  {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable
  {α : Type*} [AddCommGroup α] [SMul 𝕜 α]
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 9.2.2 states that the binary infimal convolution `f₁ □ f₂` of two
  closed proper convex functions is again closed proper convex, and that its defining infimum is
  attained, provided the sum of the two recession functions is strictly positive away from `0`.
- `core/canonical`: the owner abstraction for this domain is the finite-family
  `finiteInfimalConvolution` API from Corollary 9.2.1 together with the chapter owners
  `(·)₀⁺`, `Function.IsConvex`, `Function.IsProper`,
  and `LowerSemicontinuous`.
- `bridge/view`: the binary operation `f₁ □ f₂` is the `Fin 2`
  specialization of `finiteInfimalConvolution`, via
  `finiteInfimalConvolution_two_eq_infimal_convolution`. Clause (3) is already owned upstream by
  `Function.IsConvex.infimal_convolution`, so this file should recall that theorem directly
  instead of introducing a parallel local name. The attainment clause is kept in the textbook
  variable order `f₁ (x - y) + f₂ y`, while the owner definition uses the equivalent one-parameter
  infimum `⨅ y, f₁ y + f₂ (x - y)`.

Domain-style sampling used here:
- `finiteInfimalConvolution_two_eq_infimal_convolution`;
- `finiteInfimalConvolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession`;
- `exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession`;
- `Function.isConvex_finiteInfimalConvolution`;
- `Function.recessionFunction`;
- the finite-dimensional Hausdorff topological vector space ambient assumptions over the ordered
  scalar field `𝕜`, with codomain layer `WithTopBot α`, already used by Corollary 9.2.1.

Primitive data vs derived API:
- primitive inputs: the two functions `f₁`, `f₂` together with the convexity and closedness
  hypotheses, the pointwise lower-bound hypotheses `∀ x, ⊥ < fᵢ x` used by the closedness and
  attainment clauses, the properness hypotheses used only by the properness clause, and the
  owner-level binary recession-kernel hypothesis
  `noZeroSumAsymmetricRecession[![f₁, f₂]]`; the source-facing positivity
  condition is kept as a bridge implication into that owner hypothesis. Clause (3) adds no
  primitive data beyond
  the upstream owner theorem's convexity inputs;
- derived API: lower semicontinuity, properness, convexity, and pointwise attainment for
  `infimal_convolution f₁ f₂`.

Layer target: this item stays `source-facing`, but its binary statements are refined to the
existing finite-family owner pattern rather than treated as a separate root abstraction. The
closedness, properness, and attainment clauses are the `Fin 2` specialization of Corollary 9.2.1,
while the convexity clause is a `bridge/view` recall of the existing owner theorem
`Function.IsConvex.infimal_convolution` and therefore does not keep a second public theorem name
or the other clauses' stronger hypotheses as primitive data.

Ambient-space refinement: the binary specialization uses no coordinates. Since the upstream owner
API in Corollary 9.2.1 already lives on an arbitrary finite-dimensional Hausdorff topological
vector space over `𝕜`, this file stays at that intrinsic ambient level rather than specializing
back to the textbook display model `R^n`.
-/

section Binary

variable (f₁ f₂ : E → WithTopBot α)

-- Proof sketch: this binary statement is the `Fin 2` specialization of the owner theorem from
-- Corollary 9.2.1. The owner theorem for this clause needs only convexity, closedness, the
-- pointwise exclusion of `⊥`, and the recession hypothesis, so the redundant properness binders
-- are removed here as well. `finiteInfimalConvolution_two_eq_infimal_convolution` rewrites the
-- owner conclusion into lower semicontinuity of `f₁ □ f₂`.
theorem infimal_convolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hkernel : noZeroSumAsymmetricRecession[![f₁, f₂]]) :
    LowerSemicontinuous (f₁ □ f₂) := by
  let F : Fin 2 → E → WithTopBot α := (![f₁, f₂] : Fin 2 → E → WithTopBot α)
  have hkernelF : Function.NoZeroSumAsymmetricRecession F := by
    simpa [F] using hkernel
  have hfin : LowerSemicontinuous (finiteInfimalConvolution F) :=
    finiteInfimalConvolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
      (f := F)
      (hf_convex := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_convex
        · simpa [F] using hf₂_convex)
      (hf_closed := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_closed
        · simpa [F] using hf₂_closed)
      (hkernel := hkernelF)
      (hf_bot := by
        intro i x
        fin_cases i
        · simpa [F] using hf₁_bot x
        · simpa [F] using hf₂_bot x)
  have hfin' : LowerSemicontinuous
      (Function.verticalInfimum (finiteInfimalConvolutionSupport F)) := by
    simpa [finiteInfimalConvolution] using hfin
  have htwo : Function.verticalInfimum (finiteInfimalConvolutionSupport F) = f₁ □ f₂ := by
    simpa [finiteInfimalConvolution, F] using
      finiteInfimalConvolution_two_eq_infimal_convolution (f := F)
  exact htwo ▸ hfin'

/-- Corollary 9.2.2 (1): if
`f₁0⁺(z) + f₂0⁺(-z) > 0` for every nonzero `z`, then the infimal
convolution `f₁ □ f₂` is closed, expressed as lower semicontinuity. -/
theorem infimal_convolution_lowerSemicontinuous_of_positive_recession_sum
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z)) :
    LowerSemicontinuous (f₁ □ f₂) := by
  exact infimal_convolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
    (f₁ := f₁) (f₂ := f₂)
    hf₁_convex hf₁_bot hf₁_closed hf₂_convex hf₂_bot hf₂_closed
    (noZeroSumAsymmetricRecession_two_of_positive_recession_sum
      (f₁ := f₁) (f₂ := f₂) hrecession)

-- Proof sketch: apply the same `Fin 2` specialization of Corollary 9.2.1 and rewrite the owner
-- conclusion across `finiteInfimalConvolution_two_eq_infimal_convolution`.
theorem infimal_convolution_isProper_of_no_zero_sum_asymmetric_recession
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_proper : f₁.IsProper)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_proper : f₂.IsProper)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hkernel : noZeroSumAsymmetricRecession[![f₁, f₂]]) :
    (f₁ □ f₂).IsProper := by
  let F : Fin 2 → E → WithTopBot α := (![f₁, f₂] : Fin 2 → E → WithTopBot α)
  have hkernelF : Function.NoZeroSumAsymmetricRecession F := by
    simpa [F] using hkernel
  have hfin : (finiteInfimalConvolution F).IsProper :=
    finiteInfimalConvolution_isProper_of_no_zero_sum_asymmetric_recession
      (f := F)
      (hf_convex := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_convex
        · simpa [F] using hf₂_convex)
      (hf_closed := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_closed
        · simpa [F] using hf₂_closed)
      (hkernel := hkernelF)
      (hf_proper := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_proper
        · simpa [F] using hf₂_proper)
  have hfin' : Function.IsProper
      (Function.verticalInfimum (finiteInfimalConvolutionSupport F)) := by
    simpa [finiteInfimalConvolution] using hfin
  have htwo : Function.verticalInfimum (finiteInfimalConvolutionSupport F) = f₁ □ f₂ := by
    simpa [finiteInfimalConvolution, F] using
      finiteInfimalConvolution_two_eq_infimal_convolution (f := F)
  exact htwo ▸ hfin'

/-- Corollary 9.2.2 (2): under the same recession-sum positivity hypothesis, the infimal
convolution `f₁ □ f₂` is proper. -/
theorem infimal_convolution_isProper_of_positive_recession_sum
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_proper : f₁.IsProper)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_proper : f₂.IsProper)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z)) :
    (f₁ □ f₂).IsProper := by
  exact infimal_convolution_isProper_of_no_zero_sum_asymmetric_recession
    (f₁ := f₁) (f₂ := f₂)
    hf₁_convex hf₁_proper hf₁_closed hf₂_convex hf₂_proper hf₂_closed
    (noZeroSumAsymmetricRecession_two_of_positive_recession_sum
      (f₁ := f₁) (f₂ := f₂) hrecession)

/- Corollary 9.2.2 (3) is the direct canonical owner theorem for binary infimal convolution
convexity. Unlike the closedness and properness clauses, this conclusion uses only convexity of
the two inputs, so the faithful refined surface is a recall of
`Function.IsConvex.infimal_convolution` rather than a duplicate local wrapper. -/
recall Function.IsConvex.infimal_convolution

-- Proof sketch: specialize the attainment clause of Corollary 9.2.1 to the binary family
-- `![f₁, f₂]`. The resulting minimizing decomposition `x = x₁ + x₂` is then rewritten in the
-- textbook variable order by taking `y := x₂`, so `x₁ = x - y`.
theorem exists_argmin_infimal_convolution_of_no_zero_sum_asymmetric_recession
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hkernel : noZeroSumAsymmetricRecession[![f₁, f₂]])
    (x : E) :
    ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y := by
  let F : Fin 2 → E → WithTopBot α := (![f₁, f₂] : Fin 2 → E → WithTopBot α)
  have hkernelF : Function.NoZeroSumAsymmetricRecession F := by
    simpa [F] using hkernel
  obtain ⟨xs, hsum, hvalue⟩ :=
    exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession
      (f := F)
      (hf_convex := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_convex
        · simpa [F] using hf₂_convex)
      (hf_closed := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_closed
        · simpa [F] using hf₂_closed)
      (hkernel := hkernelF)
      (hf_bot := by
        intro i x'
        fin_cases i
        · simpa [F] using hf₁_bot x'
        · simpa [F] using hf₂_bot x')
      x
  refine ⟨xs 1, ?_⟩
  have hx0 : xs 0 = x - xs 1 := by
    rw [eq_sub_iff_add_eq]
    simpa [Fin.sum_univ_two, add_comm] using hsum
  have hvalue' :
      Function.verticalInfimum (finiteInfimalConvolutionSupport F) x =
        f₁ (x - xs 1) + f₂ (xs 1) := by
    simpa [finiteInfimalConvolution, F, Fin.sum_univ_two, hx0] using hvalue
  have htwo : Function.verticalInfimum (finiteInfimalConvolutionSupport F) = f₁ □ f₂ := by
    simpa [finiteInfimalConvolution, F] using
      finiteInfimalConvolution_two_eq_infimal_convolution (f := F)
  exact htwo ▸ hvalue'

/-- Corollary 9.2.2 (4): for every `x`, the infimum in the textbook formula
`(f₁ □ f₂)(x) = inf_y (f₁ (x - y) + f₂ y)` is attained by some `y`. -/
theorem exists_argmin_infimal_convolution_of_positive_recession_sum
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z))
    (x : E) :
    ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y := by
  exact exists_argmin_infimal_convolution_of_no_zero_sum_asymmetric_recession
    (f₁ := f₁) (f₂ := f₂)
    hf₁_convex hf₁_bot hf₁_closed hf₂_convex hf₂_bot hf₂_closed
    (noZeroSumAsymmetricRecession_two_of_positive_recession_sum
      (f₁ := f₁) (f₂ := f₂) hrecession)
    x

end Binary

end
