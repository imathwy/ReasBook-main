import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_16
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_13

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

namespace Bifunction

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.14 upgrades Lemma 31.0.13 from existence to uniqueness of a
  Kuhn-Tucker functional for the identity-map Fenchel perturbation problem, and in the Euclidean
  bridge specialization identifies the unique vector representative as the gradient of the
  perturbation value function at `0`.
- `core/canonical`: the owner abstractions already present upstream are
  `Bifunction.perturbationFunction`, `Bifunction.adjoint` together with the zero-slice
  objective owner `(·)₀`, `Bifunction.IsStrictlyConsistent`, `Function.realBranch`,
  `_root_.subdifferentialAt`,
  `DifferentiableAt`, and the Euclidean bridge owner `Function.subdifferentialAt` with gradient
  notation `∇`.
- `bridge/view`: the source phrase “`p` is finite and differentiable at `0`” is expressed
  canonically as strict consistency `IsStrictlyConsistent F` together with differentiability of
  the real branch `p.realBranch`. The primary uniqueness theorem is stated on the intrinsic dual
  owner, with a separate Euclidean bridge theorem for vector-valued statements.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `_root_.subdifferentialAt` and `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `Bifunction.isKuhnTuckerVector_iff_mem_subdifferentialAt_perturbationFunction_zero` from
  `Lemma_31_0_13`;
- `Bifunction.isKuhnTuckerVector_iff_dualObjective_eq_perturbationFunction_zero` from
  `Lemma_31_0_13`;
- `Bifunction.dualObjective_eq_perturbationFunction_zero_iff_mem_subdifferentialAt` from
  `Lemma_31_0_13`;
- `Function.realBranch` from `Chap02/Theorem_10_4`, used on the theorem surface as `p.realBranch`;
- the Chapter 25 singleton-subdifferential versus differentiability bridge for `p.realBranch`;
- the Chapter 23 directional-derivative/gradient bridge for the same real branch.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, the perturbation owner
  `perturbationFunction (fenchelPerturbation (LinearMap.id : E →ₗ[ℝ] E) f g)` and the
  owner-level hypotheses actually used downstream here: convexity `p.IsConvex ℝ`,
  pointwise finiteness `p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤`, and the dual-value identification
  from Lemma 31.0.13;
- derived API: uniqueness of the Kuhn-Tucker functional in `StrongDual ℝ E`, plus the Euclidean
  bridge uniqueness of a Kuhn-Tucker vector and the source-facing gradient formula. Dual
  attainment at value `p 0` remains a companion bridge from `Lemma_31_0_13`, not the main owner
  surface. The theorem surface carries pointwise finiteness at `0` directly as primitive data
  (`p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤`), while strict consistency continues to provide the
  canonical local interior-domain owner `IsStrictlyConsistent F`; the dual objective stays the
  existing Chapter 6 owner `(F⋆)₀` through the short local surface `dualObjective`.

Layer target: `source-facing`, but phrased directly on the canonical perturbation-function owner
and the existing Chapter 23/25 differentiability and subdifferential owners, with the intrinsic
dual layer primary and the inner-product vector layer as bridge.
-/

variable (f g : E → WithBotTop ℝ)

local notation "F" => fenchelPerturbation (LinearMap.id : E →ₗ[ℝ] E) f g
local notation "p" => perturbationFunction F
local notation "F⋆" => adjoint (StrongDual ℝ E) (StrongDual ℝ E) F
local notation "dualObjective" => ((F⋆)₀ : StrongDual ℝ E → WithBotTop ℝ)
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set (StrongDual ℝ E))

-- Proof sketch: translate uniqueness of the canonical Kuhn-Tucker owner into singletonhood of the
-- dual-valued subdifferential owner of `p` at `0`, using only the convex/pointwise-finiteness/
-- value data actually consumed from Lemma 31.0.13; then apply the Chapter 25
-- singleton-subdifferential
-- versus differentiability correspondence to the finite real branch `p.realBranch`.
/-- Lemma 31.0.14, intrinsic-dual owner form: under the convex perturbation hypothesis, finite
value at `0`, and the dual-value identity, there exists a unique Kuhn-Tucker functional
exactly when the
perturbation function is finite and differentiable at `0`. In the owner language, local finiteness
at `0` is represented by strict consistency `IsStrictlyConsistent F`, and pointwise finiteness at
`0` is carried directly by the primitive hypothesis `p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤` for the
canonical real branch
`p.realBranch`. -/
theorem existsUnique_kuhnTuckerFunctional_iff_differentiableAt_perturbationFunction_zero
    [FiniteDimensional ℝ E]
    (hp_convex : ConvexOn ℝ (Set.univ : Set E) p)
    (hp0_finite : p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hdual : (⨆ xStar : StrongDual ℝ E, dualObjective xStar) = p 0) :
    (∃! xStar : StrongDual ℝ E, xStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := by
  sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f g : E → WithBotTop ℝ)

local notation "F" => fenchelPerturbation (LinearMap.id : E →ₗ[ℝ] E) f g
local notation "p" => perturbationFunction F
local notation "F⋆" => adjoint E E F
local notation "dualObjective" => ((F⋆)₀ : E → WithBotTop ℝ)
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set E)

/-- Lemma 31.0.14, Euclidean bridge form: uniqueness of a Kuhn-Tucker vector is equivalent to
strict consistency and differentiability of the real branch of the perturbation function at `0`.
This specializes the intrinsic dual-owner statement to the inner-product model owner. -/
theorem existsUnique_kuhnTuckerVector_iff_differentiableAt_perturbationFunction_zero
    [FiniteDimensional ℝ E]
    (hp_convex : ConvexOn ℝ (Set.univ : Set E) p)
    (hp0_finite : p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hdual : (⨆ xStar : E, dualObjective xStar) = p 0) :
    (∃! xStar : E, xStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := by
  sorry

-- Proof sketch: once the previous theorem yields uniqueness together with differentiability of the
-- finite branch, the unique supporting vector is the gradient of `p.realBranch` at `0`; the only
-- owner data needed on `p` are convexity, pointwise finiteness at `0`, and the dual-value
-- identity.
/-- In the differentiable case of Lemma 31.0.14, the unique Kuhn-Tucker vector is the gradient of
the real branch of the perturbation function at `0`. -/
theorem gradient_is_kuhnTuckerVector_of_differentiableAt_perturbationFunction_zero
    [CompleteSpace E]
    (hp_convex : ConvexOn ℝ (Set.univ : Set E) p)
    (hp0_finite : p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hdual : (⨆ xStar : E, dualObjective xStar) = p 0)
    (hstrict : IsStrictlyConsistent F)
    (hdiff : DifferentiableAt ℝ p.realBranch 0) :
    (∇ p.realBranch 0) ∈ KT(F) := by
  sorry

end

end Bifunction
