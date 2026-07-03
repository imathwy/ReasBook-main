import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_4_1_1 (from Chap03) -/
noncomputable section

open scoped BigOperators Pointwise Rockafellar

section

variable {𝕜 : Type*} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {ι X Y : Type*}
variable [AddCommMonoid Y]
variable [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]

@[simp] private theorem pairing_zero_right_finset
    {𝕜 X Y : Type*} [AddCommGroup 𝕜] [AddCommMonoid Y]
    [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜] (xStar : X) :
    (⟪xStar, (0 : Y)⟫ₚ : 𝕜) = 0 := by
  have h0 : (⟪xStar, (0 : Y)⟫ₚ : 𝕜) =
      (⟪xStar, (0 : Y)⟫ₚ : 𝕜) + (⟪xStar, (0 : Y)⟫ₚ : 𝕜) := by
    simpa using
      (HasPairingAddRight.pairing_add_right
        (X := X) (Y := Y) (𝕜 := 𝕜) xStar (0 : Y) (0 : Y))
  have h0' : (⟪xStar, (0 : Y)⟫ₚ : 𝕜) + 0 =
      (⟪xStar, (0 : Y)⟫ₚ : 𝕜) + (⟪xStar, (0 : Y)⟫ₚ : 𝕜) := by
    simpa using h0
  have hcancel : (0 : 𝕜) = (⟪xStar, (0 : Y)⟫ₚ : 𝕜) := add_left_cancel h0'
  simpa using hcancel.symm

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.4.1.1 states that the support function of the Minkowski sum
  `C₁ + ··· + C_m` is the sum of the individual support functions.
- `core/canonical`: the owner abstractions are the project support function `supportFunction` on
  subsets of a pairing space and the finite pointwise set sum over a finite family.
- `bridge/view`: Rockafellar's notation `δ^*(· | C)` is rendered by `supportFunction C`.

Domain-style sampling used here:
- `supportFunction` from `Defintion_4_8_2`;
- `supportFunction_eq_iSup`, confirming that the owner already lives on arbitrary pairing spaces
  rather than only on the concrete inner-product model;
- the binary owner theorem `supportFunction_set_add` from `Text_13_1_3`;
- the canonical finite-sum recursion `Finset.sum_insert`.

Primitive data vs derived API:
- primitive inputs: a finite family of sets `C : ι → Set Y`;
- derived API: the support-function identity for the finite pointwise sum, with the reusable
  finite-aggregation owner theorem on `Finset` and the source-facing `δᵛ` theorem surface as its
  pointwise companion.

Layer target: `source-facing`, stated directly in the canonical support-function language already
used across the project.

Semantic note: the displayed support-function identity is already meaningful in the project's
canonical API for an arbitrary finite family of subsets of a pairing-space codomain, so the
textbook's convexity and nonemptiness hypotheses are omitted from the Lean statement.
-/

/-- The support function of a finite Minkowski sum is the sum of the individual support
functions. This is the canonical finite-aggregation owner theorem behind Corollary 16.4.1.1. -/
theorem supportFunction_finset_sum
    (s : Finset ι) (C : ι → Set Y) :
    (supportFunction (∑ i ∈ s, C i) : X → WithTopBot 𝕜) =
      ∑ i ∈ s, (supportFunction (C i) : X → WithTopBot 𝕜) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext xStar
      change (δᵛ(xStar | ({0} : Set Y)) : WithTopBot 𝕜) = 0
      rw [supportFunction_singleton]
      change (((⟪xStar, (0 : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) = 0)
      simp
  | @insert i s hi hs =>
      have hadd :
          (supportFunction (C i + ∑ x ∈ s, C x) : X → WithTopBot 𝕜) =
            (supportFunction (C i) : X → WithTopBot 𝕜) +
              (supportFunction (∑ x ∈ s, C x) : X → WithTopBot 𝕜) := by
        simpa using
          (supportFunction_set_add
            (C1 := C i) (C2 := (∑ x ∈ s, C x)))
      rw [Finset.sum_insert hi, hadd, hs, Finset.sum_insert hi]

/-- Pointwise form of `supportFunction_finset_sum`, written in Rockafellar's support-function
notation `δᵛ`. -/
theorem supportFunction_finset_sum_apply
    (s : Finset ι) (C : ι → Set Y) (xStar : X) :
    (δᵛ(xStar | ∑ i ∈ s, C i) : WithTopBot 𝕜) = ∑ i ∈ s, δᵛ(xStar | C i) := by
  simpa using congrFun (supportFunction_finset_sum s C) xStar

-- Proof sketch: specialize the public `Finset` aggregation theorem
-- `supportFunction_finset_sum` to the full finite family `Finset.univ`.
/-- Corollary 16.4.1.1: for a finite family `C`, the support value of the Minkowski sum `∑ i, C i`
is the sum of the individual support values. -/
theorem supportFunction_sum_eq_sum_supportFunction
    [Fintype ι] (C : ι → Set Y) (xStar : X) :
    (δᵛ(xStar | ∑ i, C i) : WithTopBot 𝕜) = ∑ i, δᵛ(xStar | C i) := by
  classical
  simpa using supportFunction_finset_sum_apply Finset.univ C xStar

end

/-! ### Corollary_16_4_1_2 (from Chap03) -/
noncomputable section

section

open scoped BigOperators
open scoped Rockafellar

universe u

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.4.1.2 states that the support function of the finite intersection
  of the closures `closure (C i)` is the lower-semicontinuous closure of the infimal convolution
  of the individual support functions.
- `core/canonical`: the owner abstractions already present are `supportFunction` for
  `δ*(· | C)`, set closure `closure`, indexed intersections `⋂ i, ...`,
  `finiteInfimalConvolution` for `⊕`, and `lowerSemicontinuousHull` for the function closure
  `cl`.
- `bridge/view`: the textbook support-function notation `δ*(· | C_i)` is rendered by
  `δᵛ(· | C i)`, while the right-hand-side closure is
  `cl(finiteInfimalConvolution ...)`.

Domain-style sampling used here:
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Text_13_1_4`;
- `convexConjugate_supportFunction_eq_indicatorFunction_closure` from `Text_13_1_5`;
- `lowerSemicontinuousHull_indicator_eq_indicator_closure` from `Text_7_0_14`;
- `convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_proper_convex`
  from `Theorem_16_4_2`;
- finite indexed intersections `⋂ i, closure (C i)`.

Primitive data vs derived API:
- primitive inputs: a finite family `C : ι → Set E` together with the convexity hypotheses;
- derived output: the displayed support-function identity itself.

Layer target: `source-facing`, stated directly in the canonical support-function and
finite-infimal-convolution language already used across the project.

Ambient refinement: the supporting owner theorem `Theorem_16_4_2` already lives on arbitrary
finite-dimensional scalar-field spaces with a continuous linear self-pairing and arbitrary finite
index types, so this corollary is stated at that same owner layer.
-/

omit [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
  [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜] in
private theorem indicatorFunction_isProper_of_nonempty
    (C : Set E) (hC_nonempty : C.Nonempty) :
    (δ[𝕜](· | C) : E → WithBotTop 𝕜).IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨?_, ?_⟩
  · rcases hC_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [mem_effectiveDomain] using
      (indicator_lt_top_iff_mem (α := 𝕜) (C := C) (x := x)).2 hx
  · intro x
    by_cases hx : x ∈ C
    · simp [hx]
    · simp [hx]

omit [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
  [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜] in
private theorem sum_indicatorFunction_eq_indicatorFunction_iInter
    (C : ι → Set E) :
    (fun x : E ↦ ∑ i, δ[𝕜](x | C i)) =
      (δ[𝕜](· | ⋂ i, C i) : E → WithBotTop 𝕜) := by
  classical
  funext x
  by_cases hx : ∀ i, x ∈ C i
  · have hmem : x ∈ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have hnot_union_compl : x ∉ ⋃ i, (C i)ᶜ := by
      intro hx_union
      rcases Set.mem_iUnion.mp hx_union with ⟨i, hi⟩
      exact hi (hx i)
    have hzero : ∀ i, δ[𝕜](x | C i) = 0 := by
      intro i
      simp [hx i]
    calc
      (∑ i, δ[𝕜](x | C i)) = ∑ i, (0 : WithBotTop 𝕜) := by
        congr with i
        exact hzero i
      _ = 0 := by simp
      _ = δ[𝕜](x | ⋂ i, C i) := by simp [hnot_union_compl]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hnotmem : x ∉ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have hmem_union_compl : x ∈ ⋃ i, (C i)ᶜ := by
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have hsum_ne_bot :
        Finset.sum (Finset.univ.erase i)
          (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) ≠ (⊥ : WithBotTop 𝕜) := by
      refine WithBotTop.sum_ne_bot_of_forall_ne_bot ?_
      intro j hj
      by_cases hjx : x ∈ C j
      · simp [hjx]
      · simp [hjx]
    have htail_bot :
        ⊥ < Finset.sum (Finset.univ.erase i)
          (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) := by
      simpa [WithBot.bot_lt_iff_ne_bot] using hsum_ne_bot
    have hsum_top_if :
        (∑ j, (if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤)) = ⊤ := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) (Finset.mem_univ i)]
      simp [hi]
      change (⊤ : WithBotTop 𝕜)
          + Finset.sum (Finset.univ.erase i)
              (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) = ⊤
      exact WithBotTop.top_add_of_ne_bot (bot_lt_iff_ne_bot.mp htail_bot)
    have hsum_top : ∑ j, δ[𝕜](x | C j) = ⊤ := by
      simpa [indicator_def] using hsum_top_if
    calc
      (∑ j, δ[𝕜](x | C j)) = ⊤ := hsum_top
      _ = δ[𝕜](x | ⋂ i, C i) := by simp [hmem_union_compl]

omit [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
  [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
  [TopologicalSpace E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜] in
private theorem finiteInfimalConvolution_eq_bot_of_exists_eq_bot
    (f : ι → E → WithBotTop 𝕜) {i : ι} (hi : f i = ⊥) :
    finiteInfimalConvolution f = ⊥ := by
  classical
  ext x
  rw [finiteInfimalConvolution_eq_sInf_decompositions]
  refine le_antisymm ?_ bot_le
  refine sInf_le ?_
  refine ⟨fun j ↦ if i = j then x else 0, ?_, ?_⟩
  · simp
  · rw [← Finset.add_sum_erase Finset.univ
      (fun j ↦ f j (if i = j then x else 0)) (Finset.mem_univ i)]
    simp [hi]

-- Proof sketch: if every `C i` is nonempty, specialize Theorem 16.4.2 to the indicator family
-- `fun i ↦ δ[𝕜](· | C i)`. Convexity comes from `indicator_isConvex_iff`, properness
-- comes from nonemptiness, and Text 13.1.5 rewrites each `cl(δ(· | C i))` as
-- `δ(· | closure (C i))`. Text 13.1.4 rewrites each conjugate to `supportFunction (C i)`. The
-- sum of these closure indicators is the indicator of `⋂ i, closure (C i)`, so the left side
-- becomes the support function of that intersection. If some `C i` is empty, then
-- `⋂ i, closure (C i) = ∅` and one support-function summand is `⊥`, so both sides are `⊥`.
/-- Corollary 16.4.1.2 at the pairing owner layer: for a finite family of convex sets on a
finite-dimensional scalar-field space with a continuous linear self-pairing, the support function
of `⋂ i, closure (C i)` is the lower-semicontinuous closure of the finite infimal convolution of
the support functions of the sets `C i`. If some `C i` is empty, both sides are the constant `⊥`
function. -/
theorem supportFunction_iInter_closure_eq_lowerSemicontinuousHull_finiteInfimalConvolution_supportFunctions
    (C : ι → Set E) (hC_convex : ∀ i, Convex 𝕜 (C i)) :
    (δᵛ(· | ⋂ i, closure (C i)) : E → WithBotTop 𝕜) =
      cl(finiteInfimalConvolution
        (fun i ↦ (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
  classical
  by_cases hC_nonempty : ∀ i, (C i).Nonempty
  · let f : ι → E → WithBotTop 𝕜 := fun i ↦ (δ[𝕜](· | C i) : E → WithBotTop 𝕜)
    have hf_convex : ∀ i, (f i).IsConvex 𝕜 := by
      intro i
      rw [show f i = (δ[𝕜](· | C i) : E → WithBotTop 𝕜) by rfl]
      exact (indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) (C i)).2 (hC_convex i)
    have hf_proper : ∀ i, (f i).IsProper := by
      intro i
      rw [show f i = (δ[𝕜](· | C i) : E → WithBotTop 𝕜) by rfl]
      exact indicatorFunction_isProper_of_nonempty (C i) (hC_nonempty i)
    have hsum :
        (∑ i, lowerSemicontinuousHull (f i)) = (δ[𝕜](· | ⋂ i, closure (C i)) : E → WithBotTop 𝕜) := by
      have hcl :
          ∀ i, lowerSemicontinuousHull (f i) = (δ[𝕜](· | closure (C i)) : E → WithBotTop 𝕜) := by
        intro i
        simpa [f] using
          (lowerSemicontinuousHull_indicator_eq_indicator_closure
            (X := E) (𝕜 := 𝕜) (C := C i))
      ext x
      calc
        (∑ i, lowerSemicontinuousHull (f i)) x = ∑ i, δ[𝕜](x | closure (C i)) := by
          simp [hcl]
        _ = δ[𝕜](x | ⋂ i, closure (C i)) := by
          simpa using
            congrFun
              (sum_indicatorFunction_eq_indicatorFunction_iInter (E := E) (𝕜 := 𝕜)
                (fun i ↦ closure (C i))) x
    have hconj :
        (fun i ↦ convexConjugate (f i)) =
          fun i ↦ (δᵛ(· | C i) : E → WithBotTop 𝕜) := by
      funext i
      simpa [f] using
        (convexConjugate_indicatorFunction_eq_supportFunction
          (E := E) (EStar := E) (α := 𝕜) (C := C i))
    calc
      (δᵛ(· | ⋂ i, closure (C i)) : E → WithBotTop 𝕜) =
          convexConjugate (δ[𝕜](· | ⋂ i, closure (C i))) := by
            simpa using
              (convexConjugate_indicatorFunction_eq_supportFunction
                (E := E) (EStar := E) (α := 𝕜) (C := (⋂ i, closure (C i)))).symm
      _ = convexConjugate (∑ i, lowerSemicontinuousHull (f i)) := by
        rw [hsum.symm]
      _ = lowerSemicontinuousHull (finiteInfimalConvolution (fun i ↦ convexConjugate (f i))) :=
        convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_proper_convex
          f hf_convex hf_proper
      _ = lowerSemicontinuousHull (finiteInfimalConvolution
            (fun i ↦ (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
        rw [hconj]
  · obtain ⟨i, hi⟩ := not_forall.mp hC_nonempty
    have hCi_empty : C i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    have hInter_empty : (⋂ j, closure (C j)) = ∅ := by
      ext x
      constructor
      · intro hx
        have hxi : x ∈ closure (C i) := Set.mem_iInter.mp hx i
        simp [hCi_empty] at hxi
      · intro hx
        simp at hx
    have hsupport_empty :
        (δᵛ(· | C i) : E → WithBotTop 𝕜) = ⊥ := by
      ext x
      simp [hCi_empty, supportFunction_def]
    have hfininf_bot :
        finiteInfimalConvolution
          (fun j ↦ (δᵛ(· | C j) : E → WithBotTop 𝕜)) = ⊥ :=
      finiteInfimalConvolution_eq_bot_of_exists_eq_bot
        (fun j ↦ (δᵛ(· | C j) : E → WithBotTop 𝕜))
        hsupport_empty
    calc
      (δᵛ(· | ⋂ j, closure (C j)) : E → WithBotTop 𝕜) =
          (δᵛ(· | (∅ : Set E)) : E → WithBotTop 𝕜) := by
        rw [hInter_empty]
      _ = (⊥ : E → WithBotTop 𝕜) := by
        ext x
        simp [supportFunction_def]
      _ = lowerSemicontinuousHull (⊥ : E → WithBotTop 𝕜) := by
        apply le_antisymm
        · intro x
          exact bot_le
        · exact lowerSemicontinuousHull_le (f := (⊥ : E → WithBotTop 𝕜))
      _ = lowerSemicontinuousHull (finiteInfimalConvolution
            (fun j ↦ (δᵛ(· | C j) : E → WithBotTop 𝕜))) := by
        rw [hfininf_bot]

end

/-! ### Corollary_16_4_1_3 (from Chap03) -/
noncomputable section

open scoped BigOperators
open scoped Rockafellar

section

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]
local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.4.1.3 removes the closure from Corollary 16.4.1.2 for a finite
  nonempty family of convex sets whose relative interiors share a common point, and it adds
  attainment of the infimum in the support-function infimal-convolution formula.
- `core/canonical`: the owner abstractions already present in the project are
  `δ[𝕜](· | ·)`
  for Rockafellar's indicator `δ(· | C)`, `supportFunction` for `δ^*(· | C)`,
  `finiteInfimalConvolution` for the finite infimal convolution, and `intrinsicInterior 𝕜` for
  `ri`.
- `bridge/view`: the source common-relative-interior hypothesis is rendered directly as
  `(⋂ i, intrinsicInterior 𝕜 (C i)).Nonempty`, and the support-function formula is obtained as the
  indicator specialization of the owner theorem
  `convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior`.

Domain-style sampling used here:
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Text_13_1_4`;
- `convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior` from
  `Theorem_16_4_3`;
- `exists_sum_eq_finiteInfimalConvolution_conjugates_of_common_intrinsicInterior` from
  `Theorem_16_4_3`;
- `δ[𝕜](· | ·)` as the owner bridge from sets to the chapter conjugacy API.

Primitive data vs derived API:
- primitive inputs: a finite nonempty family `C : ι → Set E` and the convexity
  hypothesis `hC_convex`;
- source-essential regularity: a common point of the relative interiors
  `(⋂ i, intrinsicInterior 𝕜 (C i)).Nonempty`;
- derived API: the closure-free support-function identity and the pointwise attainment statement,
  both obtained by rewriting the owner theorem for the indicator family
  `(δ[𝕜](· | C i) : E → WithBotTop 𝕜)`.

Layer target: `source-facing`, but refined to a thin specialization of the chapter owner theorem
for finite-family conjugacy.

Semantic note: the separate source nonemptiness hypothesis is redundant once a common
relative-interior point is assumed, so it is omitted from the Lean header.
-/

private theorem indicator_isProper_of_nonempty
    (C : Set E) (hC_nonempty : C.Nonempty) :
    (δ[𝕜](· | C) : E → WithBotTop 𝕜).IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨?_, ?_⟩
  · rcases hC_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [mem_effectiveDomain] using
      (indicator_lt_top_iff_mem (α := 𝕜) (C := C) (x := x)).2 hx
  · intro x
    by_cases hx : x ∈ C
    · simp [hx]
    · simp [hx]

private theorem family_nonempty_of_common_intrinsicInterior
    (C : ι → Set E)
    (hri : (⋂ i, intrinsicInterior 𝕜 (C i)).Nonempty) :
    ∀ i, (C i).Nonempty := by
  rcases hri with ⟨x, hx⟩
  have hx : ∀ i, x ∈ intrinsicInterior 𝕜 (C i) := by
    simpa [Set.mem_iInter] using hx
  intro i
  exact ⟨x, intrinsicInterior_subset (hx i)⟩

private theorem sum_indicatorFunction_eq_indicatorFunction_iInter
    (C : ι → Set E) :
    (fun x : E ↦ ∑ i, δ[𝕜](x | C i)) =
      (δ[𝕜](· | ⋂ i, C i) : E → WithBotTop 𝕜) := by
  classical
  funext x
  by_cases hx : ∀ i, x ∈ C i
  · have hmem : x ∈ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have hnot_union_compl : x ∉ ⋃ i, (C i)ᶜ := by
      intro hx_union
      rcases Set.mem_iUnion.mp hx_union with ⟨i, hi⟩
      exact hi (hx i)
    have hzero : ∀ i, δ[𝕜](x | C i) = 0 := by
      intro i
      simp [hx i]
    calc
      (∑ i, δ[𝕜](x | C i)) = ∑ i, (0 : WithBotTop 𝕜) := by
        congr with i
        exact hzero i
      _ = 0 := by simp
      _ = δ[𝕜](x | ⋂ i, C i) := by simp [hnot_union_compl]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hmem_union_compl : x ∈ ⋃ i, (C i)ᶜ := by
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have hsum_ne_bot :
        Finset.sum (Finset.univ.erase i)
          (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) ≠ (⊥ : WithBotTop 𝕜) := by
      refine WithBotTop.sum_ne_bot_of_forall_ne_bot ?_
      intro j hj
      by_cases hjx : x ∈ C j
      · simp [hjx]
      · simp [hjx]
    have htail_bot :
        ⊥ < Finset.sum (Finset.univ.erase i)
          (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) := by
      simpa [WithBot.bot_lt_iff_ne_bot] using hsum_ne_bot
    have hsum_top_if :
        (∑ j, (if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤)) = ⊤ := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) (Finset.mem_univ i)]
      simp [hi]
      change (⊤ : WithBotTop 𝕜)
          + Finset.sum (Finset.univ.erase i)
              (fun j ↦ if x ∈ C j then (0 : WithBotTop 𝕜) else ⊤) = ⊤
      exact WithBotTop.top_add_of_ne_bot (bot_lt_iff_ne_bot.mp htail_bot)
    have hsum_top : ∑ j, δ[𝕜](x | C j) = ⊤ := by
      simpa [indicator_def] using hsum_top_if
    calc
      (∑ j, δ[𝕜](x | C j)) = ⊤ := hsum_top
      _ = δ[𝕜](x | ⋂ i, C i) := by simp [hmem_union_compl]

private theorem indicatorFamily_convex
    (C : ι → Set E)
    (hC_convex : ∀ i, Convex 𝕜 (C i)) :
    ∀ i, (δ[𝕜](· | C i) : E → WithBotTop 𝕜).IsConvex 𝕜 := by
  intro i
  exact (indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) (C i)).2 (hC_convex i)

private theorem indicatorFamily_proper
    (C : ι → Set E)
    (hri : (⋂ i, intrinsicInterior 𝕜 (C i)).Nonempty) :
    ∀ i, Function.IsProper (δ[𝕜](· | C i) : E → WithBotTop 𝕜) := by
  intro i
  exact indicator_isProper_of_nonempty (C i)
    (family_nonempty_of_common_intrinsicInterior C hri i)

private theorem indicatorFamily_hri
    (C : ι → Set E)
    (hri : (⋂ i, intrinsicInterior 𝕜 (C i)).Nonempty) :
    (⋂ i, riDom[𝕜]((δ[𝕜](· | C i) : E → WithBotTop 𝕜))).Nonempty := by
  rcases hri with ⟨x, hx⟩
  have hxri : ∀ i, x ∈ intrinsicInterior 𝕜 (C i) := by
    simpa [Set.mem_iInter] using hx
  refine ⟨x, ?_⟩
  refine Set.mem_iInter.mpr ?_
  intro i
  let f : E → WithBotTop 𝕜 := (δ[𝕜](· | C i) : E → WithBotTop 𝕜)
  have hdom : dom(f) = C i := by
    simpa [f] using (effectiveDomain_indicator (α := 𝕜) (C := C i))
  have hri_f : x ∈ riDom[𝕜](f) := by
    rw [riDom_eq_intrinsicInterior_dom, hdom]
    exact hxri i
  simpa [f] using hri_f

-- Proof sketch: specialize Theorem 16.4.3 to the indicator family `δ[𝕜](· | C i)`.
-- The effective domain of each indicator is exactly `C i`, the sum of the indicators is the
-- indicator of `⋂ i, C i`, and Text 13.1.4 rewrites the conjugates as the support functions.
/-- Corollary 16.4.1.3: for a finite nonempty family of convex sets in a finite-dimensional
pairing space whose relative
interiors have a common point, the support function of the intersection is the finite infimal
convolution of the individual support functions, so the closure operation from Corollary 16.4.1.2
may be omitted. -/
theorem
    supportFunction_iInter_eq_finiteInfimalConvolution_supportFunctions_of_common_intrinsicInterior
    (C : ι → Set E)
    (hC_convex : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, intrinsicInterior 𝕜 (C i)).Nonempty) :
    (supportFunction (⋂ i, C i) : E → WithBotTop 𝕜) =
      finiteInfimalConvolution (fun i ↦ (supportFunction (C i) : E → WithBotTop 𝕜)) := by
  let f : ι → E → WithBotTop 𝕜 := fun i ↦ (δ[𝕜](· | C i) : E → WithBotTop 𝕜)
  have hf_convex : ∀ i, (f i).IsConvex 𝕜 := by
    intro i
    simpa [f] using indicatorFamily_convex C hC_convex i
  have hf_proper : ∀ i, (f i).IsProper := by
    intro i
    simpa [f] using indicatorFamily_proper C hri i
  have hf_hri : (⋂ i, riDom[𝕜](f i)).Nonempty := by
    simpa [f] using indicatorFamily_hri C hri
  have hsum :
      (fun x : E ↦ ∑ i, f i x) = (δ[𝕜](· | ⋂ i, C i) : E → WithBotTop 𝕜) := by
    simpa [f] using sum_indicatorFunction_eq_indicatorFunction_iInter (C := C)
  have hconj :
      (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) =
        fun i ↦ (supportFunction (C i) : E → WithBotTop 𝕜) := by
    funext i
    simpa [f] using
      (convexConjugate_indicatorFunction_eq_supportFunction
        (E := E) (EStar := E) (α := 𝕜) (C := C i))
  calc
    (supportFunction (⋂ i, C i) : E → WithBotTop 𝕜) =
        convexConjugate ((δ[𝕜](· | ⋂ i, C i) : E → WithBotTop 𝕜)) := by
          simpa using
            (convexConjugate_indicatorFunction_eq_supportFunction
              (E := E) (EStar := E) (α := 𝕜) (C := (⋂ i, C i))).symm
    _ = convexConjugate (fun x : E ↦ ∑ i, f i x) := by rw [hsum.symm]
    _ = finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) :=
          convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior
            f hf_convex hf_proper hf_hri
    _ = finiteInfimalConvolution (fun i ↦ (supportFunction (C i) : E → WithBotTop 𝕜)) := by
          rw [hconj]

-- Proof sketch: the attainment clause of Theorem 16.4.3 applies to the same indicator family.
-- The relative-interior hypothesis is unchanged because the effective domain of each indicator is
-- `C i`, and the conjugates rewrite to the support functions of the sets.
/-- Under the common-relative-interior hypothesis, the infimum defining the finite infimal
convolution of the support functions of the sets `C i` is attained at every `xStar`. -/
theorem exists_sum_eq_finiteInfimalConvolution_supportFunctions_of_common_intrinsicInterior
    (C : ι → Set E)
    (hC_convex : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, intrinsicInterior 𝕜 (C i)).Nonempty)
    (xStar : E) :
    ∃ xs : ι → E,
      (∑ i, xs i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ (supportFunction (C i) : E → WithBotTop 𝕜)) xStar =
          ∑ i, (supportFunction (C i) : E → WithBotTop 𝕜) (xs i) := by
  let f : ι → E → WithBotTop 𝕜 := fun i ↦ (δ[𝕜](· | C i) : E → WithBotTop 𝕜)
  have hf_convex : ∀ i, (f i).IsConvex 𝕜 := by
    intro i
    simpa [f] using indicatorFamily_convex C hC_convex i
  have hf_proper : ∀ i, (f i).IsProper := by
    intro i
    simpa [f] using indicatorFamily_proper C hri i
  have hf_hri : (⋂ i, riDom[𝕜](f i)).Nonempty := by
    simpa [f] using indicatorFamily_hri C hri
  have hconj :
      (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) =
        fun i ↦ (supportFunction (C i) : E → WithBotTop 𝕜) := by
    funext i
    simpa [f] using
      (convexConjugate_indicatorFunction_eq_supportFunction
        (E := E) (EStar := E) (α := 𝕜) (C := C i))
  rcases exists_sum_eq_finiteInfimalConvolution_conjugates_of_common_intrinsicInterior
      f hf_convex hf_proper hf_hri xStar with ⟨xs, hxs, hval⟩
  have hsum_conj :
      (∑ i, ((f i)⋆ : E → WithBotTop 𝕜) (xs i)) =
        ∑ i, (supportFunction (C i) : E → WithBotTop 𝕜) (xs i) := by
    exact congrArg (fun g : ι → E → WithBotTop 𝕜 => ∑ i, g i (xs i)) hconj
  refine ⟨xs, hxs, ?_⟩
  calc
    finiteInfimalConvolution (fun i ↦ (supportFunction (C i) : E → WithBotTop 𝕜)) xStar
        = finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) xStar := by
            rw [hconj]
    _ = ∑ i, ((f i)⋆ : E → WithBotTop 𝕜) (xs i) := hval
    _ = ∑ i, (supportFunction (C i) : E → WithBotTop 𝕜) (xs i) := hsum_conj

end

/-! ### Text_16_4_1 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

variable {E EStar : Type*}
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable [SeminormedAddCommGroup EStar] [NormedSpace ℝ EStar]
variable [HasPairing EStar E ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.4.1 identifies the Fenchel conjugate of the distance function
  `x ↦ d(x, C)` for a nonempty set `C`.
- `core/canonical`: the owner abstractions are mathlib's canonical point-to-set owner
  `Metric.infEDist`, the chapter Fenchel conjugate `convexConjugate`, and the support function
  `supportFunction`.
- `bridge/view`: Rockafellar's `δ*(x⋆ | C)` is `δᵛ(x⋆ | C)` on an abstract dual owner `EStar`
  paired with `E`; the condition `|x⋆| ≤ 1` is rendered by `‖xStar‖ ≤ 1` in the dual norm; the
  source notation `d(x, C)` is used directly on the theorem surface in codomain `WithBotTop ℝ`.

Domain-style sampling used here:
- `Metric.infEDist`, recalled in `Defintion_4_8_3`;
- `infimal_convolution_norm_indicator_eq_distanceToSet` from Text 5.4.1.4;
- the canonical pairing-swap indicator/support bridge
  `convexConjugate_indicatorFunction_eq_supportFunction` from Text 13.1.4;
- `convexConjugate_finiteInfimalConvolution_eq_sum` from Theorem 16.4.1, with the
  needed `⊥`-exclusion supplied at the call site.

Primitive data vs derived API:
- primitive input: only the set `C`;
- derived APIs: the owner-level conjugate decomposition and the source-facing pointwise
  `if ‖x⋆‖ ≤ 1 then ... else ...` companion (which needs nonemptiness only to eliminate
  the `⊤ + ⊥` path at points outside the unit ball).

Layer target: `core/canonical` for the main theorem (an owner-level function equality) on an
abstract paired dual owner `EStar`, with a source-facing pointwise companion theorem for the
textbook conditional form.
-/

omit [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup EStar] [NormedSpace ℝ EStar] in
private theorem bot_lt_supportFunction_of_nonempty {C : Set E} (hC_nonempty : C.Nonempty)
    (xStar : EStar) :
    (⊥ : WithBotTop ℝ) < δᵛ[WithBotTop ℝ](xStar | C) := by
  rcases hC_nonempty with ⟨y, hy⟩
  rw [supportFunction_def]
  exact lt_of_lt_of_le (WithBotTop.bot_lt_coe _)
    (le_iSup (fun z : C ↦ ((⟪xStar, (z : E)⟫ₚ : ℝ) : WithBotTop ℝ)) ⟨y, hy⟩)

-- Proof sketch: write the distance function as the infimal convolution of the norm with
-- the `0/+∞` indicator of `C` using Text 5.4.1.4. Apply Theorem 16.4.1 to that two-term infimal
-- convolution. Then rewrite the indicator conjugate as `supportFunction C` by
-- `convexConjugate_indicatorFunction_eq_supportFunction`.
variable [HasPairing E EStar ℝ] [HasPairingAddLeft E EStar ℝ] [HasPairingSwap E EStar ℝ]

/-- Text 16.4.1 at the owner layer: for any set `C`, the Fenchel conjugate of the Chapter 1
distance function (lifted from `ℝ≥0∞` to `WithBotTop ℝ` by `ENNReal.toEReal`) is the sum of the
dual unit-ball indicator and the support function of `C` on an abstract paired dual owner
`EStar`. The statement is parameterized by the norm-conjugate bridge hypothesis
`((fun x ↦ ‖x‖)⋆ = δ(· | closedBall (0 : EStar) 1))`, so the theorem surface is not tied to a
concrete dual model. -/
theorem convexConjugate_distanceToSet_eq_indicator_unitBall_add_supportFunction
    {C : Set E}
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ)) :
    ((ENNReal.toEReal ∘ (d(·, C) : E → ENNReal))⋆ : EStar → WithBotTop ℝ) =
      (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ) +
        (δᵛ[WithBotTop ℝ](· | C) : EStar → WithBotTop ℝ) := by
  sorry

-- Proof sketch: evaluate the owner-level theorem
-- `convexConjugate_distanceToSet_eq_indicator_unitBall_add_supportFunction` at `xStar`
-- and simplify the unit-ball indicator pointwise. Nonemptiness is only used outside the unit ball
-- to simplify `⊤ + δᵛ(xStar | C)` to `⊤` by excluding `δᵛ(xStar | C) = ⊥`.
/-- Source-facing pointwise companion of Text 16.4.1: if `C` is nonempty, then the conjugate of
 the distance function is `δᵛ(x⋆ | C)` on the dual closed unit ball and `+∞` outside. -/
theorem convexConjugate_distanceToSet_eq_supportFunction_if_norm_le_one_of_nonempty
    {C : Set E} (hC_nonempty : C.Nonempty)
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ))
    (xStar : EStar) :
    ((ENNReal.toEReal ∘ (d(·, C) : E → ENNReal))⋆ : EStar → WithBotTop ℝ) xStar =
      if ‖xStar‖ ≤ 1 then δᵛ[WithBotTop ℝ](xStar | C) else ⊤ := by
  sorry

end

/-! ### Theorem_16_4_1 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

section

variable {X : Type*} {Y : Type*} {ι : Type*} {α : Type*}
variable [Fintype ι]
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [AddCommMonoid X]
variable [HasPairing X Y α] [HasPairingAddLeft X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.4.1 states that the Fenchel conjugate of a finite infimal
  convolution of a finite family is the pointwise sum of the individual conjugates.
- `core/canonical`: the project owners already present are `finiteInfimalConvolution` for
  `f₁ □ ⋯ □ f_m` and `convexConjugate` with notation `f⋆` for `f*`; for the codomain-general
  `WithTopBot α` identity, the relevant owner-side side condition is direct exclusion of the value
  `⊥`, stated as `∀ i x, f i x ≠ ⊥`.
- the ambient owner abstraction for the pairing term is `HasPairing X Y α` together with
  `HasPairingAddLeft X Y α`, since the
  equality uses only additivity of finite decompositions in the primal variable; the source
  linear and inner-product settings are specializations through canonical bridge instances from
  `HasLinearPairing`. At the
  codomain level, the `WithTopBot α` conjugacy/infimal-convolution identities are kept at the
  minimal lattice/additive-order layer (`ConditionallyCompleteLattice` + `AddCommGroup`) rather
  than a concrete numeric model or a linear-order specialization.
- `bridge/view`: the textbook properness wording is exposed only as a thin companion theorem,
  because at the owner level it reduces immediately to the `⊥`-exclusion hypothesis above via
  `Function.IsProper.ne_bot`.

Domain-style sampling used here:
- `finiteInfimalConvolution` and its decomposition companion API from Text 5.4.1;
- `convexConjugate` and its scoped notation `f⋆` from Defn 12.2;
- `HasPairing` / `HasPairingAddLeft` from `Chap01.HasPairing`, which are the chapter owners for
  the primal-additive pairing identities used by finite decomposition formulas;
- the chapter predicate `Function.IsProper` from Definition 4.6;
- `Function.isConvex_finiteInfimalConvolution` from Theorem 5.4, which is a
  derived convexity result for the owner `finiteInfimalConvolution`, not primitive data for this
  conjugacy identity.

Primitive data vs derived API:
- primitive input: a finite family `f : ι → X → WithTopBot α`;
- owner-side hypothesis actually used by the displayed identity: `∀ i x, f i x ≠ ⊥`;
- derived API: the owner-side finite-family conjugacy equality itself and its thin properness-form
  specialization.

Layer target: `core/canonical`. The main public theorem below is stated for an arbitrary finite
index type on the chapter pairing owner augmented by primal additivity, with the minimal
owner-side `⊥`-exclusion hypothesis; the source-facing properness form is kept only as a thin
companion specialization.
-/

-- Proof sketch: expand the Fenchel conjugate of the finite infimal convolution using the
-- decomposition formula for `finiteInfimalConvolution`, interchange the outer supremum with the
-- supremum over all finite decompositions, and then separate the resulting expression into the sum
-- of the independent Fenchel suprema defining the individual conjugates. Additivity of the
-- pairing in the primal variable is the only ambient structure needed to rewrite the pairing of a
-- decomposition sum as the sum of the pairings. The only function-side exclusion needed at this
-- owner level is that no summand
-- takes the value `⊥`, so that `WithTopBot α` addition does not encounter the `⊥ + ⊤` pathology.
/-- Theorem 16.4.1 in owner form: for a finite family on a pairing additive in the primal
variable, and hence in particular in the linear and self-paired inner-product settings of the
source, if each summand is
never equal to `⊥`, then the Fenchel conjugate of the finite infimal convolution is the pointwise
sum of the individual conjugates. The textbook properness wording is recovered at use sites via
`Function.IsProper.ne_bot`. -/
theorem convexConjugate_finiteInfimalConvolution_eq_sum
    (f : ι → X → WithTopBot α)
    (hf_ne_bot : ∀ i x, f i x ≠ ⊥) :
    (finiteInfimalConvolution f)⋆ = (∑ i, (f i)⋆ : Y → WithTopBot α) := sorry

/-- Properness-form specialization of Theorem 16.4.1. This companion adds no new mathematics: it
only repackages the owner-side `⊥`-exclusion as the canonical consequence
`Function.IsProper.ne_bot`. -/
theorem convexConjugate_finiteInfimalConvolution_eq_sum_of_proper
    (f : ι → X → WithTopBot α)
    (hf_proper : ∀ i, (f i).IsProper) :
    (finiteInfimalConvolution f)⋆ = (∑ i, (f i)⋆ : Y → WithTopBot α) :=
  convexConjugate_finiteInfimalConvolution_eq_sum f
    (fun i ↦ (hf_proper i).ne_bot)

end

/-! ### Corollary_16_4_2_1 (from Chap03) -/
open scoped BigOperators Pointwise Rockafellar PolarCone

section

variable {ι : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.4.2.1 states that the polar cone of a finite Minkowski sum of
  nonempty cones is the intersection of the individual polar cones.
- `core/canonical`: the owner objects already present in the project are the pairing-layer
  set-valued polar operator `polarCone` (used below via the canonical notation `Kᵒ[𝕜]`), its owner
  dual-cone API `PointedCone.dual` from `Text_14_0_1`, the cone predicate `Set.IsCone 𝕜`,
  pointwise finite set sums, and indexed intersections.
- `bridge/view`: the textbook finite family is rendered by an arbitrary finite index type `ι`,
  which is the minimal canonical layer because no order or coordinate data is used.

Domain-style sampling used here:
- `polarCone` / notation `Kᵒ[𝕜]` from `Text_14_0_1`;
- `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `Set.IsCone 𝕜` from `Definition_2_5_9`;
- `Set.IsCone.finset_sum` from `Definition_2_5_9`;
- `Set.IsCone.pairing_upperBound_nonneg_of_nonempty` from `Definition_2_5_9`;
- finite pointwise set sums `∑ i in s, K i`;
- finite indexed intersections `⋂ i ∈ s, (K i)ᵒ[𝕜]`.

Primitive data vs derived API:
- primitive inputs: the family of sets `K` together with nonemptiness and cone hypotheses;
- derived output: the polar/intersection identity itself.

The source's convexity hypothesis is redundant for this identity, so the Lean statement keeps only
the mathematically active assumptions. Familywise nonemptiness is essential: without it, an empty
summand makes the pointwise sum empty, so the displayed identity need not hold. The theorem lives
on the pairing owner layer, not on the concrete self-dual inner-product model.
The primal ambient additive structure is kept at the primitive `AddCommMonoid` layer; the
remaining scalar/order assumptions are exactly those currently required by
`Set.IsCone.pairing_upperBound_nonneg_of_nonempty`, which is the upstream cone-level bridge used
in the proof.
-/

-- Proof sketch: if `xStar` lies in every `(K i)ᵒ[𝕜]` over `i ∈ s`, then bilinearity makes it lie
-- in the polar of the finite sum `∑ i in s, K i`. Conversely, fix `i ∈ s` and `x ∈ K i`. Replace
-- the `i`-th summand by `{0}` and keep the others unchanged; this gives a nonempty cone family
-- whose finite sum is again a cone by `Set.IsCone.finset_sum`. Membership of `xStar` in the polar
-- of the original finite sum yields an upper bound `-⟪x, xStar⟫ₚ` for the pairing on that
-- auxiliary cone, and
-- `Set.IsCone.pairing_upperBound_nonneg_of_nonempty` forces `⟪x, xStar⟫ ≤ 0`.
/-- Corollary 16.4.2.1 at the pairing owner layer: for a finite family of nonempty cones, the
polar of a finite Minkowski sum is the finite intersection of the individual polars.
The source states this for convex cones, but convexity is redundant for the displayed identity and
is therefore omitted from the Lean header. -/
theorem polarCone_finset_sum_eq_iInter
    (s : Finset ι)
    (K : ι → Set X)
    (hK : ∀ i ∈ s, (K i).Nonempty ∧ Set.IsCone 𝕜 (K i)) :
    (((∑ i ∈ s, K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) =
      ⋂ i ∈ s, (((K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
  classical
  have hK_nonempty : ∀ i ∈ s, (K i).Nonempty := fun i hi ↦ (hK i hi).1
  have hK_cone : ∀ i ∈ s, Set.IsCone 𝕜 (K i) := fun i hi ↦ (hK i hi).2
  ext xStar
  constructor
  · intro hxStar
    have hxStar_pair :
        ∀ x ∈ ∑ i ∈ s, K i, (⟪x, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) :=
      (mem_polarCone_iff_pairing (K := ∑ i ∈ s, K i) (xStar := xStar)).1 hxStar
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hi
    refine (mem_polarCone_iff_pairing (K := K i) (xStar := xStar)).2 ?_
    intro x hx
    let L : ι → Set X := fun j ↦ if j = i then ({0} : Set X) else K j
    have hL_nonempty : ∀ j ∈ s, (L j).Nonempty := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact ⟨0, by simp [L]⟩
      · simpa [L, hji] using hK_nonempty j hj
    have hL_cone : ∀ j ∈ s, Set.IsCone 𝕜 (L j) := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        intro a y ha hy
        have hy0 : y = 0 := by simpa [L] using hy
        simp [L, hy0]
      · simpa [L, hji] using hK_cone j hj
    have hLsum_nonempty : (∑ j ∈ s, L j).Nonempty := by
      choose y hy using hL_nonempty
      let g : ι → X := fun j ↦ if hj : j ∈ s then y j hj else 0
      refine ⟨∑ j ∈ s, g j, ?_⟩
      refine (Set.mem_finset_sum (t := s) (f := L) (a := ∑ j ∈ s, g j)).2 ?_
      refine ⟨g, ?_, rfl⟩
      intro j hj
      simp [g, hj, hy j hj]
    have hbound : ∀ y ∈ ∑ j ∈ s, L j, (⟪y, xStar⟫ₚ : 𝕜) ≤ -(⟪x, xStar⟫ₚ : 𝕜) := by
      intro y hy
      have hxy : x + y ∈ ∑ j ∈ s, K j := by
        rcases (Set.mem_finset_sum (t := s) (f := L) (a := y)).1 hy with ⟨g, hg, rfl⟩
        refine (Set.mem_finset_sum (t := s) (f := K) (a := x + ∑ j ∈ s, g j)).2 ?_
        refine ⟨fun j ↦ if j = i then x else g j, ?_, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · simpa [hji] using hx
          · simpa [L, hji] using hg (i := j) hj
        · have hgi_zero : g i = 0 := by
            have : g i ∈ ({0} : Set X) := by simpa [L] using hg (i := i) hi
            simpa using this
          calc
            ∑ j ∈ s, (if j = i then x else g j) =
                ∑ j ∈ s, (if j = i then x else 0) + ∑ j ∈ s, g j := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun j _ ↦ ?_
                  by_cases hj : j = i
                  · subst hj
                    simp [hgi_zero]
                  · simp [hj]
            _ = x + ∑ j ∈ s, g j := by
              have hsum_ite : ∑ j ∈ s, (if j = i then x else (0 : X)) = x := by
                calc
                  ∑ j ∈ s, (if j = i then x else (0 : X)) = if i ∈ s then x else 0 := by
                    exact Finset.sum_ite_eq' (s := s) (a := i) (b := fun _ : ι ↦ x)
                  _ = x := by simp [hi]
              rw [hsum_ite]
      have hy_le : (⟪x + y, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) := hxStar_pair (x + y) hxy
      have hxy_pair :
          (⟪x + y, xStar⟫ₚ : 𝕜) = ⟪x, xStar⟫ₚ + ⟪y, xStar⟫ₚ := by
        exact
          (HasPairingAddLeft.pairing_add_left (𝕜 := 𝕜) (x₁ := x) (x₂ := y) (y := xStar))
      have hy_le' : (⟪x, xStar⟫ₚ : 𝕜) + (⟪y, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) := by
        simpa [hxy_pair] using hy_le
      linarith
    have hneg : (0 : 𝕜) ≤ -(⟪x, xStar⟫ₚ : 𝕜) :=
      Set.IsCone.pairing_upperBound_nonneg_of_nonempty
        (Set.IsCone.finset_sum hL_cone) hLsum_nonempty hbound
    linarith
  · intro hxStar
    rw [Set.mem_iInter] at hxStar
    refine (mem_polarCone_iff_pairing (K := ∑ i ∈ s, K i) (xStar := xStar)).2 ?_
    intro x hx
    rcases (Set.mem_finset_sum (t := s) (f := K) (a := x)).1 hx with ⟨g, hg, rfl⟩
    have hg_nonpos : ∀ i ∈ s, (⟪g i, xStar⟫ₚ : 𝕜) ≤ (0 : 𝕜) := by
      intro i hi
      have hxStar_i : xStar ∈ (K i)ᵒ[𝕜] := (Set.mem_iInter.mp (hxStar i)) hi
      exact (mem_polarCone_iff_pairing).mp hxStar_i (g i) (hg (i := i) hi)
    have hsum_pair :
        (⟪∑ i ∈ s, g i, xStar⟫ₚ : 𝕜) = ∑ i ∈ s, ⟪g i, xStar⟫ₚ := by
      calc
        (⟪∑ i ∈ s, g i, xStar⟫ₚ : 𝕜) =
            (HasLinearPairing.pairingLinear (∑ i ∈ s, g i)) xStar := by
              rfl
        _ = (∑ i ∈ s, HasLinearPairing.pairingLinear (g i)) xStar := by
              exact congrArg (fun φ : Module.Dual 𝕜 Y => φ xStar)
                (map_sum (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y) g s)
        _ = ∑ i ∈ s, ⟪g i, xStar⟫ₚ := by
              simp [HasLinearPairing.pairing_eq_pairingLinear]
    calc
      (⟪∑ i ∈ s, g i, xStar⟫ₚ : 𝕜) = ∑ i ∈ s, ⟪g i, xStar⟫ₚ := hsum_pair
      _ ≤ (0 : 𝕜) := Finset.sum_nonpos fun i hi ↦ hg_nonpos i hi

/-- `Fintype`-indexed specialization of `polarCone_finset_sum_eq_iInter` (`s = Finset.univ`). -/
theorem polarCone_sum_eq_iInter [Fintype ι]
    (K : ι → Set X)
    (hK : ∀ i, (K i).Nonempty ∧ Set.IsCone 𝕜 (K i)) :
    (((∑ i, K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) =
      ⋂ i, (((K i)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
  simpa using
    (polarCone_finset_sum_eq_iInter (s := (Finset.univ : Finset ι)) K
      (fun i _ ↦ hK i))

end

/-! ### Corollary_16_4_2_2 (from Chap03) -/
open scoped BigOperators Pointwise PolarCone

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
variable [HasLinearPairing E E 𝕜]

/-!
Source/core/bridge triage:
- source-facing statement: Corollary 16.4.2.2, phrased with intersections, closure, and finite
  sums of polars.
- core/canonical: a scalar-generic pairing-layer corollary that takes the bipolar-closure bridge
  as primitive input.
-/

-- Proof sketch:
-- - Nonempty case: apply `polarCone_sum_eq_iInter` to `P i := (K i)ᵒ[𝕜]`, rewrite each double
--   polar by `hbipolar`, then apply `hbipolar` once more to `∑ i, P i`.
-- - Empty-index case: if some `K i = ∅`, then `⋂ i, closure (K i) = ∅`, so the left side is
--   `∅ᵒ = univ`; the right side is also `univ` because `(K i)ᵒ = univ` and a finite sum with one
--   `univ` summand is `univ`.
/-- Corollary 16.4.2.2 at the scalar-generic pairing layer: for a finite family of convex cones,
the polar of the intersection of their closures is the closure of the finite sum of their polar
cones, provided the bipolar-closure bridge is available at this scalar layer. -/
theorem polarCone_iInter_closure_eq_closure_sum_polarCone
    (hbipolar : ∀ {S : Set E}, S.Nonempty → Set.IsConvexCone 𝕜 S →
      ((Sᵒ[𝕜] : Set E)ᵒ[𝕜] = closure S))
    (K : ι → Set E)
    (hK : ∀ i, Set.IsConvexCone 𝕜 (K i)) :
    (⋂ i, closure (K i))ᵒ[𝕜] = closure (∑ i, ((K i)ᵒ[𝕜] : Set E)) := by
  classical
  let P : ι → Set E := fun i ↦ (K i)ᵒ[𝕜]
  have hP_nonempty : ∀ i, (P i).Nonempty := fun i ↦ ⟨0, by
    simp [P]⟩
  have hP_zero : ∀ i, (0 : E) ∈ P i := fun i ↦ by
    simp [P]
  have hP_convex : ∀ i, Convex 𝕜 (P i) := fun i ↦ by
    simpa [P] using convex_polarCone (K i)
  have hP_cone : ∀ i, Set.IsCone 𝕜 (P i) := fun i ↦ by
    simpa [P] using isCone_polarCone (K i)
  by_cases hK_nonempty : ∀ i, (K i).Nonempty
  · have hdouble : ∀ i, ((K i)ᵒ[𝕜])ᵒ[𝕜] = closure (K i) := fun i ↦ by
      exact hbipolar (hK_nonempty i) (hK i)
    have hsum : (∑ i, P i)ᵒ[𝕜] = ⋂ i, closure (K i) := by
      calc
        (∑ i, P i)ᵒ[𝕜] = ⋂ i, ((K i)ᵒ[𝕜])ᵒ[𝕜] := by
          simpa [P] using polarCone_sum_eq_iInter P (fun i ↦ ⟨hP_nonempty i, hP_cone i⟩)
        _ = ⋂ i, closure (K i) := by
          ext x
          simp [hdouble]
    have hsum_nonempty : (∑ i, P i).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Set.mem_fintype_sum]
      exact ⟨fun _ ↦ 0, hP_zero, by simp⟩
    have hsum_convex : Convex 𝕜 (∑ i, P i) := by
      exact convex_sum P (fun i _ ↦ hP_convex i)
    have hsum_cone : Set.IsCone 𝕜 (∑ i, P i) := by
      exact Set.IsCone.fintype_sum hP_cone
    have hsum_convexCone : Set.IsConvexCone 𝕜 (∑ i, P i) := ⟨hsum_cone, hsum_convex⟩
    calc
      (⋂ i, closure (K i))ᵒ[𝕜] = ((∑ i, P i)ᵒ[𝕜])ᵒ[𝕜] := by
        rw [hsum.symm]
      _ = closure (∑ i, P i) := by
        exact hbipolar hsum_nonempty hsum_convexCone
      _ = closure (∑ i, (K i)ᵒ[𝕜]) := by
        simp [P]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (K i).Nonempty := by
      simpa only [not_forall] using hK_nonempty
    have hKi : K i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    have hInter_empty : (⋂ j, closure (K j)) = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ closure (K i) := Set.mem_iInter.mp hx i
        simp [hKi] at hx'
      · simp
    have hsum_univ : (∑ j, P j) = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        rw [Set.mem_fintype_sum]
        refine ⟨Pi.single i x, ?_, ?_⟩
        · intro j
          by_cases hj : j = i
          · subst hj
            simp [P, hKi]
          · simpa [Pi.single, hj] using hP_zero j
        · simp
    calc
      (⋂ j, closure (K j))ᵒ[𝕜] = Set.univ := by
        ext x
        rw [mem_polarCone_iff]
        simp [hInter_empty]
      _ = closure (∑ j, P j) := by
        rw [hsum_univ]
        simp
      _ = closure (∑ j, (K j)ᵒ[𝕜]) := by
        simp [P]

end

/-! ### Corollary_16_4_2_3 (from Chap03) -/
open scoped BigOperators Pointwise Rockafellar PolarCone

noncomputable section

section

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

private theorem withBotTop_top_add_of_ne_bot
    {x : WithBotTop 𝕜} (hx : x ≠ ⊥) :
    (⊤ : WithBotTop 𝕜) + x = ⊤ := by
  cases x using WithBotTop.rec
  · exact (hx rfl).elim
  · rfl
  · rfl

private theorem isProper_indicatorFunction
    (C : Set E) (hC_nonempty : C.Nonempty) :
    Function.IsProper (δ[𝕜](· | C) : E → WithBotTop 𝕜) := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  constructor
  · rcases hC_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_effectiveDomain, indicator_def, if_pos hx]
    exact WithBotTop.zero_lt_top
  · intro x
    by_cases hx : x ∈ C
    · rw [indicator_def, if_pos hx]
      exact WithBotTop.bot_lt_zero
    · rw [indicator_def, if_neg hx]
      exact lt_of_lt_of_le WithBotTop.bot_lt_zero le_top

private theorem sum_indicatorFunction_eq_indicatorFunction_iInter
    (C : ι → Set E) :
    (fun x : E ↦ ∑ i, (δ[𝕜](x | C i) : WithBotTop 𝕜)) =
      (δ[𝕜](· | ⋂ i, C i) : E → WithBotTop 𝕜) := by
  classical
  funext x
  by_cases hx : ∀ i, x ∈ C i
  · have hmem : x ∈ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    rw [indicator_def, if_pos hmem]
    have hzero : ∀ i, (δ[𝕜](x | C i) : WithBotTop 𝕜) = 0 := by
      intro i
      rw [indicator_def, if_pos (hx i)]
    calc
      (∑ i, (δ[𝕜](x | C i) : WithBotTop 𝕜)) = ∑ i, (0 : WithBotTop 𝕜) := by
        congr with i
        exact hzero i
      _ = 0 := by simp
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hnotmem : x ∉ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have htail_bot :
        (⊥ : WithBotTop 𝕜) <
          ∑ j ∈ Finset.univ.erase i, (δ[𝕜](x | C j) : WithBotTop 𝕜) := by
      simpa using
        WithBot.sum_lt_bot (s := Finset.univ.erase i)
          (f := fun j ↦ (δ[𝕜](x | C j) : WithBotTop 𝕜)) (fun j hj ↦ by
          by_cases hjx : x ∈ C j
          · simpa [indicator_def, hjx] using (WithBotTop.coe_ne_bot (a := (0 : 𝕜)))
          · simpa [indicator_def, hjx] using (WithBotTop.top_ne_bot : (⊤ : WithBotTop 𝕜) ≠ ⊥))
    rw [indicator_def, if_neg hnotmem]
    rw [← Finset.add_sum_erase Finset.univ
      (fun j ↦ (δ[𝕜](x | C j) : WithBotTop 𝕜)) (Finset.mem_univ i)]
    rw [indicator_def, if_neg hi]
    have htail_ne_bot :
        (∑ j ∈ Finset.univ.erase i, (δ[𝕜](x | C j) : WithBotTop 𝕜)) ≠ ⊥ :=
      bot_lt_iff_ne_bot.mp htail_bot
    have htop :
        (⊤ : WithBotTop 𝕜) + ∑ j ∈ Finset.univ.erase i, (δ[𝕜](x | C j) : WithBotTop 𝕜) = ⊤ :=
      withBotTop_top_add_of_ne_bot (𝕜 := 𝕜) htail_ne_bot
    simpa [indicator_def] using htop

private theorem finiteInfimalConvolution_indicatorFunction_eq_indicatorFunction_sum
    (P : ι → Set E) :
    finiteInfimalConvolution (fun i ↦ (δ[𝕜](· | P i) : E → WithBotTop 𝕜)) =
      (δ[𝕜](· | (∑ i, P i)) : E → WithBotTop 𝕜) := by
  classical
  funext x
  rw [finiteInfimalConvolution_eq_sInf_decompositions]
  by_cases hx : x ∈ ((∑ i, P i) : Set E)
  · rw [indicator_def, if_pos hx]
    refine le_antisymm ?_ ?_
    · rcases (Set.mem_fintype_sum P x).1 hx with ⟨xs, hxs_mem, hxs_sum⟩
      refine sInf_le ?_
      refine ⟨xs, hxs_sum, ?_⟩
      have hxs_zero :
          ∀ i, (δ[𝕜](xs i | P i) : WithBotTop 𝕜) = 0 := by
        intro i
        rw [indicator_def, if_pos (hxs_mem i)]
      have hsum_zero :
          ∑ i, (δ[𝕜](xs i | P i) : WithBotTop 𝕜) = 0 := by
        simp [hxs_zero]
      exact hsum_zero.symm
    · refine le_sInf ?_
      intro r hr
      rcases hr with ⟨xs, -, rfl⟩
      exact Finset.sum_nonneg fun i _ ↦ by
        by_cases hmem : xs i ∈ P i
        · simp [indicator_def, hmem]
        · simp [indicator_def, hmem]
  · rw [indicator_def, if_neg hx]
    refine le_antisymm le_top ?_
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨xs, hxs_sum, rfl⟩
    have hnot_all : ¬ ∀ i, xs i ∈ P i := by
      intro hxs_mem
      exact hx ((Set.mem_fintype_sum P x).2 ⟨xs, hxs_mem, hxs_sum⟩)
    obtain ⟨i, hi⟩ := not_forall.mp hnot_all
    have htail_bot :
        ⊥ < ∑ j ∈ Finset.univ.erase i, (δ[𝕜](xs j | P j) : WithBotTop 𝕜) := by
      simpa using
        WithBot.sum_lt_bot (s := Finset.univ.erase i)
          (f := fun j ↦ (δ[𝕜](xs j | P j) : WithBotTop 𝕜)) (fun j hj ↦ by
          by_cases hmem : xs j ∈ P j
          · simpa [indicator_def, hmem] using (WithBotTop.coe_ne_bot (a := (0 : 𝕜)))
          · simpa [indicator_def, hmem] using (WithBotTop.top_ne_bot : (⊤ : WithBotTop 𝕜) ≠ ⊥))
    rw [← Finset.add_sum_erase Finset.univ
      (fun j ↦ (δ[𝕜](xs j | P j) : WithBotTop 𝕜)) (Finset.mem_univ i)]
    rw [indicator_def, if_neg hi]
    change (⊤ : WithBotTop 𝕜) ≤ (⊤ : WithBotTop 𝕜) +
      ∑ j ∈ Finset.univ.erase i, (δ[𝕜](xs j | P j) : WithBotTop 𝕜)
    have htail_ne_bot :
        (∑ j ∈ Finset.univ.erase i, (δ[𝕜](xs j | P j) : WithBotTop 𝕜)) ≠ ⊥ :=
      bot_lt_iff_ne_bot.mp htail_bot
    rw [withBotTop_top_add_of_ne_bot (𝕜 := 𝕜) htail_ne_bot]

/-- Corollary 16.4.2.3 at the pairing owner layer: for a finite nonempty family of convex cones
with a common relative-interior point, the polar cone of the intersection is the finite sum of
the individual polar cones. -/
theorem polarCone_iInter_eq_sum_polarCone_of_common_intrinsicInterior
    (K : ι → Set E)
    (hK_convex : ∀ i, Convex 𝕜 (K i))
    (hK_cone : ∀ i, Set.IsCone 𝕜 (K i))
    (hri : (⋂ i, intrinsicInterior 𝕜 (K i)).Nonempty) :
    ((⋂ i, K i)ᵒ[𝕜] : Set E) = (∑ i, ((K i)ᵒ[𝕜] : Set E)) := by
  have hK_nonempty : ∀ i, (K i).Nonempty := by
    rcases hri with ⟨x, hx⟩
    have hxri : ∀ i, x ∈ intrinsicInterior 𝕜 (K i) := by
      simpa [Set.mem_iInter] using hx
    intro i
    exact ⟨x, intrinsicInterior_subset (hxri i)⟩
  have hInter_nonempty : (⋂ i, K i).Nonempty := by
    rcases hri with ⟨x, hx⟩
    have hxri : ∀ i, x ∈ intrinsicInterior 𝕜 (K i) := by
      simpa [Set.mem_iInter] using hx
    refine ⟨x, ?_⟩
    simpa [Set.mem_iInter] using fun i ↦ intrinsicInterior_subset (hxri i)
  have hInter_cone : Set.IsCone 𝕜 (⋂ i, K i) := Set.IsCone.iInter hK_cone
  have hri_indicator :
      (⋂ i, intrinsicInterior 𝕜 dom((δ[𝕜](· | K i) : E → WithBotTop 𝕜))).Nonempty := by
    classical
    rcases hri with ⟨x, hx⟩
    refine ⟨x, (Set.mem_iInter).2 ?_⟩
    have hx' : ∀ i : ι, x ∈ intrinsicInterior 𝕜 (K i) := by
      simpa [Set.mem_iInter] using hx
    intro i
    have hdom_if :
        dom((fun y : E ↦ if y ∈ K i then (0 : WithBotTop 𝕜) else ⊤)) = K i := by
      ext y
      rw [mem_effectiveDomain]
      by_cases hy : y ∈ K i
      · constructor
        · intro _
          exact hy
        · intro _
          simpa [hy] using (WithBotTop.zero_lt_top : (0 : WithBotTop 𝕜) < ⊤)
      · constructor
        · intro hylt
          simpa [hy] using hylt
        · intro hyin
          exact (hy hyin).elim
    have hxif :
        x ∈ intrinsicInterior 𝕜 dom((fun y : E ↦ if y ∈ K i then (0 : WithBotTop 𝕜) else ⊤)) := by
      simpa [hdom_if] using hx' i
    simpa [riDom_eq_intrinsicInterior_dom, indicator_def] using hxif
  have hconv :
      convexConjugate (fun x : E ↦ ∑ i, (δ[𝕜](x | K i) : WithBotTop 𝕜)) =
        finiteInfimalConvolution
          (fun i ↦ (((δ[𝕜](· | K i) : E → WithBotTop 𝕜)⋆) : E → WithBotTop 𝕜)) := by
    simpa using
      convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior
        (f := fun i ↦ (δ[𝕜](· | K i) : E → WithBotTop 𝕜))
        (fun i ↦ (indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) (K i)).2 (hK_convex i))
        (fun i ↦ isProper_indicatorFunction (𝕜 := 𝕜) (K i) (hK_nonempty i))
        hri_indicator
  have hconj_family :
      (fun i ↦ (((δ[𝕜](· | K i) : E → WithBotTop 𝕜)⋆) : E → WithBotTop 𝕜)) =
        fun i ↦ (δ[𝕜](· | (K i)ᵒ[𝕜]) : E → WithBotTop 𝕜) := by
    funext i
    exact
      convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone
        (K i) (hK_nonempty i) (hK_cone i)
  have hindicator :
      (δ[𝕜](· | (⋂ i, K i)ᵒ[𝕜]) : E → WithBotTop 𝕜) =
        (δ[𝕜](· | (∑ i, ((K i)ᵒ[𝕜] : Set E))) : E → WithBotTop 𝕜) := by
    calc
      (δ[𝕜](· | (⋂ i, K i)ᵒ[𝕜]) : E → WithBotTop 𝕜) =
          convexConjugate (δ[𝕜](· | ⋂ i, K i) : E → WithBotTop 𝕜) := by
            symm
            exact
              convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone
                (⋂ i, K i) hInter_nonempty hInter_cone
      _ = convexConjugate (fun x : E ↦ ∑ i, (δ[𝕜](x | K i) : WithBotTop 𝕜)) := by
            rw [sum_indicatorFunction_eq_indicatorFunction_iInter (𝕜 := 𝕜) (C := K)]
      _ = finiteInfimalConvolution
            (fun i ↦ (((δ[𝕜](· | K i) : E → WithBotTop 𝕜)⋆) : E → WithBotTop 𝕜)) := hconv
      _ = finiteInfimalConvolution (fun i ↦ (δ[𝕜](· | (K i)ᵒ[𝕜]) : E → WithBotTop 𝕜)) := by
            rw [hconj_family]
      _ = (δ[𝕜](· | (∑ i, ((K i)ᵒ[𝕜] : Set E))) : E → WithBotTop 𝕜) := by
            simpa using
              finiteInfimalConvolution_indicatorFunction_eq_indicatorFunction_sum
                (𝕜 := 𝕜) (fun i ↦ ((K i)ᵒ[𝕜] : Set E))
  ext xStar
  constructor
  · intro hxStar
    by_contra hxSum
    have hleft :
        (δ[𝕜](xStar | (⋂ i, K i)ᵒ[𝕜]) : WithBotTop 𝕜) = 0 := by
      simp [hxStar]
    have hright :
        (δ[𝕜](xStar | (∑ i, ((K i)ᵒ[𝕜] : Set E))) : WithBotTop 𝕜) = ⊤ := by
      simp [hxSum]
    have hvalue := congrFun hindicator xStar
    rw [hleft, hright] at hvalue
    have hneq : (0 : WithBotTop 𝕜) ≠ ⊤ := by
      simpa using (WithBotTop.coe_ne_top (a := (0 : 𝕜)))
    exact hneq hvalue
  · intro hxSum
    by_contra hxStar
    have hleft :
        (δ[𝕜](xStar | (⋂ i, K i)ᵒ[𝕜]) : WithBotTop 𝕜) = ⊤ := by
      simp [hxStar]
    have hright :
        (δ[𝕜](xStar | (∑ i, ((K i)ᵒ[𝕜] : Set E))) : WithBotTop 𝕜) = 0 := by
      simp [hxSum]
    have hvalue := congrFun hindicator xStar
    rw [hleft, hright] at hvalue
    have hneq : (⊤ : WithBotTop 𝕜) ≠ 0 := by
      simpa using (WithBotTop.coe_ne_top (a := (0 : 𝕜))).symm
    exact hneq hvalue

end

/-! ### Text_16_4_2 (from Chap03) -/
noncomputable section

open scoped BigOperators
open scoped Rockafellar

section

variable {ι κ 𝕜 : Type*} [Fintype ι]
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]

local notation "E" => ι → 𝕜
local notation "D" => (coordinateL1Ball : Set E)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.4.2 fixes a finite family `a : κ → E`, with `E = ι → 𝕜`, and studies
  the function
  `x ↦ inf {‖x - ∑ t c t • a t‖∞ | c : κ → 𝕜}` together with the dual set `D ∩ Lᗮₚ`.
- `core/canonical`: the owner abstractions already present in the project are
  `coordinateL1Ball`, `linftyNorm`, `Submodule.span`, `Submodule.pairingOrthogonal`,
  `infimal_convolution`, `indicator`, `supportFunction`, and `Set.IsPolyhedral`.
- `bridge/view`: the source's coordinate tuple `(ξ₁, …, ξ_m)` is a coefficient function
  `c : κ → 𝕜`; the source dual set is rendered by `linftyApproximationDualSet`.

Primitive data vs derived API:
- primitive inputs: the family `a : κ → E`, the canonical set owner `coordinateL1Ball`, and the
  pairing annihilator of the span;
- owner-level function data: `linftyDistanceToSpan` is stated directly as an infimal-convolution
  owner on the chapter codomain layer `WithBotTop 𝕜`, rather than through a private bridge;
- derived API: the coordinate `sInf` companion formula, polyhedrality, and the support-function
  identity.

Layer target: `source-facing`, with the main function owner now at the codomain layer
`WithBotTop 𝕜` and scalar layer `𝕜`, specialized to textbook `ℝ^n` by taking `𝕜 = ℝ` and
finite index types.
-/

private def spanFamily (a : κ → E) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range a)

/-- The explicit dual set from Text 16.4.2, with canonical owner `D ∩ Lᗮₚ`,
where `D = coordinateL1Ball` and `L` is the span of the family `a`. -/
def linftyApproximationDualSet (a : κ → E) : Set E :=
  {x | x ∈ D ∧ x ∈ (spanFamily a)ᗮₚ}

/-- Canonical owner for the source function in Text 16.4.2: the infimal convolution of the
support function of `D` and the indicator of `spanFamily a`. -/
def linftyDistanceToSpan (a : κ → E) : E → WithBotTop 𝕜 :=
  infimal_convolution
    (δᵛ[WithBotTop 𝕜](· | D))
    (δ[𝕜](· | spanFamily a))

/-- Unfolding form of `linftyDistanceToSpan` at the canonical owner layer. -/
theorem linftyDistanceToSpan_def (a : κ → E) :
    linftyDistanceToSpan a =
      infimal_convolution
        (δᵛ[WithBotTop 𝕜](· | D))
        (δ[𝕜](· | spanFamily a)) :=
  rfl

/-- Source-facing coordinate companion for Text 16.4.2:
`linftyDistanceToSpan` agrees pointwise with
`x ↦ inf {‖x - ∑ t c t • a t‖∞ | c : κ → 𝕜}`. -/
theorem linftyDistanceToSpan_eq_sInf_coefficients [Fintype κ] (a : κ → E) (x : E) :
    linftyDistanceToSpan a x =
      sInf
        (Set.range fun c : κ → 𝕜 ↦
          ((linftyNorm (x - ∑ t, c t • a t) : 𝕜) : WithBotTop 𝕜)) := by
  sorry

-- Proof sketch: `D = coordinateL1Ball` is polyhedral convex by coordinate half-space inequalities,
-- and `spanFamily a` is a linear subspace, so its pairing annihilator is a linear-equality slice;
-- finite intersections of polyhedral sets are polyhedral.
/-- The explicit dual set from Text 16.4.2 is polyhedral convex. -/
theorem linftyApproximationDualSet_isPolyhedral (a : κ → E) :
    (linftyApproximationDualSet a).IsPolyhedral 𝕜 := by
  sorry

/-- The coordinate `ℓ¹` unit ball is polyhedral convex. This is the empty-family specialization of
Text 16.4.2's dual-set construction. -/
theorem coordinateL1Ball_isPolyhedral :
    (coordinateL1Ball : Set E).IsPolyhedral 𝕜 := by
  sorry

-- Proof sketch: combine `linftyDistanceToSpan_def` with the finite infimal-convolution conjugacy
-- pattern from Section 16 and the indicator-conjugate bridge for pairing annihilators, yielding
-- the support function of `D ∩ Lᗮₚ`.
/-- Text 16.4.2 at the canonical codomain layer: for a family `a : κ → (ι → 𝕜)`, and hence in
particular for finite real coordinates, the source function
`x ↦ inf {‖x - ∑ t c t • a t‖∞ | c : κ → 𝕜}` is the support function of
`linftyApproximationDualSet a = D ∩ Lᗮₚ`. -/
theorem supportFunction_linftyApproximationDualSet_eq_linftyDistanceToSpan (a : κ → E) :
    (δᵛ[WithBotTop 𝕜](· | linftyApproximationDualSet a) : E → WithBotTop 𝕜) =
      linftyDistanceToSpan a := by
  sorry

end
