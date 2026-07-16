import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_3

-- Declarations for this item will be appended below by the statement pipeline.

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
