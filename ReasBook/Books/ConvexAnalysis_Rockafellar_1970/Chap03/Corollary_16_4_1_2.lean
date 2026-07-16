import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_2

-- Declarations for this item will be appended below by the statement pipeline.

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
