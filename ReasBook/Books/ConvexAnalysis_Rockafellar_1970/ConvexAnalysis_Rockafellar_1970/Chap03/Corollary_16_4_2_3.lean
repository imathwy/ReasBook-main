import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_1

-- Declarations for this item will be appended below by the statement pipeline.

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
