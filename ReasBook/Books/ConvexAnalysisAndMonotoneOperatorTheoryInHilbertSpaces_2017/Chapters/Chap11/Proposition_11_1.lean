import Mathlib
import BauschkeLean.Chap01.Text_1_0_28
import BauschkeLean.Chap03.Proposition_3_4
import BauschkeLean.Chap03.Proposition_3_44
import BauschkeLean.Chap07.Proposition_7_13
import BauschkeLean.Chap08.Corollary_8_5
import BauschkeLean.Chap08.Proposition_8_11
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Proposition 11.1 (1): if `f` is lower semicontinuous, then `f` has the same
supremum on `C` and on `closure C`. -/
omit [InnerProductSpace ℝ H] in
theorem sSup_image_closure_eq_of_lowerSemicontinuous {f : H → EReal}
    (hf : LowerSemicontinuous f) (C : Set H) :
    sSup (f '' closure C) = sSup (f '' C) := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, hx_closure, rfl⟩
    -- If `f x` were strictly above the supremum on `C`, a real threshold would separate them.
    by_contra hx
    have hx' : sSup (f '' C) < f x := lt_of_not_ge hx
    rcases EReal.lt_iff_exists_real_btwn.mp hx' with ⟨ξ, hsξ, hξx⟩
    have hclosed : IsClosed (lowerLevelSet f ξ) :=
      by simpa [lowerLevelSet] using hf.isClosed_preimage ((ξ : ℝ) : EReal)
    have hC_subset : C ⊆ lowerLevelSet f ξ := by
      -- Every value on `C` is bounded by the supremum, hence by the separating level `ξ`.
      intro y hy
      rw [mem_lowerLevelSet_iff]
      exact le_trans ((isLUB_sSup _).1 (Set.mem_image_of_mem _ hy)) hsξ.le
    have hx_level : x ∈ lowerLevelSet f ξ :=
      (closure_minimal hC_subset hclosed) hx_closure
    rw [mem_lowerLevelSet_iff] at hx_level
    exact (not_le_of_gt hξx) hx_level
  · -- The direct inclusion `C ⊆ closure C` gives the reverse inequality immediately.
    exact sSup_le_sSup <| by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, subset_closure hx, rfl⟩

/-- Helper for Proposition 11.1: Jensen convexity implies convexity of the epigraph. -/
private theorem convex_epigraph_of_isConvex {f : H → EReal} (hf : IsConvex f) :
    Convex ℝ (epigraph f) := by
  -- Convert the Chapter 9 Jensen-style predicate into the Chapter 8 epigraph owner theorem.
  refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
  intro x y hx hy a ha0 ha1
  exact hf ha0.le ha1.le

/-- Helper for Proposition 11.1: a convex extended-real-valued function has the same supremum on a
set and on its convex hull. -/
private theorem sSup_image_convexHull_eq_of_isConvex {f : H → EReal}
    (hf : IsConvex f) {C : Set H} :
    sSup (f '' convexHull ℝ C) = sSup (f '' C) := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, hx_hull, rfl⟩
    -- Route correction: propagate a separating real level through the convex lower level set.
    by_contra hx
    have hx' : sSup (f '' C) < f x := lt_of_not_ge hx
    rcases EReal.lt_iff_exists_real_btwn.mp hx' with ⟨ξ, hsξ, hξx⟩
    have hC_subset : C ⊆ lowerLevelSet f ξ := by
      -- Every point of `C` lies below the same separating level `ξ`.
      intro y hy
      rw [mem_lowerLevelSet_iff]
      exact le_trans ((isLUB_sSup _).1 (Set.mem_image_of_mem _ hy)) hsξ.le
    have hlevel_convex : Convex ℝ (lowerLevelSet f ξ) :=
      convex_lowerLevelSet_of_convex_epigraph f (convex_epigraph_of_isConvex hf) ξ
    have hx_level : x ∈ lowerLevelSet f ξ :=
      (convexHull_min hC_subset hlevel_convex) hx_hull
    rw [mem_lowerLevelSet_iff] at hx_level
    exact (not_le_of_gt hξx) hx_level
  · -- The original set sits inside its convex hull.
    exact sSup_le_sSup <| by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, subset_convexHull ℝ C hx, rfl⟩

/-- Proposition 11.1 (2): if `f` is convex, then `f` has the same supremum on
`C` and on `convexHull ℝ C`. -/
theorem proposition_11_1_2 {f : H → EReal}
    (hf : IsConvex f) {C : Set H} :
    sSup (f '' convexHull ℝ C) = sSup (f '' C) := by
  -- Apply the convex-hull supremum theorem proved from convex lower level sets.
  exact sSup_image_convexHull_eq_of_isConvex hf

/-- The inner-product infimum on `C` is the negative of the support function of `C`
evaluated at `-u`. -/
theorem innerInfimumOn_eq_neg_supportFunction_neg (C : Set H) (u : H) :
    innerInfimumOn C u = -σ[C] (-u) := by
  rw [innerInfimumOn_eq_sInf_image]
  let S : Set EReal := (fun x : H ↦ (⟪x, u⟫_ℝ : EReal)) '' C
  have hneg_image : (fun x : H ↦ (⟪x, -u⟫_ℝ : EReal)) '' C = (-·) '' S := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟪x, u⟫_ℝ : EReal), ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      rcases hs with ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
  calc
    sInf S = -sSup ((-·) '' S) := by
      rw [EReal.sSup_eq_neg_sInf_image_neg ((-·) '' S)]
      simp
    _ = -σ[C] (-u) := by
      rw [supportFunction_eq_sSup_image, hneg_image]

/-- Proposition 11.1 (4): the inner-product infimum is unchanged by passing to
the closed convex hull. -/
theorem innerInfimumOn_closure_convexHull_eq (C : Set H) :
    innerInfimumOn (closure (convexHull ℝ C)) = innerInfimumOn C := by
  ext u
  have hσ : σ[closure (convexHull ℝ C)] = σ[C] := by
    obtain ⟨hconv, hclosure⟩ := supportFunction_eq_convexHull_and_closure_convexHull C
    exact (hconv.trans hclosure).symm
  simpa [innerInfimumOn_eq_neg_supportFunction_neg] using
    congrArg (fun g : H → EReal ↦ -g (-u)) hσ

/-- Proposition 11.1 (5): if `f ∈ Γ₀(H)`, `C` is convex, and `dom f ∩ interior C` is nonempty,
then the infimum of `f` is unchanged by passing from `C` to `closure C`. -/
theorem proposition_11_1_5
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} (hC : Convex ℝ C)
    (hinter : (effectiveDomain f ∩ interior C).Nonempty) :
    sInf (f.asEReal '' closure C) = sInf (f.asEReal '' C) := by
  rcases hinter with ⟨c, hc_dom, hc_int⟩
  have hf_lsc : LowerSemicontinuous f.asEReal := hf.1
  have hf_conv : ConvexOn f (effectiveDomain f) := hf.2
  have hf_epi : Convex ℝ (epigraph f.asEReal) :=
    convex_epigraph_asEReal_of_mem_gammaZero hf
  apply le_antisymm
  · exact sInf_le_sInf (Set.image_mono subset_closure)
  · refine le_sInf ?_
    rintro _ ⟨x, hx_closure, rfl⟩
    by_cases hx_dom : x ∈ effectiveDomain f
    · have hx_finite : (f x : EReal) < ⊤ := mem_effectiveDomain_iff.mp hx_dom
      have hc_finite : (f c : EReal) < ⊤ := mem_effectiveDomain_iff.mp hc_dom
      have hα_lt_one : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      have hline_tendsto :
          Filter.Tendsto (fun α : ℝ ↦ (f (AffineMap.lineMap x c α) : EReal))
            (𝓝[>] (0 : ℝ)) (𝓝 (f x : EReal)) :=
        tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
          hf_lsc (by simpa [epigraph] using hf_epi) hx_finite hc_finite
      have hlower :
          ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
            sInf (f.asEReal '' C) ≤ (f (AffineMap.lineMap x c α) : EReal) := by
        filter_upwards [self_mem_nhdsWithin, hα_lt_one] with α hα_pos hα_lt_one
        have hline_int :
            AffineMap.lineMap x c α ∈ interior C := by
          have hmem :
              AffineMap.lineMap c x (1 - α) ∈ interior C :=
            lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure hC hc_int hx_closure
              ⟨sub_nonneg.mpr hα_lt_one.le, sub_lt_self 1 hα_pos⟩
          simpa [AffineMap.lineMap_apply_one_sub] using hmem
        have hline_mem : AffineMap.lineMap x c α ∈ C := interior_subset hline_int
        exact (isGLB_sInf _).1 ⟨AffineMap.lineMap x c α, hline_mem, rfl⟩
      exact (isClosed_Ici.mem_of_tendsto hline_tendsto hlower : f.asEReal x ∈ Set.Ici _)
    · have hx_top : f.asEReal x = ⊤ := by
        exact le_antisymm le_top <| not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx_dom)
      simpa [hx_top]

end Hilbert

end ERealFunction
