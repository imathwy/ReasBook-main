import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_26_3_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_5_0_2

universe u

section

open scoped Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local notation "IsClosedProperConvexℝ" => Function.IsClosedProperConvex (𝕜 := ℝ)

/- Definition 26.4.1.4: the project owner for a convex function of Legendre type is the
canonical Chapter 26 class `Function.IsLegendreTypeOn`. It records exactly that `C` is nonempty
and open, and that `f` is strictly convex and essentially smooth on `C`. -/
recall Function.IsLegendreTypeOn

-- Proof sketch: Corollary 26.3.1 identifies one-to-one-ness of the subdifferential graph with
-- strict convexity of `f.realBranch` on `interior (dom(f))` together with essential smoothness of
-- `f`. Via `riDom(f) = interior (dom(f))` under essential smoothness, this yields the intrinsic
-- owner surface `Function.IsLegendreTypeOn (riDom(f)) f.realBranch`.
/-- For a closed proper convex function, the subdifferential mapping is one-to-one exactly when
its intrinsic-domain pair `(riDom(f), f.realBranch)` is of Legendre type. -/
theorem biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvexℝ f) :
    (gph∂(f)).BiUnique ↔
      Function.IsLegendreTypeOn (riDom(f)) f.realBranch := by
  rw [biUnique_subdifferentialGraph_iff_strictConvexOn_interior_dom_and_isEssentiallySmooth hf,
    Function.isLegendreTypeOn_iff]
  constructor
  · rintro ⟨hstrict, hess⟩
    have hri_eq : riDom(f) = interior (dom(f)) := hess.riDom_eq_interior_dom
    exact
      ⟨hess.toIsEssentiallySmoothOn_riDom, by simp [hri_eq],
        by simpa [hri_eq] using hstrict⟩
  · rintro ⟨hessOn, hri_open, hstrict⟩
    have hri_subset_dom : riDom(f) ⊆ dom(f) := by
      intro x hx
      exact intrinsicInterior_subset (by simpa [riDom_real_eq_intrinsicInterior_dom] using hx)
    have hinterior_nonempty : (interior (dom(f))).Nonempty := by
      rcases hessOn.nonempty with ⟨x, hx⟩
      exact ⟨x, (interior_maximal hri_subset_dom hri_open) hx⟩
    have hess : f.IsEssentiallySmooth :=
      Function.isEssentiallySmooth_of_isEssentiallySmoothOn_riDom
        hf.convex hf.proper hessOn hinterior_nonempty
    exact ⟨by simpa [hess.riDom_eq_interior_dom] using hstrict, hess⟩

end
