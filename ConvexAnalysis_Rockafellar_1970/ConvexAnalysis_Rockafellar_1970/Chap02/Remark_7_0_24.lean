import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_15
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u

variable {𝕜 E : Type u}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: in the improper case, Text 7.0.15 identifies `f` with its lower-semicontinuous
-- hull `cl(f)` on `riDom[𝕜](f)`. In the proper case, Theorem 7.4 gives the same identification
-- away from the relative frontier `rb[𝕜](dom(f))`. If `x ∉ closure (dom(f))`, then a neighborhood
-- of
-- `x` is disjoint from `dom(f)`, so `f = ⊤` near `x` and lower semicontinuity is immediate.
/-- Remark 7.0.24: a convex extended-real-valued function is lower semicontinuous at every point
outside the relative boundary `rb[𝕜](dom(f))` of its effective domain. Equivalently, any failure
of lower semicontinuity can occur only at relative-boundary points of `dom(f)`. -/
theorem lowerSemicontinuousAt_of_not_mem_intrinsicFrontier_dom
    (hf : f.IsConvex 𝕜) {x : E} (hx : x ∉ rb[𝕜](dom(f))) :
    LowerSemicontinuousAt f x := by
  by_cases hx_closure : x ∈ closure (dom(f))
  · have hx_ri : x ∈ riDom[𝕜](f) := by
      rw [← closure_diff_intrinsicFrontier (dom(f))]
      exact ⟨hx_closure, hx⟩
    have hcl_eq_fx : cl(f) x = f x := by
      by_cases hf_proper : f.IsProper
      · have hEqOn : Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ := by
          simpa using
            hf.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper hf_proper
        exact hEqOn (by simpa using hx)
      · exact hf.cl_eqOn_riDom_of_not_isProper hf_proper hx_ri
    have hcl_lsc_at : LowerSemicontinuousAt (cl(f)) x :=
      (lowerSemicontinuous_lowerSemicontinuousHull f).lowerSemicontinuousAt x
    have hcl_liminf : cl(f) x ≤ Filter.liminf (cl(f)) (nhds x) :=
      (lowerSemicontinuousAt_iff_le_liminf).1 hcl_lsc_at
    have hliminf_mono :
        Filter.liminf (cl(f)) (nhds x) ≤ Filter.liminf f (nhds x) :=
      Filter.liminf_le_liminf <| Filter.Eventually.of_forall (lowerSemicontinuousHull_le f)
    exact (lowerSemicontinuousAt_iff_le_liminf).2 <|
      by simpa [hcl_eq_fx] using hcl_liminf.trans hliminf_mono
  · have hx_not_dom : x ∉ dom(f) := fun hx_dom ↦ hx_closure (subset_closure hx_dom)
    have hfx_top : f x = ⊤ := by
      by_contra hfx_ne_top
      exact hx_not_dom <| mem_effectiveDomain.2 <| lt_of_le_of_ne le_top hfx_ne_top
    change SemicontinuousAt (fun x' y ↦ y < f x') x
    intro y hy
    have hy_top : y < (⊤ : WithBotTop 𝕜) := by
      simpa [hfx_top] using hy
    have hnhds :
        (closure (dom(f)))ᶜ ∈ nhds x :=
      (isOpen_compl_iff.mpr isClosed_closure).mem_nhds hx_closure
    filter_upwards [hnhds] with x' hx'
    have hx'_not_dom : x' ∉ dom(f) := fun hx'_dom ↦ hx' (subset_closure hx'_dom)
    have hfx'_top : f x' = ⊤ := by
      by_contra hfx'_ne_top
      exact hx'_not_dom <| mem_effectiveDomain.2 <| lt_of_le_of_ne le_top hfx'_ne_top
    simpa [hfx'_top] using hy_top

/-- The `ri(dom f)` formulation in Remark 7.0.24 is the relative-interior specialization of the
full off-boundary theorem. -/
theorem lowerSemicontinuousAt_of_mem_riDom
    (hf : f.IsConvex 𝕜) {x : E} (hx : x ∈ riDom[𝕜](f)) :
    LowerSemicontinuousAt f x := by
  apply hf.lowerSemicontinuousAt_of_not_mem_intrinsicFrontier_dom
  intro hx_frontier
  have hpair : x ∈ closure (dom(f)) \ rb[𝕜](dom(f)) := by
    rw [closure_diff_intrinsicFrontier (dom(f))]
    simpa using hx
  exact hpair.2 hx_frontier

end Function.IsConvex

/- The relative continuity assertion mentioned in this remark is exactly the Chapter 10 owner
theorem `Function.IsConvex.continuousOn_riDom`. -/
recall Function.IsConvex.continuousOn_riDom

end
