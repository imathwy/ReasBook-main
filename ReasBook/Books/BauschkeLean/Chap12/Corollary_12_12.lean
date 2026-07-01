import Mathlib
import BauschkeLean.Chap08.Example_8_3
import BauschkeLean.Chap08.Proposition_8_4
import BauschkeLean.Chap12.Example_12_2
import BauschkeLean.Chap12.Proposition_12_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: use Example 12.2 to rewrite `fun x ↦ (Metric.infEDist x C : EReal)` as the
-- infimal convolution of the indicator of `C` with the norm, observe from Example 8.3 and
-- Example 8.9 that these two functions are convex when `C` is convex, and apply Proposition
-- 12.11.
/-- Corollary 12.12: if `C` is convex, then the extended-real distance function `d_C` is convex on
the ambient space. -/
theorem convex_epigraph_distanceToSet (C : Set H) (hC : Convex ℝ C) :
    Convex ℝ (epigraph (fun x ↦ (Metric.infEDist x C : EReal))) := by
  by_cases hC_nonempty : C.Nonempty
  · have hindicator_dom : effectiveDomain (ι[C]) = C := by
      ext x
      by_cases hx : x ∈ C <;> simp [effectiveDomain, indicator, hx]
    have hindicator_epi : Convex ℝ (epigraph (fun x ↦ (ι[C] x : EReal))) := by
      simpa [epigraph, indicator_apply] using
        (convex_epigraph_indicator_iff_convex C).2 hC
    have hindicator_jensen :=
      (convex_epigraph_iff_jensen_on_dom (fun x ↦ (ι[C] x : EReal))).1 hindicator_epi
    have hindicator :
        ConvexOn (ι[C]) (effectiveDomain (ι[C])) := by
      refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hx ↦ hx, ?_⟩
      intro x hx y hy α hα0 hα1
      exact hindicator_jensen
        (by simpa [hindicator_dom, effectiveDomain, dom] using hx)
        (by simpa [hindicator_dom, effectiveDomain, dom] using hy)
        hα0 hα1
    let κ : H → Set.Ioi (⊥ : EReal) := scaledNormKernel (1 : NNReal)
    have hnorm_real : _root_.ConvexOn ℝ (Set.univ : Set H) (norm : H → ℝ) := convexOn_univ_norm
    have hscaledNorm_epi :
        Convex ℝ (epigraph (fun x : H ↦ (κ x : EReal))) := by
      simpa [κ, epigraph, scaledNormKernel, one_mul] using hnorm_real.convex_epigraph
    have hscaledNorm_jensen :=
      (convex_epigraph_iff_jensen_on_dom (fun x : H ↦ (κ x : EReal))).1 hscaledNorm_epi
    have hscaledNorm : ConvexOn κ (effectiveDomain κ) := by
      refine ⟨by simp [κ, scaledNormKernel, Function.effectiveDomain_toEReal], fun _ hx ↦ hx, ?_⟩
      intro x hx y hy α hα0 hα1
      exact hscaledNorm_jensen
        (by simp [κ, dom, scaledNormKernel])
        (by simp [κ, dom, scaledNormKernel])
        hα0 hα1
    simpa [κ, distanceToSet_eq_indicator_infimalConvolution_norm C] using
      convex_epigraph_infimalConvolution (ι[C]) κ hindicator hscaledNorm
  · simpa [epigraph, Set.not_nonempty_iff_eq_empty.mp hC_nonempty, Metric.infEDist_empty] using
      (convex_empty : Convex ℝ (∅ : Set (H × ℝ)))

end

end ERealFunction
