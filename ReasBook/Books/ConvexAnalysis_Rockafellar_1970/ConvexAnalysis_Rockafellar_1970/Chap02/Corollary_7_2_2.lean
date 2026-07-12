import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_15

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.2.2 says that the closure of an improper convex function is again a
  closed improper convex function and agrees with the original function on `ri (dom f)`.
- `core/canonical`: the owner predicates already fixed in the chapter are `Function.IsConvex 𝕜`,
  `LowerSemicontinuous`, `Function.IsProper`, and Rockafellar's chapter closure owner `cl(·)`.
- `bridge/view`: Rockafellar's `ri (dom f)` is represented by the scalar-parameterized chapter
  notation `riDom[𝕜](f)`, and agreement there is expressed by `Set.EqOn`; Text 7.0.15 already
  supplies the owner-level `riDom` bridge for `cl(f)`.

Domain-style sampling used here:
- the lower-semicontinuous hull owner `cl(·)` and the owner theorem
  `lowerSemicontinuous_lowerSemicontinuousHull` from `Text_7_0_4`;
- `Function.isConvex_verticalInfimum` from `Theorem_5_3`, which is the owner theorem for
  convexity of functions built from epigraph sets;
- the properness owner `Function.IsProper` from `Definition_4_6`;
- `Function.not_isProper_iff` from `Definition_4_7`;
- Text 7.0.15 in the owner form
  `Function.IsConvex.cl_eqOn_riDom_of_not_isProper`.

Primitive data vs derived API:
- primitive data: an extended-codomain function `f : E → WithBotTop 𝕜`, together with the chapter
  owner `cl(f)`;
- source-facing extra hypotheses: convexity of `f` and, only where genuinely needed, the
  improperness hypothesis `¬ f.IsProper`;
- derived outputs: convexity and lower semicontinuity of `cl(f)`, failure of properness for that
  closure, and agreement with `f` on `riDom[𝕜](f)`.

Layer target: clause (1) and clause (3) are `source-facing` consequences on the chapter owner
`cl(f)`; clause (2) is `core/canonical`, since lower semicontinuity is an owner property of
`cl(f)` itself and does not use the source's extra convex/improper hypotheses; clause (4) is
`bridge/view`, and is reused directly from `Text_7_0_15` rather than restated through a duplicate
local wrapper.
-/

section Convexity

variable {𝕜 E : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable {f : E → WithBotTop 𝕜}

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: `cl(f)` is by definition the vertical infimum attached to `closure (epi f)`, and
-- convexity of `epi f` passes to its closure. The source's improperness hypothesis is redundant
-- for this owner-level convexity consequence and is removed from the statement.
/-- Corollary 7.2.2 (1), owner form: the chapter closure `cl(f)` of a convex function is convex. -/
theorem lowerSemicontinuousHull_isConvex
    (hf : f.IsConvex 𝕜) :
    (cl(f)).IsConvex 𝕜 := by
  simpa [lowerSemicontinuousHull] using
    Function.isConvex_verticalInfimum (hf.convex_epi.closure)

end Function.IsConvex

end Convexity

/- Corollary 7.2.2 (2): this is exactly the canonical `cl(·)` lower-semicontinuity owner theorem
from `Text_7_0_4`. -/
recall lowerSemicontinuous_lowerSemicontinuousHull

/- Corollary 7.2.2 (4): this is exactly the owner theorem from `Text_7_0_15`. -/
recall Function.IsConvex.cl_eqOn_riDom_of_not_isProper

section Properness

variable {𝕜 E : Type*}
variable [TopologicalSpace E]
variable [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [NoBotOrder 𝕜]
variable {f : E → WithBotTop 𝕜}

namespace Function

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: if `f` already attains `⊥`, then `cl(f) ≤ f` gives the same bottom value for
-- `cl(f)`. If `dom(f) = ∅`, then `epi f = ∅`, hence
-- `epi (cl(f)) = closure (epi f) = ∅`, so `dom(cl(f)) = ∅` as well.
/-- Corollary 7.2.2 (3), owner form: if `f` is improper, then `cl(f)` is improper. The source's
convexity hypothesis is redundant for this owner-level persistence statement. -/
theorem lowerSemicontinuousHull_not_isProper_of_not_isProper
    (hf_not_proper : ¬ f.IsProper) :
    ¬ (cl(f)).IsProper := by
  rw [Function.not_isProper_iff]
  rw [Function.not_isProper_iff] at hf_not_proper
  rcases hf_not_proper with hdom_not_nonempty | ⟨x, hx⟩
  · left
    have hdom_empty : dom(f) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hdom_not_nonempty
    have hepi_empty : epi f = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨y, μ⟩ hy
      have hy_dom : y ∈ dom(f) := by
        exact lt_of_le_of_lt (by simpa [mem_epi_iff] using hy) (WithBotTop.coe_lt_top μ)
      simp [hdom_empty] at hy_dom
    calc
      dom(cl(f)) = Prod.fst '' closure (epi f) := by
        simpa [lowerSemicontinuousHull] using
          Function.effectiveDomain_verticalInfimum_eq_image_fst (closure (epi f))
      _ = ∅ := by simp [hepi_empty]
  · right
    refine ⟨x, ?_⟩
    exact le_bot_iff.mp <| by
      simpa [hx] using (lowerSemicontinuousHull_le f x)

end Function

end Properness

end
