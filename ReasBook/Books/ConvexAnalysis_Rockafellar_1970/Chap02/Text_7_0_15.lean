import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.15 says that for an improper convex function, the Chapter 2 closure
  `cl(f)` agrees with `f` on the relative interior of the effective domain.
- `core/canonical`: the owner abstractions already fixed earlier in the chapter are
  `Function.IsConvex 𝕜`, `Function.IsProper`, the closure owner `cl(·)`, and the scalar-indexed
  relative-interior notation `riDom[𝕜](·)`.
- `bridge/view`: the source-facing improperness assumption `¬ f.IsProper` is a wrapper over the
  primitive bottom-attainment datum `∃ x, f x = ⊥` once one has a domain point.

Domain-style sampling used here:
- `Function.IsConvex.eq_bot_of_mem_riDom_of_exists_eq_bot` from `Theorem_7_2`;
- `Function.not_isProper_iff_exists_eq_bot_of_nonempty_dom` from `Definition_4_6`;
- `lowerSemicontinuousHull_le` from `Text_7_0_4`;
- `Set.EqOn` as the canonical owner for agreement on `riDom[𝕜](f)`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop 𝕜`, the convexity owner
  `Function.IsConvex 𝕜 f`, and bottom-attainment data `∃ x, f x = ⊥`;
- derived output: agreement of `cl(f)` with `f` on `riDom[𝕜](f)`;
- source-facing wrapper: the same agreement theorem under `¬ f.IsProper`, discharged through the
  canonical improperness bridge once a domain point is provided by `riDom`.

Layer target: primitive owner theorem first, with a thin source-facing improperness wrapper.
-/

namespace Function.IsConvex

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithBotTop 𝕜}

/-- Primitive-data form of Text 7.0.15: if a convex function attains `⊥`, then `cl(f)` agrees
with `f` on `ri (dom f)`, represented here by `riDom[𝕜](f)`. -/
-- Proof sketch: Theorem 7.2 gives `f x = ⊥` on `riDom[𝕜](f)`. Also `cl(f) ≤ f` pointwise, so on
-- `riDom[𝕜](f)` one gets `cl(f) x ≤ ⊥`, hence `cl(f) x = ⊥` as well.
theorem cl_eqOn_riDom_of_exists_eq_bot
    (hf : f.IsConvex 𝕜) (hbot : ∃ x, f x = ⊥) :
    Set.EqOn (cl(f)) f riDom[𝕜](f) := by
  intro x hx
  have hfx_bot : f x = ⊥ := hf.eq_bot_of_mem_riDom_of_exists_eq_bot hbot hx
  have hcl_le : cl(f) x ≤ f x := lowerSemicontinuousHull_le f x
  have hcl_bot : cl(f) x = ⊥ := le_bot_iff.mp (by simpa [hfx_bot] using hcl_le)
  simp [hcl_bot, hfx_bot]

/-- Source-facing improperness form of Text 7.0.15. -/
theorem cl_eqOn_riDom_of_not_isProper
    (hf : f.IsConvex 𝕜) (hf_not_proper : ¬ f.IsProper) :
    Set.EqOn (cl(f)) f riDom[𝕜](f) := by
  intro x hx
  have hdom_nonempty : dom(f).Nonempty := ⟨x, intrinsicInterior_subset hx⟩
  rcases (Function.not_isProper_iff_exists_eq_bot_of_nonempty_dom (f := f) hdom_nonempty).1
      hf_not_proper with ⟨u, hu_eq_bot⟩
  exact cl_eqOn_riDom_of_exists_eq_bot hf ⟨u, hu_eq_bot⟩ hx

end Function.IsConvex

end
