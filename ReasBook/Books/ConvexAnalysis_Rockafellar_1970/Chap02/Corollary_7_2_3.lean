import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.2.3 gives a dichotomy for a convex function whose effective domain
  is relatively open.
- `core/canonical`: the owner abstractions already fixed upstream in this chapter are
  `Function.IsConvex`, `Function.IsProper`, `IsRelativelyOpen`, and the effective-domain owners
  `dom(·)` / `riDom[𝕜](·)`.
- `bridge/view`: relative openness is converted to the owner equality
  `riDom[𝕜](f) = dom(f)` via `IsRelativelyOpen`, while the textbook
  phrase "f(x) is infinite" is rendered pointwise as `f x = ⊥ ∨ f x = ⊤`.

Domain-style sampling used here:
- the chapter owner predicate `Function.IsConvex`;
- the owner effective-domain notation `dom(·)`;
- the chapter relative-interior notation `riDom[𝕜](·)`;
- the chapter properness owner `Function.IsProper` and the consequence `Function.IsProper.bot_lt`;
- the chapter source-facing predicate `IsRelativelyOpen 𝕜`;
- Theorem 7.2 in its owner form
  `Function.IsConvex.eq_bot_of_mem_riDom`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the owner convexity hypothesis `Function.IsConvex 𝕜 f`, and
  the owner equality `riDom[𝕜](f) = dom(f)`;
- source-facing bridge input: the relative-openness hypothesis `IsRelativelyOpen 𝕜` on `dom(f)`,
  which is definitionally this owner equality;
- canonical owner conclusion: either `f` is everywhere strictly above `⊥`, or
  `f x = ⊥ ↔ x ∈ dom(f)` pointwise on the effective-domain owner;
- derived source-style conclusion: every value is an infinite endpoint of `WithBotTop 𝕜`.
- Layer target: this item is `source-facing`, but it is expressed directly through the chapter's
  owner predicates and effective-domain notation rather than through duplicate raw
  `intrinsicInterior 𝕜 dom(f)` / `{x | f x < ⊤}` presentations.
-/

-- Proof sketch: split on properness. In the proper case, proper functions are everywhere strictly
-- above `⊥` by `Function.IsProper.bot_lt`. In the improper case, `IsRelativelyOpen` turns the
-- relative-openness hypothesis into `riDom[𝕜](f) = dom(f)`, so Theorem 7.2
-- yields `f x = ⊥` on the effective domain. Outside the effective domain one has `f x = ⊤`, since
-- nonmembership in `dom(f)` is exactly `¬ f x < ⊤`, hence every value is infinite.
namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Bridge lemma: this is the intrinsic-equality expansion of the source-facing
-- `IsRelativelyOpen 𝕜 dom(f)` hypothesis.
private theorem all_gt_bot_or_eq_bot_iff_mem_dom_of_riDom_eq_dom
    (hf_convex : f.IsConvex 𝕜) (hriDom_eq : riDom[𝕜](f) = dom(f)) :
    (∀ x, ⊥ < f x) ∨ (∀ x, f x = ⊥ ↔ x ∈ dom(f)) := by
  by_cases hproper : f.IsProper
  · exact Or.inl hproper.bot_lt
  · refine Or.inr ?_
    intro x
    constructor
    · intro hxb
      simp [mem_effectiveDomain, hxb]
    · intro hx
      exact hf_convex.eq_bot_of_mem_riDom hproper <| by
        simpa [hriDom_eq] using hx

/-! Corollary 7.2.3 in source-facing relatively-open owner form:
`IsRelativelyOpen 𝕜 dom(f)` is the public hypothesis surface, and the
`riDom[𝕜](f) = dom(f)` equality is used only as an internal bridge. -/

/-- Corollary 7.2.3, relatively-open owner form with effective-domain branch:
either `f` is everywhere strictly above `⊥`, or `f x = ⊥` holds exactly on `dom(f)`. -/
theorem all_gt_bot_or_eq_bot_iff_mem_dom
    (hf_convex : f.IsConvex 𝕜) (hdom_open : IsRelativelyOpen 𝕜 dom(f)) :
    (∀ x, ⊥ < f x) ∨ (∀ x, f x = ⊥ ↔ x ∈ dom(f)) := by
  exact all_gt_bot_or_eq_bot_iff_mem_dom_of_riDom_eq_dom hf_convex <| by
    simpa [IsRelativelyOpen] using hdom_open

/-- Corollary 7.2.3: if a convex function has relatively open effective domain, for instance if
`dom(f) = Set.univ`, then either it is everywhere strictly above `⊥` or every value is
infinite, i.e. equal to `⊥` or `⊤` in the `WithBotTop 𝕜` codomain. -/
theorem all_gt_bot_or_all_infinite
    (hf_convex : f.IsConvex 𝕜) (hdom_open : IsRelativelyOpen 𝕜 dom(f)) :
    (∀ x, ⊥ < f x) ∨ (∀ x, f x = ⊥ ∨ f x = ⊤) := by
  rcases hf_convex.all_gt_bot_or_eq_bot_iff_mem_dom hdom_open with hgt | hbot
  · exact Or.inl hgt
  · refine Or.inr ?_
    intro x
    by_cases hx : x ∈ dom(f)
    · exact Or.inl ((hbot x).2 hx)
    · refine Or.inr ?_
      exact top_unique <| not_lt.mp <| by
        simpa [mem_effectiveDomain] using hx

end Function.IsConvex

end
