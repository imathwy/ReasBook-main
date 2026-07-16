import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_2

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Remark 4.4.7 fixes the book-wide convention that a "convex function" is
  globally defined on the ambient space (the source `R^n` wording is a specialization).
- `core/canonical`: the owner predicate for this global convention is
  `ConvexOn 𝕜 (Set.univ : Set E) f`; the chapter owner for the implicit domain convention is
  `effectiveDomain` with membership theorem `mem_effectiveDomain`.
- `bridge/view`: the remark's comment that the effective domain is implicit from the formula for
  `f` is mediated by the chapter's canonical domain owner `dom(f)`, rather than by introducing a
  second local wrapper around finiteness.
- Primitive data vs derived API: the primitive object is a total function
  `f : E → WithTopBot α`; the convention "convex function" is represented by
  `ConvexOn 𝕜 Set.univ f`, and the
  implicit-domain observation is derived from `dom(f) = {x | f x < ⊤}` (with `EReal` recovered by
  specialization).
- Domain-style sampling used here: `ConvexOn`,
  `convexOn_iff_convex_epigraph`, `convexOn_withTopBot_iff_convex_epigraph`,
  `effectiveDomain`, and `mem_effectiveDomain`.
-/

/- Remark 4.4.7: throughout the book, a "convex function" means a globally defined convex
function (with source `R^n` / `EReal` language recovered by specialization); in this chapter the
source-facing owner predicate for that convention is `ConvexOn 𝕜 Set.univ`, with epigraph
convexity used as a bridge. -/
recall ConvexOn

/- The canonical bridge for the owner is convexity of the ordinary epigraph set. -/
recall convexOn_iff_convex_epigraph

/- Chapter bridge theorem specialized to the `WithTopBot` codomain owner layer. -/
recall convexOn_withTopBot_iff_convex_epigraph

/- The effective domain itself is the chapter's canonical owner for the implicit finiteness domain
of a globally defined function into an ordered codomain with top (including the source
`WithTopBot α` / `EReal` case). -/
recall effectiveDomain

/- The effective domain is read directly from the defining formula as the finiteness set
`dom(f) = {x | f x < ⊤}`. -/
recall mem_effectiveDomain

section

universe u v

variable {E : Type u}
variable {β : Type v} [LT β] [Top β]

/-- Set-level bridge form of the defining formula for the effective domain owner `dom(f)`. -/
@[simp] theorem dom_eq_setOf_lt_top (f : E → β) :
    dom(f) = {x | f x < ⊤} :=
  rfl

end

section

universe u v w

variable {𝕜 : Type w}
variable {E : Type u}
variable {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedAddMonoid (WithTopBot α)]
variable [Module 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]

/-- Global-owner specialization for Remark 4.4.7: saying "`f` is convex" on the ambient space is
exactly the `Set.univ` instance of the canonical `ConvexOn` owner. -/
theorem convexOn_univ_withTopBot_iff_convex_epigraph (f : E → WithTopBot α) :
    ConvexOn 𝕜 (Set.univ : Set E) f ↔
      Convex 𝕜 {p : E × WithTopBot α | f p.1 ≤ p.2} := by
  simpa using
    (convexOn_withTopBot_iff_convex_epigraph (𝕜 := 𝕜) (C := (Set.univ : Set E)) (f := f))

end
