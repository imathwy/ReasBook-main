import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_29_1

universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [Bot β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.29.3 identifies the parameter domain of a convex bifunction
  whose graph is nowhere `⊥` with the set of parameters whose slices are proper convex functions.
- `core/canonical`: the already-built chapter owners available here are the one-variable
  effective-domain notation `dom(·)`, the bifunction-domain owner `dom F`,
  `Function.IsProper` for properness of a codomain-agnostic slice, and the primitive
  pointwise `⊥`-exclusion `f x ≠ ⊥` built into that owner,
  `Function.IsConvex 𝕜` for convexity.
- `bridge/view`: Definition 6.29.8 identifies the parameter domain `dom F` with slice
  effective-domain nonemptiness. The properness part is the genuine new content here, while the
  convexity part comes from restricting graph convexity to a fixed first variable.

Domain-style sampling used here:
- `Bifunction.dom` from `Definition_6_29_8`;
- the notation `dom(·)` and `mem_effectiveDomain` from
  `Chap01.Definition_4_4`, available through `Chap01.Definition_4_6`;
- `Function.IsProper`, `Function.isProper_iff`, and `Function.IsProper.ne_bot` from
  `Chap01.Definition_4_6`;
- `Function.IsConvex 𝕜` from `Chap01.Theorem_4_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- primitive owner hypothesis for the properness clause: no-`⊥` on the parameter domain,
  i.e. `∀ ⦃u⦄, u ∈ dom F → ∀ x, F u x ≠ ⊥`;
- derived companion hypothesis: full graph properness
  `(Function.uncurry F).IsProper`, used only to recover that primitive no-`⊥` data;
- derived conclusions: slice properness and slice convexity for each `u`.

Layer target: `source-facing`, stated directly with the existing chapter owners and the defining
owner from Definition 6.29.8 rather than through a new packaged notion of “proper convex slice”.
-/

-- Proof sketch: from `u ∈ dom F`, the hypothesis `hF_ne_bot_on_dom` gives that the whole slice
-- `F u` is nowhere `⊥`, while `u ∈ dom F` itself is exactly nonempty slice effective domain.
-- Hence `F u` is proper. Conversely, if the slice `F u` is proper, then its domain is nonempty,
-- so `u ∈ dom F`.
/-- The parameter domain from Definition 6.29.8 is exactly the set of parameters whose slices are
proper, provided slices over that domain are nowhere `⊥`. -/
theorem dom_eq_setOf_slice_isProper
    {F : U → X → β}
    (hF_ne_bot_on_dom : ∀ ⦃u⦄, u ∈ dom F → ∀ x, F u x ≠ ⊥) :
    dom F = {u : U | (F u).IsProper} := by
  ext u
  constructor
  · intro hu
    exact ⟨mem_dom.mp hu, hF_ne_bot_on_dom hu⟩
  · intro hu
    exact mem_dom.mpr hu.nonempty_dom

/-- Properness-form restatement of `dom_eq_setOf_slice_isProper`. The graph-proper hypothesis is
used only to recover the primitive graphwise no-`⊥` condition. -/
theorem dom_eq_setOf_slice_isProper_of_isProper
    {F : U → X → β}
    (hF_proper : (Function.uncurry F).IsProper) :
    dom F = {u : U | (F u).IsProper} :=
  dom_eq_setOf_slice_isProper (fun {u} _ x ↦ hF_proper.ne_bot (u, x))

end

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α] [LT α]

-- Proof sketch: the properness part is exactly `dom_eq_setOf_slice_isProper`. The extra convexity
-- requirement on the right is supplied by a primitive slice-wise convexity hypothesis, so the
-- right-hand side reduces to "slice proper and slice convex" without introducing graph-level
-- assumptions.
/-- Core owner form of Proposition 6.29.3: if slices over `dom F` are convex and nowhere `⊥`,
then the parameter domain from Definition 6.29.8 is exactly the set of parameters whose slices are
proper convex functions. -/
theorem dom_eq_setOf_slice_isProperConvex_of_sliceConvex
    {F : U → X → WithBotTop α}
    (hF_slice_convex_on_dom : ∀ ⦃u⦄, u ∈ dom F → (F u).IsConvex 𝕜)
    (hF_ne_bot_on_dom : ∀ ⦃u⦄, u ∈ dom F → ∀ x, F u x ≠ ⊥) :
    dom F = {u : U | (F u).IsProper ∧ (F u).IsConvex 𝕜} := by
  ext u
  rw [dom_eq_setOf_slice_isProper hF_ne_bot_on_dom]
  constructor
  · intro hu
    exact ⟨hu, hF_slice_convex_on_dom hu.nonempty_dom⟩
  · intro hu
    exact hu.1

section

variable [AddCommMonoid U] [Module 𝕜 U]

-- Proof sketch: apply the primitive slice-convex theorem above, using Proposition 6.29.1 to
-- obtain slice convexity from graph convexity of `Function.uncurry F`.
/-- Proposition 6.29.3, source-facing graph form: if a bifunction graph is convex and nowhere
`⊥`, then its parameter domain from Definition 6.29.8 is exactly the set of parameters whose
slices are proper convex functions. -/
theorem dom_eq_setOf_slice_isProperConvex
    {F : U → X → WithBotTop α}
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_ne_bot : ∀ u x, F u x ≠ ⊥) :
    dom F = {u : U | (F u).IsProper ∧ (F u).IsConvex 𝕜} := by
  refine dom_eq_setOf_slice_isProperConvex_of_sliceConvex ?_ ?_
  · intro u _
    exact hF_convex.slice_uncurry u
  · intro u _ x
    exact hF_ne_bot u x

/-- Textbook proper-convex restatement of Proposition 6.29.3. The graph-proper hypothesis adds no
new primitive data beyond the graphwise no-`⊥` condition used by the main theorem. -/
theorem dom_eq_setOf_slice_isProperConvex_of_isProper
    {F : U → X → WithBotTop α}
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_proper : (Function.uncurry F).IsProper) :
    dom F = {u : U | (F u).IsProper ∧ (F u).IsConvex 𝕜} :=
  dom_eq_setOf_slice_isProperConvex hF_convex (fun u x ↦ hF_proper.ne_bot (u, x))

end

end

end Bifunction
