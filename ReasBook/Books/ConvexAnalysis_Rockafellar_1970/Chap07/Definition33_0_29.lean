import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 33.0.29 names the source domains `dom F` and `dom F*` attached to a
  convex bifunction and its adjoint.
- `core/canonical`: the primal owner is already Chapter 6's bifunction domain `Bifunction.dom`,
  with membership owned by `Bifunction.mem_dom`.
- `bridge/view`: the adjoint-side clause is the same owner applied to the negated adjoint
  bifunction `-adjoint XStar UStar F`, which converts the source phrase
  “not identically `-∞`” into the existing domain language once one specializes to an
  extended-value codomain such as `WithTopBot α`.

Primary mathematical domain:
- convex-analysis effective domains of bifunction slices and adjoint slices.

Domain-style sampling used here:
- `effectiveDomain` / `dom(·)` from `Chap01.Definition_4_4`;
- `Bifunction.dom` and `Bifunction.mem_dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: the existing bifunction domain `dom F`;
- derived bridge/view: the adjoint-side source domain written canonically as
  `dom (-(F⋆ : XStar → UStar → L))`, definitionally equal to
  `dom (-adjoint XStar UStar F)`.

Layer target: `bridge/view`. This item reuses the Chapter 6 owner directly and adds no parallel
Chapter 33 domain wrapper.
-/

/- Definition 33.0.29 reuses the existing bifunction-domain owner `Bifunction.dom` for the primal
clause `dom F`. -/
recall Bifunction.dom

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type w}
variable [Preorder α] [Neg α]

-- Proof sketch: apply `Bifunction.mem_dom_iff_exists` to `-G`, then rewrite each slice condition
-- `-G u x < ⊤` by the Chapter 1 bridge `mem_dom_neg_iff` on the one-variable slice `G u`.
/-- A parameter belongs to `dom (-G)` exactly when some slice value of `G` is strictly above
`⊥`. -/
@[simp] theorem mem_dom_neg_iff_exists_bot_lt
    {G : U → X → WithTopBot α} {u : U} :
    u ∈ dom (-G) ↔ ∃ x : X, ⊥ < G u x := by
  rw [Bifunction.mem_dom_iff_exists]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_dom_neg_iff (g := G u) (x := x)).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_dom_neg_iff (g := G u) (x := x)).2 hx⟩

/-- Set-level form of `mem_dom_neg_iff_exists_bot_lt`: the bifunction domain `dom (-G)` is exactly
the set of parameters where some slice value of `G` lies strictly above `⊥`. -/
@[simp] theorem dom_neg_eq_setOf_exists_bot_lt
    (G : U → X → WithTopBot α) :
    dom (-G) = {u : U | ∃ x : X, ⊥ < G u x} := by
  ext u
  exact mem_dom_neg_iff_exists_bot_lt (G := G) (u := u)

section

variable [Sub (WithTopBot α)] [SupSet (WithTopBot α)]
variable [Neg UStar] [HasPairing (U × X) (UStar × XStar) (WithTopBot α)]

variable (F : U → X → WithTopBot α)

local notation "F⋆" => adjoint XStar UStar F

/-- A dual parameter belongs to the adjoint-side domain exactly when the corresponding adjoint
slice is not identically `-∞`, i.e. when some adjoint value is strictly above `⊥`. -/
@[simp] theorem mem_dom_neg_adjoint_iff_exists
    {xStar : XStar} :
    xStar ∈ dom (-F⋆) ↔ ∃ uStar : UStar, ⊥ < F⋆ xStar uStar := by
  simpa using
    (mem_dom_neg_iff_exists_bot_lt
      (G := F⋆) (u := xStar))

/-- Set-level source-domain formula for the adjoint side: `dom (-F⋆)` is exactly the set of
dual parameters whose adjoint slices attain a value strictly above `⊥`. -/
@[simp] theorem dom_neg_adjoint_eq_setOf_exists_bot_lt :
    dom (-F⋆) = {xStar : XStar | ∃ uStar : UStar, ⊥ < F⋆ xStar uStar} := by
  ext xStar
  exact mem_dom_neg_adjoint_iff_exists (F := F) (xStar := xStar)

end

end

end Bifunction
