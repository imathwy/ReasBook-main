import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [Preorder α] [AddZeroClass α]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.2 identifies the parameter domain of the bifunction
  `F u x = f₀ x + δ[α](x | S u)` with the set of parameters whose slice `S u` meets
  `dom(f₀)`.
- `core/canonical`: the existing owner layer already provides the indicator `δ[α](· | C)`, the
  one-variable effective-domain owner `dom(f₀)`, and the bifunction-domain owner `dom F`.
- `bridge/view`: this file should therefore state the result directly as a bridge from
  `dom F` to the intersection description, rather than reintroducing the raw set
  `{u | ∃ x, F u x < ⊤}` as a parallel public owner.

Domain-style sampling used here:
- `dom F` and `mem_dom_iff_exists` from `Definition_6_29_8`;
- `indicator_of_mem`, `indicator_of_notMem`, and `mem_effectiveDomain` from Chapter 1;
- `WithBotTop.add_top_of_ne_bot` from the canonical additive layer.

Primitive data vs derived API:
- primitive data: the slice family `S`, the extended-valued branch `f₀`, and the pointwise
  no-`⊥` hypothesis outside each slice `x ∉ S u → f₀ x ≠ ⊥` required by the
  `WithBotTop` additive semantics;
- derived API: the source intersection formula for the bifunction-domain owner.

Layer target: `bridge/view`.
-/

-- Proof sketch: use the canonical owner test `mem_dom_iff_exists`. If
-- `f₀ x + δ[α](x | S u) < ⊤`, then `x` must belong to `S u`; otherwise the indicator contributes
-- `⊤`, and the no-`⊥` hypothesis forces the sum to be `⊤`. On `S u`, the indicator vanishes, so
-- the same inequality is exactly `f₀ x < ⊤`, i.e. `x ∈ dom(f₀)`.
/-- Lemma 6.29.2: if the objective branch `f₀` never takes `⊥` outside the active slice `S u`,
then the bifunction domain of `u ↦ f₀ + δ[α](· | S u)` is exactly the set of parameters whose
slice set `S u` meets the effective domain `dom(f₀)`. This is the source formula
`dom F = {u | S_u ∩ C ≠ ∅}` with `C = dom f₀`, expressed on the canonical bifunction-domain
owner. -/
theorem dom_add_indicator_eq_setOf_inter_dom_nonempty
    (f₀ : X → WithBotTop α) (S : U → Set X)
    (hf₀_ne_bot : ∀ ⦃u x⦄, x ∉ S u → f₀ x ≠ ⊥) :
    dom ((fun _ : U ↦ f₀) + δᵇ[α](S)) =
      {u | (S u ∩ dom(f₀)).Nonempty} := by
  ext u
  rw [mem_dom_iff_exists]
  constructor
  · rintro ⟨x, hx⟩
    change f₀ x + δ[α](x | S u) < ⊤ at hx
    by_cases hxS : x ∈ S u
    · refine ⟨x, hxS, ?_⟩
      rw [indicator_of_mem (S u) hxS, add_zero] at hx
      rw [mem_effectiveDomain]
      exact hx
    · have hsum : f₀ x + δ[α](x | S u) = ⊤ := by
        rw [indicator_of_notMem (S u) hxS]
        exact WithBotTop.add_top_of_ne_bot (hf₀_ne_bot hxS)
      exact False.elim ((ne_of_lt hx) hsum)
  · rintro ⟨x, hxS, hxdom⟩
    refine ⟨x, ?_⟩
    change f₀ x + δ[α](x | S u) < ⊤
    rw [mem_effectiveDomain] at hxdom
    rw [indicator_of_mem (S u) hxS, add_zero]
    exact hxdom

end

end Bifunction
