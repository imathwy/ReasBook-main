import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

section

variable {E : Type u} {α : Type v} [Preorder α] [Nonempty α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.3 identifies the union of all finite-height sublevel sets of a
  function with its effective domain.
- `core/canonical`: the owner abstraction is `dom(·)` with membership bridge
  `mem_effectiveDomain`; finite-height sublevel sets are the raw sets
  `{x | f x ≤ (a : WithTopBot α)}`.
- `bridge/view`: the textbook properness hypothesis is redundant once `α` is inhabited, because the
  value `⊥` already lies in every finite-height sublevel set. The primitive ambient datum is only
  the existence of a finite level.

Domain-style sampling used here:
- `dom(·)` and `mem_effectiveDomain` from `Chap01.Definition_4_4`;
- explicit `WithTop.recTopCoe`/`WithBot.recBotCoe` decomposition of finite values;
- `WithTop.coe_lt_top` from the ambient extended-order API.

Primitive data vs derived API:
- primitive data: a function `f : E → WithTopBot α` and an inhabited finite layer `α`;
- derived API: the union-of-sublevel-set description of `dom(f)`.

Layer target: `source-facing`, stated directly on the canonical owner `dom(f)` with the redundant
properness binder removed.
-/

namespace Function

private theorem withTopBot_exists_coe_of_ne_top_ne_bot {z : WithTopBot α}
    (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥) :
    ∃ a : α, (a : WithTopBot α) = z := by
  cases hz : z using WithTop.recTopCoe with
  | top => exact False.elim (hz_top hz)
  | coe z' =>
      cases hz' : z' using WithBot.recBotCoe with
      | bot => exact False.elim (hz_bot (by simp [hz, hz']))
      | coe a => exact ⟨a, rfl⟩

-- Proof sketch: rewrite pointwise using `mem_effectiveDomain`. If `f x ≤ a` for some finite
-- `a`, then automatically `f x < ⊤`. Conversely, if `f x < ⊤`, then either `f x = ⊥`, in which
-- case `x` lies in every finite sublevel set, or `f x` is an actual finite value and
-- explicit outer/inner boundary decomposition supplies the needed finite level.
/-- Proposition 6.27.3: if the finite codomain layer `α` is inhabited, then the union of all
finite-height sublevel sets of a `WithTopBot α`-valued function is exactly the effective domain
`dom(f)`. Specializing to `α = ℝ` recovers the textbook statement for
`f : ℝ^n → (-∞, +∞]`; the textbook properness hypothesis is redundant for this set identity. -/
theorem iUnion_sublevel_eq_dom (f : E → WithTopBot α) :
    (⋃ a : α, {x : E | f x ≤ (a : WithTopBot α)}) = dom(f) := by
  ext x
  rw [mem_effectiveDomain]
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨a, hxa⟩
    exact lt_of_le_of_lt hxa (WithTop.coe_lt_top (a : WithBot α))
  · intro hx_top
    by_cases hx_bot : f x = ⊥
    · obtain ⟨a⟩ := ‹Nonempty α›
      exact ⟨a, by simp [hx_bot]⟩
    · rcases withTopBot_exists_coe_of_ne_top_ne_bot (ne_of_lt hx_top) hx_bot with ⟨a, ha⟩
      exact ⟨a, by simp [ha]⟩

end Function

end
