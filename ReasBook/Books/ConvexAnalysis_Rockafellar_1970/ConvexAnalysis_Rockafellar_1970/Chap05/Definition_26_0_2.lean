import Mathlib.Data.Rel
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.0.2 defines the inverse `ρ⁻¹` of a multivalued mapping `ρ` by
  the textbook membership condition `x ∈ ρ⁻¹(x*) ↔ x* ∈ ρ(x)`.
- `core/canonical`: mathlib's owner abstraction for multivalued mappings is `SetRel α β`, and the
  inverse mapping is the canonical relation inverse `SetRel.inv`.
- `bridge/view`: the source set-builder description is already the canonical theorem
  `SetRel.mem_inv`, on the chapter notation surface `ρ⁻¹`.

Domain-style sampling used here:
- `SetRel` from `Mathlib/Data/Rel.lean`;
- `SetRel.inv`;
- `SetRel.mem_inv`;
- the domain/codomain swap lemmas `SetRel.dom_inv` and `SetRel.cod_inv`, which confirm that this
  owner has the expected multivalued-mapping behavior.

Primitive data vs derived API:
- primitive input: a multivalued mapping `ρ`, represented canonically as a relation `SetRel α β`;
- primitive owner: `SetRel.inv`, written on the chapter surface as `ρ⁻¹`;
- derived/source-facing API: the textbook characterization
  `xStar ~[ρ⁻¹] x ↔ x ~[ρ] xStar`, already owned by `SetRel.mem_inv`.

Layer target: `bridge/view`.

This file keeps only direct canonical recall/use and chapter notation.
-/

namespace SetRel
scoped postfix:max "⁻¹" => SetRel.inv
end SetRel

variable (ρ : SetRel α β)

/- Definition 26.0.2: the inverse multivalued mapping is the canonical inverse relation
`SetRel.inv`, with the textbook Chapter 26 surface notation `ρ⁻¹`. -/
#check ρ⁻¹

/- Definition 26.0.2, source-facing membership formula on the canonical owner:
membership in the inverse multivalued mapping is equivalent to reversed membership in the
original mapping. This is exactly `SetRel.mem_inv`. -/
recall SetRel.mem_inv

namespace SetRel

/-- Source-facing value-set form of Definition 26.0.2: membership in the inverse value set is
equivalent to reversed membership in the original value set. -/
@[simp] theorem mem_image_singleton_inv_iff (ρ : SetRel α β) {x : α} {xStar : β} :
    x ∈ (ρ⁻¹)[[xStar]] ↔ xStar ∈ ρ[[x]] := by
  simp

end SetRel

/- Definition 26.0.2 companion owner facts: inverse swaps domain and codomain. -/
recall SetRel.dom_inv
recall SetRel.cod_inv

end
