import Mathlib.Data.Rel
import Mathlib.Data.Set.Subsingleton
import Mathlib.Logic.Relator
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.0.1 introduces a multivalued mapping `ρ`, meaning a pointwise
  assignment `x ↦ ρ(x) ⊆ β`, and says that `ρ` is single-valued when each value set contains at
  most one point.
- `core/canonical`: mathlib's canonical owner for multivalued mappings is `SetRel α β`, i.e. a
  relation between `α` and `β`, together with its pointwise image operation `SetRel.image`.
- `bridge/view`: the source value set `ρ(x)` is the singleton-image `ρ[[x]] := ρ.image {x}`,
  with explicit relation-membership bridge `xStar ∈ ρ[[x]] ↔ x ~[ρ] xStar`, while the
  single-valuedness clause is the right-uniqueness predicate on the underlying relation.

Domain-style sampling used here:
- `SetRel` from `Mathlib/Data/Rel.lean`;
- `SetRel.image`;
- `SetRel.mem_image`;
- `Relator.RightUnique`;
- `Relator.LeftUnique`;
- `Relator.BiUnique`;
- `Set.Subsingleton`.

Primitive data vs derived API:
- primitive owner data: a relation `ρ : SetRel α β`;
- primitive owner predicates: `ρ.RightUnique`, `ρ.LeftUnique`, and `ρ.BiUnique`;
- derived/source-facing API: the equivalence between right-uniqueness of `ρ` and subsingleton
  singleton-image fibers.

Layer target: `core/canonical`, with the source-facing fiber characterization retained only as a
companion theorem.
-/

/- Definition 26.0.1: a multivalued mapping from `α` to `β` is the canonical relation type
`SetRel α β`, equivalently a set-valued assignment sending each `x : α` to a subset of `β`. -/
#check (SetRel α β)

/- Definition 26.0.1: single-valuedness of a multivalued mapping is the canonical relation
predicate `Relator.RightUnique`. -/
recall Relator.RightUnique
recall Relator.LeftUnique
recall Relator.BiUnique

-- Proof sketch: membership in `ρ[[x]]` is the same as relation membership
-- `x ~[ρ] xStar` by `SetRel.mem_image`, because the only point in `{x}` is `x` itself. The
-- right-uniqueness predicate for `ρ` is then exactly the statement that any two elements of the
-- singleton-image fiber over `x` coincide.
namespace SetRel

/-- Source-facing pointwise value-set notation for a multivalued mapping relation. -/
scoped notation:arg ρ "[[" x "]]" => SetRel.image ρ ({x} : Set _)

/-- Canonical owner on `SetRel` for single-valuedness of a multivalued mapping. -/
abbrev RightUnique (ρ : SetRel α β) : Prop :=
  Relator.RightUnique (· ~[ρ] ·)

/-- Canonical owner on `SetRel` for inverse single-valuedness (left-uniqueness). -/
abbrev LeftUnique (ρ : SetRel α β) : Prop :=
  Relator.LeftUnique (· ~[ρ] ·)

/-- Canonical owner on `SetRel` for one-to-one multivalued mappings. -/
abbrev BiUnique (ρ : SetRel α β) : Prop :=
  Relator.BiUnique (· ~[ρ] ·)

/-- Membership in the source-facing value set is exactly relation membership. -/
@[simp] theorem mem_image_singleton_iff (ρ : SetRel α β) {x : α} {xStar : β} :
    xStar ∈ ρ[[x]] ↔ x ~[ρ] xStar := by
  simp [Set.mem_singleton_iff]

/-- The singleton image of `x` under a relation is exactly its intrinsic relation fiber. -/
@[simp] theorem image_singleton_eq_fiber (ρ : SetRel α β) (x : α) :
    ρ[[x]] = {xStar : β | x ~[ρ] xStar} := by
  ext xStar
  exact mem_image_singleton_iff (ρ := ρ)

/-- Canonical intrinsic owner form: a relation is right-unique iff each relation fiber over `x`
is subsingleton. -/
@[simp] theorem rightUnique_iff_fiber_subsingleton (ρ : SetRel α β) :
    ρ.RightUnique ↔ ∀ x : α, ({xStar : β | x ~[ρ] xStar}).Subsingleton := by
  constructor
  · intro h x y hy z hz
    exact h hy hz
  · intro h x y z hxy hxz
    exact h x hxy hxz

/-- The source single-valuedness clause on a multivalued mapping is equivalent to every pointwise
value set containing at most one element. -/
@[simp] theorem rightUnique_iff_image_singleton_subsingleton (ρ : SetRel α β) :
    ρ.RightUnique ↔ ∀ x : α, (ρ[[x]]).Subsingleton := by
  simp [image_singleton_eq_fiber, rightUnique_iff_fiber_subsingleton]

end SetRel

end
