import Mathlib.RepresentationTheory.Maschke

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra

universe u v

section

variable {k : Type u} {G : Type v}
variable [Field k] [CharZero k] [Group G] [Finite G]

local instance : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩

/- Proposition 6-6.1-1: if `k` is a field of characteristic zero and `G` is a finite group,
then the group algebra `k[G]` is semisimple. Layer triage: this item is a `bridge/view`; the
core owner abstraction is Maschke's canonical instance `IsSemisimpleRing k[G]`; the primitive
data for that owner is `[NeZero (Nat.card G : k)]`, derived here from `[CharZero k]`. -/
#check (inferInstance : IsSemisimpleRing k[G])

end
