import Mathlib.RingTheory.Idempotents

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]

namespace RingHom

/-- The canonical map on idempotents induced by a ring homomorphism. -/
def idempotentMap {S : Type v} [CommRing S] (f : R →+* S) :
    {e : R // IsIdempotentElem e} → {e : S // IsIdempotentElem e} :=
  fun e ↦ ⟨f e.1, e.2.map f⟩

end RingHom

end
