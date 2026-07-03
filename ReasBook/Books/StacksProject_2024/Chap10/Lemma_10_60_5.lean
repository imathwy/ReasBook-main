import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.60.5: a commutative ring is Artinian if and only if it is Noetherian and has Krull
dimension at most `0`. This is the canonical mathlib theorem
`isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`, which packages both textbook directions:
"Noetherian of dimension `0` implies Artinian" and "Artinian implies Noetherian of dimension
zero". -/
recall isArtinianRing_iff_isNoetherianRing_krullDimLE_zero

end
