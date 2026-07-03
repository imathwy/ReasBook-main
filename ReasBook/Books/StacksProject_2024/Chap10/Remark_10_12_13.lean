import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {R : Type*} [CommRing R]
variable {N : Type*} [AddCommGroup N] [Module R N]

/- Remark 10.12.13: an `R`-module `N` for which tensoring on the right preserves exact
sequences is called a flat `R`-module; the canonical predicate for this notion is
`Module.Flat R N`. -/
recall Module.Flat

/- Companion recall: over a commutative ring, flatness is equivalent to exactness of tensoring on
the right by `N`; this is exactly the canonical theorem `Module.Flat.iff_rTensor_exact`. -/
recall Module.Flat.iff_rTensor_exact

end
