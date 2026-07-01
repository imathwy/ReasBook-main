import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section module_flat

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Definition 10.39.1 (1): an `R`-module `M` is flat when tensoring with `M` preserves exact
sequences; the canonical mathlib predicate for this notion is `Module.Flat R M`. -/
recall Module.Flat

/- Companion recall: the textbook exact-sequence formulation of flatness is the canonical
equivalence `Module.Flat.iff_lTensor_preserves_shortComplex_exact`. -/
recall Module.Flat.iff_lTensor_preserves_shortComplex_exact

/- Definition 10.39.1 (2): an `R`-module `M` is faithfully flat when tensoring with `M`
preserves and reflects exact sequences; the canonical mathlib predicate for this notion is
`Module.FaithfullyFlat R M`. -/
recall Module.FaithfullyFlat

/- Companion recall: the textbook exact-sequence characterization of faithful flatness is the
canonical equivalence `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`. -/
recall Module.FaithfullyFlat.iff_exact_iff_lTensor_exact

end module_flat

section ring_hom_flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S)

/- Definition 10.39.1 (3): a ring map `f : R →+* S` is flat when `S` is flat as an `R`-module;
the canonical mathlib predicate for this notion is `RingHom.Flat f`. -/
recall RingHom.Flat

/- Definition 10.39.1 (4): a ring map `f : R →+* S` is faithfully flat when `S` is faithfully flat
as an `R`-module; the canonical mathlib predicate for this notion is `RingHom.FaithfullyFlat f`. -/
recall RingHom.FaithfullyFlat

end ring_hom_flat

section algebra_flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Companion recall for Definition 10.39.1 (3): for the canonical algebra map, the textbook
wording "flat as an `R`-module" is exactly `RingHom.flat_algebraMap_iff`. -/
recall RingHom.flat_algebraMap_iff

/- Companion recall for Definition 10.39.1 (4): for the canonical algebra map, the textbook
wording "faithfully flat as an `R`-module" is exactly
`RingHom.faithfullyFlat_algebraMap_iff`. -/
recall RingHom.faithfullyFlat_algebraMap_iff

end algebra_flat
