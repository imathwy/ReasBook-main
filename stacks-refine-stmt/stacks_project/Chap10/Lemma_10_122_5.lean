import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Lemma 10.122.5: for a finite type ring map `R → S`, quasi-finiteness is exactly the canonical
condition that every fiber algebra `κ(𝔭) ⊗[R] S` is finite over `κ(𝔭)`. This is the canonical
theorem `Algebra.quasiFinite_iff`. -/
recall Algebra.quasiFinite_iff

end
