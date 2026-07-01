import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.131.2: the module of Kähler differentials of the `R`-algebra `S`, together with
its universal derivation `d`, is the canonical pair consisting of `Ω[S⁄R]` and
`KaehlerDifferential.D R S`. -/
recall KaehlerDifferential.D (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
  Derivation R S Ω[S⁄R]
