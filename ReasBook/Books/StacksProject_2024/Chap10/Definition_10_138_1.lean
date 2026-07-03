import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.138.1: an `R`-algebra `S` is formally smooth if every `R`-algebra map
`S → A ⧸ I` lifts across the quotient map `A → A ⧸ I` whenever `I` is a square-zero ideal. -/
recall FormallySmooth

/- The infinitesimal lifting formulation of formal smoothness is the square-zero lifting criterion
for maps into quotient algebras `A ⧸ I`. -/
recall FormallySmooth.iff_comp_surjective

end Algebra
