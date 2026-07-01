import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.144.1: the canonical notion that the ring map `R → S` is standard étale is
`IsStandardEtale R S`. The textbook's concrete presentation is the bridge object
`StandardEtalePresentation R S`, which extends a `StandardEtalePair R` by choosing the image of
`X` in `S` and an `R`-algebra identification of `S` with the associated standard étale algebra. -/
recall IsStandardEtale

/- A `StandardEtalePresentation R S` is the source-facing bridge from the textbook polynomial data
to the intrinsic owner predicate `IsStandardEtale R S`. -/
recall StandardEtalePresentation

end Algebra
