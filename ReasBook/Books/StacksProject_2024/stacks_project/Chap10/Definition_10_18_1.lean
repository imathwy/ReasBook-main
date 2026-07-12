import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.18.1: a local ring is the canonical mathlib predicate `IsLocalRing`. -/
recall IsLocalRing

/- Companion recall: for a local ring `R`, the unique maximal ideal is the canonical ideal
`IsLocalRing.maximalIdeal R`. -/
recall IsLocalRing.maximalIdeal

/- Companion recall: for a local ring `R`, the residue field is the quotient
`IsLocalRing.ResidueField R`. -/
recall IsLocalRing.ResidueField

/- Companion recall: for a local ring `R`, the canonical residue map is
`IsLocalRing.residue R : R →+* IsLocalRing.ResidueField R`. -/
recall IsLocalRing.residue

/- Companion recall: the canonical mathlib notion of a local ring homomorphism is `IsLocalHom`. -/
recall IsLocalHom
