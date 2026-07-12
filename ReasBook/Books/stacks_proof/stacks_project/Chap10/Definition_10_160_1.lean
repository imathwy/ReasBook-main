import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R]

-- Domain-style sampling:
-- * primary domain: local rings and adic completion.
-- * layer: `source-facing`; this item introduces the chapter owner for complete local rings.
-- * sampled owner declarations:
--   `IsAdicComplete`,
--   `AdicCompletion.of_bijective_iff`,
--   `AdicCompletion.ofAlgEquiv`,
--   `isLocalRing_of_isAdicComplete_maximal`.
-- * owner abstraction: `IsAdicComplete (maximalIdeal R) R`.
-- * primitive data: locality and maximal-ideal adic completeness.
-- * derived API: completion-map bijectivity and the induced completion equivalence.

/-- Definition 10.160.1: a complete local ring is a local ring that is complete for the adic
topology defined by its maximal ideal. -/
@[stacks 0324]
class IsCompleteLocalRing : Prop extends IsLocalRing R, IsAdicComplete (maximalIdeal R) R

variable {R}

/-- Any local ring that is adically complete with respect to its maximal ideal is a complete local
ring. -/
instance [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] : IsCompleteLocalRing R := {}

end
