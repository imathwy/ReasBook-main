import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 10.35.1 is recalled canonically by `IsJacobsonRing R`: a commutative ring is Jacobson
if every radical ideal is the intersection of the maximal ideals containing it, equivalently if
every radical ideal equals its Jacobson radical.
-/
recall IsJacobsonRing

/- Companion recall: the defining radical-ideal formulation is the canonical equivalence
`isJacobsonRing_iff`. -/
recall isJacobsonRing_iff
