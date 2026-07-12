import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.7.1: a ring map `φ : R → S` is finite exactly in the canonical sense of
`RingHom.Finite`, namely when the target ring is finite as a module over the source ring. -/
recall RingHom.Finite

/- Companion recall: for an `R`-algebra `S`, finiteness of the canonical map `algebraMap R S`
is exactly the module-finiteness statement `Module.Finite R S`. -/
recall RingHom.finite_algebraMap
