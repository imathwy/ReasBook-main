import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.6.1 (1): a ring map `R → S` is of finite type exactly in the canonical sense of
`RingHom.FiniteType`; equivalently, for an `R`-algebra `S`, this is the algebra-map notion
`Algebra.FiniteType R S`. -/
recall RingHom.FiniteType

/- Companion recall: for an `R`-algebra `S`, the finite-type condition on `algebraMap R S` is
equivalent to the owner typeclass `Algebra.FiniteType R S`. -/
recall RingHom.finiteType_algebraMap

/- Definition 10.6.1 (2): a ring map `R → S` is of finite presentation exactly in the canonical
sense of `RingHom.FinitePresentation`; equivalently, for an `R`-algebra `S`, this is the
algebra-map notion `Algebra.FinitePresentation R S`. -/
recall RingHom.FinitePresentation

/- Companion recall: for an `R`-algebra `S`, the finite-presentation condition on `algebraMap R S`
is equivalent to the owner typeclass `Algebra.FinitePresentation R S`. -/
recall RingHom.finitePresentation_algebraMap
