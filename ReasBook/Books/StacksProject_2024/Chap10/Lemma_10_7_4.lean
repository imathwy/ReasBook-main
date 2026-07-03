import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.7.4 (1): a finite ring map `φ : R → S` is of finite type. This is exactly the
canonical mathlib theorem `RingHom.Finite.to_finiteType`. -/
recall RingHom.Finite.to_finiteType

/- Lemma 10.7.4 (2), owner abstraction: if an `R`-algebra `S` is finitely presented as an
`R`-module, then `S` is finitely presented as an `R`-algebra. -/
recall Algebra.FinitePresentation.of_finitePresentation

/- Lemma 10.7.4 (2), `bridge/view` layer: the ring-map formulation is obtained from the owner
abstraction `Algebra.FinitePresentation` via the canonical equivalence for `algebraMap`. -/
recall RingHom.finitePresentation_algebraMap
