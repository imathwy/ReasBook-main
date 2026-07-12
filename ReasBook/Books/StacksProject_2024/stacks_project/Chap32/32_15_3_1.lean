import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- 32.15.3.1: the solid part of the displayed diagram
`Spec K ⟶ X' ⟶ \mathbf{P}^n_S`
over `Spec A ⟶ \mathbf{P}^n_S` is the canonical owner
`AlgebraicGeometry.ValuativeCommSq`. The dotted arrow `Spec A ⟶ X'`, when it exists, is a lift of
the underlying commutative square. -/
recall AlgebraicGeometry.ValuativeCommSq

/- Companion recall: existence of the dotted arrow `Spec A ⟶ X'` is `HasLift` for the underlying
commutative square. -/
recall CategoryTheory.CommSq.HasLift

/- Companion recall: a chosen dotted arrow `Spec A ⟶ X'` is packaged as a `LiftStruct` for the
underlying commutative square. -/
recall CategoryTheory.CommSq.LiftStruct
