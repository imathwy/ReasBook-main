import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: valuative commutative squares in algebraic geometry
- sampled owner declarations:
  `AlgebraicGeometry.ValuativeCommSq`,
  `CategoryTheory.CommSq.HasLift`,
  `CategoryTheory.CommSq.LiftStruct`
- `source-facing`: the solid valuative square and the existence of its dotted-arrow completion
- `core/canonical`: `AlgebraicGeometry.ValuativeCommSq`
- `bridge/view`: `CategoryTheory.CommSq.HasLift` and `CategoryTheory.CommSq.LiftStruct` for
  existence and chosen-lift views of the underlying square
- primitive data vs derived API: the primitive owner is the canonical valuative square attached to
  a morphism of schemes; existence of the dotted arrow and a chosen dotted arrow are derived
  square-level API.
-/

/- 32.15.2.1: the displayed diagram
`Spec(K) ⟶ X_α`
over
`Spec(A) ⟶ S_α`
with a dotted arrow `Spec(A) ⟶ X_α` has solid part formalized by the canonical owner
`AlgebraicGeometry.ValuativeCommSq` attached to `f : X_α ⟶ S_α`. The existence of the dotted arrow
is `HasLift` for the underlying commutative square, and a chosen dotted arrow is a `LiftStruct`. -/
recall AlgebraicGeometry.ValuativeCommSq

/- Companion check: existence of the dotted arrow `Spec(A) ⟶ X_α` is `HasLift`. -/
recall CategoryTheory.CommSq.HasLift

/- Companion check: a chosen dotted arrow `Spec(A) ⟶ X_α` is a `LiftStruct`. -/
recall CategoryTheory.CommSq.LiftStruct
