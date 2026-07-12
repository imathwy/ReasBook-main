import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_43_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w

/-
Domain triage:
- `source-facing`: clause `(1)` promotes reduced `k`-algebras over a perfect field to the owner
  class `Algebra.IsGeometricallyReduced`.
- `core/canonical`: the owner abstraction is `IsGeometricallyReduced k R`, and the tensor-product
  statement in clause `(2)` is already owned by `isReduced_tensorProduct_of_geometricallyReduced`.
- `bridge/view`: the perfect-field hypothesis supplies the owner instance in clause `(1)`; clause
  `(2)` is then recovered by specialization of the owner theorem, so no parallel wrapper API is
  needed.
-/

section

variable {k : Type u} [Field k]

/-- Lemma 10.45.6 (1): over a perfect field, every reduced commutative algebra is geometrically
reduced. This is the owner-level `IsGeometricallyReduced` instance. -/
-- Proof sketch: by the canonical definition of geometric reducedness, it suffices to show that
-- `AlgebraicClosure k ⊗[k] R` is reduced. Over a perfect field, `AlgebraicClosure k / k` is
-- separable, so Lemma `10.43.6` applies to the reduced algebra `R`.
instance perfectField_isGeometricallyReduced
    {R : Type v} [PerfectField k] [CommRing R] [Algebra k R] [IsReduced R] :
    IsGeometricallyReduced k R :=
  ⟨Lemma_10_43_6⟩

attribute [instance low] perfectField_isGeometricallyReduced

/- Clause (2): if `R` and `S` are reduced `k`-algebras over a perfect field `k`, then
their tensor product `R ⊗[k] S` is reduced. With clause `(1)` installed as the owner-level
instance above, this is exactly the canonical theorem
`isReduced_tensorProduct_of_geometricallyReduced`. -/
recall isReduced_tensorProduct_of_geometricallyReduced

end
