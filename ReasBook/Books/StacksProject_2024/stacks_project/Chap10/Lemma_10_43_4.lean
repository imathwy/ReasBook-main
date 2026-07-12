import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- A pair of finitely generated `k`-subalgebras of `R` and `S`. -/
structure FGSubalgebraPair where
  left : Subalgebra k R
  right : Subalgebra k S
  left_fg : left.FG
  right_fg : right.FG

/-- A witness that a ring contains two nonzero elements whose product is zero. -/
structure NonzeroZeroDivisorWitness (A : Type*) [Mul A] [Zero A] where
  left : A
  right : A
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  mul_eq_zero : left * right = 0

/-- A witness that a ring contains an idempotent different from `0` and `1`. -/
structure NontrivialIdempotentWitness (A : Type*) [Mul A] [One A] [Zero A] where
  elem : A
  isIdempotent : IsIdempotentElem elem
  ne_zero : elem ≠ 0
  ne_one : elem ≠ 1

/-
Domain triage:
- `source-facing`: the three public statements detect nonreducedness, zerodivisors, and nontrivial
  idempotents in `R ⊗[k] S` on finitely generated `k`-subalgebras on both sides.
- `core/canonical`: one-sided finite descent in tensor products is already owned by
  `exists_fg_and_mem_baseChange`, and reducedness over a field is detected from finitely generated
  subalgebras by `IsReduced.tensorProduct_of_flat_of_forall_fg`.
- `bridge/view`: for parts `(2)` and `(3)`, the finite-family bookkeeping is derived by iterating
  `exists_fg_and_mem_baseChange` and commuting tensor factors, rather than by introducing a
  parallel local helper abstraction.

Primitive data are only the two `k`-algebras and the witness tensor elements. No extra wrapper
carrying finite-stage data is mathematically primary here.
-/

-- Proof sketch: use the contrapositive of
-- `IsReduced.tensorProduct_of_flat_of_forall_fg` twice, first in the `S`-variable and then in the
-- `R`-variable. Over a field, all modules are flat, so the nonreduced nilpotent element already
-- lives in the tensor product of finitely generated subalgebras on both sides.
/-- Lemma 10.43.4 (1): if `R ⊗[k] S` is not reduced, then there exist finitely generated
`k`-subalgebras `R' ⊆ R` and `S' ⊆ S` such that `R' ⊗[k] S'` is not reduced. -/
theorem exists_fg_subalgebras_not_isReduced_tensorProduct
    (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      ¬ IsReduced (T.left ⊗[k] T.right) := sorry

-- Proof sketch: apply `exists_fg_and_mem_baseChange` to `z`, then after commuting tensor factors
-- apply it again to the resulting coefficients needed for `w`, obtaining a common finitely
-- generated stage on both sides. The equalities `z ≠ 0`, `w ≠ 0`, and `z * w = 0` then descend
-- along the induced map from the smaller tensor product.
/-- Lemma 10.43.4 (2): if `R ⊗[k] S` contains a nonzero zerodivisor, then it already appears in
the tensor product of finitely generated `k`-subalgebras on both sides. -/
theorem exists_fg_subalgebras_tensorProduct_has_nonzero_zerodivisor
    (h : Nonempty (NonzeroZeroDivisorWitness (R ⊗[k] S))) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      Nonempty (NonzeroZeroDivisorWitness (T.left ⊗[k] T.right)) := sorry

-- Proof sketch: iterate `exists_fg_and_mem_baseChange` to place the idempotent `e` in a common
-- finitely generated tensor stage, then transport the equations `e * e = e`, `e ≠ 0`, and
-- `e ≠ 1` along the comparison map.
/-- Lemma 10.43.4 (3): if `R ⊗[k] S` contains a nontrivial idempotent, then it already appears in
finitely generated `k`-subalgebras on both sides. -/
theorem exists_fg_subalgebras_tensorProduct_has_nontrivial_idempotent
    (h : Nonempty (NontrivialIdempotentWitness (R ⊗[k] S))) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      Nonempty (NontrivialIdempotentWitness (T.left ⊗[k] T.right)) := sorry

end
