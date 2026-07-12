import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uS uL uM uN

/-
Domain triage:
* primary domain: differential operators between modules with a commuting scalar action, organized
  by the recursive scalar-commutator owner;
* sampled owner API:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LinearMap.isDifferentialOperatorOfOrder_zero_iff`,
  `LinearMap.isDifferentialOperatorOfOrder_succ_iff`,
  `differential_operators_postcompose_mem`;
* best owner abstraction: the predicate `LinearMap.IsDifferentialOperatorOfOrder`;
* primitive data: an `R`-linear map together with the recursive scalar-commutator condition;
* derived API: closure properties such as this composition lemma, plus the bounded-order submodule.

Source/core/bridge triage:
* source-facing: this lemma is a source-facing closure property for differential operators;
* core/canonical: it is stated directly for the owner predicate
  `LinearMap.IsDifferentialOperatorOfOrder`;
* bridge/view: the order-bounded differential-operator submodule is a downstream packaging layer.

Refinement note:
This lemma belongs at the same primitive ambient level as the owner predicate itself. Its
mathematics uses only the scalar-commutator calculus, so the public statement should not be pinned
to the stronger commutative-algebra tower used by later applications.
-/

section

variable {R : Type uR} {S : Type uS} {L : Type uL} {M : Type uM} {N : Type uN}
variable [Semiring R]
variable [AddCommGroup L] [Module R L] [DistribSMul S L] [SMulCommClass S R L]
variable [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
variable [AddCommGroup N] [Module R N] [DistribSMul S N] [SMulCommClass S R N]

namespace LinearMap

/-- Helper for Lemma 10.133.2: the scalar commutator is additive in the operator. -/
-- Proof sketch: evaluate both sides on an element and regroup the four resulting terms.
theorem scalarCommutator_add
    (D E : M →ₗ[R] N) (g : S) :
    (D + E).scalarCommutator g = D.scalarCommutator g + E.scalarCommutator g := by
  -- Evaluate the commutators pointwise and collect matching terms.
  ext m
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 10.133.2: the scalar commutator of a composite splits into two lower-order
pieces. -/
-- Proof sketch: expand the commutator formula and insert the middle term `D' (g • D m)`.
theorem scalarCommutator_comp
    (D : L →ₗ[R] M) (D' : M →ₗ[R] N) (g : S) :
    (D'.comp D).scalarCommutator g =
      D'.comp (D.scalarCommutator g) + (D'.scalarCommutator g).comp D := by
  -- Evaluate on an element and use linearity of `D'` to split the first summand.
  ext m
  simp [sub_eq_add_neg, add_assoc, add_left_comm]

/-- Helper for Lemma 10.133.2: differential operators of a fixed order are closed under
addition. -/
-- Proof sketch: induct on the order and combine the recursive commutator descriptions termwise.
theorem isDifferentialOperatorOfOrder_add
    {k : ℕ} {D E : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hE : E.IsDifferentialOperatorOfOrder S k) :
    (D + E).IsDifferentialOperatorOfOrder S k := by
  induction k generalizing D E with
  | zero =>
      rw [isDifferentialOperatorOfOrder_zero_iff] at hD hE ⊢
      intro g m
      -- Order-zero operators commute with scalar multiplication pointwise, so their sum does too.
      calc
        (D + E) (g • m) = D (g • m) + E (g • m) := by
          simp
        _ = g • D m + g • E m := by
          rw [hD g m, hE g m]
        _ = g • (D m + E m) := by
          simp [smul_add]
        _ = g • (D + E) m := by
          rfl
  | succ k ih =>
      rw [isDifferentialOperatorOfOrder_succ_iff] at hD hE ⊢
      intro g
      -- The recursive step reduces to additivity of the scalar commutator.
      rw [scalarCommutator_add]
      exact ih (hD g) (hE g)

/-- Lemma 10.133.2: the composition of differential operators of orders `k` and `k'` is a
differential operator of order `k + k'`. -/
-- Proof sketch: induct on `k + k'` and use that the commutator of `D'.comp D` with multiplication
-- by `g` splits into a sum of composites of lower-order scalar commutators.
@[stacks 09CJ]
theorem isDifferentialOperatorOfOrder_comp
    {k k' : ℕ} {D : L →ₗ[R] M} {D' : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hD' : D'.IsDifferentialOperatorOfOrder S k') :
    (D'.comp D).IsDifferentialOperatorOfOrder S (k + k') :=
  -- Follow the source proof by strong induction on the total order `k + k'`.
  Nat.strong_induction_on (p := fun n =>
      ∀ {k k' : ℕ} {D : L →ₗ[R] M} {D' : M →ₗ[R] N},
        k + k' = n →
          D.IsDifferentialOperatorOfOrder S k →
          D'.IsDifferentialOperatorOfOrder S k' →
          (D'.comp D).IsDifferentialOperatorOfOrder S n) (k + k') (by
      intro n ih k k' D D' hsum hD hD'
      subst n
      cases k with
      | zero =>
          cases k' with
          | zero =>
              rw [isDifferentialOperatorOfOrder_zero_iff] at hD hD' ⊢
              intro g m
              -- In the base case, both maps commute with scalars, hence so does the composite.
              calc
                D' (D (g • m)) = D' (g • D m) := by
                  rw [hD g m]
                _ = g • D' (D m) := by
                  rw [hD' g (D m)]
          | succ k' =>
              have hD_zero : D.IsDifferentialOperatorOfOrder S 0 := hD
              rw [isDifferentialOperatorOfOrder_zero_iff] at hD
              rw [isDifferentialOperatorOfOrder_succ_iff] at hD'
              simpa using (isDifferentialOperatorOfOrder_succ_iff (D'.comp D) k').2 (by
                intro g
                -- When `D` has order zero, its scalar commutator vanishes and only one lower-order
                -- composite remains.
                have hcomm : D.scalarCommutator g = 0 := by
                  ext m
                  simpa [scalarCommutator_apply, hD g m]
                have hcomp :
                    ((D'.scalarCommutator g).comp D).IsDifferentialOperatorOfOrder S k' := by
                  have hlt : k' < 0 + (k' + 1) := by
                    simpa using Nat.lt_succ_self k'
                  exact ih k' hlt (by simp) hD_zero (hD' g)
                simpa [scalarCommutator_comp, hcomm] using hcomp)
      | succ k =>
          cases k' with
          | zero =>
              have hD'_zero : D'.IsDifferentialOperatorOfOrder S 0 := hD'
              rw [isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
              rw [isDifferentialOperatorOfOrder_zero_iff] at hD'
              intro g
              -- Symmetrically, if `D'` has order zero then its scalar commutator vanishes.
              have hcomm : D'.scalarCommutator g = 0 := by
                ext m
                simpa [scalarCommutator_apply, hD' g m]
              have hcomp :
                  (D'.comp (D.scalarCommutator g)).IsDifferentialOperatorOfOrder S k := by
                exact ih k (Nat.lt_succ_self k) rfl (hD g) hD'_zero
              simpa [scalarCommutator_comp, hcomm] using hcomp
          | succ k' =>
              have hD_succ : D.IsDifferentialOperatorOfOrder S (Nat.succ k) := hD
              have hD'_succ : D'.IsDifferentialOperatorOfOrder S (Nat.succ k') := hD'
              rw [isDifferentialOperatorOfOrder_succ_iff] at hD hD'
              simpa [Nat.add_assoc] using
                (isDifferentialOperatorOfOrder_succ_iff (D'.comp D) (Nat.succ k + k')).2 (by
                  intro g
                  -- Route correction: keep the source-proof decomposition of the composite
                  -- commutator, then prove each summand has smaller total order.
                  have hleft' :
                      (D'.comp (D.scalarCommutator g)).IsDifferentialOperatorOfOrder S
                        (k + Nat.succ k') := by
                    have hlt : k + Nat.succ k' < Nat.succ k + Nat.succ k' := by
                      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        Nat.lt_succ_self (k + Nat.succ k')
                    exact ih (k + Nat.succ k') hlt rfl (hD g) hD'_succ
                  have hleft :
                      (D'.comp (D.scalarCommutator g)).IsDifferentialOperatorOfOrder S
                        (Nat.succ k + k') := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hleft'
                  have hright :
                      ((D'.scalarCommutator g).comp D).IsDifferentialOperatorOfOrder S
                        (Nat.succ k + k') := by
                    have hlt : Nat.succ k + k' < Nat.succ k + Nat.succ k' := by
                      simpa using Nat.lt_succ_self (Nat.succ k + k')
                    exact ih (Nat.succ k + k') hlt rfl hD_succ (hD' g)
                  have hsum :
                      IsDifferentialOperatorOfOrder
                        ((D'.comp (D.scalarCommutator g)) + ((D'.scalarCommutator g).comp D))
                        S (Nat.succ k + k') := by
                    exact isDifferentialOperatorOfOrder_add hleft hright
                  simpa [scalarCommutator_comp] using hsum)) rfl hD hD'

end LinearMap

end
