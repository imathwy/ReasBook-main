import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w'

namespace LinearMap

section Smul

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w'}
variable [Semiring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [DistribSMul S M] [DistribSMul S N]
variable [SMulCommClass S R M] [SMulCommClass S R N]

/- Domain-style sampling for Definition 10.133.1:
- primary domain: differential operators between modules with commuting scalar actions, organized
  around iterated scalar commutators;
- sampled project declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `differential_operators_order_le`,
  `principal_parts_linear_map_equiv_differential_operators`,
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the recursive predicate
  `LinearMap.IsDifferentialOperatorOfOrder`, whose native ambient layer is the commuting
  scalar-action calculus; bounded-order operator submodules and principal-parts representations
  are derived from it;
- primitive data: an `R`-linear map `D : M →ₗ[R] N` and the recursive scalar-commutator condition;
- derived API: the order-zero and successor characterizations, then the order-`k` operator
  submodule and subtype.

Source/core/bridge triage:
- `source-facing`: Definition 10.133.1, the recursive order condition itself;
- `core/canonical`: the same owner predicate on `LinearMap`;
- `bridge/view`: `differential_operators_order_le_submodule` and
  `differential_operators_order_le`, which package the predicate into the canonical operator
  submodule/subtype used downstream, without reintroducing the stronger commutative-algebra tower
  needed only by later applications. -/

/-- The scalar commutator of an `R`-linear map with multiplication by an element of `S`. -/
abbrev scalarCommutator
    (D : M →ₗ[R] N) (g : S) : M →ₗ[R] N :=
  D.comp (DistribSMul.toLinearMap R M g) - (DistribSMul.toLinearMap R N g).comp D

/-- Evaluating the scalar commutator gives the usual commutator formula. -/
-- Proof sketch: unfold `LinearMap.scalarCommutator` and evaluate the two compositions at `m`.
theorem scalarCommutator_apply
    (D : M →ₗ[R] N) (g : S) (m : M) :
    D.scalarCommutator g m = D (g • m) - g • D m :=
  rfl

end Smul

section DifferentialOperatorOfOrder

variable {R : Type u} {M : Type w} {N : Type w'}
variable [Semiring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- Helper for Chap10 Definition 10 133 1: in the relative algebra situation, an `R`-linear map
`D : M → N` is a differential operator of order `k` if, for every `g : S`, its scalar commutator
`m ↦ D (g • m) - g • D m` is a differential operator of order `k - 1`; order `0` means that
`D` commutes with the `S`-action, equivalently is `S`-linear when `S` is a semiring acting by
linear maps. -/
def IsDifferentialOperatorOfOrder
    (D : M →ₗ[R] N) (S : Type v)
    [DistribSMul S M] [DistribSMul S N] [SMulCommClass S R M] [SMulCommClass S R N] :
    ℕ → Prop
  | 0 => ∀ g : S, D.scalarCommutator g = 0
  | k + 1 => ∀ g : S, (D.scalarCommutator g).IsDifferentialOperatorOfOrder S k

end DifferentialOperatorOfOrder

section Smul

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w'}
variable [Semiring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [DistribSMul S M] [DistribSMul S N]
variable [SMulCommClass S R M] [SMulCommClass S R N]

/-- Order-zero differential operators are exactly the `R`-linear maps commuting with the
`S`-action. -/
-- Proof sketch: unfold the recursive definition at `0` and identify vanishing of each scalar
-- commutator with the pointwise `S`-linearity condition.
theorem isDifferentialOperatorOfOrder_zero_iff
    (D : M →ₗ[R] N) :
    D.IsDifferentialOperatorOfOrder S 0 ↔
      ∀ g : S, ∀ m : M, D (g • m) = g • D m := by
  constructor
  · intro h g m
    exact sub_eq_zero.mp <| by
      simpa [scalarCommutator_apply] using DFunLike.congr_fun (h g) m
  · intro h g
    ext m
    simpa using sub_eq_zero.mpr (h g m)

/-- A differential operator has order at most `k + 1` exactly when every scalar commutator has
order at most `k`. -/
-- Proof sketch: unfold the recursive clause for `IsDifferentialOperatorOfOrder` at `k + 1`.
theorem isDifferentialOperatorOfOrder_succ_iff
    (D : M →ₗ[R] N) (k : ℕ) :
    D.IsDifferentialOperatorOfOrder S (k + 1) ↔
      ∀ g : S, (D.scalarCommutator g).IsDifferentialOperatorOfOrder S k :=
  Iff.rfl

end Smul

end LinearMap

section DifferentialOperators

open LinearMap

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w'}
variable [Semiring R] [CommSemiring S]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [DistribSMul S M] [Module S N]
variable [SMulCommClass S R M] [SMulCommClass S R N]

namespace LinearMap

/-- Helper for Chap10 Definition 10 133 1: the zero map has every finite differential-operator
order. -/
private theorem isDifferentialOperatorOfOrder_zero
    (k : ℕ) :
    (0 : M →ₗ[R] N).IsDifferentialOperatorOfOrder S k := by
  -- The recursive definition reduces the successor step to the same fact for the zero
  -- commutator.
  induction k with
  | zero =>
      rw [isDifferentialOperatorOfOrder_zero_iff]
      intro g m
      simp
  | succ k ih =>
      rw [isDifferentialOperatorOfOrder_succ_iff]
      intro g
      simpa [scalarCommutator] using ih

/-- Helper for Chap10 Definition 10 133 1: scalar commutators are additive in the operator. -/
private theorem scalarCommutator_add
    (D E : M →ₗ[R] N) (g : S) :
    (D + E).scalarCommutator g = D.scalarCommutator g + E.scalarCommutator g := by
  -- Evaluate both sides and regroup the four additive terms.
  ext m
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Chap10 Definition 10 133 1: fixed-order differential operators are closed under
addition. -/
private theorem isDifferentialOperatorOfOrder_add
    {k : ℕ} {D E : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hE : E.IsDifferentialOperatorOfOrder S k) :
    (D + E).IsDifferentialOperatorOfOrder S k := by
  -- Induct on the order; the successor case transports additivity through scalar commutators.
  induction k generalizing D E with
  | zero =>
      rw [isDifferentialOperatorOfOrder_zero_iff] at hD hE ⊢
      intro g m
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
      rw [scalarCommutator_add]
      exact ih (hD g) (hE g)

variable [SMulCommClass R S N]

/-- Helper for Chap10 Definition 10 133 1: scalar commutators commute with scalar
multiplication of the operator. -/
private theorem scalarCommutator_smul
    (c g : S) (D : M →ₗ[R] N) :
    (c • D).scalarCommutator g = c • D.scalarCommutator g := by
  -- Evaluate at an element; the only non-linear-looking step is commuting the two `S`-scalars.
  ext m
  simp only [LinearMap.smul_apply]
  rw [scalarCommutator_apply, scalarCommutator_apply]
  simp only [LinearMap.smul_apply]
  rw [smul_sub, smul_comm g c (D m)]

/-- Helper for Chap10 Definition 10 133 1: fixed-order differential operators are closed under
scalar multiplication. -/
private theorem isDifferentialOperatorOfOrder_smul
    {k : ℕ} {D : M →ₗ[R] N}
    (c : S) (hD : D.IsDifferentialOperatorOfOrder S k) :
    (c • D).IsDifferentialOperatorOfOrder S k := by
  -- Induct on the order; the successor case uses compatibility of commutators with scalar
  -- multiplication.
  induction k generalizing D with
  | zero =>
      rw [isDifferentialOperatorOfOrder_zero_iff] at hD ⊢
      intro g m
      calc
        (c • D) (g • m) = c • D (g • m) := by
          rfl
        _ = c • (g • D m) := by
          rw [hD g m]
        _ = g • (c • D m) := by
          rw [smul_comm c g (D m)]
        _ = g • (c • D) m := by
          rfl
  | succ k ih =>
      rw [isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro g
      rw [scalarCommutator_smul]
      exact ih (hD g)

end LinearMap

/-- Chap10 Definition 10 133 1: the `S`-submodule of `R`-linear differential operators `M → N`
of order at most `k`. -/
@[stacks 09CI]
def differential_operators_order_le_submodule
    (R : Type u) (S : Type v) (M : Type w)
    [Semiring R] [CommSemiring S]
    [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
    (k : ℕ) (N : Type w')
    [AddCommGroup N] [Module R N] [Module S N]
    [SMulCommClass S R N] [SMulCommClass R S N] :
    Submodule S (M →ₗ[R] N) where
  -- The carrier records exactly the recursive order bound from Definition 10.133.1.
  carrier := { D | D.IsDifferentialOperatorOfOrder S k }
  -- The submodule laws are the closure properties of fixed-order differential operators.
  zero_mem' := LinearMap.isDifferentialOperatorOfOrder_zero k
  add_mem' := fun hD hE =>
    LinearMap.isDifferentialOperatorOfOrder_add hD hE
  smul_mem' := fun c _ hD =>
    LinearMap.isDifferentialOperatorOfOrder_smul c hD

/-- The type of order-`k` differential operators `M → N`. -/
abbrev differential_operators_order_le
    (R : Type u) (S : Type v) (M : Type w)
    [Semiring R] [CommSemiring S]
    [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
    (k : ℕ) (N : Type w')
    [AddCommGroup N] [Module R N] [Module S N]
    [SMulCommClass S R N] [SMulCommClass R S N] :=
  ↥(differential_operators_order_le_submodule R S M k N)

end DifferentialOperators
