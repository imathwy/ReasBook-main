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

/-- Definition 10.133.1: in the relative algebra situation, an `R`-linear map `D : M → N` is a
differential operator of order `k` if, for every `g : S`, its scalar commutator
`m ↦ D (g • m) - g • D m` is a differential operator of order `k - 1`; order `0` means that `D`
commutes with the `S`-action, equivalently is `S`-linear when `S` is a semiring acting by
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
variable [SMulCommClass S R M] [SMulCommClass S R N] [SMulCommClass R S N]

/-- The `S`-submodule of `R`-linear differential operators `M → N` of order at most `k`. -/
def differential_operators_order_le_submodule
    (R : Type u) (S : Type v) (M : Type w)
    [Semiring R] [CommSemiring S]
    [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
    (k : ℕ) (N : Type w')
    [AddCommGroup N] [Module R N] [Module S N]
    [SMulCommClass S R N] [SMulCommClass R S N] :
    Submodule S (M →ₗ[R] N) where
  carrier := { D | D.IsDifferentialOperatorOfOrder S k }
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

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
