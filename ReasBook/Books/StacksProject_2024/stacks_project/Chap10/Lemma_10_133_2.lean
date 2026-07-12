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

/-- Lemma 10.133.2: the composition of differential operators of orders `k` and `k'` is a
differential operator of order `k + k'`. -/
-- Proof sketch: induct on `k + k'` and use that the commutator of `D'.comp D` with multiplication
-- by `g` splits into a sum of composites of lower-order scalar commutators.
theorem isDifferentialOperatorOfOrder_comp
    {k k' : ℕ} {D : L →ₗ[R] M} {D' : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hD' : D'.IsDifferentialOperatorOfOrder S k') :
    (D'.comp D).IsDifferentialOperatorOfOrder S (k + k') :=
  sorry

end LinearMap

end
