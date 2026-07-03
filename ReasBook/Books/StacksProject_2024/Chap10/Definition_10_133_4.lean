import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_133_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable (k : ℕ)

/- Domain triage:
* primary domain: principal parts and differential operators for a commutative `R`-algebra `S`;
* sampled owner API:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `principal_parts_module`,
  `principal_parts_universal_differential`,
  `principal_parts_linear_map_equiv_differential_operators`;
* source-facing owner: `principal_parts_module R S M k`;
* core/canonical operator owner: `differential_operators_order_le R S M k N`;
* bridge/view: maps out of `principal_parts_module` classify order-`k` differential operators.

Definition 10.133.4 is recall-only: the source names the already introduced module of principal
parts, so the correct refinement is direct reuse of `principal_parts_module` rather than a second
alias or wrapper. The notation `P^{k}_{S⁄R}(M)` is already the derived notation attached to that
owner in Lemma `10.133.3`.
-/
/-
Definition 10.133.4: the module `P^k_{S/R}(M)` constructed in Lemma `10.133.3` is the module of
principal parts of order `k` of `M`.
-/
recall principal_parts_module
