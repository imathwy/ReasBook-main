import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Module

/-
Domain-style sampling:
- primary domain: module duality, reflexivity, and torsion for modules over commutative domains;
- sampled owner API:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.evalEquiv`,
  `Module.IsReflexive.to_isTorsionFree`;
- best owner abstraction: the canonical owner object is the reflexivity class `Module.IsReflexive`
  together with the canonical evaluation map `Module.Dual.eval`; torsion and torsion-freeness are
  already owned by `Module.IsTorsion` and `Module.IsTorsionFree`, both available through the
  owner import `Mathlib.LinearAlgebra.Dual.Defs`;
- source/core/bridge triage:
  `source-facing`: the torsion statements about the kernel and cokernel of the evaluation map and
  the finite-module injectivity criterion;
  `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `Module.IsTorsionFree`,
  `Module.IsTorsion`;
  `bridge/view`: clause `(1)` is exact-interface reuse of the canonical owner instance
  `Module.IsReflexive.to_isTorsionFree`.

Primitive data are the ambient semiring/module for clause `(1)`, and the finite module plus the
canonical map `Module.Dual.eval` for clauses `(2)` through `(4)`. No extra wrapper around the
double dual or its evaluation map is mathematically needed, and clause `(1)` should remain a direct
recall of the upstream owner instance rather than a local theorem shell.
-/

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 15.23.2 (1): a reflexive module is torsion free. The source states this over a domain,
but the canonical owner instance already works over a commutative semiring. -/
recall IsReflexive.to_isTorsionFree

end

section Finite

open Module.Dual

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

-- Proof sketch: choose generators of `M`, pass to the fraction field, extract a basis of
-- `M ⊗[R] K`, and clear denominators to produce maps `R^r → M → R^r` whose two composites are
-- multiplication by a single nonzero scalar `c`. Comparing the induced diagram with the double
-- dual evaluation map `eval R M` shows that `c` annihilates the kernel.
/-- Lemma 15.23.2 (2): if `M` is finite, then the kernel of the canonical map from `M` to its
double dual is a torsion module. -/
theorem eval_ker_isTorsion :
    IsTorsion R (eval R M).ker := sorry

-- Proof sketch: use the same denominator-clearing maps `R^r → M → R^r` as in the kernel case.
-- The induced commutative diagram with `eval R M` shows that the same
-- nonzero scalar `c` annihilates the quotient of the double dual by the image of `M`.
/-- Lemma 15.23.2 (3): if `M` is finite, then the cokernel of the canonical map from `M` to its
double dual is a torsion module. -/
theorem eval_cokernel_isTorsion :
    IsTorsion R (Dual R (Dual R M) ⧸ (eval R M).range) := sorry

-- Proof sketch: if `M` is torsion free, the denominator-clearing map to a finite free module
-- constructed above is injective, forcing the evaluation map to be injective. Conversely, if the
-- evaluation map is injective, then `M` embeds into its torsion-free double dual.
/-- Lemma 15.23.2 (4): for a finite module over a domain, the canonical map to the double dual is
injective exactly when the module is torsion free. -/
theorem eval_injective_iff_isTorsionFree :
    Function.Injective (eval R M) ↔ IsTorsionFree R M := sorry

end Finite
