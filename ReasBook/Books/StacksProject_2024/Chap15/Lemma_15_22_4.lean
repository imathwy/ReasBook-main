import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct
open Module

/-
Domain-style sampling:
- primary domain: commutative algebra of torsion-free modules under flat base change;
- sampled owner API:
  `Module.IsTorsionFree`,
  `TensorProduct`,
  `Module.Flat`,
  `LinearEquiv.moduleIsTorsionFree`;
- best owner abstraction: the canonical owner is the tensor-product base change `S ⊗[R] M`,
  with `Module.IsTorsionFree` as the target owner predicate;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for `R' ⊗[R] M`;
  `core/canonical`: the tensor-product base-change object together with the owner predicate
    `Module.IsTorsionFree`;
  `bridge/view`: no extra bridge owner is needed here, since the source statement already lives on
    the canonical tensor-product base change and no direct downstream file uses an intermediate
    `IsBaseChange` formulation.

Primitive data are the flat algebra `R → S` and the torsion-free `R`-module `M`. The tensor
product `S ⊗[R] M` is already the canonical base-change object, so this file should expose only the
source-facing theorem instead of introducing an additional owner-level wrapper theorem.
-/

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
variable [Flat R R'] [AddCommGroup M] [Module R M] [IsTorsionFree R M]

/-- Lemma 15.22.4: if `R → R'` is a flat homomorphism of domains and `M` is a torsion-free
`R`-module, then the base-changed module `R' ⊗[R] M` is a torsion-free `R'`-module. -/
theorem isTorsionFree_baseChange_of_flat :
    IsTorsionFree R' (R' ⊗[R] M) := sorry

end
