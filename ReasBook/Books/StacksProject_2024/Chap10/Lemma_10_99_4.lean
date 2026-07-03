import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct
open IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/- Domain sampling pass:
* primary domain: local commutative algebra of finite modules over flat local homomorphisms and
  their closed fibers;
* sampled owner declarations:
  - `Ideal.Fiber`, the canonical closed-fiber ring owner `κ(maximalIdeal R) ⊗[R] S`;
  - `Definition_10_65_2.mem_relativeAssassin_iff_fiber`, which uses the fiber module
    `((q.asIdeal.under R).Fiber S) ⊗[S] N` as the canonical module-level fiber;
  - `Lemma_10_39_15.nontrivial_tensor_residueField_iff_nontrivial_quotSMul`, the quotient bridge
    between residue-field fibers and reduction modulo the maximal ideal;
  - `Lemma_10_39_10.algebraMap_flat_of_flat_of_faithfullyFlat`, the owner descent statement for
    flatness of the algebra map.

Source/core/bridge triage:
* source-facing: the two textbook statements about freeness of `M` and flatness of `R → S`;
* core/canonical: the closed-fiber ring `ClosedFiber` and its fiber module `ClosedFiber ⊗[S] M`;
* bridge/view: the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`.

Primitive data vs derived API:
* primitive owner data is the ambient local algebra map and the finite `S`-module `M`;
* freeness of the closed fiber is naturally a property of the canonical fiber module over
  `ClosedFiber`, not of a bespoke quotient wrapper.
-/

-- Proof sketch: choose lifts in `M` of a basis of the closed fiber module
-- `ClosedFiberModule = ClosedFiber ⊗[S] M`, equivalently
-- `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, yielding an
-- `S`-linear map `S^n → M`. The induced map on the closed fiber is injective because the chosen
-- images form a basis there, so Lemma 10.99.1 gives injectivity upstairs. Nakayama's lemma gives
-- surjectivity, and hence `M` is free over `S`.
/-- Lemma 10.99.4 (1): if the closed fiber module `ClosedFiber ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is free over the closed
fiber ring `ClosedFiber = (maximalIdeal R).Fiber S` and `M` is flat over `R`, then `M` is free
over `S`. -/
theorem free_of_flat_of_free_closedFiber [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    Module.Free S M := sorry

-- Proof sketch: part (1) makes `M` into a free `S`-module. Because `M` is nontrivial, a nonzero
-- free `S`-module is faithfully flat over `S`; then apply Lemma 10.39.10 to descend the given
-- `R`-flatness of `M` to flatness of the algebra map `R → S`.
/-- Lemma 10.99.4 (2): if the closed fiber module `ClosedFiber ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is free over the closed
fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, `M` is flat over `R`, and `M` is nonzero,
then the local homomorphism `R → S` is flat. -/
theorem algebraMap_flat_of_nontrivial_flat_module_of_free_closedFiber
    [Nontrivial M] [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    (algebraMap R S).Flat := sorry

end
