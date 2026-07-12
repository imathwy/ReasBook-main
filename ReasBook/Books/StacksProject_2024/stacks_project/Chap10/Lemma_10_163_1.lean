import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] N

/- Domain-style sampling pass:
* primary domain: local commutative algebra of depth for finite modules under flat local base
  change, with the closed fiber carried by the canonical fiber-ring owner;
* sampled owner declarations:
  `moduleDepth`,
  `Ideal.Fiber`,
  `Module.Finite.base_change`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`;
* best owner abstraction: the right-hand side belongs on the canonical local depth
  `moduleDepth ClosedFiber ClosedFiberModule`, where
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] N`; the quotient module
  `N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))` is only a bridge.

Primitive data vs. derived API:
* primitive data: the local flat map `R → S`, the finite `R`-module `M`, and the finite
  `S`-module `N` that is flat over `R`;
* derived API: the quotient presentation of the closed fiber and of the closed-fiber module.

Source/core/bridge triage:
* `source-facing`: the Stacks additivity formula for depth under flat local base change;
* `core/canonical`: `moduleDepth` on the owner ring/module pair `ClosedFiber` and
  `ClosedFiberModule`;
* `bridge/view`: the quotient presentation `S ⧸ 𝔪S` and
  `N ⧸ (𝔪S • (⊤ : Submodule S N))`.
-/

/-- The canonical closed fiber `ClosedFiber = (maximalIdeal R).Fiber S` is a local ring. -/
local instance closedFiber_isLocalRing : IsLocalRing ClosedFiber := by
  let e : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
      (Algebra.TensorProduct.comm _ _ _).trans
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)
  letI : IsLocalRing (S ⧸ 𝔪S) := by
    have h𝔪S : 𝔪S < (⊤ : Ideal S) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
    have : Nontrivial (S ⧸ 𝔪S) :=
      Quotient.nontrivial_iff.mpr h𝔪S.ne
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔪S) Ideal.Quotient.mk_surjective
  exact (e.symm : S ⧸ 𝔪S ≃+* ClosedFiber).isLocalRing

/-- The tensor product `N ⊗[R] M`, which represents `M ⊗[R] N` in a form carrying its natural
`S`-module structure, is finite over `S` under the flat local algebra hypotheses. -/
local instance : Module.Finite S (N ⊗[R] M) := sorry

-- Proof sketch: argue by induction on the sum of the two depths. If the closed fiber has positive
-- depth, choose a nonzerodivisor in the maximal ideal of `S` on the closed fiber, use the flat
-- lifting lemma to show it is a nonzerodivisor on `N`, reduce to `N / fN`, and apply the depth
-- drop lemma. If the closed fiber has depth zero but the sum is positive, choose a
-- nonzerodivisor in the maximal ideal of `R` on `M`, use flatness of `N` to keep it regular on
-- the tensor product, pass to `M / xM`, and conclude by induction.
/-- Lemma 10.163.1: for a flat local homomorphism `R → S` of Noetherian local rings, a finite
`R`-module `M`, and a finite `S`-module `N` that is flat over `R`, the local depth of the tensor
product equals the local depth of `M` plus the local depth of the canonical closed-fiber module
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] N`, equivalently
`N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))`, over the canonical
closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`. -/
theorem depth_tensorProduct_eq_depth_add_depth_closedFiber :
    moduleDepth S (N ⊗[R] M) =
      moduleDepth R M + moduleDepth ClosedFiber ClosedFiberModule := sorry

end
