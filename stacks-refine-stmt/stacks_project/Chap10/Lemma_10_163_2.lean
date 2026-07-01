import Mathlib
import stacks_project.Chap10.Lemma_10_163_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain-style sampling pass:
* primary domain: local commutative algebra of depth under flat local base change, with the closed
  fiber carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `moduleDepth`,
  `Ideal.Fiber`,
  `depth_tensorProduct_eq_depth_add_depth_closedFiber`,
  `Algebra.TensorProduct.rid`;
* best owner abstraction: the public statement should live on the local-depth bridge
  `moduleDepth` and on the canonical closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`,
  while the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` is only a
  bridge/view.

Primitive data vs. derived API:
* primitive data: the flat local algebra map `R → S`;
* derived API: the tensor-product presentations `S ⊗[R] R` and `ClosedFiber ⊗[S] S`, and the
  quotient presentation of the closed fiber.

Source/core/bridge triage:
* `source-facing`: the Stacks depth formula for the ring map `R → S`;
* `core/canonical`: `moduleDepth` and `Ideal.Fiber`;
* `bridge/view`: the tensor and quotient identifications used to compare this source-facing
  statement with the module-level owner theorem `depth_tensorProduct_eq_depth_add_depth_closedFiber`.
-/
attribute [local instance] closedFiber_isLocalRing

private theorem regularSequenceLengths_eq_of_equiv {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (I : Ideal A)
    (e : M ≃ₗ[A] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

private theorem ideal_depth_eq_of_equiv {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M] [Module.Finite A N] (I : Ideal A)
    (e : M ≃ₗ[A] N) :
    Ideal.depth I M = Ideal.depth I N := by
  have htop : I • (⊤ : Submodule A M) = ⊤ ↔ I • (⊤ : Submodule A N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule A M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_equiv I e]

private theorem moduleDepth_eq_of_equiv {A M N : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N] (e : M ≃ₗ[A] N) :
    moduleDepth A M = moduleDepth A N :=
  ideal_depth_eq_of_equiv (maximalIdeal A) e

-- Proof sketch: specialize Lemma `10.163.1` to `M = R` and `N = S`, so the tensor product on the
-- left becomes `S ⊗[R] R` and the closed-fiber module on the right becomes `ClosedFiber ⊗[S] S`.
-- Then transport the two depth terms across the canonical algebra-tensor identifications
-- `S ⊗[R] R ≃ S` and `ClosedFiber ⊗[S] S ≃ ClosedFiber`.
/-- Lemma 10.163.2: for a flat local homomorphism `R → S` of Noetherian local rings, the depth of
`S` equals the depth of `R` plus the depth of the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`. -/
theorem depth_target_eq_depth_source_add_depth_closed_fiber :
    moduleDepth S S = moduleDepth R R + moduleDepth ClosedFiber ClosedFiber := by
  rw [← moduleDepth_eq_of_equiv (Algebra.TensorProduct.rid R S S).toLinearEquiv,
    ← moduleDepth_eq_of_equiv (Algebra.TensorProduct.rid S ClosedFiber ClosedFiber).toLinearEquiv]
  simpa using
    (depth_tensorProduct_eq_depth_add_depth_closedFiber :
      moduleDepth S (S ⊗[R] R) =
        moduleDepth R R + moduleDepth ClosedFiber (ClosedFiber ⊗[S] S))

end
