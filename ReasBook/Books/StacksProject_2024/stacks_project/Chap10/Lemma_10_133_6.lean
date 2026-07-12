import Mathlib
import StacksProject_2024.Chap10.Remark_10_133_7

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain triage:
* primary domain: first principal parts and their order-one universal property;
* sampled owner API:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `principal_parts_module`,
  `principal_parts_universal_differential`,
  `principalPartsBaseChangeMap`,
  `ShortComplex.moduleCatMk`;
* source-facing owner: `principal_parts_module R S M 1`;
* core/canonical operator owner: `differential_operators_order_le R S M 1 N`;
* bridge/view in this file: the short exact principal-parts sequence.

This file specializes the canonical owner from Lemma `10.133.3`, reuses the chapter base-change
map for module functoriality, and keeps the public derived API on the ambient `Module` owner.
-/

universe u

noncomputable section

open KaehlerDifferential
open CategoryTheory
open scoped PrincipalParts

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The class of a generator `[m]` in the first principal-parts module. -/
private abbrev principalPartsClass (M : Type u) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (m : M) : P^{1}_{S⁄R}(M) :=
  @principal_parts_universal_differential R S M _ _ _ _ _ _ _ 1 m

/-- The identity map is an order-`1` differential operator. -/
private theorem id_mem_differential_operators_order_le_submodule
    (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    (LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M)) ∈
      differential_operators_order_le_submodule R S M 1 M := by
  change
    (LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M)).IsDifferentialOperatorOfOrder S 1
  rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
  intro g
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro h m
  simp

namespace Module

section PrincipalParts

variable (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The canonical projection `P^1_{S/R}(M) → M`. -/
noncomputable abbrev principalPartsProjection :
    P^{1}_{S⁄R}(M) →ₗ[S] M :=
  (@principal_parts_linear_map_equiv_differential_operators R S M _ _ _ _ _ _ _ 1 M _ _ _ _).symm
    ⟨LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M),
      id_mem_differential_operators_order_le_submodule R S M⟩

-- Proof sketch: expand the class of `[(s + t) • m] - (s + t)[m]` in the quotient and rearrange
-- terms using additivity of scalar multiplication in `M` and in the module of principal parts.
/-- Additivity of the principal-parts commutator in the scalar variable. -/
private theorem principalPartsDerivationLinearMap_map_add (m : M) (s t : S) :
    principalPartsClass R S M ((s + t) • m) - (s + t) • principalPartsClass R S M m =
      (principalPartsClass R S M (s • m) - s • principalPartsClass R S M m) +
        (principalPartsClass R S M (t • m) - t • principalPartsClass R S M m) := sorry

-- Proof sketch: use compatibility of the presentation with the `R`-module structure on `M` and
-- factor out the scalar `r` through the quotient map.
/-- `R`-linearity of the principal-parts commutator in the scalar variable. -/
private theorem principalPartsDerivationLinearMap_map_smul (m : M) (r : R) (s : S) :
    principalPartsClass R S M ((r • s) • m) -
        (r • s) • principalPartsClass R S M m =
      r • (principalPartsClass R S M (s • m) - s • principalPartsClass R S M m) := sorry

/-- The derivation `s ↦ [s m] - s [m]` valued in first principal parts. -/
private def principalPartsDerivationLinearMap (m : M) :
    S →ₗ[R] P^{1}_{S⁄R}(M) :=
  { toFun := fun s ↦ principalPartsClass R S M (s • m) - s • principalPartsClass R S M m
    map_add' := principalPartsDerivationLinearMap_map_add R S M m
    map_smul' := principalPartsDerivationLinearMap_map_smul R S M m }

-- Proof sketch: modulo the order-one relations, the commutator identity
-- `[st m] - st[m] = s([t m] - t[m]) + t([s m] - s[m])` is exactly the Leibniz rule.
/-- The principal-parts commutator defines an `R`-derivation in the scalar variable. -/
private theorem principalPartsDerivationLinearMap_leibniz (m : M) (s t : S) :
    principalPartsDerivationLinearMap R S M m (s * t) =
      s • principalPartsDerivationLinearMap R S M m t +
        t • principalPartsDerivationLinearMap R S M m s := sorry

/-- The derivation `S → P^1_{S/R}(M)` attached to an element `m : M`. -/
private def principalPartsDerivation (m : M) :
    Derivation R S (P^{1}_{S⁄R}(M)) :=
  Derivation.mk' (principalPartsDerivationLinearMap R S M m)
    (principalPartsDerivationLinearMap_leibniz R S M m)

/-- The `S`-linear map `Ω[S⁄R] → P^1_{S/R}(M)` corresponding to the derivation attached to `m`. -/
private noncomputable def principalPartsCotangentComponent (m : M) :
    Ω[S⁄R] →ₗ[S] P^{1}_{S⁄R}(M) :=
  (linearMapEquivDerivation R S).symm (principalPartsDerivation R S M m)

-- Proof sketch: both sides correspond under `linearMapEquivDerivation R S` to the sum of the two
-- derivations attached to `m` and `m'`.
/-- Additivity of the cotangent component in the module variable. -/
private theorem principalPartsCotangentComponent_map_add (m m' : M) :
    principalPartsCotangentComponent R S M (m + m') =
      principalPartsCotangentComponent R S M m +
        principalPartsCotangentComponent R S M m' := sorry

-- Proof sketch: under the universal property of Kähler differentials, scaling `m` by `s` scales
-- the attached derivation by `s`.
/-- `S`-linearity of the cotangent component in the module variable. -/
private theorem principalPartsCotangentComponent_map_smul (s : S) (m : M) :
    principalPartsCotangentComponent R S M (s • m) =
      s • principalPartsCotangentComponent R S M m := sorry

/-- The linear family `m ↦ (Ω[S⁄R] → P^1_{S/R}(M))` used to build the principal-parts sequence. -/
private def principalPartsCotangentLinear :
    M →ₗ[S] (Ω[S⁄R] →ₗ[S] P^{1}_{S⁄R}(M)) :=
  { toFun := principalPartsCotangentComponent R S M
    map_add' := principalPartsCotangentComponent_map_add R S M
    map_smul' := principalPartsCotangentComponent_map_smul R S M }

/-- The canonical map `Ω[S⁄R] ⊗[S] M → P^1_{S/R}(M)`. -/
noncomputable def principalPartsCotangentToPrincipalParts :
    TensorProduct S (Ω[S⁄R]) M →ₗ[S] P^{1}_{S⁄R}(M) :=
  (TensorProduct.uncurry (RingHom.id S) M Ω[S⁄R] (P^{1}_{S⁄R}(M))
      (principalPartsCotangentLinear R S M)).comp
    (TensorProduct.comm S Ω[S⁄R] M).toLinearMap

-- Proof sketch: both composites encode the same elementwise formula
-- `η ⊗ m ↦ principalPartsCotangentComponent m η`, and applying the projection kills the
-- commutator part by construction.
/-- The projection `P^1_{S/R}(M) → M` annihilates the image of `Ω[S⁄R] ⊗[S] M`. -/
private theorem principalPartsSequence_comp_zero :
    (principalPartsProjection R S M).comp (principalPartsCotangentToPrincipalParts R S M) = 0 :=
  sorry

/-- The short complex `Ω[S⁄R] ⊗[S] M ⟶ P^1_{S/R}(M) ⟶ M` attached to principal parts. -/
abbrev principalPartsSequence : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk
    (principalPartsCotangentToPrincipalParts R S M)
    (principalPartsProjection R S M)
    (principalPartsSequence_comp_zero R S M)

end PrincipalParts

section Map

variable (M N : Type u)
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

-- Proof sketch: both composites send the class of `[m]` to `f m`, so they agree by the quotient
-- presentation of `P^1_{S/R}(M)`.
/-- Naturality of the projection `P^1_{S/R}(-) → id`. -/
private theorem principalPartsSequenceMap_comm₂₃ (f : M →ₗ[S] N) :
    (principalPartsProjection R S N).comp
        (principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N)) =
      f.comp (principalPartsProjection R S M) := sorry

-- Proof sketch: both composites represent the bilinear rule
-- `(η, m) ↦ principalPartsCotangentComponent (f m) η`, so they agree by the tensor-product
-- universal property.
/-- Naturality of the map `Ω[S⁄R] ⊗[S] - → P^1_{S/R}(-)`. -/
private theorem principalPartsSequenceMap_comm₁₂ (f : M →ₗ[S] N) :
    (principalPartsCotangentToPrincipalParts R S N).comp
        (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f) =
      (principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N)).comp
        (principalPartsCotangentToPrincipalParts R S M) := sorry

/-- The morphism of principal-parts sequences induced by an `S`-linear map `M → N`. -/
abbrev principalPartsSequenceMap (f : M →ₗ[S] N) :
    principalPartsSequence R S M ⟶ principalPartsSequence R S N :=
  ShortComplex.Hom.mk
    (ModuleCat.ofHom (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f))
    (ModuleCat.ofHom
      (principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N)))
    (ModuleCat.ofHom f)
    (by
      simpa using congrArg ModuleCat.ofHom (principalPartsSequenceMap_comm₁₂ R S M N f))
    (by
      simpa using congrArg ModuleCat.ofHom (principalPartsSequenceMap_comm₂₃ R S M N f))

end Map

end Module

section Main

variable (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

-- Proof sketch: construct the canonical maps above, identify the right map as the quotient map
-- onto `M`, identify the left map by the universal property of `Ω[S⁄R]`, and then prove
-- injectivity by reduction to the free case exactly as in the Stacks Project argument.
/-- Lemma 10.133.6: there is a canonical short exact sequence
`0 ⟶ Ω[S⁄R] ⊗[S] M ⟶ P^1_{S/R}(M) ⟶ M ⟶ 0`, functorial in the `S`-module `M`, called the
sequence of principal parts. -/
theorem principal_parts_sequence_shortExact :
    (Module.principalPartsSequence R S M).ShortExact := sorry

end Main

end
