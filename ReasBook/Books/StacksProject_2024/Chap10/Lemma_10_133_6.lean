import Mathlib
import StacksProject_2024.Chap10.Lemma_10_10_1
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

/-- Helper for Lemma 10.133.6: the universal class map `m ↦ [m]` is the order-`1` differential
operator represented by the identity on `P^1_{S/R}(M)`. -/
private theorem principalPartsClass_isDifferentialOperatorOfOrder_one
    (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    (LinearMap.restrictScalars R (principal_parts_universal_differential (R := R) (S := S)
      (M := M) 1)).IsDifferentialOperatorOfOrder S 1 := by
  -- The principal-parts representation sends the identity on `P^1_{S/R}(M)` to the universal
  -- order-`1` differential operator `m ↦ [m]`.
  change
    (((principal_parts_linear_map_equiv_differential_operators R S M 1 P^{1}_{S⁄R}(M))
      (LinearMap.id : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(M))).1).IsDifferentialOperatorOfOrder
        S 1
  exact
    (((principal_parts_linear_map_equiv_differential_operators R S M 1 P^{1}_{S⁄R}(M))
      (LinearMap.id : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(M))).2)

/-- Helper for Lemma 10.133.6: the scalar commutator of the universal class map is `S`-linear in
the module variable. -/
private theorem principalPartsClass_scalarCommutator_smul
    (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (s t : S) (m : M) :
    principalPartsClass R S M (s • (t • m)) -
        s • principalPartsClass R S M (t • m) =
      t • (principalPartsClass R S M (s • m) -
        s • principalPartsClass R S M m) := by
  -- The order-`1` bound says every scalar commutator of `m ↦ [m]` is order `0`, hence `S`-linear
  -- in `m`; evaluating that linearity at `t • m` gives the commutator transport formula.
  have hδ :
      (LinearMap.restrictScalars R
        (principal_parts_universal_differential (R := R) (S := S) (M := M) 1)).IsDifferentialOperatorOfOrder
          S 1 := by
    exact principalPartsClass_isDifferentialOperatorOfOrder_one R S M
  rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hδ
  have hs := hδ s
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at hs
  simpa [principalPartsClass, LinearMap.scalarCommutator_apply] using hs t m

namespace Module

section PrincipalParts

variable (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The canonical projection `P^1_{S/R}(M) → M`. -/
noncomputable abbrev principalPartsProjection :
    P^{1}_{S⁄R}(M) →ₗ[S] M :=
  (@principal_parts_linear_map_equiv_differential_operators R S M _ _ _ _ _ _ _ 1 M _ _ _ _).symm
    ⟨LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M),
      id_mem_differential_operators_order_le_submodule R S M⟩

/-- Helper for Lemma 10.133.6: the projection `P^1_{S/R}(M) → M` sends the universal class `[m]`
back to `m`. -/
private theorem principalPartsProjection_apply_class (m : M) :
    principalPartsProjection R S M (principalPartsClass R S M m) = m := by
  let e := @principal_parts_linear_map_equiv_differential_operators R S M _ _ _ _ _ _ _ 1 M _ _ _ _
  -- Evaluate the defining identity `e (e.symm id) = id` at the generator `[m]`.
  have h : (e (principalPartsProjection R S M)).1 m = m := by
    simpa [e, principalPartsProjection] using
      congrArg (fun D : differential_operators_order_le R S M 1 M => D.1 m)
        (e.apply_symm_apply
          ⟨LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M),
            id_mem_differential_operators_order_le_submodule R S M⟩)
  change (e (principalPartsProjection R S M)).1 m = m
  exact h

/-- Helper for Lemma 10.133.6: principal-parts base change sends the generator `[m]` to
`[f m]`. -/
private theorem principalPartsBaseChangeMap_apply_class
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (f : M →ₗ[S] N) (m : M) :
    (principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N))
      (principalPartsClass R S M m) =
    principalPartsClass R S N (f m) := by
  -- Precomposing the quotient map by the free-generator class map reduces the claim to the
  -- explicit free-module map used to define `principalPartsBaseChangeMap`.
  have hcomp :
      (principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N)).comp
          (principal_parts_relation_submodule R S M 1).mkQ =
        ((principal_parts_relation_submodule R S N 1).mkQ).comp
          ((Finsupp.mapRange.linearMap (Algebra.linearMap S S)).comp
            (Finsupp.lmapDomain S S f)) := by
    rw [principalPartsBaseChangeMap]
    rfl
  -- Evaluating at the basis vector `[m]` gives the concrete formula on principal-parts classes.
  have h := LinearMap.congr_fun hcomp (Finsupp.single m (1 : S))
  simpa [principalPartsClass] using h

-- Proof sketch: expand the class of `[(s + t) • m] - (s + t)[m]` in the quotient and rearrange
-- terms using additivity of scalar multiplication in `M` and in the module of principal parts.
/-- Additivity of the principal-parts commutator in the scalar variable. -/
private theorem principalPartsDerivationLinearMap_map_add (m : M) (s t : S) :
    principalPartsClass R S M ((s + t) • m) - (s + t) • principalPartsClass R S M m =
      (principalPartsClass R S M (s • m) - s • principalPartsClass R S M m) +
        (principalPartsClass R S M (t • m) - t • principalPartsClass R S M m) := by
  -- Rewrite `(s + t) • m` as `s • m + t • m`, then use additivity of `m ↦ [m]`.
  calc
    principalPartsClass R S M ((s + t) • m) - (s + t) • principalPartsClass R S M m
      = principalPartsClass R S M (s • m + t • m) -
          (s + t) • principalPartsClass R S M m := by
            rw [add_smul]
    _ = (principalPartsClass R S M (s • m) - s • principalPartsClass R S M m) +
          (principalPartsClass R S M (t • m) - t • principalPartsClass R S M m) := by
            change principal_parts_universal_differential (R := R) (S := S) (M := M) 1
                (s • m + t • m) -
                  (s + t) • principalPartsClass R S M m =
                (principalPartsClass R S M (s • m) - s • principalPartsClass R S M m) +
                  (principalPartsClass R S M (t • m) - t • principalPartsClass R S M m)
            rw [map_add, add_smul]
            abel

-- Proof sketch: use compatibility of the presentation with the `R`-module structure on `M` and
-- factor out the scalar `r` through the quotient map.
/-- `R`-linearity of the principal-parts commutator in the scalar variable. -/
private theorem principalPartsDerivationLinearMap_map_smul (m : M) (r : R) (s : S) :
    principalPartsClass R S M ((r • s) • m) -
        (r • s) • principalPartsClass R S M m =
      r • (principalPartsClass R S M (s • m) - s • principalPartsClass R S M m) := by
  -- Rewrite the `R`-scalar through the ambient `S`-module structures and use `R`-linearity of
  -- the universal class map.
  rw [show r • s = (algebraMap R S r) * s by simp [Algebra.smul_def]]
  simpa [Algebra.smul_def] using
    (show
        principalPartsClass R S M (((algebraMap R S r) * s) • m) -
            ((algebraMap R S r) * s) • principalPartsClass R S M m =
          (algebraMap R S r) •
            (principalPartsClass R S M (s • m) - s • principalPartsClass R S M m) by
      simp [principalPartsClass, smul_sub, mul_smul])

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
        t • principalPartsDerivationLinearMap R S M m s := by
  -- Expand the commutator at `s * t`, split off the `s`-part, and then use that the scalar
  -- commutator of the universal class map is `S`-linear in `m`.
  calc
    principalPartsDerivationLinearMap R S M m (s * t)
      = (principalPartsClass R S M (s • (t • m)) -
          s • principalPartsClass R S M (t • m)) +
          s • principalPartsDerivationLinearMap R S M m t := by
            simp [principalPartsDerivationLinearMap, sub_eq_add_neg, smul_smul, add_assoc,
              add_left_comm]
    _ = t • principalPartsDerivationLinearMap R S M m s +
          s • principalPartsDerivationLinearMap R S M m t := by
          rw [principalPartsClass_scalarCommutator_smul R S M s t m]
          simp [principalPartsDerivationLinearMap]
    _ = s • principalPartsDerivationLinearMap R S M m t +
          t • principalPartsDerivationLinearMap R S M m s := by
          abel

/-- The derivation `S → P^1_{S/R}(M)` attached to an element `m : M`. -/
private def principalPartsDerivation (m : M) :
    Derivation R S (P^{1}_{S⁄R}(M)) :=
  Derivation.mk' (principalPartsDerivationLinearMap R S M m)
    (principalPartsDerivationLinearMap_leibniz R S M m)

/-- The `S`-linear map `Ω[S⁄R] → P^1_{S/R}(M)` corresponding to the derivation attached to `m`. -/
private noncomputable def principalPartsCotangentComponent (m : M) :
    Ω[S⁄R] →ₗ[S] P^{1}_{S⁄R}(M) :=
  (linearMapEquivDerivation R S).symm (principalPartsDerivation R S M m)

/-- Helper for Lemma 10.133.6: the cotangent component sends `d s` to the commutator
`[s m] - s [m]`. -/
private theorem principalPartsCotangentComponent_D (m : M) (s : S) :
    principalPartsCotangentComponent R S M m (KaehlerDifferential.D R S s) =
      principalPartsClass R S M (s • m) - s • principalPartsClass R S M m := by
  -- The linear map `Ω[S⁄R] → P^1_{S/R}(M)` was defined as the lift of the derivation
  -- `s ↦ [s m] - s [m]`, so evaluating it on `d s` recovers that derivation.
  simpa [principalPartsCotangentComponent, principalPartsDerivation, principalPartsDerivationLinearMap]
    using Derivation.liftKaehlerDifferential_comp_D
      (principalPartsDerivation R S M m) s

-- Proof sketch: both sides correspond under `linearMapEquivDerivation R S` to the sum of the two
-- derivations attached to `m` and `m'`.
/-- Additivity of the cotangent component in the module variable. -/
private theorem principalPartsCotangentComponent_map_add (m m' : M) :
    principalPartsCotangentComponent R S M (m + m') =
      principalPartsCotangentComponent R S M m +
        principalPartsCotangentComponent R S M m' := by
  -- The Kähler-differential lift is determined by its values on `d s`, so it is enough to
  -- compare the two sides on those generators.
  apply Derivation.liftKaehlerDifferential_unique
  ext s
  simp [principalPartsCotangentComponent_D, principalPartsClass]
  abel

-- Proof sketch: under the universal property of Kähler differentials, scaling `m` by `s` scales
-- the attached derivation by `s`.
/-- `S`-linearity of the cotangent component in the module variable. -/
private theorem principalPartsCotangentComponent_map_smul (s : S) (m : M) :
    principalPartsCotangentComponent R S M (s • m) =
      s • principalPartsCotangentComponent R S M m := by
  -- Again, the lift is determined on `d t`, where the claim is exactly the scalar-commutator
  -- transport identity.
  apply Derivation.liftKaehlerDifferential_unique
  ext t
  simpa [principalPartsCotangentComponent_D] using
    principalPartsClass_scalarCommutator_smul R S M t s m

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

/-- Helper for Lemma 10.133.6: the canonical tensor map sends a pure tensor `η ⊗ m` to the
cotangent component attached to `m`, evaluated at `η`. -/
private theorem principalPartsCotangentToPrincipalParts_tmul (η : Ω[S⁄R]) (m : M) :
    principalPartsCotangentToPrincipalParts R S M (η ⊗ₜ[S] m) =
      principalPartsCotangentComponent R S M m η := by
  -- Route correction: expose the pure-tensor formula once so the later proofs can use
  -- `TensorProduct.ext'` instead of repeatedly reopening the uncurry construction.
  simp [principalPartsCotangentToPrincipalParts, principalPartsCotangentLinear,
    TensorProduct.comm_tmul]

/-- Helper for Lemma 10.133.6: the canonical tensor map sends `d s ⊗ m` to the scalar commutator
`[s m] - s [m]`. -/
private theorem principalPartsCotangentToPrincipalParts_D_tmul (s : S) (m : M) :
    principalPartsCotangentToPrincipalParts R S M ((KaehlerDifferential.D R S s) ⊗ₜ[S] m) =
      principalPartsClass R S M (s • m) - s • principalPartsClass R S M m := by
  -- Specialize the pure-tensor formula to `η = d s`, then use the explicit generator formula for
  -- the cotangent component.
  rw [principalPartsCotangentToPrincipalParts_tmul, principalPartsCotangentComponent_D]

-- Proof sketch: both composites encode the same elementwise formula
-- `η ⊗ m ↦ principalPartsCotangentComponent m η`, and applying the projection kills the
-- commutator part by construction.
/-- The projection `P^1_{S/R}(M) → M` annihilates the image of `Ω[S⁄R] ⊗[S] M`. -/
private theorem principalPartsSequence_comp_zero :
    (principalPartsProjection R S M).comp (principalPartsCotangentToPrincipalParts R S M) = 0 :=
  by
    -- Evaluate on pure tensors and reduce to the claim that each cotangent component lands in
    -- the kernel of the projection.
    apply TensorProduct.ext'
    intro η m
    rw [LinearMap.comp_apply, principalPartsCotangentToPrincipalParts_tmul]
    change ((principalPartsProjection R S M).comp (principalPartsCotangentComponent R S M m)) η = 0
    have hcomponent :
        (principalPartsProjection R S M).comp (principalPartsCotangentComponent R S M m) = 0 := by
      -- On `d s`, the projection of the commutator `[s m] - s [m]` is visibly zero.
      apply Derivation.liftKaehlerDifferential_unique
      ext s
      simp [principalPartsCotangentComponent_D, principalPartsProjection_apply_class]
    simpa using LinearMap.congr_fun hcomponent η

/-- The short complex `Ω[S⁄R] ⊗[S] M ⟶ P^1_{S/R}(M) ⟶ M` attached to principal parts. -/
abbrev principalPartsSequence : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk
    (principalPartsCotangentToPrincipalParts R S M)
    (principalPartsProjection R S M)
    (principalPartsSequence_comp_zero R S M)

/-- Helper for Lemma 10.133.6: the principal-parts projection is surjective because every
`m : M` is the image of its universal class `[m]`. -/
private theorem principalPartsProjection_surjective :
    Function.Surjective (principalPartsProjection R S M) := by
  intro m
  exact ⟨principalPartsClass R S M m, principalPartsProjection_apply_class (R := R) (S := S)
    (M := M) m⟩

/-- Helper for Lemma 10.133.6: the principal-parts row
`Ω[S⁄R] ⊗[S] M ⟶ P^1_{S/R}(M) ⟶ M` is exact. -/
theorem principalPartsSequence_exact :
    Function.Exact (principalPartsCotangentToPrincipalParts R S M)
      (principalPartsProjection R S M) := by
  -- The source proof first checks exactness after applying `Hom_S(-, N)` for every target `N`.
  -- We package that represented sequence using `exact_iff_exact_hom_into`.
  exact
    ((exact_iff_exact_hom_into
      (R := S)
      (f := principalPartsCotangentToPrincipalParts R S M)
      (g := principalPartsProjection R S M)).2 <| by
        intro (N : Type u) _ _
        refine ⟨LinearMap.lcomp_injective_of_surjective _ <|
          principalPartsProjection_surjective R S M, ?_⟩
        intro L
        constructor
        · intro hL
          -- Vanishing on `Ω[S⁄R] ⊗[S] M` says exactly that `L` kills the commutators
          -- `[s m] - s [m]`, so `m ↦ L([m])` is `S`-linear and factors through the projection.
          let ψ : M →ₗ[S] N :=
            { toFun := fun m ↦ L (principalPartsClass R S M m)
              map_add' := by
                intro m m'
                simp [principalPartsClass, map_add]
              map_smul' := by
                intro s m
                have hcomm :
                    L (principalPartsClass R S M (s • m) -
                        s • principalPartsClass R S M m) = 0 := by
                  simpa [LinearMap.comp_apply,
                    principalPartsCotangentToPrincipalParts_D_tmul]
                    using LinearMap.congr_fun hL ((KaehlerDifferential.D R S s) ⊗ₜ[S] m)
                have hcomm' :
                    L (principalPartsClass R S M (s • m)) -
                        s • L (principalPartsClass R S M m) = 0 := by
                  simpa [map_sub] using hcomm
                exact sub_eq_zero.mp hcomm' }
          refine ⟨ψ, ?_⟩
          -- The quotient `P^1_{S/R}(M)` is generated by the universal classes `[m]`.
          apply Submodule.linearMap_qext
          apply Finsupp.lhom_ext'
          intro m
          apply LinearMap.ext_ring
          change
            ψ ((principalPartsProjection R S M) (principalPartsClass R S M m)) =
              L (principalPartsClass R S M m)
          rw [principalPartsProjection_apply_class]
          rfl
        · rintro ⟨ψ, rfl⟩
          -- Any map factoring through the projection kills the tensor map because the sequence
          -- was constructed with zero composite.
          apply TensorProduct.ext'
          intro η m
          have hzero := LinearMap.congr_fun
            (principalPartsSequence_comp_zero R S M) (η ⊗ₜ[S] m)
          simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
          simpa [LinearMap.comp_apply] using congrArg ψ hzero).1

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
      f.comp (principalPartsProjection R S M) := by
  -- The quotient `P^1_{S/R}(M)` is generated by the universal classes `[m]`, so it suffices to
  -- compare the two maps on those generators.
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext'
  intro m
  apply LinearMap.ext_ring
  change
    (principalPartsProjection R S N)
        ((principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N))
          (principalPartsClass R S M m)) =
      f ((principalPartsProjection R S M) (principalPartsClass R S M m))
  rw [principalPartsBaseChangeMap_apply_class, principalPartsProjection_apply_class,
    principalPartsProjection_apply_class]

-- Proof sketch: both composites represent the bilinear rule
-- `(η, m) ↦ principalPartsCotangentComponent (f m) η`, so they agree by the tensor-product
-- universal property.
/-- Naturality of the map `Ω[S⁄R] ⊗[S] - → P^1_{S/R}(-)`. -/
private theorem principalPartsSequenceMap_comm₁₂ (f : M →ₗ[S] N) :
    (principalPartsCotangentToPrincipalParts R S N).comp
        (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f) =
      (principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N)).comp
        (principalPartsCotangentToPrincipalParts R S M) := by
  -- Compare both maps on pure tensors and then identify the two cotangent components by their
  -- values on `d s`.
  apply TensorProduct.ext'
  intro η m
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.comp_apply,
    principalPartsCotangentToPrincipalParts_tmul, principalPartsCotangentToPrincipalParts_tmul]
  have hcomponent :
      (principalPartsBaseChangeMap 1 f : P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N)).comp
          (principalPartsCotangentComponent R S M m) =
        principalPartsCotangentComponent R S N (f m) := by
    -- Both cotangent components are the unique lifts of the same derivation-valued formula after
    -- applying `f`.
    apply Derivation.liftKaehlerDifferential_unique
    ext s
    simp [principalPartsCotangentComponent_D, principalPartsBaseChangeMap_apply_class]
  simpa using (LinearMap.congr_fun hcomponent η).symm

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

/-- Helper for Lemma 10.133.6: every derivation is an order-`1` differential operator. -/
private theorem derivation_isDifferentialOperatorOfOrder_one
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (δ : Derivation R S N) :
    (δ.toLinearMap : S →ₗ[R] N).IsDifferentialOperatorOfOrder S 1 := by
  -- A derivation has scalar commutator `t ↦ t • δ s`, which is `S`-linear and hence order `0`.
  rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
  intro s
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro a t
  simp [δ.leibniz, smul_add, smul_smul, sub_eq_add_neg, add_assoc, add_comm]
  abel

section SelfAndFree

variable {ι : Type u}

/-- The cotangent-valued first-order operator `s ↦ d s`, represented on first principal parts. -/
private noncomputable def principalPartsSelfToCotangent :
    P^{1}_{S⁄R}(S) →ₗ[S] Ω[S⁄R] :=
  (principal_parts_linear_map_equiv_differential_operators R S S 1 Ω[S⁄R]).symm
    ⟨(KaehlerDifferential.D R S).toLinearMap,
      derivation_isDifferentialOperatorOfOrder_one (R := R) (S := S)
        (KaehlerDifferential.D R S)⟩

/-- Helper for Lemma 10.133.6: the represented map `P^1_{S/R}(S) → Ω[S⁄R]` sends `[s]` to
`d s`. -/
private theorem principalPartsSelfToCotangent_apply_class (s : S) :
    principalPartsSelfToCotangent (R := R) (S := S)
        (principalPartsClass R S S s) =
      KaehlerDifferential.D R S s := by
  -- Evaluate the representing identity on the universal generator `[s]`.
  let e := principal_parts_linear_map_equiv_differential_operators R S S 1 Ω[S⁄R]
  have h :
      (e (principalPartsSelfToCotangent (R := R) (S := S))).1 s =
        KaehlerDifferential.D R S s := by
    simpa [e, principalPartsSelfToCotangent] using
      congrArg (fun D : differential_operators_order_le R S S 1 Ω[S⁄R] => D.1 s)
        (e.apply_symm_apply
          ⟨(KaehlerDifferential.D R S).toLinearMap,
            derivation_isDifferentialOperatorOfOrder_one (R := R) (S := S)
              (KaehlerDifferential.D R S)⟩)
  change (e (principalPartsSelfToCotangent (R := R) (S := S))).1 s =
      KaehlerDifferential.D R S s
  exact h

/-- Helper for Lemma 10.133.6: for `M = S`, the represented cotangent retraction sends the
principal-parts commutator to right multiplication on `Ω[S⁄R]`. -/
private theorem principalPartsSelfToCotangent_comp_component (t : S) :
    (principalPartsSelfToCotangent (R := R) (S := S)).comp
        (Module.principalPartsCotangentComponent R S S t) =
      t • (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) := by
  -- Both sides are `Ω[S⁄R]`-linear maps, so it is enough to compare them on the generators `d s`.
  apply Derivation.liftKaehlerDifferential_unique
  ext s
  change (principalPartsSelfToCotangent (R := R) (S := S))
      ((Module.principalPartsCotangentComponent R S S t) (KaehlerDifferential.D R S s)) =
    (t • (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R])) (KaehlerDifferential.D R S s)
  rw [Module.principalPartsCotangentComponent_D, map_sub, map_smul,
    principalPartsSelfToCotangent_apply_class, principalPartsSelfToCotangent_apply_class]
  -- The derivation formula `d (s t) = s • d t + t • d s` isolates the desired right-multiple.
  have hs := congrArg (fun z => z - s • KaehlerDifferential.D R S t)
    ((KaehlerDifferential.D R S).leibniz s t)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs

/-- Helper for Lemma 10.133.6: the canonical map `Ω[S⁄R] ⊗[S] S → P^1_{S/R}(S)` is injective. -/
private theorem principalPartsCotangentToPrincipalParts_self_injective :
    Function.Injective (Module.principalPartsCotangentToPrincipalParts R S S) := by
  -- The represented map `P^1_{S/R}(S) → Ω[S⁄R]` is a left inverse after the canonical
  -- identification `Ω[S⁄R] ⊗[S] S ≃ Ω[S⁄R]`.
  have hret :
      (principalPartsSelfToCotangent (R := R) (S := S)).comp
          (Module.principalPartsCotangentToPrincipalParts R S S) =
        (TensorProduct.rid S Ω[S⁄R]).toLinearMap := by
    apply TensorProduct.ext'
    intro η t
    rw [LinearMap.comp_apply, Module.principalPartsCotangentToPrincipalParts_tmul]
    change (principalPartsSelfToCotangent (R := R) (S := S))
        ((Module.principalPartsCotangentComponent R S S t) η) = t • η
    simpa using
      LinearMap.congr_fun
        (principalPartsSelfToCotangent_comp_component (R := R) (S := S) t) η
  intro x y hxy
  let φ := Module.principalPartsCotangentToPrincipalParts R S S
  let ρ := principalPartsSelfToCotangent (R := R) (S := S)
  have hxy' : ((ρ.comp φ) x) = ((ρ.comp φ) y) := by
    simpa [LinearMap.comp_apply, φ, ρ] using congrArg ρ hxy
  have hxy'' : (TensorProduct.rid S Ω[S⁄R]).toLinearMap x =
      (TensorProduct.rid S Ω[S⁄R]).toLinearMap y := by
    rw [← hret]
    exact hxy'
  apply (TensorProduct.rid S Ω[S⁄R]).injective
  exact hxy''

/-- Helper for Lemma 10.133.6: the canonical map is injective on a free module presented as
finitely supported `S`-valued functions. -/
private theorem principalPartsCotangentToPrincipalParts_finsupp_injective :
    Function.Injective (Module.principalPartsCotangentToPrincipalParts R S (ι →₀ S)) := by
  classical
  intro x y hxy
  let φ := Module.principalPartsCotangentToPrincipalParts R S (ι →₀ S)
  let e := TensorProduct.finsuppScalarRight S S Ω[S⁄R] ι
  suffices hcoord : e x = e y by
    exact e.injective hcoord
  ext i
  -- Reduce to the `M = S` case by projecting to the `i`-th coordinate and using functoriality.
  have hnat := Module.principalPartsSequenceMap_comm₁₂ (R := R) (S := S)
    (M := ι →₀ S) (N := S) (Finsupp.lapply i)
  have hproj :
      (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) (Finsupp.lapply i)) x =
        (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) (Finsupp.lapply i)) y := by
    apply principalPartsCotangentToPrincipalParts_self_injective (R := R) (S := S)
    have hx := LinearMap.congr_fun hnat x
    have hy := LinearMap.congr_fun hnat y
    calc
      Module.principalPartsCotangentToPrincipalParts R S S
          ((TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) (Finsupp.lapply i)) x)
        = (principalPartsBaseChangeMap 1 (Finsupp.lapply i)) (φ x) := by
            simpa [LinearMap.comp_apply] using hx
      _ = (principalPartsBaseChangeMap 1 (Finsupp.lapply i)) (φ y) := by
            simpa [φ] using congrArg (principalPartsBaseChangeMap 1 (Finsupp.lapply i)) hxy
      _ = Module.principalPartsCotangentToPrincipalParts R S S
          ((TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) (Finsupp.lapply i)) y) := by
            simpa [LinearMap.comp_apply] using hy.symm
  -- The coordinate of `e` is exactly the right-tensor projection followed by `rid`.
  rw [show e x i =
      TensorProduct.AlgebraTensorModule.rid S S Ω[S⁄R] ((Finsupp.lapply i).lTensor Ω[S⁄R] x) by
        simpa [e] using
          (TensorProduct.finsuppScalarRight_apply (R := S) (S := S) (M := Ω[S⁄R]) (ι := ι) x i)]
  rw [show e y i =
      TensorProduct.AlgebraTensorModule.rid S S Ω[S⁄R] ((Finsupp.lapply i).lTensor Ω[S⁄R] y) by
        simpa [e] using
          (TensorProduct.finsuppScalarRight_apply (R := S) (S := S) (M := Ω[S⁄R]) (ι := ι) y i)]
  simpa [LinearMap.lTensor_def] using
    congrArg (TensorProduct.AlgebraTensorModule.rid S S Ω[S⁄R]) hproj

end SelfAndFree

/-- Helper for Lemma 10.133.6: the canonical free cover of an `S`-module by a free module on its
underlying set. -/
private abbrev principalPartsFreeCover
    (M : Type u) [AddCommGroup M] [Module S M] :
    (M →₀ S) →ₗ[S] M :=
  Finsupp.linearCombination S (id : M → M)

/-- Helper for Lemma 10.133.6: the kernel inclusion for the canonical free cover. -/
private abbrev principalPartsFreeCoverKernelInclusion
    (M : Type u) [AddCommGroup M] [Module S M] :
    LinearMap.ker (principalPartsFreeCover (S := S) M) →ₗ[S] (M →₀ S) :=
  (LinearMap.ker (principalPartsFreeCover (S := S) M)).subtype

/-- Helper for Lemma 10.133.6: the canonical free cover is surjective. -/
private theorem principalPartsFreeCover_surjective
    (M : Type u) [AddCommGroup M] [Module S M] :
    Function.Surjective (principalPartsFreeCover (S := S) M) := by
  -- The free cover sends the basis vector indexed by `m` to `m`, so every element is hit.
  simpa [principalPartsFreeCover] using
    (Finsupp.linearCombination_surjective (R := S) (v := (id : M → M))
      (fun m ↦ ⟨m, rfl⟩))

/-- Helper for Lemma 10.133.6: precomposition of first-order differential operators along an
`S`-linear source map. -/
private noncomputable def differentialOperatorsPrecompose
    {M N P : Type u}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    (f : M →ₗ[S] N) :
    differential_operators_order_le R S N 1 P →ₗ[S] differential_operators_order_le R S M 1 P :=
  { toFun := fun D ↦
      ⟨D.1.comp (f.restrictScalars R), by
        -- An `S`-linear source map is order `0`, so composing it with an order-`1` operator
        -- preserves the order bound.
        have hf₀ : (f.restrictScalars R).IsDifferentialOperatorOfOrder S 0 := by
          rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
          intro s m
          simpa using f.map_smul s m
        simpa [Nat.zero_add] using LinearMap.isDifferentialOperatorOfOrder_comp hf₀ D.2⟩
    map_add' := by
      intro D E
      ext m
      rfl
    map_smul' := by
      intro s D
      ext m
      rfl }

/-- Helper for Lemma 10.133.6: source precomposition evaluates by ordinary composition on the
underlying `R`-linear maps. -/
private theorem differentialOperatorsPrecompose_apply
    {M N P : Type u}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    (f : M →ₗ[S] N) (D : differential_operators_order_le R S N 1 P) (m : M) :
    ((differentialOperatorsPrecompose (R := R) (S := S) (P := P) f D : M →ₗ[R] P) m) =
      (D : N →ₗ[R] P) (f m) := by
  rfl

namespace Module

section FreeCoverDescent

variable (M N : Type u)
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Helper for Lemma 10.133.6: the represented differential operator attached to a map out of
`P^1_{S/R}(M)` evaluates on the universal class `[m]` by applying that map to `[m]`. -/
private theorem principal_parts_linear_map_equiv_symm_apply_class
    {P : Type u} [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    (D : differential_operators_order_le R S M 1 P) (m : M) :
    (principal_parts_linear_map_equiv_differential_operators R S M 1 P).symm D
      (principalPartsClass R S M m) = D.1 m := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M 1 P
  -- Evaluate the identity `e (e.symm D) = D` on `m`.
  have h : (e (e.symm D)).1 m = D.1 m := by
    simpa using
      congrArg (fun E : differential_operators_order_le R S M 1 P ↦ E.1 m)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 m = D.1 m
  exact h

/-- Helper for Lemma 10.133.6: the represented differential operator attached to a map out of
`P^1_{S/R}(M)` evaluates on the universal class `[m]` by applying that map to `[m]`. -/
private theorem principal_parts_linear_map_equiv_differential_operators_apply_class
    {P : Type u} [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    (L : P^{1}_{S⁄R}(M) →ₗ[S] P) (m : M) :
    ((principal_parts_linear_map_equiv_differential_operators R S M 1 P L).1 m) =
      L (principalPartsClass R S M m) := by
  -- Route correction: evaluate the representing equivalence on the universal class by reducing to
  -- the already proved formula for `e.symm`.
  let e := principal_parts_linear_map_equiv_differential_operators R S M 1 P
  simpa [e] using
    (principal_parts_linear_map_equiv_symm_apply_class (R := R) (S := S) (M := M)
      (P := P) (D := e L) m).symm

/-- Helper for Lemma 10.133.6: if `f : M → N` is surjective, then the induced map
`P^1_{S/R}(M) → P^1_{S/R}(N)` is surjective. -/
private theorem principalPartsBaseChange_surjective_of_surjective
    (f : M →ₗ[S] N) (hf : Function.Surjective f) :
    Function.Surjective (principalPartsBaseChangeMap 1 f :
      P^{1}_{S⁄R}(M) →ₗ[S] P^{1}_{S⁄R}(N)) := by
  intro y
  obtain ⟨m, hm⟩ := hf ((principalPartsProjection R S N) y)
  let y₀ := y - principalPartsClass R S N (f m)
  have hy₀ : principalPartsProjection R S N y₀ = 0 := by
    -- Subtract a lift of the projected class to reduce to the kernel of the projection row.
    dsimp [y₀]
    rw [map_sub, principalPartsProjection_apply_class, hm]
    simp
  obtain ⟨t, ht⟩ := (principalPartsSequence_exact R S N y₀).mp hy₀
  have htensor_surj :
      Function.Surjective
        (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f) := by
    -- Tensoring with `Ω[S⁄R]` preserves surjectivity on the source variable.
    simpa [LinearMap.lTensor_def] using LinearMap.lTensor_surjective (Ω[S⁄R]) hf
  obtain ⟨u, hu⟩ := htensor_surj t
  refine ⟨principalPartsClass R S M m +
      principalPartsCotangentToPrincipalParts R S M u, ?_⟩
  have hcomm := LinearMap.congr_fun (principalPartsSequenceMap_comm₁₂ R S M N f) u
  have hcomm' :
      (principalPartsBaseChangeMap 1 f)
          (principalPartsCotangentToPrincipalParts R S M u) =
        (principalPartsCotangentToPrincipalParts R S N)
          ((TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f) u) := by
    simpa [LinearMap.comp_apply] using hcomm.symm
  -- Rebuild `y` from the chosen class lift and the lifted tensor correction term.
  calc
    (principalPartsBaseChangeMap 1 f)
        (principalPartsClass R S M m + principalPartsCotangentToPrincipalParts R S M u)
      = principalPartsClass R S N (f m) +
          (principalPartsCotangentToPrincipalParts R S N)
            ((TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f) u) := by
              rw [map_add, principalPartsBaseChangeMap_apply_class, hcomm']
    _ = principalPartsClass R S N (f m) + y₀ := by rw [hu, ht]
    _ = y := by
      dsimp [y₀]
      abel

/-- Helper for Lemma 10.133.6: source precomposition of first-order differential operators is
exact for the canonical free cover `ker π ↪ (M →₀ S) ⟶ M`. -/
private theorem differentialOperatorsPrecompose_exact_of_free_cover
    {P : Type u} [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P] :
    let π : (M →₀ S) →ₗ[S] M := principalPartsFreeCover (S := S) M
    let i : LinearMap.ker π →ₗ[S] (M →₀ S) := principalPartsFreeCoverKernelInclusion (S := S) M
    Function.Exact
      (differentialOperatorsPrecompose (R := R) (S := S) (P := P) π)
      (differentialOperatorsPrecompose (R := R) (S := S) (P := P) i) := by
  -- TODO: descend the underlying `R`-linear map across `ker π ↪ (M →₀ S) ⟶ M`, then descend each
  -- scalar commutator across the same exact sequence on `S`-linear maps to recover the order-`1`
  -- condition on the descended map.
  sorry

/-- Helper for Lemma 10.133.6: the middle principal-parts column for the canonical free cover is
exact. -/
private theorem principalPartsBaseChange_exact_of_free_cover :
    let π : (M →₀ S) →ₗ[S] M := principalPartsFreeCover (S := S) M
    let i : LinearMap.ker π →ₗ[S] (M →₀ S) := principalPartsFreeCoverKernelInclusion (S := S) M
    Function.Exact
      (principalPartsBaseChangeMap 1 i :
        P^{1}_{S⁄R}(LinearMap.ker π) →ₗ[S] P^{1}_{S⁄R}(M →₀ S))
      (principalPartsBaseChangeMap 1 π :
        P^{1}_{S⁄R}(M →₀ S) →ₗ[S] P^{1}_{S⁄R}(M)) := by
  -- TODO: apply `exact_iff_exact_hom_into` to the middle column and transport the exactness from
  -- `differentialOperatorsPrecompose_exact_of_free_cover` using the class-evaluation lemma proved
  -- above.
  sorry

/-- Helper for Lemma 10.133.6: the canonical tensor map is injective, by descending from the
canonical free cover exactly as in the source proof. -/
private theorem principalPartsCotangentToPrincipalParts_injective_of_free_cover_descent :
    Function.Injective (principalPartsCotangentToPrincipalParts R S M) := by
  -- TODO: after `principalPartsBaseChange_exact_of_free_cover` is available, run the textbook
  -- three-row chase: lift to the free row, cross the exact middle column, descend through the `K`
  -- row, then kill the remaining tensor by free-row injectivity and `π ∘ i = 0`.
  sorry

end FreeCoverDescent

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
    (Module.principalPartsSequence R S M).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    -- Reuse the row exactness extracted above so the remaining work is isolated in the mono step.
    exact Module.principalPartsSequence_exact R S M
  · exact (ModuleCat.mono_iff_injective _).2 <|
      Module.principalPartsCotangentToPrincipalParts_injective_of_free_cover_descent
        (R := R) (S := S) (M := M)
  · exact (ModuleCat.epi_iff_surjective _).2 (Module.principalPartsProjection_surjective R S M)

end Main

end
