import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_10
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_15
import StacksProject_2024.stacks_project.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open CategoryTheory.Limits
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type x}
variable [CommRing R] [CommRing S]
variable [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M]
variable [IsScalarTower R S M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/- Domain-style sampling for the Noetherian fiberwise flatness criterion:
* primary domain: flatness of modules and algebra maps across local homomorphisms of Noetherian
  local rings, with the closed fiber carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Ideal.Fiber`,
  `length_base_change_eq_length_mul_closed_fiber`,
  `free_of_flat_of_free_closedFiber`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`;
* best owner abstraction: flatness lives on the canonical owners `Module.Flat`,
  `Module.FaithfullyFlat`, and `RingHom.Flat`, while the closed fiber and the fiber module belong
  on the owners `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] M`; the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` is only a bridge to
  the local criterion `10.99.10`.

Primitive data vs. derived API:
* primitive data: the local diagram `R → S → S'`, the finite nonzero `S'`-module `M`, flatness of
  `M` over `R`, and flatness of the canonical closed-fiber module `ClosedFiberModule` over
  `ClosedFiber`;
* derived API: flatness of `M` over `S`, faithful flatness of `M` over `S`, and then flatness of
  the algebra map `R → S`.

Source/core/bridge triage:
* `source-facing`: the two Stacks statements below;
* `core/canonical`: the owner predicates `Module.Flat`, `Module.FaithfullyFlat`, and
  `RingHom.Flat`, together with the canonical closed-fiber ring/module owners `ClosedFiber` and
  `ClosedFiberModule`;
* `bridge/view`: the quotient presentation of the closed fiber
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and of the fiber module
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`.
-/

-- Proof sketch: apply the variant of the local criterion for flatness to the local homomorphism
-- `S → S'` and the ideal `Ideal.map (algebraMap R S) (maximalIdeal R) ⊂ S`. The canonical
-- hypothesis that `ClosedFiberModule = ClosedFiber ⊗[S] M` is flat over
-- `ClosedFiber = (maximalIdeal R).Fiber S` is transported internally to the quotient presentation
-- needed by Lemma `10.99.10`, while flatness of `M` over `R` identifies the required
-- `Tor₁^S(S / 𝔪_R S, M)` vanishing via the injectivity argument from the textbook and Remark
-- `10.75.9`.
/-- Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): for local homomorphisms
`R → S → S'` of Noetherian local rings and a finite nonzero `S'`-module `M`, if the closed fiber
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is flat over the
closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, and `M` is flat over `R`, then `M` is flat
over `S`. -/
theorem flat_over_middleRing_of_flat_closedFiber_and_flat_over_base
    (S' : Type w) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing S'] [IsLocalHom (algebraMap S S')] [IsNoetherianRing S']
    [Module S' M] [IsScalarTower S S' M] [IsScalarTower R S' M] [Module.Finite S' M]
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    Module.Flat S M := by
  sorry

-- Proof sketch: the main theorem gives flatness of `M` over `S`. Using that `M` is finite over the local
-- ring `S'` and nonzero, Nakayama gives a nonzero residue-field fiber over `S'`; the closed-fiber
-- flatness hypothesis then forces `M / maximalIdeal S • ⊤` to be nontrivial, so Lemma `10.39.15`
-- yields faithful flatness of `M` over `S`. Finally apply the descent lemma saying that an
-- `S`-module which is flat over `R` and faithfully flat over `S` forces `R → S` to be flat.
/-- Under the same closed-fiber flatness and base-flatness hypotheses, the local homomorphism
`R → S` is flat. -/
theorem algebraMap_flat_of_flat_closedFiber_and_flat_over_base
    (S' : Type w) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing S'] [IsLocalHom (algebraMap S S')] [IsNoetherianRing S'] [Module S' M]
    [IsScalarTower S S' M] [IsScalarTower R S' M] [Module.Finite S' M] [Nontrivial M]
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    (algebraMap R S).Flat := by
  have hflat_S : Module.Flat S M :=
    flat_over_middleRing_of_flat_closedFiber_and_flat_over_base S' hflat_closedFiber hflat_R
  letI : Module.Flat S M := hflat_S
  let P' : Submodule S' M := maximalIdeal S' • (⊤ : Submodule S' M)
  let P : Submodule S M := P'.restrictScalars S
  have hquot_P' : Nontrivial (M ⧸ P') := by
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    have hmax_jac : maximalIdeal S' ≤ Ring.jacobson S' := by
      simp [IsLocalRing.ringJacobson_eq_maximalIdeal]
    have hsub : Subsingleton M :=
      subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
        (maximalIdeal S') htop hmax_jac
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  have hquot_P : Nontrivial (M ⧸ P) :=
    (Submodule.Quotient.restrictScalarsEquiv S P').surjective.nontrivial
  have hsmul : maximalIdeal S • (⊤ : Submodule S M) ≤ P := by
    refine Submodule.smul_le.2 fun a ha m hm ↦ ?_
    change a • m ∈ P'.restrictScalars S
    change a • m ∈ P'
    rw [← IsScalarTower.algebraMap_smul S' a m]
    have hmem_map : algebraMap S S' a ∈ Ideal.map (algebraMap S S') (maximalIdeal S) :=
      Ideal.mem_map_of_mem _ ha
    have hmem : algebraMap S S' a ∈ maximalIdeal S' :=
      (IsLocalRing.map_maximalIdeal_le (algebraMap S S')) hmem_map
    exact
      Submodule.smul_mem_smul hmem (by simp)
  have hquot_S : Nontrivial (M ⧸ (maximalIdeal S • (⊤ : Submodule S M))) :=
    (Submodule.factor_surjective hsmul).nontrivial
  have hff_S : Module.FaithfullyFlat S M := by
    refine
      faithfullyFlat_iff_forall_nontrivial_tensor_residueField.2 fun m hm ↦ ?_
    have hm_eq : m = maximalIdeal S := IsLocalRing.eq_maximalIdeal hm
    subst hm_eq
    exact
      (nontrivial_tensor_residueField_iff_nontrivial_quotSMul (maximalIdeal S)).2 hquot_S
  -- The remaining step is exactly the owner descent theorem `10.39.10`.
  sorry

end
