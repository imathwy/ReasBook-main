import stacks_proof.stacks_project.Chap10.Lemma_10_99_11.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits IsLocalRing
open scoped TensorProduct Pointwise

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling for Lemma 10.99.11:
- primary domain: flatness of a finite module over a Noetherian base, detected primewise after
  localizing the target ring and using flatness of the quotient modules by ideal powers;
- sampled owner declarations in the same domain:
  `Module.Flat`,
  `LocalizedModule.AtPrime`,
  `flat_iff_flat_localizedModule_atPrime_over_under`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
- best owner abstraction: the public conclusions belong on the canonical flatness owner
  `Module.Flat`, with `LocalizedModule.AtPrime` as the prime-local view and
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal` as the local owner theorem reused in the
  proof;
- primitive data: the ideal `I`, the prime `q` containing `IS`, and the hypothesis that every
  quotient `M / I^n M` is flat over `R / I^n`;
- derived API: flatness of `M_q` over `R`, and the local-ring specialization obtained by taking
  the unique closed point.

Source/core/bridge triage:
- `source-facing`: the Stacks prime-local flatness criterion and its local-ring specialization;
- `core/canonical`: `Module.Flat`, `LocalizedModule.AtPrime`,
  `flat_iff_flat_localizedModule_atPrime_over_under`, and
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
- `bridge/view`: Lemma `10.51.5` supplies the annihilation-after-localization step needed to turn
  the quotient-flatness hypotheses into the Tor-vanishing input of the local criterion, and the
  local-ring theorem is the closed-point specialization of the prime-local statement.
-/

-- Proof sketch: localize at `q` and apply the variant of the local criterion from Lemma
-- `10.99.10` over the local map `R_(q ∩ R) → S_q`. The hypothesis on all quotients `M / I^n M`
-- gives flatness modulo powers after localization, Remark `10.75.9` identifies the relevant
-- `Tor₁` group with the kernel of `I ⊗ M → M`, and Lemma `10.51.5` kills that kernel after
-- localizing at `q`.
/-- Helper for the flatness criterion: flatness over the localized quotient base transfers across
the denominator comparison to the textbook closed fiber over `R_(q ∩ R) ⧸ J`. -/
lemma localized_closed_fiber_flat_over_target_quotient_from_mapped_target
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
    letI : Module Lbase TgtS :=
      localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
    Module.Flat Lbase TgtS →
      Module.Flat (Rp ⧸ J) (Mq ⧸ (J • (⊤ : Submodule Rp Mq))) := by
  -- Proof comment: the support file contains the implementation; this wrapper keeps the
  -- item label attached to Agent C's planned declaration.
  exact
    localized_closed_fiber_flat_over_target_quotient_from_mapped_target_core
      (R := R) (S := S) (M := M) I q hq

/-- Chap10 Lemma 10 99 11: let `R → S` be a ring map, let `I` be an ideal of `R`, and let `M`
be a finite `S`-module. Assume `R` and `S` are Noetherian and that `M / I^n M` is flat over
`R / I^n` for every `n ≥ 1`. Then for every prime `q` of `S` containing `IS`, the localization
`M_q` is flat over `R`. -/
@[stacks 0523]
theorem flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : FlatQuotientsByIdealPowers M I) :
    Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := by
  -- Route correction: the intended proof keeps the source kernel
  -- `K = ker(I ⊗[R] M → M)`, proves `K ≤ I^n (I ⊗[R] M)` by passing to the stage
  -- `(I / I^(n+1)) ⊗_{R / I^(n+1)} (M / I^(n+1) M)`, then localizes at `q` and applies
  -- Lemma `10.99.10` over `R_(q ∩ R)`.
  let p : Ideal R := q.asIdeal.under R
  let Rp := Localization.AtPrime p
  let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let f : Rp →+* Sq :=
    Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  letI : Algebra Rp Sq := f.toAlgebra
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  have hJ_ne : J ≠ ⊤ := by
    -- Proof comment: because `q` contains `IS`, the under-prime `p = q ∩ R` contains `I`, so the
    -- localized ideal `J = I R_p` is still proper.
    simpa [p, Rp, J] using
      localized_under_ideal_ne_top_at_prime
        (R := R) (S := S) I q hq
  have hsourceKerBot :
      (LinearMap.ker (source_tensor_to_module (R := R) (S := S) (M := M) I)).localized
          q.asIdeal.primeCompl = ⊥ := by
    -- Proof comment: the new helper packages the source-faithful Artin-Rees/Krull-intersection
    -- step directly on `K = ker(I ⊗[R] M → M)`.
    simpa using
      localized_source_tensor_kernel_eq_bot_at_prime
        (R := R) (S := S) (M := M) I q hq hflat
  have hsourceInj :
      Function.Injective
        (LocalizedModule.map q.asIdeal.primeCompl
          (source_tensor_to_module (R := R) (S := S) (M := M) I)) := by
    -- Proof comment: the localized source map is injective because its localized kernel is zero.
    simpa using
      localized_source_multiplication_injective_at_prime
        (R := R) (S := S) (M := M) I q hq hflat
  let eIdeal :
      LocalizedModule.AtPrime p I ≃ₗ[R] J := by
    -- Proof comment: normalize the localized ideal owner to the extended ideal inside `R_p`.
    simpa [p, Rp, J] using
      localized_under_ideal_linearEquiv_mapped_ideal
        (R := R) (S := S) I q
  let eTensor :
      LocalizedModule.AtPrime q.asIdeal M ⊗[R] LocalizedModule.AtPrime p I
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) := by
    -- Proof comment: this is the canonical `N_q ⊗[R] P_(q ∩ R) ≃ (N ⊗[R] P)_q` bridge needed
    -- for the source-owner comparison.
    simpa [p] using
      localized_tensorProduct_right_localized_linearEquiv
        (R := R) (S := S) (N := M) (P := I) q
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) := by
    -- Proof comment: localizing the tensor swap `I ⊗ M ≃ M ⊗ I` gives the corresponding local
    -- source-owner comparison.
    exact
      localized_linearEquiv_atPrime (S := S) q
        ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eOwner :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R] J ⊗[Rp] Mq := by
    -- Proof comment: the localized source owner has now been packaged into the canonical tensor
    -- owner `J ⊗[Rp] Mq`; the remaining gap is only to check the multiplication map on
    -- generators.
    simpa [p, Rp, Sq, J, Mq, f] using
      localized_source_tensor_owner_equiv_under_ideal_tensor
        (R := R) (S := S) (M := M) I q
  -- TODO: compare the injective localized source map above with the `Rp`-local multiplication map
  -- `J ⊗[Rp] Mq → Mq` from Remark `10.75.9`, and transport `hflat 1 (by simp)` to the closed
  -- fiber `Mq ⧸ J Mq` over `Rp ⧸ J`. The universe-stable local-criterion wrapper is now
  -- available below, so the remaining gap is entirely the two localization transports.
  --
  -- The remaining Lean blocker is now theorem-local and precise:
  -- 1. prove the pure-tensor formula for `eOwner.symm` and use it to conjugate the localized
  --    source multiplication map to the canonical map `J ⊗[Rp] Mq → Mq`;
  -- 2. transport `hflat 1 (by simp)` to the quotient owner over `Rp ⧸ J`;
  -- 3. feed those two bridges into the local criterion in a universe-compatible way.
  let _ := Rp
  let _ := J
  let _ := Mq
  let _ := hJ_ne
  let _ := hsourceKerBot
  let _ := hsourceInj
  let _ := eIdeal
  let _ := eTensor
  let _ := eComm
  let _ := eOwner
  haveI : IsLocalHom (algebraMap Rp Sq) := by
    -- Proof comment: the induced map `R_(q ∩ R) → S_q` is the canonical local ring hom above `R → S`.
    simpa [Rp, Sq, f] using
      Localization.isLocalHom_localRingHom p q.asIdeal (algebraMap R S) rfl
  have hμRp :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul Rp Mq).comp J.subtype)) := by
    let eSource :
        LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R] I ⊗[R] Mq :=
      localized_source_tensor_owner_equiv_source_ideal_tensor
        (R := R) (S := S) (M := M) I q
    let μRq : I ⊗[R] Mq →ₗ[R] Mq :=
      TensorProduct.lift ((LinearMap.lsmul R Mq).comp I.subtype)
    have hμRq :
        Function.Injective μRq := by
      have hcompare :
          μRq.comp eSource.toLinearMap =
            (LocalizedModule.map q.asIdeal.primeCompl
              (source_tensor_to_module (R := R) (S := S) (M := M) I)).restrictScalars R := by
        -- Proof comment: first transport the localized source multiplication map to the simpler
        -- owner `I ⊗[R] M_q`.
        simpa [eSource, μRq] using
          localized_source_tensor_map_conjugates_to_source_ideal_multiplication
            (R := R) (S := S) (M := M) I q
      -- Proof comment: injectivity is already known for the localized source multiplication map,
      -- so transport it across the canonical owner equivalence.
      exact injective_of_ladder_linearEquiv
        (A := R)
        (f := (LocalizedModule.map q.asIdeal.primeCompl
          (source_tensor_to_module (R := R) (S := S) (M := M) I)).restrictScalars R)
        (g := μRq)
        (eP := eSource)
        (eQ := LinearEquiv.refl R Mq)
        hcompare
        (by simpa using hsourceInj)
    -- Proof comment: then extend the left ideal from `I ⊂ R` to `J = I R_p` and descend
    -- injectivity through the canonical tensor bridge to the truly local owner.
    simpa [p, Rp, J, Mq] using
      mapped_ideal_tensor_to_module_injective_of_source_injective
        (A := R) (B := Rp) (I := I) (N := Mq) hμRq
  have hflatClosedFiber :
      Module.Flat (Rp ⧸ J) (Mq ⧸ (J • (⊤ : Submodule Rp Mq))) := by
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
    have hflatQ : Module.Flat Abar Qbar := by
      -- Proof comment: the stage `n = 1` of the hypothesis is exactly the quotient closed fiber
      -- `Qbar = M / ISM`, viewed over `Abar = R / I`.
      have hflatSource :
          Module.Flat Abar (M ⧸ (I • (⊤ : Submodule R M))) := by
        have hflatSourcePow :
            Module.Flat (R ⧸ I ^ 1) (M ⧸ (I ^ 1 • (⊤ : Submodule R M))) :=
          hflat 1 (by simp)
        have hI1 : I ^ 1 = I := by simp
        rw [hI1] at hflatSourcePow
        simpa [Abar] using hflatSourcePow
      have hdenom :
          (I • (⊤ : Submodule R M)) =
            ((IS • (⊤ : Submodule S M)).restrictScalars R) := by
        simpa [IS] using
          smul_top_eq_mapped_ideal_restrictScalars (R := R) (S := S) (M := M) I
      let e0 : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R]
          (M ⧸ ((IS • (⊤ : Submodule S M)).restrictScalars R)) :=
        Submodule.quotEquivOfEq _ _ hdenom
      let e1 : (M ⧸ ((IS • (⊤ : Submodule S M)).restrictScalars R)) ≃ₗ[R] Qbar :=
        (Submodule.Quotient.restrictScalarsEquiv R (IS • (⊤ : Submodule S M))).symm
      let eR : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R] Qbar := e0.trans e1
      let eA : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[Abar] Qbar :=
        eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      exact Module.Flat.of_linearEquiv eA.symm
    -- Proof comment: the remaining closed-fiber tail has been factored into a dedicated helper so
    -- the theorem body only records the source-faithful reduction to the packaged transport.
    simpa [IS, Abar, Qbar, p, Rp, J, Mq] using
      localized_closed_fiber_flat_over_target_quotient
        (R := R) (S := S) (M := M) I q hq hflatQ
  have hflatRp : Module.Flat Rp Mq := by
    -- Proof comment: once the two localized inputs are in the exact owner expected by the local
    -- criterion, the universe-stable wrapper around Lemma `10.99.10` gives flatness over `Rp`.
    exact
      flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal_univ
        (A := Rp) (B := Sq) (N := Mq) J hJ_ne hμRp hflatClosedFiber
  -- Proof comment: `M_q` is flat over `R` exactly when it is flat over the localization `R_p`.
  exact
    (Module.flat_iff_of_isLocalization Rp p.primeCompl (M := Mq)).mp hflatRp

/-- If the target ring `S` is local and `IS` is contained in its maximal ideal, then `M` is flat
over `R` under the same quotient-flatness hypotheses. -/
theorem flat_of_isLocalRing_and_flat_quotients_by_ideal_powers
    [IsLocalRing S] (I : Ideal R) (hI : I.map (algebraMap R S) ≤ maximalIdeal S)
    (hflat : FlatQuotientsByIdealPowers M I) :
    Module.Flat R M := by
  let q : PrimeSpectrum S := ⟨maximalIdeal S, inferInstance⟩
  have hflatLoc :
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := by
    -- Proof comment: apply the prime-local theorem at the closed point of the local ring `S`.
    exact
      flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers
        (R := R) (S := S) (M := M) I q (by simpa [q] using hI) hflat
  have hunits :
      (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := by
    -- Proof comment: over a local ring, every element outside the maximal ideal is a unit.
    intro x hx
    simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] using hx
  letI : IsLocalization (maximalIdeal S).primeCompl S := IsLocalization.self hunits
  letI :
      IsLocalizedModule (maximalIdeal S).primeCompl (LinearMap.id : M →ₗ[S] M) :=
    isLocalizedModule_id (S := (maximalIdeal S).primeCompl) (R := S) (M := M) S
  let eLoc :
      LocalizedModule.AtPrime (maximalIdeal S) M ≃ₗ[S] M := by
    -- Proof comment: localizing an `S`-module at the maximal ideal of a local ring gives back the
    -- original module.
    simpa [LocalizedModule.AtPrime] using
      (IsLocalizedModule.iso (maximalIdeal S).primeCompl (LinearMap.id : M →ₗ[S] M))
  have hflatLoc' :
      Module.Flat R (LocalizedModule.AtPrime (maximalIdeal S) M) := by
    simpa [q] using hflatLoc
  -- Proof comment: transport flatness across the localization-collapse equivalence.
  exact Module.Flat.of_linearEquiv (eLoc.restrictScalars R).symm

end
