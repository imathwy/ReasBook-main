import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_103_6
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_163_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Ideal.Quotient (eq_zero_iff_mem)
open scoped ENat TensorProduct nonZeroDivisors

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {k : ℕ}
variable [SerreConditionS R k] [IsNoetherianRing S] [Module.Flat R S]

/-
Domain-style sampling pass:
* primary domain: Serre's condition `(S_k)` in commutative algebra under flat base change and
  fiberwise hypotheses;
* sampled owner declarations:
  - `SerreConditionS`, the chapter owner for the ring-theoretic `(S_k)` condition from
    `Definition_10_157_1.lean`;
  - `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`, the primewise localized depth bound
    already derived from that owner;
  - `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
    the local fiber-dimension formula from `Lemma_10.112.7.lean`.

Best owner abstraction:
* the public statement should stay on the canonical ring owner `SerreConditionS`;
* the canonical fiber input is `p.asIdeal.Fiber S`;
* the local ring `fiberLocalRingAt R S q` is supporting bridge data for the proof, not a second
  public owner.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the owner hypothesis `[SerreConditionS R k]`, the
  Noetherian target hypothesis on `S`, and the fiberwise owner hypothesis `hfiber`;
* derived API: the localized depth inequalities, the closed-fiber depth formula, and the
  local-fiber dimension formula used to verify the defining primewise inequality for
  `SerreConditionS S k`.

Source/core/bridge triage:
* `source-facing`: `serreConditionS_of_flat_of_fiber`, the textbook ascent statement for `(S_k)`;
* `core/canonical`: `SerreConditionS` together with its primewise localized depth theorem;
* `bridge/view`: the local flat map `R_(q ∩ R) → S_q`, its closed fiber, and the canonical local
  fiber ring `fiberLocalRingAt R S q`.
-/

/-- Helper for Lemma 10.163.4: localizing the self-module `R` at a prime ideal agrees with the
localized ring itself. -/
noncomputable abbrev localized_self_linearEquiv (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p R ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl R).trans
    (Algebra.TensorProduct.rid R (Localization.AtPrime p) (Localization.AtPrime p)).toLinearEquiv

/-- Helper for Lemma 10.163.4: localizing `R → S` at `p = q ∩ R` and `q` gives a flat local map
`R_p → S_q`. -/
lemma localized_algebraMap_flat_local_at_under (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat ∧
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have halg :
      Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S)
          (q.asIdeal.over_def p.asIdeal) =
        algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      rw [← IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal) x]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal) x]
  have hflatRS : (algebraMap R S).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat :
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat := by
    -- Proof comment: flatness survives localization along the canonical local ring map.
    simpa [halg] using
      (RingHom.Flat.localRingHom hflatRS q.asIdeal p.asIdeal (q.asIdeal.over_def p.asIdeal))
  have hlocal :
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: the universal localized map is local by construction.
    simpa [halg] using
      (Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal
        (algebraMap R S) (q.asIdeal.over_def p.asIdeal))
  exact ⟨hflat, hlocal⟩

/-- Helper for Lemma 10.163.4: elements of `pS` vanish in the fiber ring `κ(p) ⊗[R] S`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map_at_under (p : PrimeSpectrum R) {x : S}
    (hx : x ∈ Ideal.map (algebraMap R S) p.asIdeal) :
    algebraMap S (p.asIdeal.Fiber S) x = 0 := by
  let φ : (R ⧸ p.asIdeal) ⊗[R] S →+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x :
        S ⧸ Ideal.map (algebraMap R S) p.asIdeal) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : R ⧸ p.asIdeal) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal
    have hx' :
        e (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x) =
          (1 : R ⧸ p.asIdeal) ⊗ₜ[R] x := rfl
    rw [← hx', hquot]
    simp [e]
  have hφ : φ ((1 : R ⧸ p.asIdeal) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  simpa [φ] using hφ

/-- Helper for Lemma 10.163.4: the quotient `S / pS` acts canonically on the fiber ring over
`p`. -/
private noncomputable instance fiberQuotientAlgebra_at_under (p : PrimeSpectrum R) :
    Algebra (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (p.asIdeal.Fiber S) :=
  (Ideal.Quotient.liftₐ (Ideal.map (algebraMap R S) p.asIdeal)
    (Algebra.ofId S (p.asIdeal.Fiber S))
    (fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map_at_under (R := R) (S := S) p hx)).toRingHom.toAlgebra

/-- Helper for Lemma 10.163.4: the class of `s : S` in `S / pS` maps to the pure tensor
`1 ⊗ s` in the fiber ring over `p`. -/
private theorem quotient_to_fiber_algebraMap_mk_at_under (p : PrimeSpectrum R) (s : S) :
    algebraMap (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (p.asIdeal.Fiber S)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) s) =
        1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Lemma 10.163.4: the quotient-base-changed fiber presentation recovers the usual
fiber ring over `p` as an algebra over `S / pS`. -/
private noncomputable def fiber_tensor_over_quotient_algEquiv_at_under (p : PrimeSpectrum R) :
    (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) ⊗[R ⧸ p.asIdeal] p.asIdeal.ResidueField ≃ₐ[
      S ⧸ Ideal.map (algebraMap R S) p.asIdeal] p.asIdeal.Fiber S :=
  let eRing :
      (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) ⊗[R ⧸ p.asIdeal] p.asIdeal.ResidueField ≃+*
        p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.commRight (R ⧸ p.asIdeal)
      (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) p.asIdeal.ResidueField).toRingEquiv.trans
      ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField]
            p.asIdeal.ResidueField)
          (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal)).trans
        (Algebra.TensorProduct.cancelBaseChange R (R ⧸ p.asIdeal) p.asIdeal.ResidueField
          p.asIdeal.ResidueField S)).toRingEquiv
  { toRingEquiv := eRing
    commutes' := by
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Proof comment: both quotient-side and tensor-side algebra maps send `s mod pS`
      -- to the same pure tensor `1 ⊗ s`.
      simpa [eRing, quotient_to_fiber_algebraMap_mk_at_under (R := R) (S := S) p s,
        Algebra.TensorProduct.cancelBaseChange_tmul] }

/-- Helper for Lemma 10.163.4: the fiber ring over `p` is the localization of `S / pS` at the
image of the nonzerodivisors of `R / p`. -/
private noncomputable def fiber_quotient_localization_algEquiv_at_under (p : PrimeSpectrum R) :
    Localization
        (Algebra.algebraMapSubmonoid
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (nonZeroDivisors (R ⧸ p.asIdeal))) ≃ₐ[
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal)] p.asIdeal.Fiber S :=
  -- Proof comment: this is the source proof's standard presentation
  -- `(S / pS)[(R / p)^\times] ≃ κ(p) ⊗[R] S`.
  ((Localization.tensorLeftAlgEquiv
      (nonZeroDivisors (R ⧸ p.asIdeal))
      (S ⧸ Ideal.map (algebraMap R S) p.asIdeal)).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl :
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) ≃ₐ[
            S ⧸ Ideal.map (algebraMap R S) p.asIdeal]
              (S ⧸ Ideal.map (algebraMap R S) p.asIdeal))
        (IsLocalization.algEquiv
          (nonZeroDivisors (R ⧸ p.asIdeal))
          (Localization (nonZeroDivisors (R ⧸ p.asIdeal)))
          p.asIdeal.ResidueField))).trans
    (fiber_tensor_over_quotient_algEquiv_at_under (R := R) (S := S) p)

/-- Helper for Lemma 10.163.4: quotienting by `I ≤ q` sends the prime complement of `q`
to the induced prime complement in the quotient. -/
private lemma quotient_primeCompl_eq_algebraMapSubmonoid_at_under
    {A : Type*} [CommRing A] (I q : Ideal A) [q.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk I) q).IsPrime] (hIq : I ≤ q) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk I) q).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Proof comment: if `a mod I` landed in the quotient prime, pulling back along the quotient
    -- map would force `a ∈ q`, contradicting `a ∉ q`.
    change Ideal.Quotient.mk I a ∉ Ideal.map (Ideal.Quotient.mk I) q
    intro hx
    have hqx : a ∈ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) := by
      exact hx
    exact ha <| by simpa [Ideal.comap_map_mk hIq] using hqx
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_, rfl⟩
    -- Proof comment: conversely, if `a mod I` avoids the quotient prime, then `a` itself already
    -- avoids `q`.
    intro ha
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha)

/-- Helper for Lemma 10.163.4: the quotient presentation `S_q / (q ∩ R)S_q` identifies with the
canonical fiber local ring at `q`. -/
private noncomputable def localized_quotient_ringEquiv_fiberLocalRingAt
    (q : PrimeSpectrum S) :
    ((Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) ≃+*
        fiberLocalRingAt R S q := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let I : Ideal S := Ideal.map (algebraMap R S) p.asIdeal
  let Qloc :=
    (Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I
  have hQloc :
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    -- Proof comment: extending `p` to `S` and then localizing is the same as extending `p`
    -- directly to `S_q`.
    dsimp [I]
    simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)] using
      (Ideal.map_map (I := p.asIdeal) (f := algebraMap R S)
        (g := algebraMap S (Localization.AtPrime q.asIdeal)))
  let eTarget :
      Qloc ≃+*
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal) :=
    Ideal.quotEquivOfEq hQloc
  have hqbarPrime : (Ideal.map (Ideal.Quotient.mk I) q.asIdeal).IsPrime := by
    have hI_le_q : I ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [I, p, PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective <| by
        simpa [Ideal.mk_ker] using hI_le_q
  let qbar : PrimeSpectrum (S ⧸ I) :=
    ⟨Ideal.map (Ideal.Quotient.mk I) q.asIdeal, hqbarPrime⟩
  let M : Submonoid (S ⧸ I) := Algebra.algebraMapSubmonoid (S ⧸ I) q.asIdeal.primeCompl
  let eLoc :
      Localization M ≃ₐ[S ⧸ I] Qloc :=
    Localization.algEquiv M Qloc
  have hSub :
      M = qbar.asIdeal.primeCompl := by
    -- Proof comment: quotienting by `pS` turns `q` into the induced prime `q̄`, so the
    -- denominator submonoid is exactly `q̄.primeCompl`.
    simpa [M, qbar] using
      quotient_primeCompl_eq_algebraMapSubmonoid_at_under I q.asIdeal
        (by
          rw [Ideal.map_le_iff_le_comap]
          simpa [I, p, PrimeSpectrum.comap_asIdeal])
  letI : IsLocalization M (Localization.AtPrime qbar.asIdeal) := by
    simpa [hSub] using
      (inferInstance : IsLocalization qbar.asIdeal.primeCompl (Localization.AtPrime qbar.asIdeal))
  let eQuot :
      Qloc ≃ₐ[S ⧸ I] Localization.AtPrime qbar.asIdeal :=
    eLoc.symm.trans (Localization.algEquiv M (Localization.AtPrime qbar.asIdeal))
  let T : Submonoid (S ⧸ I) :=
    Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p.asIdeal))
  let eFiber :
      Localization T ≃ₐ[S ⧸ I] p.asIdeal.Fiber S :=
    fiber_quotient_localization_algEquiv_at_under (R := R) (S := S) p
  let qT : PrimeSpectrum (Localization T) :=
    PrimeSpectrum.comap eFiber.toRingHom (fiberPrimeAt R S q)
  have hI_le_q : I ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    simpa [I, p, PrimeSpectrum.comap_asIdeal]
  have hqTcomap :
      Ideal.comap (algebraMap (S ⧸ I) (Localization T)) qT.asIdeal = qbar.asIdeal := by
    -- Proof comment: the prime of the fiber ring corresponding to `q` contracts back to the
    -- induced quotient prime `q̄`.
    have hFiberComap :
        Ideal.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q).asIdeal =
          q.asIdeal := by
      have hleft :
          ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) = q := by
        simpa [p, fiberPrimeAt] using
          congrArg Subtype.val
            ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩)
      have hcomap :
          PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q) = q := by
        calc
          PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q) =
              ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) := by
                change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
                    (fiberPrimeAt R S q) =
                  ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q))
                rfl
          _ = q := hleft
      simpa using congrArg PrimeSpectrum.asIdeal hcomap
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.comap_comap, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
    rw [show
        eFiber.toRingHom.comp
            ((algebraMap (S ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) =
          algebraMap S (p.asIdeal.Fiber S) by
            ext s
            -- Proof comment: the quotient presentation and the canonical inclusion of `S`
            -- into the fiber ring agree on generators.
            calc
              eFiber.toRingHom
                  ((algebraMap (S ⧸ I) (Localization T)) (Ideal.Quotient.mk I s)) =
                  algebraMap (S ⧸ I) (p.asIdeal.Fiber S) (Ideal.Quotient.mk I s) := by
                    exact eFiber.commutes (Ideal.Quotient.mk I s)
              _ = algebraMap S (p.asIdeal.Fiber S) s := by
                    rw [quotient_to_fiber_algebraMap_mk_at_under
                      (R := R) (S := S) (p := p)]
                    rfl]
    simpa [qbar, I, Ideal.comap_map_mk hI_le_q] using
      hFiberComap
  let qbar' : PrimeSpectrum (S ⧸ I) :=
    PrimeSpectrum.comap (algebraMap (S ⧸ I) (Localization T)) qT
  let eSource :
      Localization.AtPrime qbar.asIdeal ≃+* Localization.AtPrime qbar'.asIdeal :=
    Localization.localRingEquiv qbar.asIdeal qbar'.asIdeal (RingEquiv.refl (S ⧸ I))
      (by simpa [qbar'] using hqTcomap.symm)
  let eTower :
      Localization.AtPrime qbar'.asIdeal ≃+* Localization.AtPrime qT.asIdeal :=
    -- Proof comment: localizing the quotient presentation again at the prime over `q̄`
    -- collapses the localization tower.
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := T) qT.asIdeal).toRingEquiv
  let eFiberLocal0 :
      Localization.AtPrime qT.asIdeal ≃+*
        Localization.AtPrime (fiberPrimeAt R S q).asIdeal :=
    -- Proof comment: localizing corresponding primes along the quotient-to-fiber equivalence
    -- recovers the canonical fiber local ring.
    Localization.localRingEquiv qT.asIdeal (fiberPrimeAt R S q).asIdeal eFiber.toRingEquiv
      (PrimeSpectrum.comap_asIdeal (f := eFiber.toRingHom) (fiberPrimeAt R S q))
  let eFiberLocal :
      Localization.AtPrime qT.asIdeal ≃+* fiberLocalRingAt R S q := by
    simpa [fiberLocalRingAt] using eFiberLocal0
  -- Proof comment: composing the quotient-localization comparison with the fiber presentation
  -- gives the source proof's canonical quotient model of the local fiber ring.
  simpa [p] using
    ((((eTarget.symm.trans eQuot.toRingEquiv).trans eSource).trans eTower).trans eFiberLocal)

/-- Helper for Lemma 10.163.4: mapping a regular sequence along a surjective local algebra map
does not change its regularity on the target module. -/
private theorem isRegular_map_algebraMap_iff_for_depth_transport
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (rs : List A) :
    RingTheory.Sequence.IsRegular N (rs.map (algebraMap A B)) ↔ RingTheory.Sequence.IsRegular N rs := by
  -- Proof comment: the identity map on the underlying additive group intertwines the two scalar
  -- actions through `algebraMap A B`.
  exact
    (AddEquiv.refl N).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Helper for Lemma 10.163.4: elements of the maximal ideal of the target lift to elements of the
maximal ideal of the source under a surjective local algebra map. -/
private theorem exists_preimage_list_in_maximalIdeal_for_depth_transport
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (hsurj : Function.Surjective (algebraMap A B)) (rs : List B)
    (hI : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal B) :
    ∃ rs' : List A,
      rs'.map (algebraMap A B) = rs ∧ Ideal.ofList rs' ≤ IsLocalRing.maximalIdeal A := by
  have hmap :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  induction rs with
  | nil =>
      have hnil : Ideal.ofList ([] : List A) ≤ IsLocalRing.maximalIdeal A := by
        simpa using (bot_le : (⊥ : Ideal A) ≤ IsLocalRing.maximalIdeal A)
      exact ⟨[], rfl, hnil⟩
  | cons s rs ih =>
      have hs_mem : s ∈ IsLocalRing.maximalIdeal B := by
        apply hI
        exact Ideal.subset_span (by simp)
      have hs_map : s ∈ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) := by
        simpa [hmap] using hs_mem
      rcases (Ideal.mem_map_iff_of_surjective (f := algebraMap A B) hsurj).1 hs_map with
        ⟨r, hr, hrs⟩
      have htail_aux : Ideal.ofList rs ≤ Ideal.ofList (s :: rs) := by
        rw [Ideal.ofList_cons]
        exact le_sup_of_le_right le_rfl
      have htail : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal B := by
        exact htail_aux.trans hI
      rcases ih htail with ⟨rs', hrs', hI'⟩
      have hr_le : Ideal.span ({r} : Set A) ≤ IsLocalRing.maximalIdeal A := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        simp at hx
        simpa [hx] using hr
      have hcons : Ideal.ofList (r :: rs') ≤ IsLocalRing.maximalIdeal A := by
        rw [Ideal.ofList_cons]
        exact sup_le hr_le hI'
      exact ⟨r :: rs', by simp [hrs, hrs'], hcons⟩

/-- Helper for Lemma 10.163.4: the lengths of regular sequences in the maximal ideals agree after
restricting scalars along a surjective local algebra map. -/
private theorem regularSequenceLengths_maximalIdeal_eq_of_surjective_for_depth_transport
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal A) N =
      Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal B) N := by
  have hmap :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    have hreg' : RingTheory.Sequence.IsRegular N (rs.map (algebraMap A B)) :=
      (isRegular_map_algebraMap_iff_for_depth_transport (A := A) (B := B) (N := N) rs).2 hreg
    have hI' : Ideal.ofList (rs.map (algebraMap A B)) ≤ IsLocalRing.maximalIdeal B := by
      simpa [Ideal.map_ofList, hmap] using Ideal.map_mono (f := algebraMap A B) hI
    have hlen : (rs.length : ℕ∞) = (rs.map (algebraMap A B)).length := by
      simp
    exact ⟨rs.map (algebraMap A B), hreg', hI', hlen⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    rcases exists_preimage_list_in_maximalIdeal_for_depth_transport
        (A := A) (B := B) hsurj rs hI with
      ⟨rs', hrs', hI'⟩
    have hreg_map : RingTheory.Sequence.IsRegular N (rs'.map (algebraMap A B)) := by
      simpa [hrs'] using hreg
    have hreg' : RingTheory.Sequence.IsRegular N rs' :=
      (isRegular_map_algebraMap_iff_for_depth_transport (A := A) (B := B) (N := N) rs').1 hreg_map
    have hlen_nat : rs'.length = rs.length := by
      simpa using congrArg List.length hrs'
    have hlen : (rs'.length : ℕ∞) = rs.length :=
      congrArg (fun n : ℕ => (n : ℕ∞)) hlen_nat
    exact ⟨rs', hreg', hI', hlen.symm⟩

/-- Helper for Lemma 10.163.4: restricting scalars along a surjective local algebra map does not
change module depth. -/
private theorem moduleDepth_eq_of_surjective_for_depth_transport
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite A N] [Module.Finite B N]
    (hsurj : Function.Surjective (algebraMap A B)) :
    moduleDepth A N = moduleDepth B N := by
  have hmap :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  have hsmul :
      (IsLocalRing.maximalIdeal B • (⊤ : Submodule B N)).restrictScalars A =
        IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) := by
    simpa [hmap] using
      (Ideal.smul_restrictScalars (R := A) (S := B) (M := N) (IsLocalRing.maximalIdeal A)
        (⊤ : Submodule B N))
  have htop :
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) = ⊤ ↔
        IsLocalRing.maximalIdeal B • (⊤ : Submodule B N) = ⊤ := by
    constructor
    · intro hA
      have hA' :
          (IsLocalRing.maximalIdeal B • (⊤ : Submodule B N)).restrictScalars A = ⊤ := by
        rw [hsmul, hA]
      exact
        (Submodule.restrictScalars_eq_top_iff (S := A)
          (p := IsLocalRing.maximalIdeal B • (⊤ : Submodule B N))).mp hA'
    · intro hB
      have hB' :
          (IsLocalRing.maximalIdeal B • (⊤ : Submodule B N)).restrictScalars A = ⊤ := by
        rw [hB, Submodule.restrictScalars_top]
      simpa [hsmul] using hB'
  by_cases hA : IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) = ⊤
  · have hB : IsLocalRing.maximalIdeal B • (⊤ : Submodule B N) = ⊤ := htop.mp hA
    rw [show moduleDepth A N = ⊤ from
          Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal A) N hA,
      show moduleDepth B N = ⊤ from
          Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal B) N hB]
  · have hB : IsLocalRing.maximalIdeal B • (⊤ : Submodule B N) ≠ ⊤ := mt htop.mpr hA
    rw [show moduleDepth A N =
          sSup (Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal A) N) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (IsLocalRing.maximalIdeal A) N hA,
      show moduleDepth B N =
          sSup (Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal B) N) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (IsLocalRing.maximalIdeal B) N hB,
      regularSequenceLengths_maximalIdeal_eq_of_surjective_for_depth_transport
        (A := A) (B := B) (N := N) hsurj]

/-- Helper for Lemma 10.163.4: a ring equivalence between Noetherian local rings preserves the
self-module depth. -/
private theorem moduleDepth_self_eq_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B) :
    moduleDepth A A = moduleDepth B B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap A B) := by
    simpa using e.surjective
  let eA : A ≃ₐ[A] B :=
    AlgEquiv.ofRingEquiv (R := A) (A₁ := A) (A₂ := B) (f := e) fun _ ↦ rfl
  letI : Module.Finite A B := Module.Finite.equiv eA.toLinearEquiv
  -- Proof comment: first identify `B` with `A` as a finite `A`-module, then use the surjective
  -- local algebra map `A → B` to move the depth computation to the target ring.
  calc
    moduleDepth A A = moduleDepth A B := moduleDepth_eq_of_equiv eA.toLinearEquiv
    _ = moduleDepth B B :=
      moduleDepth_eq_of_surjective_for_depth_transport (A := A) (B := B) (N := B) hsurj

/-- Helper for Lemma 10.163.4: the closed fiber of a Noetherian local homomorphism is a local
ring via its quotient presentation. -/
private theorem closed_fiber_isLocalRing_of_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] :
    IsLocalRing ((IsLocalRing.maximalIdeal A).Fiber B) := by
  -- Route correction: build the quotient-side local ring structure first and transport it
  -- across `closedFiber_quotient_equiv`, instead of asking instance search to rediscover it on
  -- the literal fiber expression.
  let I : Ideal B := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
  letI : IsLocalRing (B ⧸ I) := by
    have hI_lt_top : I < (⊤ : Ideal B) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)
    have : Nontrivial (B ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hI_lt_top.ne
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  -- Proof comment: the canonical quotient model of the closed fiber carries the local-ring
  -- structure, so the equivalence transports it to the literal fiber ring.
  exact (closedFiber_quotient_equiv (R := A) (S := B)).toRingEquiv.isLocalRing

/-- Helper for Lemma 10.163.4: the closed fiber of a Noetherian local homomorphism is Noetherian
via its quotient presentation. -/
private theorem closed_fiber_isNoetherianRing_of_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] :
    IsNoetherianRing ((IsLocalRing.maximalIdeal A).Fiber B) :=
  isNoetherianRing_of_ringEquiv
    (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
    (closedFiber_quotient_equiv (R := A) (S := B)).toRingEquiv

/-- Helper for Lemma 10.163.4: the fiber hypothesis gives the localized depth bound at the prime
`fiberPrimeAt R S q`. -/
lemma fiberLocalRingAt_moduleDepth_ge_min_of_hfiber
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionS (p.asIdeal.Fiber S) k)
    (q : PrimeSpectrum S) :
    WithBot.some (moduleDepth (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) : ℕ∞) ≥
      min (k : WithBot ℕ∞) (ringKrullDim (fiberLocalRingAt R S q)) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  -- Proof comment: apply the fiberwise `(S_k)` hypothesis at the distinguished fiber prime
  -- corresponding to `q`.
  simpa [fiberLocalRingAt, p] using
    SerreConditionS.moduleDepth_localizationAtPrime_ge_min
      (R := p.asIdeal.Fiber S) (h := hfiber p) (fiberPrimeAt R S q)

/-- Helper for Lemma 10.163.4: the named closed fiber of the localized map
`R_(q ∩ R) → S_q`. -/
private noncomputable def local_closed_fiber_at_under (q : PrimeSpectrum S) : Type _ :=
  let Rp := Localization.AtPrime (q.asIdeal.under R)
  let Sq := Localization.AtPrime q.asIdeal
  (IsLocalRing.maximalIdeal Rp).Fiber Sq

/-- Helper for Lemma 10.163.4: the named localized closed fiber carries its canonical
commutative-ring structure. -/
instance local_closed_fiber_at_under_commRing (q : PrimeSpectrum S) :
    CommRing (local_closed_fiber_at_under (R := R) (S := S) q) := by
  dsimp [local_closed_fiber_at_under]
  infer_instance

/-- Helper for Lemma 10.163.4: the named localized closed fiber acts on itself by multiplication. -/
instance local_closed_fiber_at_under_module (q : PrimeSpectrum S) :
    Module (local_closed_fiber_at_under (R := R) (S := S) q)
      (local_closed_fiber_at_under (R := R) (S := S) q) :=
  Semiring.toModule

/-- Helper for Lemma 10.163.4: the named closed fiber of `R_(q ∩ R) → S_q` is local. -/
private theorem local_closed_fiber_at_under_isLocalRing (q : PrimeSpectrum S) :
    IsLocalRing (local_closed_fiber_at_under (R := R) (S := S) q) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  have hflatLocal := localized_algebraMap_flat_local_at_under (R := R) (S := S) q
  letI : IsLocalHom (algebraMap Rp Sq) := by
    -- Proof comment: the localized algebra map is local by the same canonical localization
    -- comparison used in the main proof.
    simpa [p, Rp, Sq, local_closed_fiber_at_under] using hflatLocal.2
  -- Proof comment: the quotient-side local structure from the closed-fiber presentation
  -- transports directly to the named local closed fiber.
  simpa [p, Rp, Sq, local_closed_fiber_at_under] using
    (closed_fiber_isLocalRing_of_localHom (A := Rp) (B := Sq))

/-- Helper for Lemma 10.163.4: the named localized closed fiber inherits its local-ring
structure from the quotient presentation. -/
instance local_closed_fiber_at_under_isLocalRing_inst (q : PrimeSpectrum S) :
    IsLocalRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
  local_closed_fiber_at_under_isLocalRing (R := R) (S := S) q

/-- Helper for Lemma 10.163.4: the named closed fiber of `R_(q ∩ R) → S_q` is Noetherian. -/
private theorem local_closed_fiber_at_under_isNoetherianRing (q : PrimeSpectrum S) :
    IsNoetherianRing (local_closed_fiber_at_under (R := R) (S := S) q) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  have hflatLocal := localized_algebraMap_flat_local_at_under (R := R) (S := S) q
  letI : IsLocalHom (algebraMap Rp Sq) := by
    -- Proof comment: the same localized algebra map supplies the local-hom hypothesis needed by
    -- the quotient presentation of the named closed fiber.
    simpa [p, Rp, Sq, local_closed_fiber_at_under] using hflatLocal.2
  simpa [p, Rp, Sq, local_closed_fiber_at_under] using
    (closed_fiber_isNoetherianRing_of_localHom (A := Rp) (B := Sq))

/-- Helper for Lemma 10.163.4: the named localized closed fiber inherits Noetherianity from its
quotient presentation. -/
instance local_closed_fiber_at_under_isNoetherianRing_inst (q : PrimeSpectrum S) :
    IsNoetherianRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
  local_closed_fiber_at_under_isNoetherianRing (R := R) (S := S) q

attribute [local instance]
  local_closed_fiber_at_under_commRing
  local_closed_fiber_at_under_module
  local_closed_fiber_at_under_isLocalRing_inst
  local_closed_fiber_at_under_isNoetherianRing_inst

/-- Helper for Lemma 10.163.4: a flat local map of Noetherian local rings splits the depth of the
target into the depth of the source and the depth of the closed fiber. -/
private theorem depth_target_eq_depth_source_add_depth_closed_fiber_local
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    [IsLocalRing (Ideal.Fiber (IsLocalRing.maximalIdeal A) B)] :
    moduleDepth B B =
      moduleDepth A A + moduleDepth (Ideal.Fiber (IsLocalRing.maximalIdeal A) B)
        (Ideal.Fiber (IsLocalRing.maximalIdeal A) B) := by
  -- Proof comment: specialize Lemma `10.163.1` to the self-modules over `A` and `B`,
  -- then transport the two tensor factors across the right-unit tensor equivalences.
  rw [← moduleDepth_eq_of_equiv (Algebra.TensorProduct.rid A B B).toLinearEquiv,
    ← moduleDepth_eq_of_equiv
      (Algebra.TensorProduct.rid B (Ideal.Fiber (IsLocalRing.maximalIdeal A) B)
        (Ideal.Fiber (IsLocalRing.maximalIdeal A) B)).toLinearEquiv]
  simpa using
    (depth_tensorProduct_eq_depth_add_depth_closedFiber :
      moduleDepth B (B ⊗[A] A) =
        moduleDepth A A + moduleDepth (Ideal.Fiber (IsLocalRing.maximalIdeal A) B)
          ((Ideal.Fiber (IsLocalRing.maximalIdeal A) B) ⊗[B] B))

/-- Helper for Lemma 10.163.4: `min(k,a) + min(k,b)` dominates `min(k,a + b)` in
`WithBot ℕ∞`. -/
lemma min_add_min_ge_min_add (a b : WithBot ℕ∞) :
    min (k : WithBot ℕ∞) a + min (k : WithBot ℕ∞) b ≥ min (k : WithBot ℕ∞) (a + b) := by
  -- Proof comment: first remove the bottom cases, where both sides simplify immediately.
  cases ha : a with
  | bot =>
      simp
  | coe a' =>
      cases hb : b with
      | bot =>
          simp
      | coe b' =>
          -- Proof comment: after reducing to honest `ℕ∞` values, branch exactly as in the source
          -- proof on whether each summand is cut off by `k`.
          by_cases hak : (a' : ℕ∞) ≤ k
          · by_cases hbk : (b' : ℕ∞) ≤ k
            · have hak' : ((a' : ℕ∞) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) := by
                exact_mod_cast hak
              have hbk' : ((b' : ℕ∞) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) := by
                exact_mod_cast hbk
              rw [min_eq_right hak', min_eq_right hbk']
              exact min_le_right _ _
            · have hkb : (k : ℕ∞) ≤ b' := le_of_not_ge hbk
              have hak' : ((a' : ℕ∞) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) := by
                exact_mod_cast hak
              have hkb' : (k : WithBot ℕ∞) ≤ ((b' : ℕ∞) : WithBot ℕ∞) := by
                exact_mod_cast hkb
              rw [min_eq_right hak', min_eq_left hkb']
              exact le_trans (min_le_left _ _) <|
                by
                  simpa [add_comm] using
                    (show (k : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) + ((a' : ℕ∞) : WithBot ℕ∞) from
                      le_add_of_nonneg_right (show 0 ≤ ((a' : ℕ∞) : WithBot ℕ∞) by simp))
          · have hka : (k : ℕ∞) ≤ a' := le_of_not_ge hak
            by_cases hbk : (b' : ℕ∞) ≤ k
            · have hka' : (k : WithBot ℕ∞) ≤ ((a' : ℕ∞) : WithBot ℕ∞) := by
                exact_mod_cast hka
              have hbk' : ((b' : ℕ∞) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) := by
                exact_mod_cast hbk
              rw [min_eq_left hka', min_eq_right hbk']
              exact le_trans (min_le_left _ _) <|
                by
                  simpa using
                    (show (k : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) + ((b' : ℕ∞) : WithBot ℕ∞) from
                      le_add_of_nonneg_right (show 0 ≤ ((b' : ℕ∞) : WithBot ℕ∞) by simp))
            · have hkb : (k : ℕ∞) ≤ b' := le_of_not_ge hbk
              have hka' : (k : WithBot ℕ∞) ≤ ((a' : ℕ∞) : WithBot ℕ∞) := by
                exact_mod_cast hka
              have hkb' : (k : WithBot ℕ∞) ≤ ((b' : ℕ∞) : WithBot ℕ∞) := by
                exact_mod_cast hkb
              rw [min_eq_left hka', min_eq_left hkb']
              exact le_trans (min_le_left _ _) <|
                by
                  simpa using
                    (show (k : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) + (k : WithBot ℕ∞) from
                      le_add_of_nonneg_right (show 0 ≤ (k : WithBot ℕ∞) by simp))

/-- Helper for Lemma 10.163.4: the named closed fiber of `R_(q ∩ R) → S_q` is canonically the
fiber local ring at `q`. -/
private noncomputable def local_closed_fiber_at_under_ringEquiv_fiberLocalRingAt
    (q : PrimeSpectrum S) :
    let _ : CommRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_commRing (R := R) (S := S) q
    local_closed_fiber_at_under (R := R) (S := S) q ≃+* fiberLocalRingAt R S q := by
  letI : CommRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_commRing (R := R) (S := S) q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : q.asIdeal.LiesOver p.asIdeal := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  let eClosedFiber :
      local_closed_fiber_at_under (R := R) (S := S) q ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) :=
    (closedFiber_quotient_equiv (R := Rp) (S := Sq)).symm.toRingEquiv
  let eRewrite :
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) ≃+*
        (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) :=
    Ideal.quotEquivOfEq
      (localized_base_prime_eq_map_maximalIdeal
        (R := R) (S := S) p.asIdeal q.asIdeal inferInstance)
  -- Proof comment: rewrite the literal closed fiber of `R_p → S_q` to the quotient `S_q / pS_q`,
  -- then use the canonical quotient presentation of the fiber local ring.
  simpa [p, Rp, Sq, local_closed_fiber_at_under] using
    (eClosedFiber.trans eRewrite).trans
      (localized_quotient_ringEquiv_fiberLocalRingAt (R := R) (S := S) q)

/-- Helper for Lemma 10.163.4: the self-depth of the named localized closed fiber agrees with the
self-depth of the canonical fiber local ring. -/
lemma closed_fiber_moduleDepth_eq_fiberLocalRingAt_moduleDepth
    (q : PrimeSpectrum S) :
    let _ : CommRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_commRing (R := R) (S := S) q
    let _ : Module (local_closed_fiber_at_under (R := R) (S := S) q)
        (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_module (R := R) (S := S) q
    let _ : IsLocalRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_isLocalRing (R := R) (S := S) q
    let _ : IsNoetherianRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_isNoetherianRing (R := R) (S := S) q
    moduleDepth (local_closed_fiber_at_under (R := R) (S := S) q)
        (local_closed_fiber_at_under (R := R) (S := S) q) =
      moduleDepth (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) := by
  letI : CommRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_commRing (R := R) (S := S) q
  letI : Module (local_closed_fiber_at_under (R := R) (S := S) q)
      (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_module (R := R) (S := S) q
  letI : IsLocalRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_isLocalRing (R := R) (S := S) q
  letI : IsNoetherianRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_isNoetherianRing (R := R) (S := S) q
  let e :
      local_closed_fiber_at_under (R := R) (S := S) q ≃+* fiberLocalRingAt R S q :=
    local_closed_fiber_at_under_ringEquiv_fiberLocalRingAt (R := R) (S := S) q
  letI : IsNoetherianRing (fiberLocalRingAt R S q) :=
    isNoetherianRing_of_ringEquiv
      (local_closed_fiber_at_under (R := R) (S := S) q) e
  -- Proof comment: once the source proof identifies the named closed fiber with the canonical
  -- fiber local ring, depth transport is exactly the ring-equivalence invariance lemma.
  exact moduleDepth_self_eq_of_ringEquiv e

/-- Helper for Lemma 10.163.4: for the flat local map `R_(q ∩ R) → S_q`, depth splits as the
depth of `R_(q ∩ R)` plus the depth of the named localized closed fiber. -/
private theorem depth_target_eq_depth_source_add_named_closed_fiber_local
    (q : PrimeSpectrum S) :
    let _ : CommRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_commRing (R := R) (S := S) q
    let _ : Module (local_closed_fiber_at_under (R := R) (S := S) q)
        (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_module (R := R) (S := S) q
    let _ : IsLocalRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_isLocalRing (R := R) (S := S) q
    let _ : IsNoetherianRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
      local_closed_fiber_at_under_isNoetherianRing (R := R) (S := S) q
    moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) =
      moduleDepth (Localization.AtPrime (q.asIdeal.under R))
          (Localization.AtPrime (q.asIdeal.under R)) +
        moduleDepth (local_closed_fiber_at_under (R := R) (S := S) q)
          (local_closed_fiber_at_under (R := R) (S := S) q) := by
  letI : CommRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_commRing (R := R) (S := S) q
  letI : Module (local_closed_fiber_at_under (R := R) (S := S) q)
      (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_module (R := R) (S := S) q
  letI : IsLocalRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_isLocalRing (R := R) (S := S) q
  letI : IsNoetherianRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_isNoetherianRing (R := R) (S := S) q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  have hflatLocal := localized_algebraMap_flat_local_at_under (R := R) (S := S) q
  letI : Module.Flat Rp Sq := (RingHom.flat_algebraMap_iff).mp <| by
    simpa [p, Rp, Sq] using hflatLocal.1
  letI : IsLocalHom (algebraMap Rp Sq) := by
    simpa [p, Rp, Sq] using hflatLocal.2
  letI : IsLocalRing ((IsLocalRing.maximalIdeal Rp).Fiber Sq) :=
    closed_fiber_isLocalRing_of_localHom (A := Rp) (B := Sq)
  letI : IsNoetherianRing ((IsLocalRing.maximalIdeal Rp).Fiber Sq) :=
    closed_fiber_isNoetherianRing_of_localHom (A := Rp) (B := Sq)
  -- Proof comment: this is Lemma `10.163.2` specialized to the localized flat local map
  -- `R_p → S_q`, with the raw closed fiber hidden behind the named owner.
  simpa [p, Rp, Sq, local_closed_fiber_at_under] using
    (depth_target_eq_depth_source_add_depth_closed_fiber_local (A := Rp) (B := Sq))

-- Proof sketch: for each `q : PrimeSpectrum S`, set `p = q.asIdeal.under R`. The owner theorem
-- `SerreConditionS.moduleDepth_localizationAtPrime_ge_min` gives the `(S_k)` bound on `R_p`, and
-- the same owner theorem applied to `hfiber p` gives the `(S_k)` bound on the local fiber over
-- `q`. The local depth formula for the flat local map `R_p → S_q` and the local dimension formula
-- `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`
-- should combine these two bounds to yield `depth S_q ≥ min(k, dim S_q)`.
/-- Lemma 10.163.4: for a flat ring map `R → S`, if `R` satisfies Serre's condition `(S_k)`, `S`
is Noetherian, and every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, satisfies
`(S_k)`, then `S` satisfies `(S_k)`. -/
@[stacks 0339]
theorem serreConditionS_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionS (p.asIdeal.Fiber S) k) :
    SerreConditionS S k := by
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro q
  -- Proof comment: first replace the localized self-module of `S` by the localized ring itself,
  -- so the source proof can run primewise on the local map `R_(q ∩ R) → S_q`.
  rw [← moduleDepth_eq_of_equiv (localized_self_linearEquiv (R := S) q.asIdeal),
    Module.supportDim_self_eq_ringKrullDim]
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : Algebra.HasGoingDown R S := by infer_instance
  letI : CommRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_commRing (R := R) (S := S) q
  letI : Module (local_closed_fiber_at_under (R := R) (S := S) q)
      (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_module (R := R) (S := S) q
  letI : IsLocalRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_isLocalRing (R := R) (S := S) q
  letI : IsNoetherianRing (local_closed_fiber_at_under (R := R) (S := S) q) :=
    local_closed_fiber_at_under_isNoetherianRing (R := R) (S := S) q
  have hbase :
      WithBot.some (moduleDepth Rp Rp : ℕ∞) ≥
        min (k : WithBot ℕ∞) (ringKrullDim Rp) :=
    SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R)
      (h := ‹SerreConditionS R k›) p
  have hfiberDepth :
      WithBot.some
          (moduleDepth (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) : ℕ∞) ≥
        min (k : WithBot ℕ∞) (ringKrullDim (fiberLocalRingAt R S q)) :=
    fiberLocalRingAt_moduleDepth_ge_min_of_hfiber (R := R) (S := S) (k := k) hfiber q
  have hdepth :
      moduleDepth Sq Sq =
        moduleDepth Rp Rp +
          moduleDepth (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) := by
    -- Proof comment: combine the flat-local depth splitting with the closed-fiber/fiber-local
    -- identification so the source proof uses the canonical fiber local ring.
    calc
      moduleDepth Sq Sq =
          moduleDepth Rp Rp +
            moduleDepth (local_closed_fiber_at_under (R := R) (S := S) q)
              (local_closed_fiber_at_under (R := R) (S := S) q) :=
        depth_target_eq_depth_source_add_named_closed_fiber_local (R := R) (S := S) q
      _ = moduleDepth Rp Rp +
          moduleDepth (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) := by
        exact congrArg (fun d : ℕ∞ => moduleDepth Rp Rp + d)
          (closed_fiber_moduleDepth_eq_fiberLocalRingAt_moduleDepth
            (R := R) (S := S) q)
  have hdepth' :
      ((moduleDepth Sq Sq : ℕ∞) : WithBot ℕ∞) =
        ((moduleDepth Rp Rp + moduleDepth (fiberLocalRingAt R S q)
          (fiberLocalRingAt R S q) : ℕ∞) : WithBot ℕ∞) :=
    congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) hdepth
  have hdim :
      ringKrullDim Sq =
        ringKrullDim Rp + ringKrullDim (fiberLocalRingAt R S q) := by
    simpa [p, Rp, Sq] using
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        (R := R) (S := S) q
  -- Proof comment: this `calc` is the textbook string of inequalities:
  -- depth decomposition, base and fiber `(S_k)` bounds, then the local dimension formula.
  calc
    min (k : WithBot ℕ∞) (ringKrullDim Sq)
        = min (k : WithBot ℕ∞)
            (ringKrullDim Rp + ringKrullDim (fiberLocalRingAt R S q)) := by
          rw [hdim]
    _ ≤ min (k : WithBot ℕ∞) (ringKrullDim Rp) +
          min (k : WithBot ℕ∞) (ringKrullDim (fiberLocalRingAt R S q)) := by
          simpa using
            (min_add_min_ge_min_add (k := k) (a := ringKrullDim Rp)
              (b := ringKrullDim (fiberLocalRingAt R S q)))
    _ ≤ WithBot.some (moduleDepth Rp Rp : ℕ∞) +
          WithBot.some
            (moduleDepth (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) : ℕ∞) := by
          exact add_le_add hbase hfiberDepth
    _ = ((moduleDepth Rp Rp + moduleDepth (fiberLocalRingAt R S q)
          (fiberLocalRingAt R S q) : ℕ∞) : WithBot ℕ∞) := by
          simp
    _ = WithBot.some (moduleDepth Sq Sq : ℕ∞) := by
          symm
          exact hdepth'

end
