import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_112_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Ideal.Quotient (eq_zero_iff_mem)
open scoped ENat TensorProduct nonZeroDivisors

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {k : ℕ}
variable [SerreConditionR R k] [IsNoetherianRing S] [Module.Flat R S]

/- Domain sampling pass:
* primary domain: commutative algebra of LinearRepresentations_Serre_1977's condition `(R_k)` under flat ring maps and
  fiberwise regularity;
* sampled owner declarations:
  - `SerreConditionR`, the chapter owner predicate for `(R_k)` from
    `Definition_10_157_1.lean`;
  - `Ideal.Fiber`, the canonical fiber-ring owner `κ(𝔭) ⊗[R] S`;
  - `serreConditionS_of_flat_of_fiber`, the sibling owner-level ascent theorem for `(S_k)` in
    `Lemma_10_163_4.lean`;
  - `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`, the local regularity transfer
    theorem for flat local maps in `Lemma_10_112_8.lean`.

Source/core/bridge triage:
* source-facing: `serreConditionR_of_flat_of_fiber`, the textbook ascent statement for `(R_k)`;
* core/canonical: the owner predicate `SerreConditionR` together with its primewise localized
  regularity field
  `SerreConditionR.isRegularLocalRing_localizationAtPrime`;
* bridge/view: the canonical fiber presentation `p.asIdeal.Fiber S`.

Primitive data already live in the owner abstraction: `(R_k)` on the base ring and on each fiber.
This file should therefore expose only the source-facing ascent theorem, not a parallel wrapper for
fiberwise regularity or localized regularity data.
-/

section fiberLocalizationBridge

variable (p : PrimeSpectrum R)

local notation "Sbar" => S ⧸ Ideal.map (algebraMap R S) p.asIdeal
local notation "Rbar" => R ⧸ p.asIdeal
local notation "Rbar⁰" => nonZeroDivisors Rbar
local notation "T" => Algebra.algebraMapSubmonoid Sbar Rbar⁰

/-- Helper for Lemma 10.163.5: elements of `pS` vanish in the fiber ring `κ(p) ⊗[R] S`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map {x : S}
    (hx : x ∈ Ideal.map (algebraMap R S) p.asIdeal) :
    algebraMap S (p.asIdeal.Fiber S) x = 0 := by
  let φ : (R ⧸ p.asIdeal) ⊗[R] S →+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x : Sbar) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : Rbar) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal
    have : e (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x) =
        (1 : Rbar) ⊗ₜ[R] x := rfl
    rw [← this, hquot]
    simp [e]
  have hφ : φ ((1 : Rbar) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  simpa [φ] using hφ

/-- Helper for Lemma 10.163.5: the quotient `S / pS` acts canonically on the fiber ring. -/
noncomputable instance fiberQuotientAlgebra :
    Algebra Sbar (p.asIdeal.Fiber S) :=
  (Ideal.Quotient.liftₐ (Ideal.map (algebraMap R S) p.asIdeal)
    (Algebra.ofId S (p.asIdeal.Fiber S))
    (fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map (R := R) (S := S) p hx)).toRingHom.toAlgebra

/-- Helper for Lemma 10.163.5: the quotient generator `s mod pS` maps to the pure tensor
`1 ⊗ s` in the fiber ring. -/
theorem quotient_to_fiber_algebraMap_mk (s : S) :
    algebraMap Sbar (p.asIdeal.Fiber S)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) s) =
        1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Lemma 10.163.5: the quotient-base-changed fiber presentation recovers the usual
fiber ring as an `S / pS`-algebra. -/
noncomputable def fiber_tensor_over_quotient_algEquiv :
    Sbar ⊗[Rbar] p.asIdeal.ResidueField ≃ₐ[Sbar] p.asIdeal.Fiber S :=
  let eRing :
      Sbar ⊗[Rbar] p.asIdeal.ResidueField ≃+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.commRight Rbar Sbar p.asIdeal.ResidueField).toRingEquiv.trans
      ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField]
            p.asIdeal.ResidueField)
          (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal)).trans
        (Algebra.TensorProduct.cancelBaseChange R Rbar p.asIdeal.ResidueField
          p.asIdeal.ResidueField S)).toRingEquiv
  { toRingEquiv := eRing
    commutes' := by
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Proof comment: both sides send `s mod pS` to the same pure tensor `1 ⊗ s`.
      simpa [eRing, quotient_to_fiber_algebraMap_mk (R := R) (S := S) (p := p),
        Algebra.TensorProduct.cancelBaseChange_tmul] }

/-- Helper for Lemma 10.163.5: the fiber ring is the localization of `S / pS` at the image of
the nonzerodivisors of `R / p`. -/
noncomputable def fiber_quotient_localization_algEquiv :
    Localization T ≃ₐ[Sbar] p.asIdeal.Fiber S :=
  -- Proof comment: this is the source proof's standard presentation
  -- `(S / pS)[(R / p)^\times] ≃ κ(p) ⊗[R] S`.
  ((Localization.tensorLeftAlgEquiv Rbar⁰ Sbar).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : Sbar ≃ₐ[Sbar] Sbar)
        (IsLocalization.algEquiv Rbar⁰ (Localization Rbar⁰) p.asIdeal.ResidueField))).trans
    (fiber_tensor_over_quotient_algEquiv (R := R) (S := S) (p := p))

end fiberLocalizationBridge

-- Proof sketch: to prove `(R_k)` for `S`, fix `q : PrimeSpectrum S` of height at most `k` and let
-- `p = q.asIdeal.under R`. Flatness gives going down, so Lemma `10.112.7` expresses
-- `dim S_q = dim R_p + dim ((κ(p) ⊗[R] S)_(q_fiber))`. The bound on `dim S_q` therefore bounds both
-- summands by `k`. Since `R` satisfies `(R_k)`, the localization `R_p` is regular; since the fiber
-- ring over `p` satisfies `(R_k)`, the corresponding localization of the fiber is regular. Lemma
-- `10.112.8` then upgrades these two regularity statements to regularity of `S_q`.
/-- Helper for Lemma 10.163.5: a height bound on `q` bounds both the contracted prime
`q ∩ R` and the corresponding fiber prime. -/
lemma primeHeight_under_and_fiberPrimeAt_le_of_primeHeight_le
    (q : PrimeSpectrum S) (hq : q.asIdeal.primeHeight ≤ k) :
    (q.asIdeal.under R).primeHeight ≤ k ∧
      (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k := by
  letI : Algebra.HasGoingDown R S := by infer_instance
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hfiberDim :
      ringKrullDim (fiberLocalRingAt R S q) =
        ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
    -- Proof comment: the local fiber ring is the localization of the fiber at its fiber prime.
    calc
      ringKrullDim (fiberLocalRingAt R S q) =
          ↑((fiberPrimeAt R S q).asIdeal.height) := by
            simpa [fiberLocalRingAt] using
              (IsLocalization.AtPrime.ringKrullDim_eq_height
                (fiberPrimeAt R S q).asIdeal (fiberLocalRingAt R S q))
      _ =
          ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
            rw [Ideal.height_eq_primeHeight]
  have hdim :
      (((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) =
        (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) +
          ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
    -- Proof comment: Lemma `10.112.7` becomes a prime-height sum after rewriting each local
    -- Krull dimension by the height of the defining prime.
    calc
      (((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) =
          ringKrullDim (Localization.AtPrime q.asIdeal) := by
            rw [← Ideal.height_eq_primeHeight]
            simpa using
              (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
                (Localization.AtPrime q.asIdeal)).symm
      _ =
          ringKrullDim (Localization.AtPrime p.asIdeal) +
            ringKrullDim (fiberLocalRingAt R S q) := by
              simpa [p] using
                ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
                  (R := R) (S := S) q
      _ =
          (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) +
            ringKrullDim (fiberLocalRingAt R S q) := by
              congr 1
              simpa [Ideal.height_eq_primeHeight] using
                (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
                  (Localization.AtPrime p.asIdeal))
      _ =
          (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) +
            ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
              rw [hfiberDim]
  have hdim_enat :
      q.asIdeal.primeHeight =
        p.asIdeal.primeHeight + (fiberPrimeAt R S q).asIdeal.primeHeight := by
    exact_mod_cast hdim
  have hp :
      p.asIdeal.primeHeight ≤ k := by
    -- Proof comment: each ENat summand is bounded by the total codimension.
    calc
      p.asIdeal.primeHeight ≤
          p.asIdeal.primeHeight + (fiberPrimeAt R S q).asIdeal.primeHeight := by
            exact le_add_right le_rfl
      _ = q.asIdeal.primeHeight := hdim_enat.symm
      _ ≤ k := hq
  have hqf :
      (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k := by
    -- Proof comment: the same argument bounds the fiber-prime contribution.
    calc
      (fiberPrimeAt R S q).asIdeal.primeHeight ≤
          p.asIdeal.primeHeight + (fiberPrimeAt R S q).asIdeal.primeHeight := by
            exact le_add_left le_rfl
      _ = q.asIdeal.primeHeight := hdim_enat.symm
      _ ≤ k := hq
  exact ⟨by simpa [p] using hp, hqf⟩

/-- Helper for Lemma 10.163.5: after quotienting by `I ≤ q`, the induced prime complement on
`A ⧸ I` is exactly the image of `q.primeCompl`. -/
lemma quotient_primeCompl_eq_algebraMapSubmonoid
    {A : Type*} [CommRing A] (I q : Ideal A) [q.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk I) q).IsPrime] (hIq : I ≤ q) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk I) q).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Proof comment: if `a mod I` lay in the quotient prime, then pulling back along the
    -- quotient map would force `a ∈ q`, contradicting `a ∉ q`.
    change Ideal.Quotient.mk I a ∉ Ideal.map (Ideal.Quotient.mk I) q
    intro hx
    have hqx : a ∈ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) := by
      exact hx
    exact ha <| by simpa [Ideal.comap_map_mk hIq] using hqx
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_, rfl⟩
    -- Proof comment: conversely, if `a mod I` avoids the quotient prime then `a` itself avoids
    -- `q`, so it already represents the required source-side denominator.
    intro ha
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha)

/-- Helper for Lemma 10.163.5: if the fiber prime of `q` has codimension at most `k`, then the
closed fiber of `R_(q ∩ R) → S_q` is a regular local ring. -/
lemma isRegularLocalRing_localized_quotient_of_fiberPrimeAt_bound
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k)
    (q : PrimeSpectrum S)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k) :
    IsRegularLocalRing
      ((Localization.AtPrime q.asIdeal) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let I : Ideal S := Ideal.map (algebraMap R S) p.asIdeal
  let Qloc :=
    (Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I
  have hQloc :
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    -- Proof comment: extending `p` to `S` and then localizing is the same as extending `p`
    -- directly to the local ring `S_q`.
    dsimp [I]
    simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)] using
      (Ideal.map_map (I := p.asIdeal) (f := algebraMap R S)
        (g := algebraMap S (Localization.AtPrime q.asIdeal)))
  let eTarget :
      Qloc ≃+*
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal) :=
    Ideal.quotEquivOfEq hQloc
  have hfiberLocal :
      IsRegularLocalRing (fiberLocalRingAt R S q) := by
    -- Proof comment: the fiberwise `(R_k)` hypothesis is used exactly at the prime
    -- `fiberPrimeAt R S q` of the fiber ring over `p = q ∩ R`.
    simpa [fiberLocalRingAt, p] using
      ((hfiber p).isRegularLocalRing_localizationAtPrime (fiberPrimeAt R S q) hqf)
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
    -- Proof comment: quotienting by `pS` turns `q` into the induced prime `q̄`, so the source
    -- denominator submonoid is exactly `q̄.primeCompl`.
    simpa [M, qbar] using
      quotient_primeCompl_eq_algebraMapSubmonoid I q.asIdeal
        (by
          rw [Ideal.map_le_iff_le_comap]
          simpa [I, p, PrimeSpectrum.comap_asIdeal])
  letI : IsLocalization M (Localization.AtPrime qbar.asIdeal) := by
    simpa [hSub] using
      (inferInstance : IsLocalization qbar.asIdeal.primeCompl (Localization.AtPrime qbar.asIdeal))
  let eQuot :
      Qloc ≃ₐ[S ⧸ I] Localization.AtPrime qbar.asIdeal :=
    eLoc.symm.trans (Localization.algEquiv M (Localization.AtPrime qbar.asIdeal))
  have hquotLocal :
      IsRegularLocalRing (Localization.AtPrime qbar.asIdeal) := by
    let T : Submonoid (S ⧸ I) :=
      Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p.asIdeal))
    let eFiber :
        Localization T ≃ₐ[S ⧸ I] p.asIdeal.Fiber S :=
      fiber_quotient_localization_algEquiv (R := R) (S := S) p
    let qT : PrimeSpectrum (Localization T) :=
      PrimeSpectrum.comap eFiber.toRingHom (fiberPrimeAt R S q)
    have hI_le_q : I ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [I, p, PrimeSpectrum.comap_asIdeal]
    have hqTcomap :
        Ideal.comap (algebraMap (S ⧸ I) (Localization T)) qT.asIdeal = qbar.asIdeal := by
      -- Proof comment: transport the fiber prime back through the quotient presentation of the
      -- fiber ring, then contract further along `S → S / pS`.
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
              -- Proof comment: the quotient presentation and the fiber inclusion agree on `S`.
              calc
                eFiber.toRingHom
                    ((algebraMap (S ⧸ I) (Localization T)) (Ideal.Quotient.mk I s)) =
                    algebraMap (S ⧸ I) (p.asIdeal.Fiber S) (Ideal.Quotient.mk I s) := by
                      exact eFiber.commutes (Ideal.Quotient.mk I s)
                _ = algebraMap S (p.asIdeal.Fiber S) s := by
                      rw [quotient_to_fiber_algebraMap_mk
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
      -- Proof comment: localizing corresponding primes along the quotient-to-fiber algebra
      -- equivalence recovers the fiber local ring.
      Localization.localRingEquiv qT.asIdeal (fiberPrimeAt R S q).asIdeal eFiber.toRingEquiv
        (PrimeSpectrum.comap_asIdeal (f := eFiber.toRingHom) (fiberPrimeAt R S q))
    let eFiberLocal :
        Localization.AtPrime qT.asIdeal ≃+* fiberLocalRingAt R S q := by
      simpa [fiberLocalRingAt] using eFiberLocal0
    letI : IsRegularLocalRing (fiberLocalRingAt R S q) := hfiberLocal
    exact IsRegularLocalRing.of_ringEquiv ((eSource.trans eTower).trans eFiberLocal).symm
  letI : IsRegularLocalRing (Localization.AtPrime qbar.asIdeal) := hquotLocal
  have hQlocRegular : IsRegularLocalRing Qloc := by
    -- Proof comment: the quotient-localization comparison reduces regularity of `Qloc` to the
    -- same property on the induced quotient-prime localization of `S / pS`.
    exact IsRegularLocalRing.of_ringEquiv eQuot.toRingEquiv.symm
  -- Proof comment: finally transport regularity from the `I = pS` quotient model back to the
  -- literal target quotient appearing in the statement.
  simpa [p] using (IsRegularLocalRing.of_ringEquiv eTarget)

/-- Helper for Lemma 10.163.5: regularity of the quotient presentation `S_q / (q ∩ R)S_q`
implies regularity of the closed fiber of `R_(q ∩ R) → S_q`. -/
lemma isRegularLocalRing_closedFiber_of_localized_quotient_regular
    (q : PrimeSpectrum S)
    [IsRegularLocalRing
      ((Localization.AtPrime q.asIdeal) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R))] :
    IsRegularLocalRing
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.under R))).Fiber
        (Localization.AtPrime q.asIdeal)) := by
  let p : Ideal R := q.asIdeal.under R
  let Sq := Localization.AtPrime q.asIdeal
  let Rp := Localization.AtPrime p
  letI : q.asIdeal.LiesOver p := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  -- Proof comment: rewrite the local closed-fiber quotient ideal as the localized base prime,
  -- then invoke the closed-fiber-from-quotient criterion from Lemma `10.112.8`.
  have hmap :
      Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp) =
        Ideal.map (algebraMap R Sq) p := by
    simpa [p, Rp, Sq] using
      localized_base_prime_eq_map_maximalIdeal (R := R) (S := S) p q.asIdeal
        (Ideal.over_under q.asIdeal)
  have hquot :
      IsRegularLocalRing
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) := by
    rw [hmap]
    infer_instance
  -- Proof comment: the closed fiber is canonically equivalent to that quotient presentation.
  letI :
      IsRegularLocalRing
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) := hquot
  simpa [p, Rp, Sq] using
    (isRegularLocalRing_closedFiber_of_quotient
      (R := Rp) (S := Sq))

/-- Helper for Lemma 10.163.5: if the fiber prime of `q` has codimension at most `k`, then the
closed fiber of `R_(q ∩ R) → S_q` is a regular local ring. -/
lemma isRegularLocalRing_closedFiber_of_fiberPrimeAt_bound
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k)
    (q : PrimeSpectrum S)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight ≤ k) :
    IsRegularLocalRing
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.under R))).Fiber
        (Localization.AtPrime q.asIdeal)) := by
  letI :
      IsRegularLocalRing
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) :=
    isRegularLocalRing_localized_quotient_of_fiberPrimeAt_bound
      (R := R) (S := S) (k := k) hfiber q hqf
  -- Proof comment: once the quotient presentation is regular, Lemma `10.112.8` converts it to
  -- the exact closed-fiber object used in the final flat-local regularity step.
  exact
    isRegularLocalRing_closedFiber_of_localized_quotient_regular
      (R := R) (S := S) q

/-- Lemma 10.163.5: for a flat ring map `R → S`, if `R` satisfies LinearRepresentations_Serre_1977's condition `(R_k)`, `S`
is Noetherian, and every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, satisfies
`(R_k)`, then `S` satisfies `(R_k)`. -/
theorem serreConditionR_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k) :
    SerreConditionR S k := by
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_localizationAtPrime := ?_ }
  intro q hq
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  letI : q.asIdeal.LiesOver p.asIdeal := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  letI : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
    -- Proof comment: the dimension formula bounds `q ∩ R` by `k`, so the base localization is
    -- regular by the `(R_k)` hypothesis on `R`.
    exact
      SerreConditionR.isRegularLocalRing_localizationAtPrime p
        (primeHeight_under_and_fiberPrimeAt_le_of_primeHeight_le
          (R := R) (S := S) (k := k) q hq).1
  have hclosedFiber :
      IsRegularLocalRing
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).Fiber
          (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: the second summand in the dimension formula is the local fiber codimension,
    -- so the fiberwise `(R_k)` hypothesis supplies the closed-fiber regularity input.
    simpa [p] using
      isRegularLocalRing_closedFiber_of_fiberPrimeAt_bound
        (R := R) (S := S) (k := k) hfiber q
        (primeHeight_under_and_fiberPrimeAt_le_of_primeHeight_le
          (R := R) (S := S) (k := k) q hq).2
  have halg :
      Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S)
          (q.asIdeal.over_def p.asIdeal) =
        algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      rw [← IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal) x]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal) x]
  have hflat :
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat := by
    have hflatRS : (algebraMap R S).Flat := by
      rw [RingHom.flat_algebraMap_iff]
      infer_instance
    -- Proof comment: flatness localizes along the canonical local map `R_p → S_q`.
    simpa [halg] using
      (RingHom.Flat.localRingHom hflatRS q.asIdeal p.asIdeal (q.asIdeal.over_def p.asIdeal))
  letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (RingHom.flat_algebraMap_iff).mp hflat
  letI : IsLocalHom
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: the localized map is a local homomorphism by construction.
    simpa [halg] using
      (Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal
        (algebraMap R S) (q.asIdeal.over_def p.asIdeal))
  -- Proof comment: Lemma `10.112.8` is now applied exactly in the source-proof form.
  exact isRegularLocalRing_of_flat_localHom_of_regular_closedFiber hclosedFiber

end
