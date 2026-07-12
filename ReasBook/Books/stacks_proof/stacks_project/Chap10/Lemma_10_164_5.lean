import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_72_11
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_163_2
import StacksProject_2024.Chap10.Lemma_10_164_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {k : ℕ}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

/-- Helper for Lemma 10.164.5: localizing the self-module `R` at a prime ideal agrees with the
localized ring itself. -/
noncomputable abbrev localized_self_linearEquiv (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p R ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl R).trans
    (Algebra.TensorProduct.rid R (Localization.AtPrime p) (Localization.AtPrime p)).toLinearEquiv

/-- Helper for Lemma 10.164.5: over a faithfully flat map, every prime `p` of `R` admits a
prime `q` of `S` above it whose corresponding fiber prime is minimal, hence has height `0`. -/
lemma exists_prime_over_with_fiberPrimeAt_primeHeight_zero
    [Algebra R S] (hf : (algebraMap R S).FaithfullyFlat) (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum S, ∃ hq : PrimeSpectrum.comap (algebraMap R S) q = p,
      (PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩).asIdeal.primeHeight = 0 := by
  letI : Module.FaithfullyFlat R S :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hf
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨q0, hq0⟩ := hsurj p
  have hnontrivial : Nontrivial (p.asIdeal.Fiber S) := by
    -- Proof comment: a prime above `p` guarantees that the fiber ring over `p` is nontrivial.
    exact
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := R) (S := S) p).2
        ⟨q0, hq0⟩
  letI : Nontrivial (p.asIdeal.Fiber S) := hnontrivial
  obtain ⟨rIdeal, hrIdeal⟩ :=
    Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal (p.asIdeal.Fiber S))) bot_ne_top
  letI : rIdeal.IsPrime := Ideal.minimalPrimes_isPrime hrIdeal
  let r : PrimeSpectrum (p.asIdeal.Fiber S) := ⟨rIdeal, inferInstance⟩
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  have hr_min : rIdeal ∈ minimalPrimes (p.asIdeal.Fiber S) := by
    simpa using hrIdeal
  have hr_zero : rIdeal.primeHeight = 0 := by
    -- Proof comment: minimal primes are exactly the height-zero primes.
    simpa using (Ideal.primeHeight_eq_zero_iff (I := rIdeal)).2 hr_min
  have hEqAsIdeal :
      (PrimeSpectrum.preimageEquivFiber R S p qover).asIdeal = r.asIdeal := by
    exact congrArg PrimeSpectrum.asIdeal
      ((PrimeSpectrum.preimageEquivFiber R S p).apply_symm_apply r)
  have hEqIdeal :
      (PrimeSpectrum.preimageEquivFiber R S p qover).asIdeal = rIdeal := by
    simpa [r] using hEqAsIdeal
  refine ⟨qover.1, qover.2, ?_⟩
  -- Proof comment: the chosen point in the fiber is literally the minimal prime `r`.
  let I : Ideal (p.asIdeal.Fiber S) := (PrimeSpectrum.preimageEquivFiber R S p qover).asIdeal
  have hI : I = rIdeal := by
    simpa [I] using hEqIdeal
  have hI_zero : I.primeHeight = 0 := by
    simpa [hI] using hr_zero
  simpa [I] using hI_zero

/-- Helper for Lemma 10.164.5: the height-zero statement on the prime produced by
`preimageEquivFiber` rewrites to the canonical `fiberPrimeAt` of `q`. -/
lemma fiberPrimeAt_primeHeight_zero_of_comap_eq
    [Algebra R S] {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (hzero : (PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩).asIdeal.primeHeight = 0) :
    (fiberPrimeAt R S q).asIdeal.primeHeight = 0 := by
  cases hq
  simpa [fiberPrimeAt] using hzero

/-- Helper for Lemma 10.164.5: if the fiber prime above `q` has height `0`, then the fiber term
in Lemma `10.112.7` vanishes and `dim S_q = dim R_(q ∩ R)`. -/
lemma ringKrullDim_localizationAtPrime_eq_of_fiberPrimeAt_primeHeight_zero
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight = 0) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  have hfiberDim : ringKrullDim (fiberLocalRingAt R S q) = 0 := by
    -- Proof comment: the local fiber ring is the localization of the fiber at a height-zero prime.
    calc
      ringKrullDim (fiberLocalRingAt R S q) =
          ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
            calc
              ringKrullDim (fiberLocalRingAt R S q) =
                  ↑((fiberPrimeAt R S q).asIdeal.height) := by
                    simpa [fiberLocalRingAt] using
                      (IsLocalization.AtPrime.ringKrullDim_eq_height
                        (fiberPrimeAt R S q).asIdeal (fiberLocalRingAt R S q))
              _ =
                  ((((fiberPrimeAt R S q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
                    rw [Ideal.height_eq_primeHeight]
      _ = 0 := by simpa [hqf]
  have hprime : PrimeSpectrum.comap (algebraMap R S) q = p := by
    -- Proof comment: the chosen upstairs prime contracts to `p`.
    apply PrimeSpectrum.ext
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using hunder
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim (fiberLocalRingAt R S q) := by
            simpa using
              ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
                (R := R) (S := S) q
    _ = ringKrullDim (Localization.AtPrime p.asIdeal) +
          ringKrullDim (fiberLocalRingAt R S q) := by
          cases hprime
          rfl
    _ = ringKrullDim (Localization.AtPrime p.asIdeal) + 0 := by
          rw [hfiberDim]
    _ = ringKrullDim (Localization.AtPrime p.asIdeal) := by simp

/-- Helper for Lemma 10.164.5: a height-zero fiber prime forces the localized closed-fiber
quotient over `R_p → S_q` to have Krull dimension `0`. -/
lemma ringKrullDim_localized_closedFiber_quotient_eq_zero_of_fiberPrimeAt_primeHeight_zero
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight = 0) :
    ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal) = 0 := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  have hprime : PrimeSpectrum.comap (algebraMap R S) q = p := by
    apply PrimeSpectrum.ext
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using hunder
  have hdim :
      ringKrullDim Sq = ringKrullDim Rp := by
    -- Proof comment: Lemma `10.112.7` loses its fiber term because the chosen fiber prime has
    -- height zero.
    simpa [Rp, Sq] using
      ringKrullDim_localizationAtPrime_eq_of_fiberPrimeAt_primeHeight_zero
        (R := R) (S := S) hunder hqf
  have hformula :
      ringKrullDim Sq =
        ringKrullDim Rp +
          ringKrullDim
            (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) := by
    -- Proof comment: this is the quotient form of Lemma `10.112.7`.
    calc
      ringKrullDim Sq =
          ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
            ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) (q.asIdeal.under R)) := by
              simpa [Sq] using
                ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
                  (R := R) (S := S) q
      _ = ringKrullDim Rp + ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) := by
            cases hprime
            rfl
  have hRp :
      ringKrullDim Rp = p.asIdeal.height := by
    simpa [Rp] using
      (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Rp)
  have hformula' :
      p.asIdeal.height + ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) =
        p.asIdeal.height := by
    -- Proof comment: insert the dimension equality `dim Sq = dim Rp` into the quotient formula.
    calc
      p.asIdeal.height + ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) =
          ringKrullDim Rp + ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) := by
            rw [hRp]
      _ = ringKrullDim Sq := hformula.symm
      _ = ringKrullDim Rp := hdim
      _ = p.asIdeal.height := hRp
  let d : ℕ := p.asIdeal.height.toNat
  have hp_ne_top : p.asIdeal.height ≠ ⊤ := by
    exact ne_of_lt (Ideal.height_lt_top Ideal.IsPrime.ne_top')
  have hd :
      ((d : ℕ∞) : WithBot ℕ∞) = p.asIdeal.height := by
    simpa [d] using
      (congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hp_ne_top).symm).symm
  have hformula'' :
      (d : WithBot ℕ∞) + ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) =
        (d : WithBot ℕ∞) := by
    have hd' : p.asIdeal.height = (d : WithBot ℕ∞) := hd.symm
    calc
      (d : WithBot ℕ∞) + ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) =
          p.asIdeal.height + ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) := by
            rw [hd']
      _ = p.asIdeal.height := hformula'
      _ = (d : WithBot ℕ∞) := by
            rw [hd']
  have hquot_zero :
      ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) = 0 := by
    -- Proof comment: cancel the finite base dimension from both sides.
    exact
      (ENat.WithBot.natCast_add_cancel
        (a := ringKrullDim (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal))
        (b := (0 : WithBot ℕ∞)) (c := d)).1 <| by
          simpa using hformula''
  simpa [Sq] using hquot_zero

/-- Helper for Lemma 10.164.5: localizing a flat map at a prime `q` above `p` produces a flat
local homomorphism `R_p → S_q`. -/
lemma localized_algebraMap_flat_local_at_liesOver
    [Algebra R S] [Module.Flat R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S} [q.asIdeal.LiesOver p.asIdeal] :
    (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat ∧
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
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
    -- Proof comment: flatness survives localization along the canonical local map.
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

/-- Helper for Lemma 10.164.5: a nontrivial Noetherian local ring of Krull dimension `0` has
depth `0` as a module over itself. -/
lemma moduleDepth_self_eq_zero_of_ringKrullDim_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Nontrivial A]
    (hdim : ringKrullDim A = 0) :
    moduleDepth A A = 0 := by
  letI : Ring.KrullDimLE 0 A := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  have hann : Module.annihilator A A = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hmin' :
      IsLocalRing.maximalIdeal A ∈ (⊥ : Ideal A).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_krullDimLE_zero (IsLocalRing.maximalIdeal A)
  have hmin :
      IsLocalRing.maximalIdeal A ∈ (Module.annihilator A A).minimalPrimes := by
    simpa [hann] using hmin'
  have hmax :
      IsLocalRing.maximalIdeal A ∈ associatedPrimes A A :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A A hmin
  have hno :
      ¬ ∃ x ∈ IsLocalRing.maximalIdeal A, IsSMulRegular A x := by
    intro hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    have hx_not_union :
        x ∉ ⋃ p ∈ associatedPrimes A A, (p : Set A) := by
      simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular A A] using hxreg
    exact hx_not_union <|
      Set.mem_iUnion.2
        ⟨IsLocalRing.maximalIdeal A, Set.mem_iUnion.2 ⟨hmax, hx⟩⟩
  exact (moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := A) (M := A)).2 hno

/-- Helper for Lemma 10.164.5: the closed fiber of a Noetherian local homomorphism is local via
its quotient presentation. -/
private theorem closed_fiber_isLocalRing_of_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] :
    IsLocalRing ((IsLocalRing.maximalIdeal A).Fiber B) := by
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

/-- Helper for Lemma 10.164.5: the closed fiber of a Noetherian local homomorphism is
Noetherian via its quotient presentation. -/
private theorem closed_fiber_isNoetherianRing_of_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] :
    IsNoetherianRing ((IsLocalRing.maximalIdeal A).Fiber B) :=
  isNoetherianRing_of_ringEquiv
    (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
    (closedFiber_quotient_equiv (R := A) (S := B)).toRingEquiv

/-- Helper for Lemma 10.164.5: for the localized map `R_p → S_q`, the extension of the maximal
ideal of `R_p` is the quotient-side ideal `pS_q`. -/
lemma localized_closedFiber_ideal_eq
    [Algebra R S] {p : PrimeSpectrum R} {q : PrimeSpectrum S} [q.asIdeal.LiesOver p.asIdeal] :
    Ideal.map
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) =
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
  -- Proof comment: this is exactly the localized ideal rewrite from Lemma `10.112.6`.
  simpa using
    localized_base_prime_eq_map_maximalIdeal
      (R := R) (S := S) p.asIdeal q.asIdeal inferInstance

/-- Helper for Lemma 10.164.5: a height-zero fiber prime forces the localized closed fiber over
`R_p → S_q` to have depth `0`. -/
private theorem moduleDepth_localized_closedFiber_eq_zero_of_fiberPrimeAt_primeHeight_zero
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    [Module.Flat R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S} [q.asIdeal.LiesOver p.asIdeal]
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight = 0) :
    moduleDepth
        (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime q.asIdeal))
        (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime q.asIdeal)) = 0 := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  have hflatLocal := localized_algebraMap_flat_local_at_liesOver
    (R := R) (S := S) (p := p) (q := q)
  letI : Module.Flat Rp Sq := (RingHom.flat_algebraMap_iff).mp <| by
    simpa [Rp, Sq] using hflatLocal.1
  letI : IsLocalHom (algebraMap Rp Sq) := by
    -- Proof comment: the localized map `R_p → S_q` is the canonical local map attached to the
    -- lies-over relation `q ∩ R = p`.
    simpa [Rp, Sq] using hflatLocal.2
  let Q : Type _ := Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal
  let Q₀ : Type _ := Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)
  letI : CommRing Q := by
    dsimp [Q]
    infer_instance
  letI : CommRing Q₀ := by
    dsimp [Q₀]
    infer_instance
  have hI₀_lt_top :
      Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp) < (⊤ : Ideal Sq) := by
    -- Proof comment: a local homomorphism sends the maximal ideal of the source to a proper
    -- ideal of the target.
    simpa [Rp, Sq] using IsLocalRing.map_maximalIdeal_lt_top (algebraMap Rp Sq)
  have hI_lt_top : Ideal.map (algebraMap R Sq) p.asIdeal < (⊤ : Ideal Sq) := by
    -- Proof comment: the localized ideal comparison identifies this proper quotient ideal with
    -- `pS_q`.
    simpa [Rp, Sq, localized_closedFiber_ideal_eq (R := R) (S := S) (p := p) (q := q)] using
      hI₀_lt_top
  letI : Nontrivial Q := by
    dsimp [Q]
    exact Ideal.Quotient.nontrivial_iff.mpr hI_lt_top.ne
  letI : Nontrivial Q₀ := by
    dsimp [Q₀]
    exact Ideal.Quotient.nontrivial_iff.mpr hI₀_lt_top.ne
  have hdimQ : ringKrullDim Q = 0 := by
    -- Proof comment: Lemma `10.112.7` already turned the height-zero fiber hypothesis into the
    -- vanishing of the quotient model's Krull dimension.
    simpa [Q, Sq] using
      ringKrullDim_localized_closedFiber_quotient_eq_zero_of_fiberPrimeAt_primeHeight_zero
        (R := R) (S := S) hunder hqf
  have hdimQ₀ : ringKrullDim Q₀ = 0 := by
    -- Proof comment: replace `pS_q` by the extension of the maximal ideal of `R_p` on the
    -- quotient side before passing to the literal closed fiber.
    have hQ₀Q : ringKrullDim Q₀ = ringKrullDim Q := by
      dsimp [Q₀, Q]
      exact ringKrullDim_eq_of_ringEquiv
        (Ideal.quotEquivOfEq
          (localized_closedFiber_ideal_eq (R := R) (S := S) (p := p) (q := q)))
    simpa [hQ₀Q] using hdimQ
  letI : Nontrivial
      (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime q.asIdeal)) := by
    exact (closedFiber_quotient_equiv
      (R := Localization.AtPrime p.asIdeal)
      (S := Localization.AtPrime q.asIdeal)).symm.toEquiv.nontrivial
  have hdimF :
      ringKrullDim
        (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime q.asIdeal)) = 0 := by
    have hQ₀F :
        ringKrullDim Q₀ =
          ringKrullDim
            (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime q.asIdeal)) := by
      dsimp [Q₀, Rp, Sq]
      exact ringKrullDim_eq_of_ringEquiv
        (closedFiber_quotient_equiv
          (R := Localization.AtPrime p.asIdeal) (S := Localization.AtPrime q.asIdeal)).toRingEquiv
    simpa [hQ₀F] using hdimQ₀
  -- Proof comment: the literal closed fiber has the same Krull dimension as the quotient model,
  -- so the depth-zero statement can be proved directly on `F`.
  exact
    moduleDepth_self_eq_zero_of_ringKrullDim_zero
      (A := Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime q.asIdeal)) hdimF

/-- Helper for Lemma 10.164.5: a height-zero fiber prime forces the local depth comparison
`depth(S_q) = depth(R_p)`. -/
lemma moduleDepth_localizationAtPrime_eq_of_fiberPrimeAt_primeHeight_zero
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    [Module.Flat R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight = 0) :
    moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) =
      moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : q.asIdeal.LiesOver p.asIdeal := by
    exact ⟨hunder.symm⟩
  have hflatLocal := localized_algebraMap_flat_local_at_liesOver
    (R := R) (S := S) (p := p) (q := q)
  letI : Module.Flat Rp Sq := (RingHom.flat_algebraMap_iff).mp <| by
    simpa [Rp, Sq] using hflatLocal.1
  letI : IsLocalHom (algebraMap Rp Sq) := by
    -- Proof comment: the localized flat map is also the local map required by Lemma `10.163.2`.
    simpa [Rp, Sq] using hflatLocal.2
  have hclosed :
      moduleDepth
        (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime q.asIdeal))
        (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime q.asIdeal)) = 0 := by
    -- Proof comment: the minimal fiber prime makes the closed fiber zero-dimensional, hence
    -- depth zero after the quotient-model transport proved above.
    exact
      moduleDepth_localized_closedFiber_eq_zero_of_fiberPrimeAt_primeHeight_zero
        (R := R) (S := S) (p := p) (q := q) hunder hqf
  -- Proof comment: route correction. Specialize the flat-local depth formula only after the
  -- closed fiber has explicit local and Noetherian structure and its depth is known to vanish.
  calc
    moduleDepth Sq Sq =
        moduleDepth Rp Rp +
          moduleDepth
            (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime q.asIdeal))
            (Ideal.Fiber (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime q.asIdeal)) := by
      simpa [Rp, Sq] using
        (depth_target_eq_depth_source_add_depth_closed_fiber (R := Rp) (S := Sq))
    _ = moduleDepth Rp Rp + 0 := by rw [hclosed]
    _ = moduleDepth Rp Rp := by simp

/- Domain-style sampling:
* primary domain: faithfully flat descent for Serre's condition `(S_k)` in commutative algebra;
* sampled owner declarations:
  `SerreConditionS`,
  `Module.SerreConditionS`,
  `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`,
  `isNoetherianRing_of_faithfullyFlat`;
* best owner abstraction: the chapter owner predicate `SerreConditionS`;
* primitive data vs. derived API: Noetherianity of `R` is canonical derived data from faithful
  flatness, while the only primitive field still to supply for the owner is the localized depth
  inequality.

Source/core/bridge triage:
* `source-facing`: `serreConditionS_of_faithfullyFlat`, the textbook descent statement for
  Serre's condition `(S_k)`;
* `core/canonical`: the owner predicate `SerreConditionS` together with the module owner
  `Module.SerreConditionS R R k`;
* `bridge/view`: the self-module identification
  `Module.supportDim_self_eq_ringKrullDim`, which converts the module owner field into the usual
  ring-theoretic depth inequality.

This file should therefore keep the source-facing theorem directly on `SerreConditionS`, derive
Noetherianity canonically from faithful flatness, and build the owner instance explicitly rather
than treating the whole class-valued conclusion as opaque proof data.
-/
-- Proof sketch: Lemma `10.164.1` gives that `R` is Noetherian. For each prime `p` of `R`, choose
-- a prime `q` of `S` lying over `p` that is minimal in the fiber over `p`. The induced local map
-- `R_p → S_q` is flat local with closed fiber of dimension `0`, so Lemmas `10.112.7` and
-- `10.163.2` identify both the Krull dimension and the depth of `R_p` with those of `S_q`.
-- Since `S` satisfies `(S_k)`, the inequality `depth R_p ≥ min(k, dim R_p)` follows.
/-- Chap10 Lemma 10 164 5: if `f : R →+* S` is faithfully flat and `S` satisfies Serre's
condition `(S_k)`, then `R` is Noetherian and satisfies `(S_k)`, i.e. `R` satisfies
`SerreConditionS R k`. -/
@[stacks 0352]
theorem serreConditionS_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    [SerreConditionS S k] : SerreConditionS R k := by
  letI := f.toAlgebra
  have hfAlg : (algebraMap R S).FaithfullyFlat := by
    simpa [RingHom.algebraMap_toAlgebra] using hf
  let _ : IsNoetherianRing R := isNoetherianRing_of_faithfullyFlat f hf
  letI : Module.FaithfullyFlat R S :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hfAlg
  have hflatRS : (algebraMap R S).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hf.flat
  letI : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp hflatRS
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro p
  obtain ⟨q, hq, hqf_chosen⟩ :=
    exists_prime_over_with_fiberPrimeAt_primeHeight_zero
      (R := R) (S := S) hfAlg p
  have hq_under : q.asIdeal.under R = p.asIdeal := by
    -- Proof comment: the chosen prime `q` lies over `p`.
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal hq
  have hqf_zero : (fiberPrimeAt R S q).asIdeal.primeHeight = 0 := by
    exact fiberPrimeAt_primeHeight_zero_of_comap_eq (R := R) (S := S) hq hqf_chosen
  have hdim :
      ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    -- Proof comment: the minimal fiber choice makes the dimension comparison an equality.
    exact
      ringKrullDim_localizationAtPrime_eq_of_fiberPrimeAt_primeHeight_zero
        (R := R) (S := S) hq_under hqf_zero
  let e := localized_self_linearEquiv (R := R) p.asIdeal
  have hsupport :
      Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal R) =
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    -- Proof comment: the localized self-module has the same support dimension as the localized
    -- ring itself.
    simpa [Module.supportDim_self_eq_ringKrullDim] using Module.supportDim_eq_of_equiv e
  have hself :
      moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal R) =
        moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
    -- Proof comment: the same linear equivalence also identifies the localized self-module depth
    -- with the depth of the localized ring.
    simpa using moduleDepth_eq_of_equiv e
  -- Route correction: keep the textbook local proof. Rewrite the target owner field from the
  -- localized self-module to `R_p`, compare `R_p` and `S_q` by the flat-local depth formula, and
  -- then reuse the `(S_k)` inequality already known for `S_q`.
  simpa [hsupport, hself, hdim,
    moduleDepth_localizationAtPrime_eq_of_fiberPrimeAt_primeHeight_zero
      (R := R) (S := S) hq_under hqf_zero] using
    (SerreConditionS.moduleDepth_localizationAtPrime_ge_min
      (R := S) (h := inferInstance) q)

end
