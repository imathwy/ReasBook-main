import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_110_9
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_164_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {k : ℕ}

/-- Helper for Lemma 10.164.6: over a faithfully flat map, every prime `p` of `R` admits a
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
    exact
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := R) (S := S) p).2
        ⟨q0, hq0⟩
  letI : Nontrivial (p.asIdeal.Fiber S) := hnontrivial
  have hbot_ne_top : (⊥ : Ideal (p.asIdeal.Fiber S)) ≠ ⊤ := bot_ne_top
  obtain ⟨rIdeal, hrIdeal⟩ :=
    Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal (p.asIdeal.Fiber S))) hbot_ne_top
  letI : rIdeal.IsPrime := Ideal.minimalPrimes_isPrime hrIdeal
  let r : PrimeSpectrum (p.asIdeal.Fiber S) := ⟨rIdeal, Ideal.minimalPrimes_isPrime hrIdeal⟩
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  have hr_min : rIdeal ∈ minimalPrimes (p.asIdeal.Fiber S) := by
    simpa using hrIdeal
  have hr_zero : rIdeal.primeHeight = 0 := by
    simpa using (Ideal.primeHeight_eq_zero_iff (I := rIdeal)).2 hr_min
  have hEqAsIdeal : (PrimeSpectrum.preimageEquivFiber R S p qover).asIdeal = r.asIdeal := by
    exact congrArg PrimeSpectrum.asIdeal
      ((PrimeSpectrum.preimageEquivFiber R S p).apply_symm_apply r)
  have hEqIdeal : (PrimeSpectrum.preimageEquivFiber R S p qover).asIdeal = rIdeal := by
    simpa [r] using hEqAsIdeal
  refine ⟨qover.1, qover.2, ?_⟩
  -- Proof comment: the chosen point of the fiber spectrum is literally the minimal prime `r`.
  let I : Ideal (p.asIdeal.Fiber S) := (PrimeSpectrum.preimageEquivFiber R S p qover).asIdeal
  have hI : I = rIdeal := by
    simpa [I] using hEqIdeal
  have hI_zero : I.primeHeight = 0 := by
    simpa [hI] using hr_zero
  simpa [I] using hI_zero

/-- Helper for Lemma 10.164.6: the height-zero statement on the prime produced by
`preimageEquivFiber` rewrites to the canonical `fiberPrimeAt` of `q`. -/
lemma fiberPrimeAt_primeHeight_zero_of_comap_eq
    [Algebra R S] {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (hzero : (PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩).asIdeal.primeHeight = 0) :
    (fiberPrimeAt R S q).asIdeal.primeHeight = 0 := by
  cases hq
  simpa [fiberPrimeAt] using hzero

/-- Helper for Lemma 10.164.6: if the fiber prime above `q` has height `0`, then the fiber term
in Lemma `10.112.7` vanishes and `dim S_q = dim R_(q ∩ R)`. -/
lemma ringKrullDim_localizationAtPrime_eq_of_fiberPrimeAt_primeHeight_zero
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight = 0) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  have hfiberDim : ringKrullDim (fiberLocalRingAt R S q) = 0 := by
    -- Proof comment: the local fiber ring is the localization of the fiber at the chosen
    -- height-zero fiber prime, so its Krull dimension is `0`.
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
  -- Proof comment: Lemma `10.112.7` now has zero fiber contribution, so only the base
  -- localization dimension remains.
  have hprime : PrimeSpectrum.comap (algebraMap R S) q = p := by
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

/-- Helper for Lemma 10.164.6: a height-zero fiber prime forces equality of the codimensions of
`q` and its contraction `p = q ∩ R`. -/
lemma primeHeight_eq_of_under_and_fiberPrimeAt_primeHeight_zero
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hqf : (fiberPrimeAt R S q).asIdeal.primeHeight = 0) :
    q.asIdeal.primeHeight = p.asIdeal.primeHeight := by
  have hdim :
      (((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) =
        (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
    -- Proof comment: rewrite both local Krull dimensions as heights and insert the previous
    -- dimension equality.
    calc
      (((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) =
          ringKrullDim (Localization.AtPrime q.asIdeal) := by
            rw [← Ideal.height_eq_primeHeight]
            simpa using
              (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
                (Localization.AtPrime q.asIdeal)).symm
      _ = ringKrullDim (Localization.AtPrime p.asIdeal) := by
            exact
              ringKrullDim_localizationAtPrime_eq_of_fiberPrimeAt_primeHeight_zero
                (R := R) (S := S) hunder hqf
      _ = (((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
            rw [← Ideal.height_eq_primeHeight]
            simpa using
              (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
                (Localization.AtPrime p.asIdeal))
  exact_mod_cast hdim

/-- Helper for Lemma 10.164.6: localizing a flat map at a prime `q` above `p` produces a flat
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

/- Domain-style sampling:
* primary domain: descent of Serre's condition `(R_k)` along faithfully flat maps in commutative
  algebra;
* sampled owner declarations:
  `SerreConditionR`,
  `isNoetherianRing_of_faithfullyFlat`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `serreConditionR_of_flat_of_fiber`;
* best owner abstraction: the chapter owner predicate `SerreConditionR`;
* primitive data vs. derived API: Noetherianity of `R` is derived canonically from faithful
  flatness by `isNoetherianRing_of_faithfullyFlat`, while the only remaining primitive field to
  supply is the primewise localized regularity clause of `SerreConditionR`.

Source/core/bridge triage:
* `source-facing`: `serreConditionR_of_faithfullyFlat`, the textbook faithfully flat descent
  statement for `(R_k)`;
* `core/canonical`: the owner predicate `SerreConditionR` and its field
  `SerreConditionR.isRegularLocalRing_localizationAtPrime`;
* `bridge/view`: local faithful-flat descent tools such as
  `isNoetherianRing_of_faithfullyFlat` and
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`.

This file should therefore keep the source-facing theorem, but build the canonical owner directly
instead of treating the whole class-valued conclusion as opaque proof data.
-/
-- Proof sketch: `SerreConditionR S k` already gives `S` Noetherian, so Lemma `10.164.1` descends
-- Noetherianity to `R`. For a prime `p` of `R` with `height p ≤ k`, choose a prime `q` of `S`
-- lying over `p` that is minimal in the fiber over `p`. Faithful flatness localizes to a flat
-- local map `R_p → S_q` with closed fiber of dimension `0`, so Lemma `10.112.7` gives
-- `dim R_p = dim S_q`. Since `S` satisfies `(R_k)`, the local ring `S_q` is regular; then Lemma
-- `10.110.9` descends regularity along the flat local map, proving that `R_p` is regular.
/-- Lemma 10.164.6: if `f : R →+* S` is faithfully flat and `S` satisfies Serre's condition
`(R_k)`, then `R` satisfies Serre's condition `(R_k)`. Since `SerreConditionR` already includes
Noetherianity, this is exactly the textbook conclusion that `R` is Noetherian and has property
`(R_k)`. -/
@[stacks 0353]
theorem serreConditionR_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    [SerreConditionR S k] : SerreConditionR R k := by
  letI := f.toAlgebra
  have hfAlg : (algebraMap R S).FaithfullyFlat := by
    simpa [RingHom.algebraMap_toAlgebra] using hf
  letI : IsNoetherianRing R := isNoetherianRing_of_faithfullyFlat f hf
  letI : Module.FaithfullyFlat R S :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp <| by
      simpa [RingHom.algebraMap_toAlgebra] using hf
  have hflatRS : (algebraMap R S).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hf.flat
  letI : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp hflatRS
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_localizationAtPrime := ?_ }
  intro p hp
  obtain ⟨q, hq, hqf_chosen⟩ :=
    exists_prime_over_with_fiberPrimeAt_primeHeight_zero
      (R := R) (S := S) hfAlg p
  have hq_under : q.asIdeal.under R = p.asIdeal := by
    -- Proof comment: the prime chosen upstairs lies over `p` by construction.
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal hq
  have hqf_zero : (fiberPrimeAt R S q).asIdeal.primeHeight = 0 := by
    exact fiberPrimeAt_primeHeight_zero_of_comap_eq (R := R) (S := S) hq hqf_chosen
  have hq_height :
      q.asIdeal.primeHeight = p.asIdeal.primeHeight := by
    -- Proof comment: the minimality of the chosen fiber prime kills the fiber term in Lemma
    -- `10.112.7`, so the codimensions of `q` and `p` coincide.
    exact
      primeHeight_eq_of_under_and_fiberPrimeAt_primeHeight_zero
        (R := R) (S := S) hq_under hqf_zero
  have hqk : q.asIdeal.primeHeight ≤ k := by
    rw [hq_height]
    exact hp
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨hq_under.symm⟩
  letI : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
    SerreConditionR.isRegularLocalRing_localizationAtPrime q hqk
  obtain ⟨hflatLocal, hlocalLocal⟩ :=
    localized_algebraMap_flat_local_at_liesOver
      (R := R) (S := S) (p := p) (q := q)
  letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (RingHom.flat_algebraMap_iff).mp hflatLocal
  letI :
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) :=
    hlocalLocal
  -- Proof comment: we are exactly in the flat local descent situation of Lemma `10.110.9`.
  exact isRegularLocalRing_of_flat_localHom_of_regularTarget (Localization.AtPrime q.asIdeal)

end
