import Mathlib
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap10.Lemma_10_105_10

noncomputable section

open PrimeSpectrum

section

variable {L : Type*} [CommRing L]

/-- Helper for Lemma 10.113.1: a height-one prime in a domain is an immediate specialization of
the zero prime. -/
theorem height_one_prime_isImmediateSpecialization_bot
    [IsDomain L] (K : Ideal L) [K.IsPrime] (hK : Ideal.primeHeight K = 1) :
    IsImmediateSpecialization (⊥ : PrimeSpectrum L) (⟨K, inferInstance⟩ : PrimeSpectrum L) := by
  let P : PrimeSpectrum L := ⟨K, inferInstance⟩
  have hbot_primeHeight : (⊥ : Ideal L).primeHeight = 0 := by
    -- In a domain, the zero ideal is the unique minimal prime.
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hK_ne_bot : K ≠ ⊥ := by
    -- A height-one prime cannot be the zero prime.
    intro hbot
    simpa [hbot, hbot_primeHeight] using hK
  -- Route correction: keep the source chain argument explicit by proving there is no prime strictly
  -- between `(0)` and `K`.
  refine ⟨?_, ?_, ?_⟩
  · -- The zero prime specializes to every prime in a domain.
    exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  · intro h
    apply hK_ne_bot
    simpa [P] using (congrArg PrimeSpectrum.asIdeal h).symm
  · intro z hzbot hzP
    by_cases hz_eq_bot : z = (⊥ : PrimeSpectrum L)
    · exact Or.inl hz_eq_bot
    · right
      have hz_le : z.asIdeal ≤ K := by
        simpa [P] using (PrimeSpectrum.le_iff_specializes z P).mpr hzP
      have hz_ne_bot : z.asIdeal ≠ ⊥ := by
        intro hz_bot
        apply hz_eq_bot
        apply PrimeSpectrum.ext
        simpa [hz_bot]
      have hz_height_ge : 1 ≤ z.asIdeal.primeHeight := by
        have hlt : (⊥ : Ideal L) < z.asIdeal := bot_lt_iff_ne_bot.mpr hz_ne_bot
        simpa [hbot_primeHeight] using Ideal.primeHeight_add_one_le_of_lt hlt
      have hz_height_eq : z.asIdeal.primeHeight = 1 := by
        refine le_antisymm ?_ hz_height_ge
        calc
          z.asIdeal.primeHeight ≤ K.primeHeight := Ideal.primeHeight_mono hz_le
          _ = 1 := hK
      have hz_asIdeal_eq : z.asIdeal = K := by
        by_contra hz_ne
        have hz_lt : z.asIdeal < K := lt_of_le_of_ne hz_le (by simpa using hz_ne)
        have hsucc : z.asIdeal.primeHeight + 1 ≤ K.primeHeight :=
          Ideal.primeHeight_add_one_le_of_lt hz_lt
        have hsucc' : ((1 : ℕ∞) + 1) ≤ 1 := by
          simpa [hz_height_eq, hK] using hsucc
        have hnot : ¬ (((1 : ℕ∞) + 1) ≤ 1) := by decide
        exact hnot hsucc'
      exact PrimeSpectrum.ext hz_asIdeal_eq

/-- Helper for Lemma 10.113.1: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    [IsLocalRing L] [IsNoetherianRing L] :
    ∃ n : ℕ, ringKrullDim L = n := by
  -- Convert the finite local dimension into its unique natural-number representative.
  have hbot : ringKrullDim L ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim L ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim L).unbot hbot).toNat
  have hneTop : (ringKrullDim L).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim L).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim L = (ringKrullDim L).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim L) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.113.1: in a Noetherian local catenary domain, quotienting by a height-one
prime lowers the Krull dimension by exactly one. -/
theorem ringKrullDim_quotient_add_eq_of_primeHeight_one_catenary_local_domain
    [IsDomain L] [IsNoetherianRing L] [IsLocalRing L] [IsCatenaryRing L]
    (K : Ideal L) [K.IsPrime] (hK : Ideal.primeHeight K = 1) :
    ringKrullDim (L ⧸ K) + 1 = ringKrullDim L := by
  let P : PrimeSpectrum L := ⟨K, inferInstance⟩
  letI : IsLocalRing (L ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have hδ :
      IsDimensionFunction
        (fun p : PrimeSpectrum L ↦ (((ringKrullDim (L ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) :=
    (isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction (A := L)).1 inferInstance
  have hImmediate :
      IsImmediateSpecialization (⊥ : PrimeSpectrum L) P := by
    -- The height-one source step is now handled by the extracted interval lemma.
    simpa [P] using height_one_prime_isImmediateSpecialization_bot (L := L) K hK
  have hbotQuot :
      ringKrullDim (L ⧸ (⊥ : Ideal L)) = ringKrullDim L := by
    simpa using
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot L : L ⧸ (⊥ : Ideal L) ≃+* L)
  obtain ⟨dQ, hQ⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (L := L ⧸ K)
  obtain ⟨dL, hL⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (L := L)
  have hstepZ :
      (dL : ℤ) = (dQ : ℤ) + 1 := by
    -- Apply the catenary dimension function to the immediate specialization `(0) ⤳ P`.
    simpa [P, hQ, hL, hbotQuot] using hδ.eq_add_one_of_immediateSpecialization hImmediate
  have hstepNat : dQ + 1 = dL := by
    omega
  have hstepWB : (((dQ + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = dL := by
    exact_mod_cast hstepNat
  calc
    ringKrullDim (L ⧸ K) + 1 = (((dQ + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [hQ]
    _ = dL := hstepWB
    _ = ringKrullDim L := hL.symm

end
