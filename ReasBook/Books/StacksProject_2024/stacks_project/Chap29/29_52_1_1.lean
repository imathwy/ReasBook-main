import StacksProject_2024.Chap10.Lemma_10_113_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S]

/- Source/core/bridge triage for 29.52.1.1:
- `source-facing`: the local-ring form of the dimension-formula inequality used in Section 29.52;
- `core/canonical`: Chapter 10's prime-spectrum owner theorem
  `primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_trdeg_of_finiteType`
  together with mathlib's localization-height owner
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- `bridge/view`: this file rewrites the prime-height inequality into the local-ring dimension
  surface used downstream in Chapter 29.

The public statement is therefore kept, but its proof should be a direct bridge to the Chapter 10
owner rather than a second independent dimension-formula development.
-/
-- Semantic recall: Lemma `10.113.1` already gives the equivalent height-plus-residue-trdeg
-- inequality; the theorem below packages it in the local-ring-dimension form used in Section 29.52.
/-- Companion bridge for 29.52.1.1: in local-ring form, the Chapter 10 owner theorem says that the
Krull dimension of `S_q` plus the transcendence degree of `κ(q)` over `κ(q ∩ R)` is bounded by the
Krull dimension of `R_(q ∩ R)` together with the transcendence degree of `Frac(S)` over
`Frac(R)`. -/
theorem ringKrullDim_localizationAtPrime_add_residueFieldTrdeg_le_ringKrullDim_localizationAtPrime_under_add_fractionRingTrdeg_of_finiteType
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) + Algebra.fractionRingTrdeg hinj := by
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have hq_ne_top : Ideal.primeHeight q.asIdeal ≠ ⊤ := by
    simpa [Ideal.height_eq_primeHeight] using
      (Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance) : q.asIdeal.height ≠ ⊤)
  have hp_ne_top : Ideal.primeHeight (q.asIdeal.under R) ≠ ⊤ := by
    simpa [Ideal.height_eq_primeHeight] using
      (Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance) :
        (q.asIdeal.under R).height ≠ ⊤)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal,
    IsLocalization.AtPrime.ringKrullDim_eq_height (q.asIdeal.under R),
    Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
  rw [← ENat.coe_toNat hq_ne_top, ← ENat.coe_toNat hp_ne_top]
  have h :
      (((ENat.toNat (Ideal.primeHeight q.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)) : ℕ) :
          WithBot ℕ∞) ≤
        (((ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
              Algebra.fractionRingTrdeg hinj) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast
      primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_trdeg_of_finiteType hinj q
  simpa [Nat.cast_add] using h

/-- 29.52.1.1: for an injective finite type map of domains `R → S` and a point `q : Spec(S)`, the
Krull dimension of the local ring `S_q` is at most the Krull dimension of the local ring
`R_(q ∩ R)` plus the transcendence degree of `Frac(S)` over `Frac(R)`, minus the transcendence
degree of the residue field extension `κ(q) / κ(q ∩ R)`. -/
theorem ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_under_add_fractionRingTrdeg_sub_residueFieldTrdeg_of_finiteType
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
        ((Algebra.fractionRingTrdeg hinj -
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)) : ℕ) := by
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have hq_ne_top : Ideal.primeHeight q.asIdeal ≠ ⊤ := by
    simpa [Ideal.height_eq_primeHeight] using
      (Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance) : q.asIdeal.height ≠ ⊤)
  have hp_ne_top : Ideal.primeHeight (q.asIdeal.under R) ≠ ⊤ := by
    simpa [Ideal.height_eq_primeHeight] using
      (Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance) :
        (q.asIdeal.under R).height ≠ ⊤)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal,
    IsLocalization.AtPrime.ringKrullDim_eq_height (q.asIdeal.under R),
    Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
  rw [← ENat.coe_toNat hq_ne_top, ← ENat.coe_toNat hp_ne_top]
  have hnat :
      ENat.toNat (Ideal.primeHeight q.asIdeal) ≤
        ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
          (Algebra.fractionRingTrdeg hinj -
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)) := by
    have h :=
      primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_trdeg_of_finiteType hinj q
    omega
  have h :
      ((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : WithBot ℕ∞) ≤
        (((ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
              (Algebra.fractionRingTrdeg hinj -
                Cardinal.toNat
                  (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField))) :
            ℕ) :
          WithBot ℕ∞) := by
    exact_mod_cast hnat
  simpa [Nat.cast_add] using h

end
