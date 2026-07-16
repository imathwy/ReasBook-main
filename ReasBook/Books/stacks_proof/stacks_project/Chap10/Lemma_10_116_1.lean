import stacks_proof.stacks_project.Chap10.Lemma_10_114_4
import stacks_proof.stacks_project.Chap10.Lemma_10_114_5
import stacks_proof.stacks_project.Chap10.Lemma_10_116_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling:
- primary domain: Krull dimension and transcendence degree for finite-type domains over a field,
  organized around the chapter's local-dimension owner theorems;
- sampled owner API:
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `FractionRing.algEquiv`;
- best owner abstraction: the local dimension formula at a prime together with the generic-point
  specialization of `Spec S`; the maximal-localization equality is already derived upstream in the
  chapter and should be reused rather than duplicated here;
- primitive data vs derived API: there is no additional source-facing data in this file beyond the
  finite-type domain hypotheses. Both displayed equalities are derived API from the sampled owner
  theorems and the canonical fraction-ring/residue-field identifications at the generic point.

Layer triage:
- `source-facing`: the first theorem, which identifies `ringKrullDim S` with the transcendence
  degree of `FractionRing S`;
- `bridge/view`: the maximal-localization theorem, which should be a thin corollary of the first
  theorem and Lemma `10.114.4`.
-/

theorem topologicalKrullDimAt_genericPoint_eq_ringKrullDim :
    topologicalKrullDimAt (⊥ : PrimeSpectrum S) = ringKrullDim S := by
  rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
    (⊥ : PrimeSpectrum S)]
  obtain ⟨m0⟩ : Nonempty (MaximalSpectrum S) := by infer_instance
  refine le_antisymm ?_ ?_
  · let m : { m : MaximalSpectrum S // (⊥ : PrimeSpectrum S).asIdeal ≤ m.asIdeal } :=
      ⟨m0, by simp⟩
    exact (iInf_le
      (fun m : { m : MaximalSpectrum S // (⊥ : PrimeSpectrum S).asIdeal ≤ m.asIdeal } ↦
        ringKrullDim (Localization.AtPrime m.1.asIdeal)) m).trans <| by
          simpa using
            (ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
              m0).symm.le
  · refine le_iInf fun m ↦ ?_
    simpa using
      (ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
        m.1).le

private noncomputable def genericResidueFieldEquiv :
    FractionRing S ≃ₐ[S] ((⊥ : Ideal S).ResidueField) := by
  let e : S ≃ₐ[S] S ⧸ (⊥ : Ideal S) := (AlgEquiv.quotientBot S S).symm
  letI : IsFractionRing S ((⊥ : Ideal S).ResidueField) := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap S ((⊥ : Ideal S).ResidueField) x =
      algebraMap (S ⧸ (⊥ : Ideal S)) ((⊥ : Ideal S).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    exact show
        algebraMap (S ⧸ (⊥ : Ideal S)) ((⊥ : Ideal S).ResidueField)
            (Ideal.Quotient.mk (⊥ : Ideal S) x) =
          algebraMap S ((⊥ : Ideal S).ResidueField) x by
      rfl
  exact FractionRing.algEquiv S ((⊥ : Ideal S).ResidueField)

private lemma ringKrullDim_localizationAtPrime_bot_eq_zero :
    ringKrullDim (Localization.AtPrime (⊥ : Ideal S)) = 0 := by
  letI : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization ((⊥ : Ideal S).primeCompl)
        (Localization.AtPrime (⊥ : Ideal S)))
  let e : FractionRing S ≃ₐ[S] Localization.AtPrime (⊥ : Ideal S) :=
    FractionRing.algEquiv S (Localization.AtPrime (⊥ : Ideal S))
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact ringKrullDim_eq_zero_of_field (FractionRing S)

-- Proof sketch: write `S` as a quotient of a polynomial ring over `k`, apply Noether
-- normalization to obtain a finite injective map from a polynomial ring in `d = ringKrullDim S`
-- variables, and use the algebraic independence of the source variables in the fraction field of
-- `S` together with finiteness of the induced fraction-field extension to identify `d` with
-- `Cardinal.toNat (Algebra.trdeg k (FractionRing S))`.
/-- Lemma 10.116.1: if `S` is a finite type `k`-algebra that is an integral domain, then the Krull
dimension of `S` equals the transcendence degree of its fraction field over `k`. -/
@[stacks 00P0]
theorem ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field :
    ringKrullDim S = Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
  have hlocal :
      topologicalKrullDimAt (⊥ : PrimeSpectrum S) =
        ringKrullDim (Localization.AtPrime (⊥ : Ideal S)) +
          Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField)) :=
    topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
      (⊥ : PrimeSpectrum S)
  have hgeneric :
      ringKrullDim S =
        Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField)) := by
    simpa [PrimeSpectrum.asIdeal_bot, topologicalKrullDimAt_genericPoint_eq_ringKrullDim,
      ringKrullDim_localizationAtPrime_bot_eq_zero] using hlocal
  have htrdeg_bot :
      (Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField)) : WithBot ℕ∞) =
        Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
    let e : FractionRing S ≃ₐ[k] ((⊥ : Ideal S).ResidueField) :=
      genericResidueFieldEquiv.restrictScalars k
    simpa using congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞))
      (congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e).symm)
  exact hgeneric.trans htrdeg_bot

-- Proof sketch: by Lemma `10.114.3`, all local rings of a finite type domain over a field at
-- maximal ideals have the same Krull dimension. Apply the main theorem to compute that common
-- value as the transcendence degree of `FractionRing S` over `k`.
/-- Every localization of a finite type domain over a field at a maximal ideal has Krull dimension
equal to the transcendence degree of the fraction field. -/
theorem ringKrullDim_localizationAtMaximal_eq_trdeg_fractionRing_of_finiteType_domain_over_field
    (m : MaximalSpectrum S) :
    ringKrullDim (Localization.AtPrime m.asIdeal) =
      Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
  rw [← ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
    m]
  exact ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field

end
