import Mathlib
import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_32_1
import stacks_proof.stacks_project.Chap10.Lemma_10_32_5
import stacks_proof.stacks_project.Chap10.Lemma_10_53_5
import stacks_proof.stacks_project.Chap10.Lemma_10_60_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

-- Proof sketch: combine Lemmas `10.53.5`, `10.53.6`, `10.60.5`, and `10.60.6`. The canonical
-- equivalences identify Artinian rings with Noetherian zero-dimensional rings and with finite
-- length over themselves; Artinian rings split as finite products of their localizations at maximal
-- ideals, and for Noetherian local rings the dimension-zero, Hilbert-Samuel-degree-zero, finite-
-- length, and nilpotent-maximal-ideal conditions are equivalent. The remaining clauses are the
-- standard zero-dimensional spectrum reformulations.
/-- Proposition 10.60.7: for a commutative ring `R`, the Artinian condition is equivalent to the
listed Noetherian, finite-length, finite-product, discrete-spectrum, nilpotent-Jacobson, and
prime-incomparability formulations. The textbook clause “Noetherian of dimension `0`” is recorded
in the canonical mathlib form `IsNoetherianRing R ∧ Ring.KrullDimLE 0 R`, which avoids the zero-
ring edge case of `ringKrullDim R = 0`, and clause `(7)` keeps the source-faithful Hilbert-Samuel
degree condition. Clause `(5)` uses the owner predicate `DiscreteTopology (PrimeSpectrum R)`,
leaving finiteness of `PrimeSpectrum R` as derived API via compactness and
`PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`. Clauses `(4)`, `(6)`, `(7)`, and
`(8)` are stated as direct existential finite-product decompositions, avoiding the non-canonical
public wrapper structures that previously repackaged this data. -/
@[stacks 00KJ]
theorem isArtinianRing_tfae :
    List.TFAE
      [ IsArtinianRing R
      , IsNoetherianRing R ∧ Ring.KrullDimLE 0 R
      , IsFiniteLength R R
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : R ≃+* ∀ i, S i),
          ∀ i, IsArtinianRing (S i)
      , IsNoetherianRing R ∧ DiscreteTopology (PrimeSpectrum R)
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : ∀ i, IsNoetherianRing (S i)) (_ : R ≃+* ∀ i, S i),
          ∀ i, Ring.KrullDimLE 0 (S i)
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : ∀ i, IsNoetherianRing (S i)) (_ : R ≃+* ∀ i, S i),
          ∀ i, hilbertSamuelPolynomialDegree (S i) (S i) = 0
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : ∀ i, IsNoetherianRing (S i)) (_ : R ≃+* ∀ i, S i),
          ∀ i, IsNilpotent (IsLocalRing.maximalIdeal (S i))
      , IsNoetherianRing R ∧
          Finite (MaximalSpectrum R) ∧
          IsNilpotent (Ring.jacobson R)
      , IsNoetherianRing R ∧
          ∀ ⦃p q : Ideal R⦄, p.IsPrime → q.IsPrime → p ≤ q → p = q
      ] := by
  classical
  tfae_have 1 ↔ 2 := isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
  tfae_have 1 ↔ 3 := isArtinianRing_iff_isFiniteLength R
  tfae_have 4 → 6 := by
    rintro ⟨ι, hι, S, hComm, hLocal, e, hArt⟩
    let _ : Fintype ι := hι
    let _ : ∀ i, CommRing (S i) := hComm
    let _ : ∀ i, IsLocalRing (S i) := hLocal
    refine ⟨ι, hι, S, hComm, hLocal, ?_, e, ?_⟩
    · intro i
      let _ : IsArtinianRing (S i) := hArt i
      infer_instance
    · intro i
      let _ : IsArtinianRing (S i) := hArt i
      exact (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp (hArt i)).2
  tfae_have 6 → 7 := by
    rintro ⟨ι, hι, S, hComm, hLocal, hNoeth, e, hdim⟩
    let _ : Fintype ι := hι
    let _ : ∀ i, CommRing (S i) := hComm
    let _ : ∀ i, IsLocalRing (S i) := hLocal
    let _ : ∀ i, IsNoetherianRing (S i) := hNoeth
    refine ⟨ι, hι, S, hComm, hLocal, hNoeth, e, ?_⟩
    intro i
    have hzero : ringKrullDim (S i) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp (hdim i)
    exact (((local_noetherian_ring_dimension_tfae 0).out 0 1 rfl rfl).mp hzero)
  tfae_have 7 → 8 := by
    rintro ⟨ι, hι, S, hComm, hLocal, hNoeth, e, hdeg⟩
    let _ : Fintype ι := hι
    let _ : ∀ i, CommRing (S i) := hComm
    let _ : ∀ i, IsLocalRing (S i) := hLocal
    let _ : ∀ i, IsNoetherianRing (S i) := hNoeth
    refine ⟨ι, hι, S, hComm, hLocal, hNoeth, e, ?_⟩
    intro i
    have hzero : ringKrullDim (S i) = 0 :=
      ((local_noetherian_ring_dimension_tfae 0).out 0 1 rfl rfl).mpr (hdeg i)
    have hdim : Ring.KrullDimLE 0 (S i) := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hzero
    have hArt : IsArtinianRing (S i) := (isArtinianRing_iff_krullDimLE_zero).mpr hdim
    exact (isArtinianRing_iff_isNilpotent_maximalIdeal (S i)).mp hArt
  tfae_have 8 → 1 := by
    rintro ⟨ι, hι, S, hComm, hLocal, hNoeth, e, hnil⟩
    let _ : Fintype ι := hι
    let _ : ∀ i, CommRing (S i) := hComm
    let _ : ∀ i, IsLocalRing (S i) := hLocal
    let _ : ∀ i, IsNoetherianRing (S i) := hNoeth
    let _ : ∀ i, IsArtinianRing (S i) := fun i ↦
      (isArtinianRing_iff_isNilpotent_maximalIdeal (S i)).mpr (hnil i)
    let _ : IsArtinianRing (∀ i, S i) := inferInstance
    exact e.symm.isArtinianRing
  tfae_have 4 → 1 := by
    rintro ⟨ι, hι, S, hComm, hLocal, e, hArt⟩
    let _ : Fintype ι := hι
    let _ : ∀ i, CommRing (S i) := hComm
    let _ : ∀ i, IsArtinianRing (S i) := hArt
    let _ : IsArtinianRing (∀ i, S i) := inferInstance
    exact e.symm.isArtinianRing
  tfae_have 1 → 9 := by
    intro h
    let _ : IsArtinianRing R := h
    refine ⟨inferInstance, inferInstance, ?_⟩
    simpa [Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)))
  tfae_have 9 → 4 := by
    rintro ⟨hNoeth, hfin, hjac⟩
    let _ : IsNoetherianRing R := hNoeth
    have hjac' : (Ring.jacobson R).IsLocallyNilpotent := by
      rw [Ideal.isLocallyNilpotent_iff]
      exact (Ideal.forall_mem_isNilpotent_iff_isNilpotent (Ring.jacobson R)).2 hjac
    haveI : DiscreteTopology (PrimeSpectrum R) :=
      primeSpectrum_discreteTopology_of_finite_of_jacobson_locallyNilpotent hfin hjac'
    have hdim : Ring.KrullDimLE 0 R :=
      (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).2
    let _ : IsArtinianRing R :=
      (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨hNoeth, hdim⟩
    let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
    refine
      ⟨MaximalSpectrum R, inferInstance, fun I ↦ Localization.AtPrime I.asIdeal,
        fun _ ↦ inferInstance, fun _ ↦ inferInstance,
        maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent hfin hjac',
        ?_⟩
    intro I
    change IsArtinianRing (Localization I.asIdeal.primeCompl)
    infer_instance
  tfae_have 9 → 5 := by
    rintro ⟨hNoeth, hfin, hjac⟩
    let _ : IsNoetherianRing R := hNoeth
    have hjac' : (Ring.jacobson R).IsLocallyNilpotent := by
      rw [Ideal.isLocallyNilpotent_iff]
      exact (Ideal.forall_mem_isNilpotent_iff_isNilpotent (Ring.jacobson R)).2 hjac
    let _ : DiscreteTopology (PrimeSpectrum R) :=
      primeSpectrum_discreteTopology_of_finite_of_jacobson_locallyNilpotent hfin hjac'
    exact ⟨hNoeth, inferInstance⟩
  tfae_have 5 → 2 := by
    rintro ⟨hNoeth, hdisc⟩
    exact
      ⟨hNoeth, (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2⟩
  tfae_have 2 → 10 := by
    rintro ⟨hNoeth, hdim⟩
    refine ⟨hNoeth, ?_⟩
    intro p q hp hq hpq
    have hpmax : p.IsMaximal := Ring.krullDimLE_zero_iff.mp hdim p hp
    exact hpmax.eq_of_le hq.ne_top hpq
  tfae_have 10 → 2 := by
    rintro ⟨hNoeth, hinc⟩
    refine ⟨hNoeth, Ring.KrullDimLE.mk₀ ?_⟩
    intro p hp
    obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
    exact hinc hp hm.isPrime hpm ▸ hm
  tfae_finish

end
