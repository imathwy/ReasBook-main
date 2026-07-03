import Mathlib
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.TFAE
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_60_1 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R]

/- Domain sampling:
* Primary domain: order-theoretic strict chains in `Spec R`, viewed through the specialization
  order on `PrimeSpectrum R`.
* Owner declarations inspected in this domain:
  - `LTSeries`
  - `RelSeries.length`
  - `PrimeSpectrum.instPartialOrder`
  - `PrimeSpectrum.asIdeal_lt_asIdeal`
* Best owner abstraction: `LTSeries (PrimeSpectrum R)` is the canonical owner for finite strict
  chains of prime ideals; `RelSeries.length` is derived API on that owner.
* Primitive vs. derived: the chain itself is primitive data, while its length is the canonical
  derived field.
* Source/core/bridge triage: this file is source-facing, but it should remain a direct recall of
  the core/canonical owner abstraction rather than introducing any chapter-local wrapper.
-/

/- Definition 10.60.1: a chain of prime ideals of `R` is the canonical order-theoretic notion
`LTSeries (PrimeSpectrum R)`, i.e. a finite strictly increasing sequence
`𝔭₀ < 𝔭₁ < ⋯ < 𝔭ₙ` in `PrimeSpectrum R`. -/
#check (LTSeries (PrimeSpectrum R))

/- Companion recall: if `p : LTSeries (PrimeSpectrum R)` is a chain of prime ideals, then its
length is the canonical field `p.length`, i.e. `RelSeries.length p`. -/
recall RelSeries.length

end

/-! ### Definition_10_60_2 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R]

/-
Definition 10.60.2 is recalled canonically by `ringKrullDim R`: the Krull dimension of a
commutative ring is the Krull dimension of the topological space `Spec(R)`, equivalently the
supremum of the lengths of strict chains of prime ideals of `R`.
-/
recall ringKrullDim

/- Companion recall: the identification of the Krull dimension of `R` with the topological Krull
dimension of `Spec(R)` is the canonical theorem
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`. -/
recall PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim

end

/-! ### Definition_10_60_3 (from Chap10) -/
/- Definition 10.60.3: the height of a prime ideal `p` of a commutative ring `R` is the canonical
mathlib invariant `Ideal.primeHeight p`. -/
recall Ideal.primeHeight

/-! ### Lemma_10_60_4 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

-- Layering for this item:
-- * source-facing: the maximal-ideal supremum formula in `WithBot ℕ∞`.
-- * core/canonical owner: `Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim` and
--   `Ideal.sup_primeHeight_eq_ringKrullDim`.
-- * bridge/view: lift those `ℕ∞`-valued owner equalities to `WithBot ℕ∞`, and handle the
--   subsingleton ring case separately.
-- Primitive data are just `[CommRing R]`; the displayed suprema are derived from
-- `Ideal.primeHeight`.

private theorem iSup_eq_bot_of_subsingleton
    (P : Ideal R → Prop) (f : ∀ I : Ideal R, P I → WithBot ℕ∞)
    (hP : ∀ ⦃I : Ideal R⦄, P I → I ≠ ⊤) [Subsingleton R] :
    (⨆ (I : Ideal R) (hI : P I), f I hI) = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine iSup_le fun I ↦ iSup_le fun hI ↦ ?_
  exact (hP hI (Subsingleton.elim I ⊤)).elim

private theorem withBot_iSup_eq_ringKrullDim {P : Ideal R → Prop} [Nontrivial R]
    (f : ∀ I : Ideal R, P I → ℕ∞)
    (hP : (↑(⨆ (I : Ideal R) (hI : P I), f I hI) : WithBot ℕ∞) = ringKrullDim R)
    (hne : Nonempty { I : Ideal R // P I }) :
    (⨆ (I : Ideal R) (hI : P I), (f I hI : WithBot ℕ∞)) = ringKrullDim R := by
  letI := hne
  simpa [iSup_subtype', WithBot.coe_iSup (OrderTop.bddAbove _)] using hP

/-- Lemma 10.60.4: the Krull dimension of `R` is the supremum of the heights of its maximal
prime ideals. This is stated in `WithBot ℕ∞`, so it also covers the subsingleton case, where both
sides are `⊥`. -/
theorem ringKrullDim_eq_iSup_primeHeight_maximal :
    (⨆ (I : Ideal R) (_ : I.IsMaximal), (I.primeHeight : WithBot ℕ∞)) = ringKrullDim R := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      haveI := hR
      rw [ringKrullDim_eq_bot_of_subsingleton]
      simpa using iSup_eq_bot_of_subsingleton Ideal.IsMaximal
        (fun (I : Ideal R) (hI : I.IsMaximal) ↦
          (@Ideal.primeHeight _ _ I hI.isPrime : WithBot ℕ∞))
        (fun {I} hI ↦ Ideal.IsMaximal.ne_top hI)
  | inr hR =>
      haveI := hR
      obtain ⟨M, hM⟩ := Ideal.exists_maximal R
      exact withBot_iSup_eq_ringKrullDim
        (fun I hI ↦ @Ideal.primeHeight _ _ I hI.isPrime)
        Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim ⟨⟨M, hM⟩⟩

/-- Lemma 10.60.4, bridge/view form: the Krull dimension of `R` is also the supremum of the
heights of all prime ideals. This is the companion canonical equality
`Ideal.sup_primeHeight_eq_ringKrullDim`, extended to the subsingleton case. -/
theorem ringKrullDim_eq_iSup_primeHeight :
    (⨆ (I : Ideal R) (_ : I.IsPrime), (I.primeHeight : WithBot ℕ∞)) = ringKrullDim R := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      haveI := hR
      rw [ringKrullDim_eq_bot_of_subsingleton]
      simpa using iSup_eq_bot_of_subsingleton Ideal.IsPrime
        (fun (I : Ideal R) (hI : I.IsPrime) ↦
          (@Ideal.primeHeight _ _ I hI : WithBot ℕ∞))
        (fun {I} hI ↦ Ideal.IsPrime.ne_top hI)
  | inr hR =>
      haveI := hR
      obtain ⟨M, hM⟩ := Ideal.exists_maximal R
      exact withBot_iSup_eq_ringKrullDim
        (fun I hI ↦ @Ideal.primeHeight _ _ I hI)
        Ideal.sup_primeHeight_eq_ringKrullDim ⟨⟨M, hM.isPrime⟩⟩

end

/-! ### Lemma_10_60_5 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.60.5: a commutative ring is Artinian if and only if it is Noetherian and has Krull
dimension at most `0`. This is the canonical mathlib theorem
`isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`, which packages both textbook directions:
"Noetherian of dimension `0` implies Artinian" and "Artinian implies Noetherian of dimension
zero". -/
recall isArtinianRing_iff_isNoetherianRing_krullDimLE_zero

end

/-! ### Lemma_10_60_6 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Domain-style sampling for Lemma 10.60.6:
- primary domain: dimension theory for Noetherian local rings via the Hilbert-Samuel polynomial;
- sampled owner declarations:
  `ringKrullDim`,
  `hilbertSamuelPolynomialDegree`,
  `local_noetherian_ring_dimension_tfae`;
- source/core/bridge triage:
  `source-facing`: the equivalence `dim(R) = 0 ↔ d(R) = 0` for a Noetherian local ring;
  `core/canonical`: the chapter owner theorem `local_noetherian_ring_dimension_tfae 0`;
  `bridge/view`: none beyond specializing clauses `(1)` and `(2)` of that owner theorem at `d = 0`.

This item adds no new local data or API beyond that exact specialization, so the correct
statement-stage surface is a labeled recall-style `#check` of the canonical owner theorem rather
than a new wrapper theorem. -/

/- Lemma 10.60.6: for a Noetherian local ring `R`, the Krull-dimension condition `dim(R) = 0` is
equivalent to the vanishing of the Hilbert-Samuel degree invariant `d(R) = 0`; in the project this
is exactly the specialization at `d = 0` of clauses `(1)` and `(2)` of
`local_noetherian_ring_dimension_tfae`. -/
#check
  ((local_noetherian_ring_dimension_tfae 0).out 0 1 rfl rfl :
    ringKrullDim R = 0 ↔ hilbertSamuelPolynomialDegree R R = 0)

end

/-! ### Proposition_10_60_7 (from Chap10) -/
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

/-! ### Lemma_10_60_8 (from Chap10) -/
universe u

open Ideal PrimeSpectrum IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
private theorem parameterIdeal_fin1_eq_span (x : Fin 1 → maximalIdeal R) :
    parameterIdeal x = span ({(x 0 : R)} : Set R) := by
  rw [parameterIdeal_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨0, rfl⟩

omit [IsNoetherianRing R] in
private theorem exists_parameterIdeal_fin1_iff_exists_principal_idealOfDefinition :
    (∃ x : Fin 1 → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ↔
      ∃ I : Ideal R, I.IsIdealOfDefinition ∧ I.IsPrincipal := by
  constructor
  · rintro ⟨x, hxdef⟩
    refine ⟨parameterIdeal x, hxdef, ?_⟩
    refine ⟨(x 0 : R), ?_⟩
    change parameterIdeal x = span ({(x 0 : R)} : Set R)
    exact parameterIdeal_fin1_eq_span x
  · rintro ⟨I, hdef, hI⟩
    let _ : I.IsPrincipal := hI
    obtain ⟨x, hxI⟩ := Submodule.IsPrincipal.principal I
    have hx𝔪 : x ∈ maximalIdeal R := by
      rw [← hdef]
      have hxrad : x ∈ I.radical := by
        rw [hxI]
        exact Ideal.le_radical (Ideal.subset_span (by simp : x ∈ ({x} : Set R)))
      simpa using hxrad
    let x' : Fin 1 → maximalIdeal R := fun _ ↦ ⟨x, hx𝔪⟩
    refine ⟨x', ?_⟩
    simpa [x', hxI, parameterIdeal_fin1_eq_span x'] using hdef

omit [IsNoetherianRing R] in
private theorem no_parameterIdeal_lt_one_iff_bot_not_isIdealOfDefinition :
    (∀ n : ℕ, n < 1 →
      ¬ ∃ x : Fin n → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ↔
        ¬ (⊥ : Ideal R).IsIdealOfDefinition := by
  constructor
  · intro h hbot
    apply h 0 (by decide)
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    simpa [parameterIdeal_eq_span] using hbot
  · intro hbot n hn
    have hn0 : n = 0 := Nat.lt_one_iff.mp hn
    subst hn0
    rintro ⟨x, hx⟩
    exact hbot <| by simpa [parameterIdeal_eq_span] using hx

omit [IsNoetherianRing R] in
private theorem one_generator_parameterIdeal_clause_iff :
    ((∃ x : Fin 1 → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ∧
      ∀ n : ℕ, n < 1 →
        ¬ ∃ x : Fin n → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ↔
      ((∃ I : Ideal R, I.IsIdealOfDefinition ∧ I.IsPrincipal) ∧
        ¬ (⊥ : Ideal R).IsIdealOfDefinition) := by
  constructor
  · rintro ⟨hexists, hmin⟩
    exact ⟨
      exists_parameterIdeal_fin1_iff_exists_principal_idealOfDefinition.mp hexists,
      no_parameterIdeal_lt_one_iff_bot_not_isIdealOfDefinition.mp hmin
    ⟩
  · rintro ⟨hexists, hbot⟩
    exact ⟨
      exists_parameterIdeal_fin1_iff_exists_principal_idealOfDefinition.mpr hexists,
      no_parameterIdeal_lt_one_iff_bot_not_isIdealOfDefinition.mpr hbot
    ⟩

omit [IsNoetherianRing R] in
private theorem zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition (x : R) :
    zeroLocus ({x} : Set R) = ({closedPoint R} : Set (PrimeSpectrum R)) ↔
      (span ({x} : Set R)).IsIdealOfDefinition := by
  have hclosed :
      ({closedPoint R} : Set (PrimeSpectrum R)) =
        PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
    simp [PrimeSpectrum.zeroLocus_eq_singleton, IsLocalRing.closedPoint]
  constructor
  · intro hxzero
    rw [Ideal.IsIdealOfDefinition]
    have hzero :
        PrimeSpectrum.zeroLocus (span ({x} : Set R) : Set R) =
          PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
      rw [PrimeSpectrum.zeroLocus_span]
      exact hxzero.trans hclosed
    simpa [Ideal.IsIdealOfDefinition, (maximalIdeal.isMaximal R).isPrime.radical] using
      (PrimeSpectrum.zeroLocus_eq_iff.mp hzero)
  · intro hxdef
    have hzero :
        PrimeSpectrum.zeroLocus (span ({x} : Set R) : Set R) =
          PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
      refine PrimeSpectrum.zeroLocus_eq_iff.mpr ?_
      simpa [Ideal.IsIdealOfDefinition, (maximalIdeal.isMaximal R).isPrime.radical] using hxdef
    rw [← PrimeSpectrum.zeroLocus_span]
    exact hzero.trans hclosed.symm

-- Source/core/bridge triage:
-- * source-facing: clauses `(3)` and `(4)` keep the textbook witness `x : R`;
-- * core/canonical: clauses `(1)` and `(2)` come from the source-facing owner theorem
--   `local_noetherian_ring_dimension_tfae 1`;
-- * bridge/view: clause `(5)` rewrites the one-generator case of clause `(3)` into the canonical
--   ideal predicate `IsIdealOfDefinition` together with
--   `IsPrincipal`. The extra hypothesis `¬ (⊥ : Ideal R).IsIdealOfDefinition` is exactly the
--   `n = 0` minimality clause and excludes the nilpotent zero-dimensional case. The source-facing
--   clause predicates below package these conjunction-heavy clauses so the public theorem surface
--   stays atomic.
/-- The source-facing clause asserting that a nonnilpotent element cuts out exactly the closed
point of `Spec R`. -/
def ExistsNonnilpotentClosedPointDefiningElement (R : Type u) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∃ x : R, ¬ IsNilpotent x ∧ zeroLocus ({x} : Set R) = ({closedPoint R} : Set (PrimeSpectrum R))

/-- The source-facing clause asserting that a nonnilpotent element generates an ideal of
definition. -/
def ExistsNonnilpotentIdealOfDefinitionGenerator (R : Type u) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∃ x : R, ¬ IsNilpotent x ∧ (span ({x} : Set R)).IsIdealOfDefinition

/-- The canonical existence clause asserting that some ideal of definition is principal. -/
def ExistsPrincipalIdealOfDefinition (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∃ I : Ideal R, I.IsIdealOfDefinition ∧ I.IsPrincipal

/-- The minimality clause asserting that the zero ideal is not an ideal of definition. -/
def ZeroIdealNotIdealOfDefinition (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ¬ (⊥ : Ideal R).IsIdealOfDefinition

/-- The canonical clause combining the existence of a principal ideal of definition with the
exclusion of the zero-dimensional nilpotent case. -/
def OneDimensionalPrincipalIdealCriterion (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ExistsPrincipalIdealOfDefinition R ∧ ZeroIdealNotIdealOfDefinition R

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.60.8: the geometric closed-point clause is equivalent to asking for a
nonnilpotent generator of an ideal of definition. -/
private theorem
    exists_nonnilpotent_closed_point_defining_element_iff_exists_nonnilpotent_idealOfDefinition_generator :
    ExistsNonnilpotentClosedPointDefiningElement R ↔
      ExistsNonnilpotentIdealOfDefinitionGenerator R := by
  constructor
  · rintro ⟨x, hx, hxzero⟩
    -- The same witness `x` converts the vanishing-locus condition into the radical condition.
    refine ⟨x, hx, ?_⟩
    exact (zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition x).mp hxzero
  · rintro ⟨x, hx, hxdef⟩
    -- Reversing the same rewrite recovers the closed-point description of `V(x)`.
    refine ⟨x, hx, ?_⟩
    exact (zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition x).mpr hxdef

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.60.8: if the zero ideal is an ideal of definition, then every element of
the maximal ideal is nilpotent. -/
private theorem nilpotent_of_mem_maximalIdeal_of_zeroIdeal_isIdealOfDefinition
    {x : R} (hbot : (⊥ : Ideal R).IsIdealOfDefinition) (hx : x ∈ maximalIdeal R) :
    IsNilpotent x := by
  -- The zero ideal having maximal radical places `x` in `√(0)`.
  have hxrad : x ∈ (⊥ : Ideal R).radical := by
    rw [Ideal.IsIdealOfDefinition] at hbot
    simpa [hbot] using hx
  -- Membership in `√(0)` is exactly nilpotence.
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxrad
  exact ⟨n, by simpa [Ideal.mem_bot] using hn⟩

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.60.8: the principal ideal-of-definition criterion is equivalent to the
existence of a nonnilpotent generator of an ideal of definition. -/
private theorem
    exists_nonnilpotent_idealOfDefinitionGenerator_iff_oneDimensionalPrincipalIdealCriterion :
    ExistsNonnilpotentIdealOfDefinitionGenerator R ↔
      OneDimensionalPrincipalIdealCriterion R := by
  constructor
  · rintro ⟨x, hx, hxdef⟩
    change ExistsPrincipalIdealOfDefinition R ∧ ZeroIdealNotIdealOfDefinition R
    refine ⟨?_, ?_⟩
    · -- The displayed ideal of definition is principal by construction.
      refine ⟨Ideal.span ({x} : Set R), hxdef, ?_⟩
      exact ⟨x, rfl⟩
    · -- If `(0)` were an ideal of definition, the same element would become nilpotent.
      change ¬ (⊥ : Ideal R).IsIdealOfDefinition
      intro hbot
      have hx𝔪 : x ∈ maximalIdeal R := by
        rw [← hxdef]
        exact Ideal.le_radical (Ideal.subset_span (by simp : x ∈ ({x} : Set R)))
      exact hx <|
        nilpotent_of_mem_maximalIdeal_of_zeroIdeal_isIdealOfDefinition hbot hx𝔪
  · intro hcriterion
    change ExistsPrincipalIdealOfDefinition R ∧ ZeroIdealNotIdealOfDefinition R at hcriterion
    rcases hcriterion with ⟨⟨I, hIdef, hIprincipal⟩, hbot⟩
    let _ : I.IsPrincipal := hIprincipal
    obtain ⟨x, hxI⟩ := Submodule.IsPrincipal.principal I
    have hspan_def : (Ideal.span ({x} : Set R)).IsIdealOfDefinition := by
      -- Rewriting the chosen generator identifies the given principal ideal with `(x)`.
      simpa [hxI] using hIdef
    refine ⟨x, ?_, hspan_def⟩
    intro hxnil
    apply hbot
    rw [Ideal.IsIdealOfDefinition]
    have hspan_radical_eq_bot :
        (Ideal.span ({x} : Set R)).radical = (⊥ : Ideal R).radical := by
      obtain ⟨n, hn⟩ := hxnil
      apply le_antisymm
      · -- Nilpotence of `x` shows that `√((x))` is contained in `√(0)`.
        have hxrad_bot : x ∈ (⊥ : Ideal R).radical := by
          exact Ideal.mem_radical_iff.mpr ⟨n, by simpa [Ideal.mem_bot] using hn⟩
        have hspan_le :
            Ideal.span ({x} : Set R) ≤ (⊥ : Ideal R).radical :=
          (Ideal.span_singleton_le_iff_mem (I := (⊥ : Ideal R).radical) (x := x)).2 hxrad_bot
        calc
          (Ideal.span ({x} : Set R)).radical ≤ ((⊥ : Ideal R).radical).radical :=
            Ideal.radical_mono hspan_le
          _ = (⊥ : Ideal R).radical := Ideal.radical_idem _
      · -- The reverse inclusion is automatic from `(0) ≤ (x)`.
        exact Ideal.radical_mono bot_le
    calc
      (⊥ : Ideal R).radical = (Ideal.span ({x} : Set R)).radical := hspan_radical_eq_bot.symm
      _ = maximalIdeal R := by
        simpa [Ideal.IsIdealOfDefinition] using hspan_def

-- Proof sketch: specialize Proposition 10.60.9 at `d = 1`, rewrite the source-facing one-element
-- parameter-ideal clause using the private equivalences above, and then compare the vanishing-locus
-- and principal-generator formulations through `zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition`.
/-- Lemma 10.60.8: for a Noetherian local ring `R`, the following are equivalent: `dim(R) = 1`,
`d(R) = 1`, there is a nonnilpotent element whose vanishing locus is exactly the closed point,
there is a nonnilpotent element whose principal ideal has radical the maximal ideal, and there is a
principal ideal of definition while the zero ideal is not an ideal of definition. -/
theorem one_dimensional_local_ring_tfae :
    List.TFAE
      [ ringKrullDim R = 1
      , hilbertSamuelPolynomialDegree R R = 1
      , ExistsNonnilpotentClosedPointDefiningElement R
      , ExistsNonnilpotentIdealOfDefinitionGenerator R
      , OneDimensionalPrincipalIdealCriterion R
      ] := by
  have howner := local_noetherian_ring_dimension_tfae (R := R) 1
  -- The owner theorem already identifies the dimension and Hilbert-Samuel clauses.
  tfae_have 1 ↔ 2 := howner.out 0 1
  -- Rewriting the owner one-generator clause yields the source-facing principal criterion.
  tfae_have 1 ↔ 5 := by
    simpa [OneDimensionalPrincipalIdealCriterion, ExistsPrincipalIdealOfDefinition,
      ZeroIdealNotIdealOfDefinition] using
      (howner.out 0 2).trans one_generator_parameterIdeal_clause_iff
  -- The two source formulations keep the same witness `x` and only rewrite the meaning of `V(x)`.
  tfae_have 3 ↔ 4 :=
    exists_nonnilpotent_closed_point_defining_element_iff_exists_nonnilpotent_idealOfDefinition_generator
  -- The final bridge packages the textbook principal-ideal criterion into the source-facing form.
  tfae_have 4 ↔ 5 :=
    exists_nonnilpotent_idealOfDefinitionGenerator_iff_oneDimensionalPrincipalIdealCriterion
  tfae_finish

end
