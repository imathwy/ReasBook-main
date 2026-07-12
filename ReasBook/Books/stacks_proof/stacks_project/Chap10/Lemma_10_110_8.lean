import Mathlib.Tactic.TFAE
import Mathlib.Tactic.StacksAttribute
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Lemma_10_72_3
import StacksProject_2024.Chap10.Lemma_10_109_13
import StacksProject_2024.Chap10.Lemma_10_110_2
import StacksProject_2024.Chap10.Proposition_10_110_5
import StacksProject_2024.Chap10.Proposition_10_110_1.SameUniverseProjective

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open CategoryTheory
open IsLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: homological and local characterizations of regular Noetherian rings;
* sampled owner declarations:
  `IsFiniteGlobalDimensionRing`,
  `IsRegularRing`,
  `globalDimension`,
  `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal`,
  `isRegularLocalRing_iff_isFiniteGlobalDimensionRing`;
* best owner abstraction: the core owners are `IsFiniteGlobalDimensionRing R` and
  `IsRegularRing R`; the fixed-`n` statements in this file should therefore use those owners
  directly, with only the equalities and localization bounds kept as source-facing clauses;
* primitive data vs. derived API: the owner predicates above are primitive, while the four fixed-
  `n` textbook clauses are derived API;
* source/core/bridge triage:
  `source-facing`: the fixed-`n` TFAE theorem and its four textbook clauses;
  `core/canonical`: `IsFiniteGlobalDimensionRing R`, `IsRegularRing R`, and the local equality
    theorem from Proposition `10.110.5`;
  `bridge/view`: the maximal-local finite-global-dimension criterion
    `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal` and the local
    equivalence `isRegularLocalRing_iff_isFiniteGlobalDimensionRing`.
-/

-- Semantic search note: `lean_leansearch` was unavailable (HTTP 502), so the owner choices below
-- were checked directly against the local chapter files `10.109.10`, `10.110.2`, and `10.110.5`.

-- Proof sketch: apply the canonical maximal-local criterion
-- `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal` together with the
-- regular-local global-dimension bound from Proposition `10.110.1`. The converse direction from
-- finite global dimension to regular-locality reuses the residue-field projective-dimension bound
-- from Lemma `10.110.4` together with the cotangent-space lower bound from Lemma `10.110.3`.
-- Definition `10.110.7` then
-- upgrades the resulting primewise regularity to `IsRegularRing R`, and maximal/prime witnesses
-- pin down the common integer `n`.

/-- Helper for Chap10 Lemma 10 110 8: on a finite-global-dimension ring, any upper bound for
`globalDimension A` induces the corresponding `HasGlobalDimensionLE A n` instance. -/
lemma hasGlobalDimensionLE_of_globalDimension_le
    {A : Type u} [CommRing A] [IsFiniteGlobalDimensionRing A] {n : ℕ}
    (hn : globalDimension A ≤ n) :
    HasGlobalDimensionLE A n := by
  -- Upgrade the canonical `globalDimension A` bound modulewise along monotonicity of projective
  -- dimension bounds.
  refine ⟨fun M ↦ ?_⟩
  let _ : HasProjectiveDimensionLE M (globalDimension A) := inferInstance
  exact CategoryTheory.hasProjectiveDimensionLT_of_ge
    M (globalDimension A + 1) (n + 1) (Nat.succ_le_succ hn)

/-- Helper for Chap10 Lemma 10 110 8: finite global dimension is preserved by localization at a
prime ideal. -/
lemma finiteGlobalDimension_localizationAtPrime
    {A : Type u} [CommRing A] [IsFiniteGlobalDimensionRing A] (p : PrimeSpectrum A) :
    IsFiniteGlobalDimensionRing (Localization.AtPrime p.asIdeal) := by
  -- Transport a global-dimension bound on `A` across the localization instance.
  rcases (inferInstance : IsFiniteGlobalDimensionRing A).exists_bound with ⟨n, hn⟩
  let _ : HasGlobalDimensionLE A n := hn
  exact ⟨⟨n, inferInstance⟩⟩

/-- Helper for Chap10 Lemma 10 110 8: the ambient global dimension is a valid localization bound at
any prime ideal. -/
lemma hasGlobalDimensionLE_localizationAtPrime_globalDimension
    {A : Type u} [CommRing A] [IsFiniteGlobalDimensionRing A] (p : PrimeSpectrum A) :
    HasGlobalDimensionLE (Localization.AtPrime p.asIdeal) (globalDimension A) := by
  -- The ambient global-dimension owner already provides the required numeric bound, and
  -- localization preserves that owner bound.
  let _ : HasGlobalDimensionLE A (globalDimension A) := inferInstance
  infer_instance

/-- Helper for Chap10 Lemma 10 110 8: if `globalDimension A = n`, then every prime localization
has Krull dimension at most `n`. -/
lemma ringKrullDim_localizationAtPrime_le_of_globalDimension_eq
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A] {n : ℕ}
    (hfinite : IsFiniteGlobalDimensionRing A) (hdim : globalDimension A = n)
    (p : PrimeSpectrum A) :
    ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n := by
  let _ : IsFiniteGlobalDimensionRing A := hfinite
  -- Route correction: reuse Proposition `10.110.5` on the localized ring instead of rebuilding
  -- the local Krull/global-dimension comparison in this file.
  let _ : IsFiniteGlobalDimensionRing (Localization.AtPrime p.asIdeal) :=
    finiteGlobalDimension_localizationAtPrime p
  have hlocalEq :
      ringKrullDim (Localization.AtPrime p.asIdeal) =
        globalDimension (Localization.AtPrime p.asIdeal) :=
    (regularLocal_and_ringKrullDim_eq_globalDimension_of_finiteGlobalDimension
      (A := Localization.AtPrime p.asIdeal)).2
  have hlocalLe' :
      (globalDimension (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) ≤ globalDimension A := by
    let _ :
        HasGlobalDimensionLE (Localization.AtPrime p.asIdeal) (globalDimension A) :=
      hasGlobalDimensionLE_localizationAtPrime_globalDimension (A := A) p
    exact_mod_cast globalDimension_le (R := Localization.AtPrime p.asIdeal)
  have hdim' : (globalDimension A : WithBot ℕ∞) = n := by
    exact_mod_cast hdim
  calc
    ringKrullDim (Localization.AtPrime p.asIdeal)
        = globalDimension (Localization.AtPrime p.asIdeal) := hlocalEq
    _ ≤ globalDimension A := hlocalLe'
    _ = n := hdim'

/-- Helper for Chap10 Lemma 10 110 8: a Noetherian local ring of finite global dimension should be
regular local. -/
lemma isRegularLocalRing_of_finiteGlobalDimension
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsFiniteGlobalDimensionRing A] :
    IsRegularLocalRing A := by
  -- Route correction: Proposition `10.110.5` already packages the local equivalence, so use its
  -- finite-global-dimension-to-regular-local direction directly.
  exact
    ((residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae
      (R := A)).out 1 2).mp (show IsFiniteGlobalDimensionRing A from inferInstance)

/-- Helper for Chap10 Lemma 10 110 8: on a Noetherian local ring, finite global dimension gives
both regular-locality and the local Krull/global-dimension equality used in the localization
clauses. -/
lemma regularLocal_and_ringKrullDim_eq_globalDimension_of_finiteGlobalDimension
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsFiniteGlobalDimensionRing A] :
    IsRegularLocalRing A ∧ ringKrullDim A = globalDimension A := by
  constructor
  · -- The local TFAE already identifies finite global dimension with regular-locality.
    exact isRegularLocalRing_of_finiteGlobalDimension (A := A)
  · -- The same owner theorem identifies the local Krull and global dimensions.
    symm
    exact globalDimension_eq_ringKrullDim_of_finiteGlobalDimension (R := A)

/-- Helper for Chap10 Lemma 10 110 8: a regular local ring of Krull dimension `d` has global
dimension at most `d`. -/
lemma hasGlobalDimensionLE_of_regularLocalRing_ringKrullDim_eq
    {A : Type u} [CommRing A] [IsRegularLocalRing A] {d : ℕ}
    (hdim : ringKrullDim A = d) :
    HasGlobalDimensionLE A d := by
  -- Reduce the ambient bound to the cyclic-quotient criterion, then apply the regular-local
  -- projective-dimension bound to each cyclic quotient.
  exact ((globalDimensionLE_tfae_finite_and_cyclic_modules (R := A) d).out 2 0).mp
    (fun I ↦ by
      by_cases hI : I = ⊤
      · subst hI
        have hzero :
            Limits.IsZero (ModuleCat.of A (A ⧸ (⊤ : Ideal A))) := by
          exact
            (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of A (A ⧸ (⊤ : Ideal A)))).2
              inferInstance
        have hpd0 :
            HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ (⊤ : Ideal A))) 0 :=
          (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
            (ModuleCat.of A (A ⧸ (⊤ : Ideal A)))).1 hzero.projective
        let _ : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ (⊤ : Ideal A))) 0 := hpd0
        exact
          CategoryTheory.hasProjectiveDimensionLT_of_ge
            (X := ModuleCat.of A (A ⧸ (⊤ : Ideal A))) 1 (d + 1)
            (Nat.succ_le_succ (Nat.zero_le d))
      · obtain ⟨e, hdepth⟩ := exists_nat_moduleDepth_of_proper_quotient (R := A) hI
        have hpd :
            HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ I)) (d - e) :=
          hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing_same_universe
            (R := A) (M₀ := A ⧸ I) hdim hdepth
        let _ : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ I)) (d - e) := hpd
        exact
          CategoryTheory.hasProjectiveDimensionLT_of_ge
            (X := ModuleCat.of A (A ⧸ I)) (d - e + 1) (d + 1)
            (Nat.succ_le_succ (Nat.sub_le _ _)))

/-- Helper for Chap10 Lemma 10 110 8: a regular local ring of Krull dimension at most `n` has
global dimension at most `n`. -/
lemma hasGlobalDimensionLE_of_regularLocalRing_ringKrullDim_le
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {n : ℕ}
    (hreg : IsRegularLocalRing A) (hdim : ringKrullDim A ≤ n) :
    HasGlobalDimensionLE A n := by
  let _ : IsRegularLocalRing A := hreg
  let d : ℕ := Module.finrank (ResidueField A) (CotangentSpace A)
  have hdimEq : ringKrullDim A = d := by
    simpa [d] using
      ((IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp hreg).symm
  let _ : HasGlobalDimensionLE A d :=
    hasGlobalDimensionLE_of_regularLocalRing_ringKrullDim_eq (A := A) hdimEq
  let _ : IsFiniteGlobalDimensionRing A := ⟨⟨d, inferInstance⟩⟩
  have hglobalLe : globalDimension A ≤ n := by
    have hd_le_nat : d ≤ n := by
      exact_mod_cast (show (d : WithBot ℕ∞) ≤ n from by simpa [hdimEq] using hdim)
    calc
      globalDimension A ≤ d := globalDimension_le (R := A)
      _ ≤ n := hd_le_nat
  exact hasGlobalDimensionLE_of_globalDimension_le (A := A) hglobalLe

/-- Helper for Chap10 Lemma 10 110 8: primewise regular-locality reconstructs the global regular
ring owner. -/
lemma isRegularRing_of_localizationsAtPrime
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hA : ∀ p : PrimeSpectrum A, IsRegularLocalRing (Localization.AtPrime p.asIdeal)) :
    IsRegularRing A :=
  { toIsNoetherian := inferInstance
    isRegularLocalRing_atPrime := hA }

/-- Helper for Chap10 Lemma 10 110 8: a maximal-local dimension witness is also a prime-local
witness. -/
lemma exists_primeLocalization_eq_of_maximalLocalization_eq
    {A : Type u} [CommRing A] {n : WithBot ℕ∞}
    (hA : ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n) :
    ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n := by
  rcases hA with ⟨m, hm⟩
  have hm' : ringKrullDim (Localization.AtPrime m.toPrimeSpectrum.asIdeal) = n := by
    simpa using hm
  exact ⟨m.toPrimeSpectrum, hm'⟩

/-- Helper for Chap10 Lemma 10 110 8: a Krull-dimension equality with a natural number gives the
canonical finiteness owner for Krull dimension. -/
lemma finiteRingKrullDim_of_eq_nat
    {A : Type u} [CommRing A] {n : ℕ} (hA : ringKrullDim A = n) :
    FiniteRingKrullDim A := by
  -- A natural-number value rules out both `⊥` and `⊤`, which is exactly the canonical finiteness
  -- criterion for Krull dimension.
  refine (finiteRingKrullDim_iff_ne_bot_and_top (R := A)).2 ?_
  constructor
  · intro hbot
    have : ((n : WithBot ℕ∞) = ⊥) := by
      simpa [hA] using hbot
    cases this
  · intro htop
    have : ((n : WithBot ℕ∞) = ⊤) := by
      simpa [hA] using htop
    cases this

/-- Helper for Chap10 Lemma 10 110 8: some maximal localization realizes the global dimension of a
Noetherian ring with finite global dimension. -/
lemma exists_maximalLocalization_eq_ringKrullDim
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A] [FiniteRingKrullDim A] :
    ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = ringKrullDim A := by
  -- Choose a maximal ideal of maximal height and rewrite its height as the localization dimension.
  obtain ⟨m, hmMax, hmHeight⟩ :
      ∃ m : Ideal A, m.IsMaximal ∧ m.height = ringKrullDim A := Ideal.exists_isMaximal_height
  let mSpec : MaximalSpectrum A := ⟨m, hmMax⟩
  refine ⟨mSpec, ?_⟩
  calc
    ringKrullDim (Localization.AtPrime mSpec.asIdeal) = mSpec.asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height mSpec.asIdeal
        (Localization.AtPrime mSpec.asIdeal)
    _ = ringKrullDim A := by
      simpa [mSpec] using hmHeight

/-- Helper for Chap10 Lemma 10 110 8: if `globalDimension A = n`, then some maximal localization
realizes `n` as its global dimension. -/
lemma exists_maximalLocalization_eq_globalDimension
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A] [IsFiniteGlobalDimensionRing A]
    {n : ℕ} (hdim : globalDimension A = n) :
    ∃ m : MaximalSpectrum A,
      ∃ _ : IsFiniteGlobalDimensionRing (Localization.AtPrime m.asIdeal),
        globalDimension (Localization.AtPrime m.asIdeal) = n := by
  by_cases hzero : n = 0
  · classical
    let m : MaximalSpectrum A := Classical.choice inferInstance
    let hlocal : IsFiniteGlobalDimensionRing (Localization.AtPrime m.asIdeal) :=
      finiteGlobalDimension_localizationAtPrime m.toPrimeSpectrum
    let _ : IsFiniteGlobalDimensionRing (Localization.AtPrime m.asIdeal) := hlocal
    have hle : globalDimension (Localization.AtPrime m.asIdeal) ≤ 0 := by
      let _ :
          HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) (globalDimension A) :=
        hasGlobalDimensionLE_localizationAtPrime_globalDimension (A := A) m.toPrimeSpectrum
      calc
        globalDimension (Localization.AtPrime m.asIdeal) ≤ globalDimension A :=
          globalDimension_le (R := Localization.AtPrime m.asIdeal)
        _ = 0 := hdim.trans hzero
    have hlocalEqZero : globalDimension (Localization.AtPrime m.asIdeal) = 0 := by
      simpa [hzero] using Nat.eq_zero_of_le_zero hle
    exact ⟨m, hlocal, hlocalEqZero⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    by_contra hmax
    have hbound :
        ∀ m : MaximalSpectrum A, HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) k := by
      intro m
      let _ : IsFiniteGlobalDimensionRing (Localization.AtPrime m.asIdeal) :=
        finiteGlobalDimension_localizationAtPrime m.toPrimeSpectrum
      have hle : globalDimension (Localization.AtPrime m.asIdeal) ≤ n := by
        let _ :
            HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) (globalDimension A) :=
          hasGlobalDimensionLE_localizationAtPrime_globalDimension (A := A) m.toPrimeSpectrum
        calc
          globalDimension (Localization.AtPrime m.asIdeal) ≤ globalDimension A :=
            globalDimension_le (R := Localization.AtPrime m.asIdeal)
          _ = n := hdim
      have hne : globalDimension (Localization.AtPrime m.asIdeal) ≠ n := by
        intro hlocal
        exact hmax ⟨m, finiteGlobalDimension_localizationAtPrime m.toPrimeSpectrum, hlocal⟩
      have hlt : globalDimension (Localization.AtPrime m.asIdeal) < n :=
        Nat.lt_of_le_of_ne hle hne
      have hle_k : globalDimension (Localization.AtPrime m.asIdeal) ≤ k := by
        have hltSucc : globalDimension (Localization.AtPrime m.asIdeal) < k + 1 := by
          simpa [hk] using hlt
        simpa [hk] using Nat.lt_succ_iff.mp hltSucc
      exact hasGlobalDimensionLE_of_globalDimension_le (A := Localization.AtPrime m.asIdeal) hle_k
    have hglobal : HasGlobalDimensionLE A k :=
      hasGlobalDimensionLE_of_uniform_bound_localizationAtMaximal (R := A) hbound
    let _ : HasGlobalDimensionLE A k := hglobal
    have hle : globalDimension A ≤ k := globalDimension_le (R := A)
    have : n ≤ k := by simpa [hdim] using hle
    have hsucc : k + 1 ≤ k := by
      simpa [hk] using this
    exact Nat.not_succ_le_self k hsucc

/-- Helper for Chap10 Lemma 10 110 8: if `globalDimension A = n`, then some prime localization has
Krull dimension exactly `n`. -/
lemma exists_primeLocalization_eq_of_globalDimension_eq
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A] [IsFiniteGlobalDimensionRing A]
    {n : ℕ} (hdim : globalDimension A = n) :
    ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n := by
  -- Route correction: find a maximal localization whose global dimension realizes `n`, then use
  -- the local equality theorem on that localization.
  rcases exists_maximalLocalization_eq_globalDimension (A := A) hdim with ⟨m, hfinite, hm⟩
  let _ : IsFiniteGlobalDimensionRing (Localization.AtPrime m.asIdeal) := hfinite
  have hm' : ringKrullDim (Localization.AtPrime m.asIdeal) = n := by
    -- The packaged local consequence of finite global dimension supplies the needed equality.
    calc
      ringKrullDim (Localization.AtPrime m.asIdeal)
          = globalDimension (Localization.AtPrime m.asIdeal) :=
            (regularLocal_and_ringKrullDim_eq_globalDimension_of_finiteGlobalDimension
              (A := Localization.AtPrime m.asIdeal)).2
      _ = n := by
        exact_mod_cast hm
  exact exists_primeLocalization_eq_of_maximalLocalization_eq ⟨m, hm'⟩

/-- Helper for Chap10 Lemma 10 110 8: a maximal-local dimension witness forces the corresponding
lower bound on the ambient global dimension. -/
lemma le_globalDimension_of_maximalLocalization_eq
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A]
    [IsFiniteGlobalDimensionRing A] {n : ℕ} {m : MaximalSpectrum A}
    (hmEq : ringKrullDim (Localization.AtPrime m.asIdeal) = n) :
    n ≤ globalDimension A := by
  let _ : IsFiniteGlobalDimensionRing (Localization.AtPrime m.asIdeal) :=
    finiteGlobalDimension_localizationAtPrime m.toPrimeSpectrum
  have hlocalLe' :
      (globalDimension (Localization.AtPrime m.asIdeal) : WithBot ℕ∞) ≤ globalDimension A := by
    let _ :
        HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) (globalDimension A) :=
      hasGlobalDimensionLE_localizationAtPrime_globalDimension (A := A) m.toPrimeSpectrum
    exact_mod_cast globalDimension_le (R := Localization.AtPrime m.asIdeal)
  have hdimGe' : (n : WithBot ℕ∞) ≤ globalDimension A := by
    -- The local equality theorem identifies the chosen local Krull dimension with local global
    -- dimension, and localization cannot increase global dimension.
    calc
      (n : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime m.asIdeal) := hmEq.symm
      _ = globalDimension (Localization.AtPrime m.asIdeal) := by
        exact
          (regularLocal_and_ringKrullDim_eq_globalDimension_of_finiteGlobalDimension
            (A := Localization.AtPrime m.asIdeal)).2
      _ ≤ globalDimension A := hlocalLe'
  exact_mod_cast hdimGe'

/-- Helper for Chap10 Lemma 10 110 8: the finite-global-dimension clause used in the TFAE list. -/
private def finiteGlobalDimensionClause (A : Type u) [CommRing A] (n : ℕ) : Prop :=
  ∃ _ : IsFiniteGlobalDimensionRing A, globalDimension A = n

/-- Helper for Chap10 Lemma 10 110 8: the regular-ring-and-dimension clause used in the TFAE
list. -/
private def regularRingDimensionClause (A : Type u) [CommRing A] (n : ℕ) : Prop :=
  IsRegularRing A ∧ ringKrullDim A = n

/-- Helper for Chap10 Lemma 10 110 8: the maximal-local clause used in the TFAE list. -/
private def maximalLocalizationClause (A : Type u) [CommRing A] (n : ℕ) : Prop :=
  (∀ m : MaximalSpectrum A,
      IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
        ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
    ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n

/-- Helper for Chap10 Lemma 10 110 8: the prime-local clause used in the TFAE list. -/
private def primeLocalizationClause (A : Type u) [CommRing A] (n : ℕ) : Prop :=
  (∀ p : PrimeSpectrum A,
      IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
        ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
    ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n

/-- Helper for Chap10 Lemma 10 110 8: finite global dimension with value `n` forces the primewise
regular-local clause with the same witness `n`. -/
lemma primeLocalizations_of_finiteGlobalDimension
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A] {n : ℕ} :
    finiteGlobalDimensionClause A n → primeLocalizationClause A n := by
  rintro ⟨hfinite, hdim⟩
  let _ : IsFiniteGlobalDimensionRing A := hfinite
  refine ⟨?_, ?_⟩
  · intro p
    let _ : IsFiniteGlobalDimensionRing (Localization.AtPrime p.asIdeal) :=
      finiteGlobalDimension_localizationAtPrime p
    have hlocal :
        IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
          ringKrullDim (Localization.AtPrime p.asIdeal) =
            globalDimension (Localization.AtPrime p.asIdeal) :=
      regularLocal_and_ringKrullDim_eq_globalDimension_of_finiteGlobalDimension
        (A := Localization.AtPrime p.asIdeal)
    refine ⟨?_, ?_⟩
    · -- Each prime localization inherits regular-locality from localized finite global dimension.
      exact hlocal.1
    · -- The ambient equality `globalDimension A = n` bounds the local Krull dimension by `n`.
      exact ringKrullDim_localizationAtPrime_le_of_globalDimension_eq (A := A) hfinite hdim p
  · -- Reuse the common ambient `ringKrullDim` witness through the extracted localization lemma.
    exact exists_primeLocalization_eq_of_globalDimension_eq (A := A) hdim

/-- Helper for Chap10 Lemma 10 110 8: a regular ring of Krull dimension `n` satisfies the
maximal-local clause at the same `n`. -/
lemma maximalLocalizations_of_regularRingDimension
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A] {n : ℕ} :
    regularRingDimensionClause A n → maximalLocalizationClause A n := by
  rintro ⟨hregular, hdim⟩
  refine ⟨?_, ?_⟩
  · intro m
    let _ : IsRegularRing A := hregular
    refine ⟨IsRegularRing.isRegularLocalRing_atPrime m.toPrimeSpectrum, ?_⟩
    -- Rewrite the local dimension as the height of the maximal ideal and compare to the ambient
    -- Krull dimension.
    calc
      ringKrullDim (Localization.AtPrime m.asIdeal) = m.asIdeal.height :=
        IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
          (Localization.AtPrime m.asIdeal)
      _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_ne_top m.2.ne_top
      _ = n := hdim
  · -- Reuse the common maximal-height witness after turning `ringKrullDim A = n` into finiteness.
    let _ : FiniteRingKrullDim A := finiteRingKrullDim_of_eq_nat (A := A) hdim
    rcases exists_maximalLocalization_eq_ringKrullDim (A := A) with ⟨m, hm⟩
    have hm' : ringKrullDim (Localization.AtPrime m.asIdeal) = n := by
      simpa [hdim] using hm
    exact ⟨m, hm'⟩

/-- Helper for Chap10 Lemma 10 110 8: the maximal-local clause forces finite global dimension with
value `n`. -/
lemma finiteGlobalDimension_of_maximalLocalizations
    {A : Type u} [CommRing A] [Nontrivial A] [IsNoetherianRing A] {n : ℕ} :
    maximalLocalizationClause A n → finiteGlobalDimensionClause A n := by
  rintro ⟨hmax, ⟨m, hmEq⟩⟩
  have hbound :
      ∀ m : MaximalSpectrum A, HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := by
    intro m
    -- Each maximal localization is regular local of Krull dimension at most `n`, so the earlier
    -- local owner theorem gives the corresponding global-dimension bound.
    exact hasGlobalDimensionLE_of_regularLocalRing_ringKrullDim_le
      (hmax m).1 (hmax m).2
  have hglobalBound : HasGlobalDimensionLE A n :=
    -- Route correction: reuse the earlier chapter companion instead of replaying the cyclic-
    -- quotient argument locally.
    hasGlobalDimensionLE_of_uniform_bound_localizationAtMaximal (R := A) hbound
  let hfinite : IsFiniteGlobalDimensionRing A := ⟨⟨n, hglobalBound⟩⟩
  let _ : IsFiniteGlobalDimensionRing A := hfinite
  have hdimLe : globalDimension A ≤ n := by
    let _ : HasGlobalDimensionLE A n := hglobalBound
    exact globalDimension_le (R := A)
  have hdimGe : n ≤ globalDimension A := by
    let _ : IsFiniteGlobalDimensionRing A := hfinite
    exact le_globalDimension_of_maximalLocalization_eq (A := A) hmEq
  -- The maximal-local witness gives the reverse inequality, so the ambient global dimension is
  -- exactly `n`.
  exact ⟨hfinite, le_antisymm hdimLe hdimGe⟩

/-- Helper for Chap10 Lemma 10 110 8: prime-local Krull-dimension bounds control the ambient
Krull dimension. -/
lemma ringKrullDim_le_of_primeLocalizationBounds
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    (hprime : ∀ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) :
    ringKrullDim A ≤ n := by
  -- Rewrite the ambient bound into prime-ideal heights and then insert the localized bound.
  rw [ringKrullDim_le_iff_height_le]
  intro I hI
  let p : PrimeSpectrum A := ⟨I, hI⟩
  calc
    I.height = ringKrullDim (Localization.AtPrime I) := by
      symm
      exact IsLocalization.AtPrime.ringKrullDim_eq_height I (Localization.AtPrime I)
    _ ≤ n := by simpa [p] using hprime p

/-- Helper for Chap10 Lemma 10 110 8: a prime-local equality witness yields the lower bound on the
ambient Krull dimension. -/
lemma le_ringKrullDim_of_primeLocalizationEq
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    (hprime : ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n) :
    (n : WithBot ℕ∞) ≤ ringKrullDim A := by
  rcases hprime with ⟨p, hpEq⟩
  -- Compare the chosen prime localization to the ambient ring through the height of `p.asIdeal`.
  calc
    (n : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime p.asIdeal) := hpEq.symm
    _ = p.asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
        (Localization.AtPrime p.asIdeal)
    _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_ne_top p.2.ne_top

/-- Helper for Chap10 Lemma 10 110 8: the prime-local clause reconstructs regularity and the
ambient Krull dimension equality. -/
lemma regularRingDimension_of_primeLocalizations
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} :
    primeLocalizationClause A n → regularRingDimensionClause A n := by
  rintro ⟨hprime, hwitness⟩
  -- Rebuild the ambient regular ring from the prime-local regularity data.
  have hregular : IsRegularRing A :=
    isRegularRing_of_localizationsAtPrime (fun q ↦ (hprime q).1)
  have hprimeBound :
      ∀ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n :=
    fun q ↦ (hprime q).2
  -- Convert the uniform prime-local bounds into the ambient upper bound for Krull dimension.
  have hdimLe : ringKrullDim A ≤ n :=
    ringKrullDim_le_of_primeLocalizationBounds (A := A) (n := n) hprimeBound
  -- The chosen prime witness supplies the reverse inequality.
  have hdimGe : (n : WithBot ℕ∞) ≤ ringKrullDim A :=
    le_ringKrullDim_of_primeLocalizationEq (A := A) (n := n) hwitness
  exact ⟨hregular, le_antisymm hdimLe hdimGe⟩

/-- Chap10 Lemma 10 110 8: for a Noetherian ring `R`, the following are equivalent: `R` has finite global
dimension `n`, `R` is a regular ring of dimension `n`, every localization at a maximal ideal is a
regular local ring of dimension at most `n` with equality for at least one maximal ideal, and
every localization at a prime ideal is a regular local ring of dimension at most `n` with
equality for at least one prime ideal. -/
@[stacks 00OE]
theorem finiteGlobalDimension_regularRing_localizations_tfae (n : ℕ) [Nontrivial R] :
    List.TFAE
      [ finiteGlobalDimensionClause R n
      , regularRingDimensionClause R n
      , maximalLocalizationClause R n
      , primeLocalizationClause R n ] := by
  -- Route correction: the forward and closing implications now run through the shared
  -- `ringKrullDim` witness route, so the theorem body only assembles the named clause lemmas.
  tfae_have 1 → 4 := by
    exact primeLocalizations_of_finiteGlobalDimension (A := R)
  -- Primewise regularity plus a prime witness reconstruct the regular ring and its dimension.
  tfae_have 4 → 2 := by
    exact regularRingDimension_of_primeLocalizations (A := R)
  -- A regular ring of Krull dimension `n` immediately controls maximal localizations.
  tfae_have 2 → 3 := by
    exact maximalLocalizations_of_regularRingDimension (A := R)
  -- Maximal-local bounds recover finite global dimension, and one maximal witness forces equality.
  tfae_have 3 → 1 := by
    exact finiteGlobalDimension_of_maximalLocalizations (A := R)
  tfae_finish

end
