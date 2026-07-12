import Mathlib
import StacksProject_2024.Chap10.Lemma_10_140_5
import StacksProject_2024.Chap16.Lemma_16_10_2
import StacksProject_2024.Chap16.Lemma_16_9_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

open PrimeSpectrum
open scoped SingularIdealNotation

section

variable {k : Type u} {A : Type v} {Λ : Type w}
variable [Field k] [CommRing A] [CommRing Λ]
variable [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ]
variable [FinitePresentation k A] [Algebra.FiniteType k Λ]

/-
Domain-style sampling:
- primary domain: primewise resolution statements for finitely presented algebras over a field,
  organized around the Chapter 16 owner predicate `ResolvableAtPrime`;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`,
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`,
  `Algebra.FiniteType.isNoetherianRing`;
- best owner abstraction: the public statement should stay source-facing on
  `ResolvableAtPrime k A Λ 𝔮`; the regular-local-ring and separable-residue-field hypotheses are
  primitive source data, and the finite-type hypothesis on `Λ` is primitive bridge-side data
  needed to reuse the chapter's canonical smoothness criterion and to recover the Noetherian
  hypothesis on `Λ` canonically via `Algebra.FiniteType.isNoetherianRing`; primewise smoothness is
  derived API coming from `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`;
- primitive data: a minimal prime `𝔮` of `h(A⁄k, Λ)`, regularity of `Λ_𝔮`, separability of
  `κ(𝔮) / k` in the Stacks Project sense, and finite type of `Λ` over `k`;
- derived API: the local smoothness input used to build the local resolution and the final passage
  from a local resolution at `𝔮` to `ResolvableAtPrime k A Λ 𝔮`.

Source/core/bridge triage:
- `source-facing`: the theorem that `k → A → Λ ⊃ 𝔮` is resolvable;
- `core/canonical`: `ResolvableAtPrime`;
- `bridge/view`: the primewise smoothness criterion
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField` together with the local-to-global
  resolution owner `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`.
-/

section Prime

variable (q : PrimeSpectrum Λ)

local notation "𝔮" => q.asIdeal
local notation "kₚ" => Localization.AtPrime (q.asIdeal.under k)
local notation "Sₚ" => Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under k))
local notation "Aₚ" => Localization Sₚ
local notation "Λ_𝔮" => Localization.AtPrime q.asIdeal
local notation "𝔮Λ_𝔮" => Ideal.map (algebraMap Λ Λ_𝔮) q.asIdeal

/-- Helper for Lemma 16.10.3: after localizing at a minimal prime of `𝔥_A`, some positive power
of the maximal ideal lands in the localized singular ideal. -/
private theorem localizedPrimePowerLeSingularIdeal
    [IsNoetherianRing Λ]
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes) :
    ∃ N : ℕ, 0 < N ∧
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ N ≤
        Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ)) := by
  have hrad :
      (Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
    -- Localizing at a minimal prime identifies the radical of the localized ideal with the
    -- maximal ideal of the local ring.
    calc
      (Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ))).radical =
          Ideal.map (algebraMap Λ Λ_𝔮) q.asIdeal := by
            exact
              IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
                Λ_𝔮 q.asIdeal (h(A⁄k, Λ)) hq
      _ = IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
            simpa using (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal Λ_𝔮)
  have hle :
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ≤
        (Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ))).radical := by
    simpa [hrad] using
      (show IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ≤
          IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) from le_rfl)
  obtain ⟨n, hn⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hle
      (Ideal.fg_of_isNoetherianRing
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)))
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  -- Replace the possibly zero exponent produced by the Noetherian argument with `n + 1`.
  exact
    le_trans
      (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
        (show n ≤ n + 1 by omega))
      hn

/-- Helper for Lemma 16.10.3: after localizing at a minimal prime of `𝔥_A`, some positive power
of the maximal ideal already lands in the localization of the mapped source Jacobian ideal. -/
private theorem localizedPrimePowerLeMappedSourceJacobian
    [IsNoetherianRing Λ]
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes) :
    ∃ N : ℕ, 0 < N ∧
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ N ≤
        Ideal.map (algebraMap Λ Λ_𝔮) (Ideal.map (algebraMap A Λ) (H[A⁄k])) := by
  let J : Ideal Λ_𝔮 := Ideal.map (algebraMap Λ Λ_𝔮) (Ideal.map (algebraMap A Λ) (H[A⁄k]))
  have hrad :
      (Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
    -- Proof comment: localizing at the chosen minimal prime identifies the radical of the
    -- localized target singular ideal with the maximal ideal of the local ring.
    calc
      (Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ))).radical =
          Ideal.map (algebraMap Λ Λ_𝔮) q.asIdeal := by
            exact
              IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
                Λ_𝔮 q.asIdeal (h(A⁄k, Λ)) hq
      _ = IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
            simpa using (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal Λ_𝔮)
  have hleSing :
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ≤
        (Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ))).radical := by
    -- Proof comment: after rewriting by `hrad`, the localized singular ideal has the right
    -- radical for the standard Noetherian power-containment argument.
    simpa [hrad] using
      (show IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ≤
          IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) from le_rfl)
  have hmap :
      Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ)) ≤ J.radical := by
    -- Proof comment: `h(A⁄k, Λ)` is the radical of the mapped source Jacobian ideal, and
    -- localization preserves containment into the radical of the localized map.
    rw [RingHom.singularIdealIn]
    exact
      Ideal.map_radical_le (f := algebraMap Λ Λ_𝔮) (I := Ideal.map (algebraMap A Λ) (H[A⁄k]))
  have hle :
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ≤ J.radical := by
    exact le_trans hleSing hmap
  obtain ⟨n, hn⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hle
      (Ideal.fg_of_isNoetherianRing
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)))
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  -- Proof comment: replace the possibly zero exponent from the Noetherian argument by `n + 1`.
  exact
    le_trans
      (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
        (show n ≤ n + 1 by omega))
      hn

/-- Helper for Lemma 16.10.3: once an auxiliary factorization `A → T → Λ` is already resolvable,
the original source algebra is resolvable as soon as `𝔥_A` is contained in the auxiliary singular
ideal. -/
private theorem resolvableAtPrime_of_auxiliarySingularContainment
    {T : Type v} [CommRing T]
    [Algebra k T] [Algebra A T] [Algebra T Λ]
    [IsScalarTower k A T] [IsScalarTower k T Λ] [IsScalarTower A T Λ]
    (hSing : h(A⁄k, Λ) ≤ h(T⁄k, Λ))
    (hres : ResolvableAtPrime k T Λ 𝔮) :
    ResolvableAtPrime k A Λ 𝔮 := by
  -- Proof comment: unfold the resolved auxiliary factorization and then precompose it with the
  -- fixed map `A → T`.
  rw [resolvableAtPrime_iff] at hres ⊢
  rcases hres with ⟨B, _, _, _, f, g, hcomp, hcontain, hnotle⟩
  refine ⟨B, inferInstance, inferInstance, inferInstance, ?_, g, ?_, ?_, hnotle⟩
  · -- The new source map is the auxiliary source map precomposed with `A → T`.
    exact f.comp (IsScalarTower.toAlgHom k A T)
  · -- Proof comment: associativity of composition identifies the new composite with `A → Λ`.
    calc
      g.comp (f.comp (IsScalarTower.toAlgHom k A T)) =
          (g.comp f).comp (IsScalarTower.toAlgHom k A T) := by
            rfl
      _ = (IsScalarTower.toAlgHom k T Λ).comp (IsScalarTower.toAlgHom k A T) := by
            rw [hcomp]
      _ = IsScalarTower.toAlgHom k A Λ := by
            ext x
            change algebraMap T Λ (algebraMap A T x) = algebraMap A Λ x
            rw [IsScalarTower.algebraMap_eq A T Λ]
            rfl
  · -- Proof comment: the auxiliary singular ideal already contains the original one.
    exact le_trans hSing hcontain

/-- Helper for Lemma 16.10.3: smoothness of `Λ` at `q` forces the intrinsic singular ideal of
`Λ` over `k` to avoid `q`. -/
private theorem singularIdeal_self_not_le_of_isSmoothAt
    (hSmooth : IsSmoothAt k 𝔮) :
    ¬ h(Λ⁄k, Λ) ≤ 𝔮 := by
  intro hle
  have hself :
      H[Λ⁄k] ≤ h(Λ⁄k, Λ) := by
    -- Proof comment: for the identity target map, `h(Λ/k, Λ)` is the radical of `H[Λ/k]`.
    simpa [RingHom.singularIdealIn] using
      (Ideal.le_radical : H[Λ⁄k] ≤ Ideal.radical (H[Λ⁄k]))
  have hqZero : q ∈ PrimeSpectrum.zeroLocus (H[Λ⁄k] : Set Λ) := by
    -- Proof comment: containment in `q` means exactly that `q` lies in the zero locus.
    rw [PrimeSpectrum.mem_zeroLocus]
    exact le_trans hself hle
  have hqNotSmooth : ¬ IsSmoothAt k 𝔮 := by
    -- Proof comment: the singular zero locus is the complement of the smooth locus.
    simpa [zeroLocus_singularIdeal_eq_compl_smoothLocus, smoothLocus] using hqZero
  exact hqNotSmooth hSmooth

/-- Helper for Lemma 16.10.3: if the intrinsic singular ideal of `Λ` over `k` already avoids `q`,
then `Λ` itself is a valid resolution witness at `q`. -/
private theorem resolvableAtPrime_self_of_singularIdeal_not_le
    (hnotle : ¬ h(Λ⁄k, Λ) ≤ 𝔮) :
    ResolvableAtPrime k Λ Λ 𝔮 := by
  letI : FinitePresentation k Λ := FinitePresentation.of_finiteType.mp inferInstance
  rw [resolvableAtPrime_iff]
  refine
    ⟨Λ, inferInstance, inferInstance, inferInstance, AlgHom.id k Λ, AlgHom.id k Λ, ?_, ?_, hnotle⟩
  · -- Proof comment: the identity factorization composes to the identity map on `Λ`.
    ext x
    rfl
  · -- Proof comment: the target singular ideal of the identity map is exactly `h(Λ/k, Λ)`.
    exact le_rfl

/-- Helper for Lemma 16.10.3: under the regular-local and separable-residue-field hypotheses, the
target ring `Λ` already resolves itself at `q`. -/
private theorem targetSelfResolvableAtPrime
    [IsRegularLocalRing Λ_𝔮]
    [IsSeparableOver k q.asIdeal.ResidueField] :
    ResolvableAtPrime k Λ Λ 𝔮 := by
  have hIsSmoothAt : IsSmoothAt k 𝔮 := by
    -- Proof comment: Lemma `10.140.5` identifies the regular-local and separable hypotheses with
    -- smoothness of `Λ` at the prime `q`.
    exact
      (isSmoothAt_iff_isRegularLocalRing_of_separable_residueField 𝔮).2 inferInstance
  have hnotle : ¬ h(Λ⁄k, Λ) ≤ 𝔮 := by
    -- Proof comment: smoothness forces the identity singular ideal of `Λ` to avoid `q`.
    exact singularIdeal_self_not_le_of_isSmoothAt (k := k) (Λ := Λ) (q := q) hIsSmoothAt
  -- Proof comment: with that noncontainment in hand, the identity factorization `Λ → Λ → Λ`
  -- is already a valid resolution witness.
  exact resolvableAtPrime_self_of_singularIdeal_not_le (k := k) (Λ := Λ) (q := q) hnotle

/-- Helper for Lemma 16.10.3: the currently buildable frontier already contains both the localized
power containment for `𝔥_A` and the target-side self-resolution at `q`. -/
private theorem existsTargetSideResolutionFrontier
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes)
    [IsRegularLocalRing Λ_𝔮]
    [IsSeparableOver k q.asIdeal.ResidueField] :
    ∃ N : ℕ, 0 < N ∧
      (maximalIdeal Λ_𝔮) ^ N ≤ Ideal.map (algebraMap Λ Λ_𝔮) (h(A⁄k, Λ)) ∧
      ResolvableAtPrime k Λ Λ 𝔮 := by
  letI : IsNoetherianRing Λ := Algebra.FiniteType.isNoetherianRing k Λ
  obtain ⟨N, hNpos, hN⟩ :=
    localizedPrimePowerLeSingularIdeal (k := k) (A := A) (Λ := Λ) q hq
  have hSelfRes : ResolvableAtPrime k Λ Λ 𝔮 := by
    -- Proof comment: the target-side self-resolution is already available from the regular-local
    -- and separable-residue-field hypotheses.
    exact targetSelfResolvableAtPrime (k := k) (Λ := Λ) (q := q)
  -- Proof comment: package the fully verified target-side data in one existential so the remaining
  -- `sorry` only ranges over the missing source-side auxiliary algebra.
  exact ⟨N, hNpos, hN, hSelfRes⟩

/-- Helper for Lemma 16.10.3: if a finite generating family for `H[A⁄k]` already maps into the
auxiliary singular ideal, then the full source singular ideal is contained in that auxiliary
singular ideal. -/
private theorem singularIdealLe_ofGeneratorImages
    {T : Type (max u v w)} [CommRing T]
    [Algebra k T] [Algebra A T] [Algebra T Λ]
    [IsScalarTower k A T] [IsScalarTower k T Λ] [IsScalarTower A T Λ]
    {r : ℕ} (a : Fin r → A)
    (haSpan : Ideal.span (Set.range a) = H[A⁄k])
    (haImage : ∀ i, algebraMap A Λ (a i) ∈ h(T⁄k, Λ)) :
    h(A⁄k, Λ) ≤ h(T⁄k, Λ) := by
  have hmap :
      Ideal.map (algebraMap A Λ) (H[A⁄k]) ≤ h(T⁄k, Λ) := by
    -- Proof comment: the chosen generators already land in the auxiliary singular ideal, so the
    -- entire mapped Jacobian ideal does as well.
    rw [← haSpan]
    refine Ideal.map_le_iff_le_comap.2 ?_
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simpa [Ideal.mem_comap] using haImage i
  have hradical := Ideal.radical_mono hmap
  -- Proof comment: `h(A⁄k, Λ)` is the radical of the mapped source Jacobian ideal by definition.
  simpa [RingHom.singularIdealIn] using hradical

/-- Helper for Lemma 16.10.3: the source singular ideal admits a finite generating family. -/
private theorem existsFiniteSingularGeneratorFamily :
    ∃ r : ℕ, ∃ a : Fin r → A, Ideal.span (Set.range a) = H[A⁄k] := by
  let _ : Algebra.FiniteType k A := inferInstance
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  -- Proof comment: Noetherianity of `A` turns finite generation of the singular ideal into a
  -- concrete `Fin r`-indexed family.
  exact
    Submodule.fg_iff_exists_fin_generating_family.mp
      (Ideal.fg_of_isNoetherianRing (H[A⁄k]))

/-- Helper for Lemma 16.10.3: the localized mapped-source-Jacobian containment upgrades via
Lemma `16.10.2` to a concrete parameter family in `Λ` with target-side annihilator stability. -/
private theorem existsParameterFamilyForMappedSourceJacobian
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes)
    [IsNoetherianRing Λ]
    [IsRegularLocalRing Λ_𝔮] :
    ∃ (N d : ℕ) (π : Fin d → Λ) (hπ : ∀ i, algebraMap Λ Λ_𝔮 (π i) ∈ maximalIdeal Λ_𝔮),
      0 < N ∧
        IsRegularSystemOfParameters (fun i ↦ ⟨algebraMap Λ Λ_𝔮 (π i), hπ i⟩) ∧
        (∀ i, π i ^ N ∈ Ideal.map (algebraMap A Λ) (H[A⁄k])) ∧
        (∀ i : Fin d,
          let J := Algebra.piPowPrefixIdeal π 8 i.1 (Nat.le_of_lt i.isLt)
          Ideal.torsionOf (Λ ⧸ J) (Λ ⧸ J) (Ideal.Quotient.mk J (π i)) =
            Ideal.torsionOf (Λ ⧸ J) (Λ ⧸ J) (Ideal.Quotient.mk J (π i ^ 2))) := by
  obtain ⟨N, hNpos, hN⟩ :=
    localizedPrimePowerLeMappedSourceJacobian (k := k) (A := A) (Λ := Λ) (q := q) hq
  let d : ℕ := ringKrullDim Λ_𝔮
  have hqSource :
      Ideal.map (algebraMap A Λ) (H[A⁄k]) ≤ 𝔮 := by
    -- Proof comment: the mapped source Jacobian ideal lies in its radical `𝔥_A`, and every
    -- minimal prime of `𝔥_A` contains that radical.
    calc
      Ideal.map (algebraMap A Λ) (H[A⁄k]) ≤ h(A⁄k, Λ) := by
        simpa [RingHom.singularIdealIn] using
          (Ideal.le_radical : Ideal.map (algebraMap A Λ) (H[A⁄k]) ≤
            Ideal.radical (Ideal.map (algebraMap A Λ) (H[A⁄k])))
      _ ≤ 𝔮 := hq.1.2
  have hqpow :
      Ideal.map (algebraMap Λ Λ_𝔮) (𝔮 ^ N) ≤
        Ideal.map (algebraMap Λ Λ_𝔮) (Ideal.map (algebraMap A Λ) (H[A⁄k])) := by
    -- Proof comment: rewrite the localized prime power to the maximal ideal power from the
    -- previous helper so that Lemma `16.10.2` applies verbatim.
    calc
      Ideal.map (algebraMap Λ Λ_𝔮) (𝔮 ^ N) =
          Ideal.map (algebraMap Λ Λ_𝔮) 𝔮 ^ N := by
            rw [Ideal.map_pow]
      _ = (maximalIdeal Λ_𝔮) ^ N := by
            rw [IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal Λ_𝔮]
      _ ≤ Ideal.map (algebraMap Λ Λ_𝔮) (Ideal.map (algebraMap A Λ) (H[A⁄k])) := hN
  obtain ⟨π, hπ, hparams, hpow, hAnnΛ⟩ :=
    exists_parameters_generating_localized_prime_pow_mem_ideal_and_annihilator_stable
      (q := q) (I := Ideal.map (algebraMap A Λ) (H[A⁄k])) (n := N) (e := 8) (d := d)
      hqSource hqpow rfl
  exact ⟨N, d, π, hπ, hNpos, hparams, hpow, hAnnΛ⟩

/-- Helper for Lemma 16.10.3: once a chosen generating family for `H[A⁄k]` is fixed, the only
remaining source-proof debt is to build an auxiliary finitely presented algebra whose singular
ideal contains the images of those generators and which is already resolvable at `q`. -/
private theorem existsSourceFaithfulAuxiliaryResolution_onChosenGenerators
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes)
    [IsRegularLocalRing Λ_𝔮]
    [IsSeparableOver k q.asIdeal.ResidueField]
    {r : ℕ} (a : Fin r → A)
    (haSpan : Ideal.span (Set.range a) = H[A⁄k]) :
    ∃ (T : Type (max u v w)) (_ : CommRing T) (_ : Algebra k T) (_ : Algebra A T)
      (_ : Algebra T Λ) (_ : IsScalarTower k A T) (_ : IsScalarTower k T Λ)
      (_ : IsScalarTower A T Λ) (_ : FinitePresentation k T),
      (∀ i, algebraMap A Λ (a i) ∈ h(T⁄k, Λ)) ∧ ResolvableAtPrime k T Λ 𝔮 := by
  letI : IsNoetherianRing Λ := Algebra.FiniteType.isNoetherianRing k Λ
  obtain ⟨N, d, π, hπ, hNpos, hparams, hpow, hAnnΛ⟩ :=
    existsParameterFamilyForMappedSourceJacobian
      (k := k) (A := A) (Λ := Λ) (q := q) hq
  let _ := haSpan
  let _ := N
  let _ := d
  let _ := π
  let _ := hπ
  let _ := hparams
  let _ := hpow
  let _ := hAnnΛ
  let _ := hNpos
  -- Route correction: the previous attempt kept only the abstract localized containment and the
  -- target self-resolution witness. The file now reaches the stronger frontier from Lemma `16.10.2`:
  -- a concrete parameter family `π` in `Λ` with `N`-th powers in the mapped source Jacobian ideal
  -- and the target-side torsion equalities needed for the eventual `16.9.2` application.
  -- The remaining blocker is now only the source-side `B → C` auxiliary model that should consume
  -- this parameter family and turn it into a resolvable auxiliary factorization.
  --
  -- TODO: replace this placeholder by the concrete source-side chart package from the textbook
  -- proof. What remains is:
  -- 1. build the polynomial/retract chart package `B → C → B` tied to the chosen generator family
  --    `a`, with smooth `a_i`-charts and variable charts;
  -- 2. extract the common strict-standard exponent on the variable charts;
  -- 3. use the already-built parameter family `π` and its annihilator equalities to define the
  --    comparison map `C → Λ` and feed the source/target data into Lemma `16.9.2`;
  -- 4. prove the quotient local-resolution input modulo the eighth powers of `π`.
  sorry

/-- Helper for Lemma 16.10.3: the remaining source-proof package is an auxiliary finitely
presented factorization `A → T → Λ` whose singular ideal dominates `𝔥_A` and which is already
resolvable at `q`. -/
private theorem existsAuxiliaryResolvedFactorizationWithSingularComparison
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes)
    [IsRegularLocalRing Λ_𝔮]
    [IsSeparableOver k q.asIdeal.ResidueField] :
    ∃ (T : Type (max u v w)) (_ : CommRing T) (_ : Algebra k T) (_ : Algebra A T)
      (_ : Algebra T Λ) (_ : IsScalarTower k A T) (_ : IsScalarTower k T Λ)
      (_ : IsScalarTower A T Λ) (_ : FinitePresentation k T),
      h(A⁄k, Λ) ≤ h(T⁄k, Λ) ∧ ResolvableAtPrime k T Λ 𝔮 := by
  obtain ⟨r, a, haSpan⟩ :=
    existsFiniteSingularGeneratorFamily (k := k) (A := A)
  obtain ⟨T, hTCommRing, hTkAlg, hATAlg, hTΛAlg, hTowerkAT, hTowerkTΛ, hTowerATΛ, hTfp,
      haImage, hres⟩ :=
    existsSourceFaithfulAuxiliaryResolution_onChosenGenerators
      (k := k) (A := A) (Λ := Λ) (q := q) hq a haSpan
  -- Proof comment: once the chosen generators land in the auxiliary singular ideal, the radical
  -- comparison from `singularIdealLe_ofGeneratorImages` upgrades that generatorwise data to the
  -- full containment `h(A⁄k, Λ) ≤ h(T⁄k, Λ)`.
  refine
    ⟨T, hTCommRing, hTkAlg, hATAlg, hTΛAlg, hTowerkAT, hTowerkTΛ, hTowerATΛ, hTfp,
      ?_, hres⟩
  exact
    singularIdealLe_ofGeneratorImages
      (k := k) (A := A) (Λ := Λ) (T := T) a haSpan haImage

-- Proof sketch: choose parameters in `Λ` as in Lemma `16.10.2`, use Lemma `16.9.2` to construct
-- a local resolution after quotienting by the corresponding eighth powers, and then apply the
-- local-to-global owner theorem `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`.
-- The finite-type and separable-residue-field hypotheses identify regularity of `Λ_𝔮` with
-- smoothness at `𝔮` via Lemma `10.140.5`, which supplies the smoothness input needed in the local
-- construction; the finite-type hypothesis also supplies the Noetherianity of `Λ` canonically via
-- `Algebra.FiniteType.isNoetherianRing`.
/-- Lemma 16.10.3: in Situation `16.9.1`, if `k` is a field, `A` is finitely presented over `k`,
`Λ` is a finite type `k`-algebra, `q` is a minimal prime of `𝔥_A`, the local ring
`Λ_q` is regular, and the residue field extension `κ(q) / k` is separable, then
`k → A → Λ ⊃ q` is resolvable. -/
theorem resolvableAtPrime_of_minimalPrime_regularLocalRing_and_separable_residueField
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes)
    [IsRegularLocalRing Λ_𝔮]
    [IsSeparableOver k q.asIdeal.ResidueField] :
    ResolvableAtPrime k A Λ 𝔮 := by
  obtain ⟨T, hTCommRing, hTkAlg, hATAlg, hTΛAlg, hTowerkAT, hTowerkTΛ, hTowerATΛ, hTfp,
      hSing, hres⟩ :=
    existsAuxiliaryResolvedFactorizationWithSingularComparison
      (k := k) (A := A) (Λ := Λ) (q := q) hq
  letI : CommRing T := hTCommRing
  letI : Algebra k T := hTkAlg
  letI : Algebra A T := hATAlg
  letI : Algebra T Λ := hTΛAlg
  letI : IsScalarTower k A T := hTowerkAT
  letI : IsScalarTower k T Λ := hTowerkTΛ
  letI : IsScalarTower A T Λ := hTowerATΛ
  letI : FinitePresentation k T := hTfp
  -- Proof comment: once the source-proof auxiliary package is available, the final step is the
  -- previously verified singular-ideal transfer from `T` back to `A`.
  exact
    resolvableAtPrime_of_auxiliarySingularContainment
      (k := k) (A := A) (Λ := Λ) (q := q) (T := T) hSing hres

end Prime

end

end Algebra
