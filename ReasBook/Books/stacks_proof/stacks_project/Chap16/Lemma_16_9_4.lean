import Mathlib
import StacksProject_2024.Chap16.Lemma_16_9_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Algebra

open PrimeSpectrum
open scoped SingularIdealNotation

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]

/- Domain-style sampling:
- primary domain: localized commutative algebra for resolution data at a prime;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `exists_factorization_with_singularIdeal_not_le_of_localResolutionAtMinimalPrime`,
  `Localization.AtPrime`,
  `Algebra.algebraMapSubmonoid`;
- best owner abstraction: the localized hypothesis is the canonical owner
  `ResolvableAtPrime` on the localized rings, exactly as in Lemma `16.9.3`;
- primitive data: the minimal prime itself, now taken canonically as `q : PrimeSpectrum Λ`,
  together with the localized rings `R_𝔭`, `A_𝔭`, `Λ_𝔮` and the prime ideal `𝔮Λ_𝔮`;
- derived API: the local-resolution hypothesis is stated directly via `ResolvableAtPrime` on those
  localized rings, with the prime structure supplied by `q` rather than repeated `let`-bound
  instance reconstruction.

Source/core/bridge triage:
- `source-facing`: Lemma `16.9.4`, which upgrades a local resolution at a minimal prime to a
  global one under the dimension-zero hypothesis;
- `core/canonical`: `ResolvableAtPrime`;
- `bridge/view`: the localized rings built from the prime-spectrum point `q`.
-/

section Prime

variable (q : PrimeSpectrum Λ)

local notation "𝔮" => q.asIdeal
local notation "Rₚ" => Localization.AtPrime (q.asIdeal.under R)
local notation "Sₚ" => Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R))
local notation "Aₚ" => Localization Sₚ
local notation "Λ_𝔮" => Localization.AtPrime q.asIdeal
local notation "𝔮Λ_𝔮" => Ideal.map (algebraMap Λ Λ_𝔮) q.asIdeal

/-- Helper for Lemma 16.9.4: noncontainment of the target singular ideal already comes from a
source singular element whose image avoids `𝔮`. -/
private theorem exists_mem_sourceSingularIdeal_not_mem_prime
    {C : Type (max u v w)} [CommRing C] [Algebra R C] [Algebra C Λ] [IsScalarTower R C Λ]
    (g : C →ₐ[R] Λ) (hnotle : ¬ g.singularIdealIn R ≤ 𝔮) :
    ∃ c : C, c ∈ H[C⁄R] ∧ g c ∉ 𝔮 := by
  -- Normalize the radical-image ideal to the source ideal via `map_le_iff_le_comap`.
  classical
  letI : q.asIdeal.IsPrime := q.isPrime
  have hmapNotLe : ¬ Ideal.map g (H[C⁄R]) ≤ 𝔮 := by
    intro hmap
    apply hnotle
    rw [RingHom.singularIdealIn]
    exact
      (Ideal.IsPrime.radical_le_iff
        (I := Ideal.map g (H[C⁄R])) (J := 𝔮) q.isPrime).2 hmap
  have hsourceNotLe : ¬ H[C⁄R] ≤ Ideal.comap g 𝔮 := by
    intro hsource
    apply hmapNotLe
    exact Ideal.map_le_iff_le_comap.2 hsource
  by_contra hnoWitness
  apply hsourceNotLe
  intro c hc
  by_contra hcg
  exact hnoWitness ⟨c, hc, hcg⟩

/-- Helper for Lemma 16.9.4: inverting an element of the source singular ideal gives a smooth
basic open chart. -/
private theorem smoothAway_of_mem_singularIdeal
    {S : Type x} [CommRing S] [Algebra R S] [FinitePresentation R S] {s : S}
    (hs : s ∈ H[S⁄R]) :
    Smooth R (Localization.Away s) := by
  -- An element of the singular ideal vanishes on the nonsmooth locus, so its basic open lies in
  -- the smooth locus.
  rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  intro p hp
  have hpzero : p ∉ zeroLocus (H[S⁄R]) := by
    rw [mem_zeroLocus]
    exact fun hHs ↦ hp (hHs hs)
  simpa [zeroLocus_singularIdeal_eq_compl_smoothLocus] using hpzero

/-- Helper for Lemma 16.9.4: if the basic open chart `D(s)` is smooth, then `s` already lies in
the source singular ideal. -/
private theorem mem_singularIdeal_of_smoothAway
    {S : Type x} [CommRing S] [Algebra R S] [FinitePresentation R S] {s : S}
    (hs : Smooth R (Localization.Away s)) :
    s ∈ H[S⁄R] := by
  -- Proof comment: translate smoothness of `D(s)` into the inclusion `D(s) ⊆ smoothLocus`,
  -- then show every prime containing `H[S⁄R]` must also contain `s`.
  rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth] at hs
  have hsubset :
      PrimeSpectrum.zeroLocus (↑(H[S⁄R]) : Set S) ⊆ PrimeSpectrum.zeroLocus ({s} : Set S) := by
    intro p hp
    rw [PrimeSpectrum.mem_zeroLocus] at ⊢
    intro x hx
    have hxs : x = s := Set.mem_singleton_iff.mp hx
    by_contra hsnot
    have hsnot' : s ∉ p.asIdeal := by simpa [hxs] using hsnot
    have hpbasic : p ∈ PrimeSpectrum.basicOpen s := by
      simpa [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] using hsnot'
    have hpsmooth : p ∈ Algebra.smoothLocus R S := hs hpbasic
    have hpnonsmooth : p ∈ (Algebra.smoothLocus R S)ᶜ := by
      simpa [zeroLocus_singularIdeal_eq_compl_smoothLocus] using hp
    exact hpnonsmooth hpsmooth
  have hrad :
      Ideal.span ({s} : Set S) ≤ (H[S⁄R]).radical :=
      (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
      (I := H[S⁄R]) (J := Ideal.span ({s} : Set S))).1 <| by
        simpa using hsubset
  have hsrad : s ∈ (H[S⁄R]).radical := by
    exact hrad (Ideal.subset_span (by simp))
  have hsingRadical : (H[S⁄R]).radical = H[S⁄R] :=
    (Algebra.singularIdeal_isRadical (R := R) (A := S)).radical
  simpa [hsingRadical] using hsrad

/-- Helper for Lemma 16.9.4: a source singular element whose image avoids `𝔮` forces the target
singular ideal of the factorization to avoid `𝔮` as well. -/
private theorem singularIdeal_not_le_of_mem_sourceSingularIdeal_not_mem_prime
    {C : Type (max u v w)} [CommRing C] [Algebra R C] [Algebra C Λ] [IsScalarTower R C Λ]
    (g : C →ₐ[R] Λ) {c : C} (hc : c ∈ H[C⁄R]) (hcg : g c ∉ 𝔮) :
    ¬ g.singularIdealIn R ≤ 𝔮 := by
  -- The image of any source singular element lies in the target singular ideal by definition.
  intro hle
  have hmem : g c ∈ g.singularIdealIn R := by
    rw [RingHom.singularIdealIn]
    rw [Ideal.mem_radical_iff]
    exact ⟨1, by simpa using Ideal.mem_map_of_mem g hc⟩
  exact hcg (hle hmem)

/-- Helper for Lemma 16.9.4: a finitely presented factorization resolves itself at `𝔮` as soon as
its own target singular ideal is not contained in `𝔮`. -/
private theorem resolvableAtPrime_self_of_singularIdeal_not_le
    {T : Type (max u v w)} [CommRing T] [Algebra R T] [Algebra T Λ] [IsScalarTower R T Λ]
    [FinitePresentation R T] (hnotle : ¬ h(T⁄R, Λ) ≤ 𝔮) :
    ResolvableAtPrime.{u, max u v w, w} R T Λ 𝔮 := by
  -- Unfold the owner definition and reuse the given finitely presented factorization itself.
  rw [resolvableAtPrime_iff]
  refine
    ⟨T, inferInstance, inferInstance, inferInstance, AlgHom.id R T,
      IsScalarTower.toAlgHom R T Λ, ?_, ?_, hnotle⟩
  · -- The identity source map leaves the factorization unchanged.
    ext t
    rfl
  · -- With source ring `T`, the target singular ideal is exactly `g.singularIdealIn R`.
    exact le_rfl

/-- Helper for Lemma 16.9.4: once an auxiliary factorization `A → T → Λ` is already resolvable,
the original source algebra is resolvable as soon as `𝔥_A` is contained in the auxiliary
singular ideal. -/
private theorem resolvableAtPrime_of_auxiliarySingularContainment
    {T : Type (max u v w)} [CommRing T]
    [Algebra R T] [Algebra A T] [Algebra T Λ]
    [IsScalarTower R A T] [IsScalarTower R T Λ] [IsScalarTower A T Λ]
    (hSing : h(A⁄R, Λ) ≤ h(T⁄R, Λ))
    (hres : ResolvableAtPrime.{u, max u v w, w} R T Λ 𝔮) :
    ResolvableAtPrime.{u, v, w} R A Λ 𝔮 := by
  -- Unfold the resolved auxiliary factorization and precompose it with the fixed map `A → T`.
  rw [resolvableAtPrime_iff] at hres ⊢
  rcases hres with ⟨B, _, _, _, f, g, hcomp, hcontain, hnotle⟩
  refine ⟨B, inferInstance, inferInstance, inferInstance, ?_, g, ?_, ?_, hnotle⟩
  · -- The new source map is the auxiliary source map precomposed with `A → T`.
    exact f.comp (IsScalarTower.toAlgHom R A T)
  · -- Associativity of composition identifies the new composite with `A → Λ`.
    calc
      g.comp (f.comp (IsScalarTower.toAlgHom R A T)) =
          (g.comp f).comp (IsScalarTower.toAlgHom R A T) := by
            rfl
      _ = (IsScalarTower.toAlgHom R T Λ).comp (IsScalarTower.toAlgHom R A T) := by
            rw [hcomp]
      _ = IsScalarTower.toAlgHom R A Λ := by
            ext a
            change algebraMap T Λ (algebraMap A T a) = algebraMap A Λ a
            rw [IsScalarTower.algebraMap_eq A T Λ]
            rfl
  · -- The auxiliary singular ideal already contains the original one.
    exact le_trans hSing hcontain

/-- Helper for Lemma 16.9.4: after choosing finitely many generators of `H[A⁄R]`, the
zero-dimensional local hypothesis at `𝔮` yields one element of `Λ \\ 𝔮` killing a common positive
power of every chosen generator in `Λ`. -/
private theorem existsFiniteSingularGenerators_and_commonAnnihilator
    [IsNoetherianRing R] [FinitePresentation R A]
    (hq : 𝔮 ∈ (h(A⁄R, Λ)).minimalPrimes)
    (hdim : ringKrullDim Λ_𝔮 = 0) :
    ∃ r : ℕ, ∃ a : Fin r → A, Ideal.span (Set.range a) = H[A⁄R] ∧
      ∃ N : ℕ, 0 < N ∧ ∃ lam : Λ, lam ∉ 𝔮 ∧
        ∀ i, lam * algebraMap A Λ (a i ^ N) = 0 := by
  classical
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  obtain ⟨r, a, haSpan⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family.mp
      (Ideal.fg_of_isNoetherianRing (H[A⁄R])))
  have hContain : h(A⁄R, Λ) ≤ 𝔮 := hq.1.2
  have hdimLE : Ring.KrullDimLE 0 Λ_𝔮 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  let n : Fin r → ℕ := fun i ↦ nilpotencyClass (algebraMap A Λ_𝔮 (a i))
  let N : ℕ := Finset.univ.sup n + 1
  have hNpos : 0 < N := by
    exact Nat.succ_pos _
  have hpowZero : ∀ i, algebraMap A Λ_𝔮 (a i ^ N) = 0 := by
    intro i
    have haiSing : algebraMap A Λ (a i) ∈ h(A⁄R, Λ) := by
      rw [RingHom.singularIdealIn]
      rw [Ideal.mem_radical_iff]
      refine ⟨1, ?_⟩
      simpa [map_pow] using Ideal.mem_map_of_mem (algebraMap A Λ) <| by
        rw [← haSpan]
        exact Ideal.subset_span ⟨i, rfl⟩
    have haiPrime : algebraMap A Λ (a i) ∈ 𝔮 := hContain haiSing
    have haiMax :
        algebraMap A Λ_𝔮 (a i) ∈ IsLocalRing.maximalIdeal Λ_𝔮 := by
      have hmapMem :
          algebraMap Λ Λ_𝔮 (algebraMap A Λ (a i)) ∈
            Ideal.map (algebraMap Λ Λ_𝔮) 𝔮 := Ideal.mem_map_of_mem _ haiPrime
      simpa [Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal),
        IsScalarTower.algebraMap_eq A Λ Λ_𝔮] using hmapMem
    have hnil :
        IsNilpotent (algebraMap A Λ_𝔮 (a i)) :=
      (Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal (R := Λ_𝔮)).2 haiMax
    have hpowNil : (algebraMap A Λ_𝔮 (a i)) ^ n i = 0 := pow_nilpotencyClass hnil
    have hle : n i ≤ N := by
      exact le_trans (Finset.le_sup (Finset.mem_univ i)) (Nat.le_succ _)
    calc
      algebraMap A Λ_𝔮 (a i ^ N) = (algebraMap A Λ_𝔮 (a i)) ^ N := by
        simp [map_pow]
      _ = 0 := pow_eq_zero_of_le hle hpowNil
  have hkillWitness :
      ∀ i, ∃ s : q.asIdeal.primeCompl, (s : Λ) * algebraMap A Λ (a i ^ N) = 0 := by
    intro i
    have hzeroMap :
        algebraMap Λ Λ_𝔮 (algebraMap A Λ (a i ^ N)) = 0 := by
      simpa [IsScalarTower.algebraMap_eq A Λ Λ_𝔮] using hpowZero i
    simpa [mul_comm] using
      (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl Λ_𝔮
        (algebraMap A Λ (a i ^ N))).1 hzeroMap
  choose s hs using hkillWitness
  let lam : q.asIdeal.primeCompl := ∏ i, s i
  refine ⟨r, a, haSpan, N, hNpos, lam, lam.2, ?_⟩
  intro i
  -- Multiply the individual annihilator by the complementary product to use one common factor.
  have hlam :
      (lam : Λ) = (s i : Λ) * ((Finset.univ.erase i).prod fun j ↦ (s j : Λ)) := by
    simpa [lam] using
      (Finset.mul_prod_erase (s := Finset.univ) (f := fun j ↦ (s j : Λ))
        (by simp : i ∈ Finset.univ)).symm
  calc
    (lam : Λ) * algebraMap A Λ (a i ^ N) =
        ((s i : Λ) * ((Finset.univ.erase i).prod fun j ↦ (s j : Λ))) *
          algebraMap A Λ (a i ^ N) := by
            rw [hlam]
    _ = ((Finset.univ.erase i).prod fun j ↦ (s j : Λ)) *
          ((s i : Λ) * algebraMap A Λ (a i ^ N)) := by
            ac_rfl
    _ = 0 := by
          rw [hs i, mul_zero]

/-- Helper for Lemma 16.9.4: a chosen generator of a spanning family for `H[A⁄R]` already lies in
the source singular ideal. -/
private theorem generator_mem_singularIdeal_of_span
    {r : ℕ} (a : Fin r → A)
    (haSpan : Ideal.span (Set.range a) = H[A⁄R]) (i : Fin r) :
    a i ∈ H[A⁄R] := by
  -- Proof comment: rewrite the singular ideal as the span of the chosen generators and use the
  -- canonical span membership of `a i`.
  rw [← haSpan]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Helper for Lemma 16.9.4: each chosen generator of `H[A⁄R]` defines a smooth basic open. -/
private theorem smoothAway_generator_of_spanSingularIdeal
    [FinitePresentation R A]
    {r : ℕ} (a : Fin r → A)
    (haSpan : Ideal.span (Set.range a) = H[A⁄R]) (i : Fin r) :
    Smooth R (Localization.Away (a i)) := by
  -- Proof comment: once the chosen generator is recognized as singular, the standard singular-ideal
  -- basic-open criterion gives the desired smoothness.
  exact
    smoothAway_of_mem_singularIdeal
      (R := R)
      (generator_mem_singularIdeal_of_span (R := R) (A := A) a haSpan i)

/-- Helper for Lemma 16.9.4: the direct product-localization carries the canonical
`S[g]`-algebra structure coming from the away-to-away map. -/
private noncomputable instance awayChartMulAlgebra
    {S : Type*} [CommRing S] (g t : S) :
    Algebra (Localization.Away g) (Localization.Away (g * t)) :=
  (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away g)
    (P := Localization.Away (g * t))
    g t).toAlgebra

/-- Helper for Lemma 16.9.4: the product-localization realizes the scalar tower
`S → S[g] → S[g * t]`. -/
private instance awayChartMulScalarTower
    {S : Type*} [CommRing S] (g t : S) :
    IsScalarTower S (Localization.Away g) (Localization.Away (g * t)) :=
  IsScalarTower.of_algebraMap_eq' <|
    RingHom.ext fun s ↦ by
      simpa using
        (IsLocalization.Away.awayToAwayRight_eq
          (S := Localization.Away g)
          (P := Localization.Away (g * t))
          g t s).symm

/-- Helper for Lemma 16.9.4: the direct localization `S[g * t]` is the away-localization of the
`g`-chart at the image of `t`. -/
private theorem awayChart_isLocalizationAway_mul
    {S : Type*} [CommRing S] (g t : S) :
    IsLocalization.Away (algebraMap S (Localization.Away g) t) (Localization.Away (g * t)) := by
  let B := Localization.Away g
  let D := Localization.Away (algebraMap S B t)
  let _ : IsScalarTower S B D := inferInstance
  let φS : D ≃ₐ[S] Localization.Away (g * t) :=
    IsLocalization.algEquiv (Submonoid.powers (g * t)) D (Localization.Away (g * t))
  let φB : D ≃ₐ[B] Localization.Away (g * t) :=
    { φS with
      commutes' := by
        have hmaps :
            ((φS : D →+* Localization.Away (g * t)).comp (algebraMap B D)) =
              algebraMap B (Localization.Away (g * t)) := by
          apply IsLocalization.ringHom_ext (Submonoid.powers g)
          ext s
          have hbaseD :
              algebraMap B D (algebraMap S B s) = algebraMap S D s := by
            simpa [B] using congrArg (fun ψ : S →+* D ↦ ψ s)
              (IsScalarTower.algebraMap_eq S B D)
          have hbaseGT :
              algebraMap B (Localization.Away (g * t)) (algebraMap S B s) =
                algebraMap S (Localization.Away (g * t)) s := by
            simpa [B] using
              (congrArg (fun ψ : S →+* Localization.Away (g * t) ↦ ψ s)
                (IsScalarTower.algebraMap_eq S B (Localization.Away (g * t)))).symm
          simp only [RingHom.comp_apply]
          calc
            φS (algebraMap B D (algebraMap S B s)) = φS (algebraMap S D s) := by rw [hbaseD]
            _ = algebraMap S (Localization.Away (g * t)) s := by simpa using φS.commutes s
            _ = algebraMap B (Localization.Away (g * t)) (algebraMap S B s) := by rw [hbaseGT]
        intro b
        exact congrArg (fun ψ : B →+* Localization.Away (g * t) ↦ ψ b) hmaps }
  -- Proof comment: transport the iterated away-localization owner across the canonical
  -- direct-vs-iterated localization equivalence.
  simpa [B, D] using
    (IsLocalization.isLocalization_of_algEquiv
      (M := Submonoid.powers (algebraMap S B t))
      (S := D)
      (P := Localization.Away (g * t))
      φB)

/-- Helper for Lemma 16.9.4: further localizing a smooth away-localization stays smooth. -/
private theorem smooth_localizationAway_mul
    {S : Type*} [CommRing S] [Algebra R S] (g t : S)
    (hg : Smooth R (Localization.Away g)) :
    Smooth R (Localization.Away (g * t)) := by
  letI :
      IsLocalization.Away
        (algebraMap S (Localization.Away g) t)
        (Localization.Away (g * t)) := by
    -- Proof comment: replace the direct product-localization by the standard iterated
    -- away-localization of the `g`-chart.
    simpa [mul_comm] using awayChart_isLocalizationAway_mul (g := g) (t := t)
  letI : IsScalarTower R (Localization.Away g) (Localization.Away (g * t)) :=
    IsScalarTower.of_algebraMap_eq' <|
      RingHom.ext fun r ↦ by
        simpa [awayChartMulAlgebra, IsScalarTower.algebraMap_eq R S (Localization.Away g),
          IsScalarTower.algebraMap_eq R S (Localization.Away (g * t))] using
          (IsLocalization.Away.awayToAwayRight_eq
            (S := Localization.Away g)
            (P := Localization.Away (g * t))
            g t (algebraMap R S r)).symm
  letI : Smooth (Localization.Away g) (Localization.Away (g * t)) :=
    Smooth.of_isLocalization_Away (algebraMap S (Localization.Away g) t)
  -- Proof comment: compose the original smooth `g`-chart with the new localization step.
  exact Smooth.comp R (Localization.Away g) (Localization.Away (g * t))

/-- Helper for Lemma 16.9.4: if both `A` and an intermediate `C` are finitely presented over `R`,
then the structural map `A → C` is finitely presented over `A`. -/
private theorem finitePresentation_over_intermediate
    {C : Type (max u v w)} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    [FinitePresentation R A] [FinitePresentation R C] :
    FinitePresentation A C := by
  -- Proof comment: this is the standard restrict-scalars theorem for finitely presented algebras
  -- over a finite-type intermediate base.
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A C

/-- Helper for Lemma 16.9.4: if positive powers of a spanning family for `H[A⁄R]` already land
in an auxiliary target singular ideal, then all of `h(A⁄R, Λ)` is contained in that auxiliary
singular ideal. -/
private theorem singularIdealLe_auxiliary_ofGeneratorPowers
    {T : Type (max u v w)} [CommRing T]
    [Algebra R T] [Algebra A T] [Algebra T Λ]
    [IsScalarTower R A T] [IsScalarTower R T Λ] [IsScalarTower A T Λ]
    {r N : ℕ} (a : Fin r → A)
    (haSpan : Ideal.span (Set.range a) = H[A⁄R])
    (hpow : ∀ i, algebraMap A Λ (a i ^ (N + 1)) ∈ h(T⁄R, Λ)) :
    h(A⁄R, Λ) ≤ h(T⁄R, Λ) := by
  -- Proof comment: each generator lands in the auxiliary singular ideal because a positive power
  -- of its image does, and the auxiliary singular ideal is radical by definition.
  have hgen :
      ∀ i, algebraMap A Λ (a i) ∈ h(T⁄R, Λ) := by
    intro i
    have hrad :
        algebraMap A Λ (a i) ∈ (h(T⁄R, Λ)).radical := by
      rw [Ideal.mem_radical_iff]
      exact ⟨N + 1, by simpa [map_pow] using hpow i⟩
    simpa [RingHom.singularIdealIn] using hrad
  have hmap :
      Ideal.map (algebraMap A Λ) (H[A⁄R]) ≤ h(T⁄R, Λ) := by
    rw [← haSpan]
    refine Ideal.map_le_iff_le_comap.2 ?_
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simpa [Ideal.mem_comap] using hgen i
  -- Proof comment: `h(A⁄R, Λ)` is the radical of the mapped source singular ideal, so monotonicity
  -- of radicals upgrades the generator-wise containment to the full ideal containment.
  have hradical := Ideal.radical_mono hmap
  simpa [RingHom.singularIdealIn] using hradical

/-- Helper for Lemma 16.9.4: an auxiliary finitely presented algebra already resolves itself at
`𝔮` once one of its source singular elements maps outside `𝔮`. -/
private theorem auxiliarySelfResolvableAtPrime
    {T : Type (max u v w)} [CommRing T]
    [Algebra R T] [Algebra T Λ] [IsScalarTower R T Λ]
    [FinitePresentation R T]
    {t : T} (ht : t ∈ H[T⁄R]) (htq : algebraMap T Λ t ∉ 𝔮) :
    ResolvableAtPrime.{u, max u v w, w} R T Λ 𝔮 := by
  have hnotle : ¬ h(T⁄R, Λ) ≤ 𝔮 := by
    -- Proof comment: one source singular element landing outside `𝔮` already forces the target
    -- singular ideal of the identity factorization `T → Λ` to avoid `𝔮`.
    exact
      singularIdeal_not_le_of_mem_sourceSingularIdeal_not_mem_prime
        (R := R) (Λ := Λ) (q := q) (g := IsScalarTower.toAlgHom R T Λ) ht htq
  -- Proof comment: once the target singular ideal avoids `𝔮`, the finitely presented algebra `T`
  -- resolves itself at `𝔮`.
  exact
    resolvableAtPrime_self_of_singularIdeal_not_le
      (R := R) (Λ := Λ) (q := q) hnotle

/-- Helper for Lemma 16.9.4: the remaining textbook gap is the explicit auxiliary finitely
presented algebra combining one escaping source singular chart from `C` with the common
annihilator of a generating family for `H[A⁄R]`. -/
private theorem existsAuxiliaryResolvedFactorization_of_sourceSingularEscape_and_commonAnnihilator
    {C : Type (max u v w)} [CommRing C] [Algebra R C] [Algebra C Λ] [IsScalarTower R C Λ]
    [FinitePresentation R A] [FinitePresentation R C]
    (f : A →ₐ[R] C) (g : C →ₐ[R] Λ)
    (hcomp : g.comp f = IsScalarTower.toAlgHom R A Λ)
    {c : C} (hc : c ∈ H[C⁄R]) (hcg : g c ∉ 𝔮)
    {r N : ℕ} (a : Fin r → A)
    (haSpan : Ideal.span (Set.range a) = H[A⁄R])
    {lam : Λ} (hlam : lam ∉ 𝔮)
    (hkill : ∀ i, lam * algebraMap A Λ (a i ^ N) = 0) :
    ∃ (T : Type (max u v w)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra A T)
      (_ : Algebra T Λ) (_ : IsScalarTower R A T) (_ : IsScalarTower R T Λ)
      (_ : IsScalarTower A T Λ) (_ : FinitePresentation R T) (u : T),
      u ∈ H[T⁄R] ∧ algebraMap T Λ u ∉ 𝔮 ∧
        (∀ i, algebraMap A Λ (a i ^ (N + 1)) ∈ h(T⁄R, Λ)) := by
  classical
  -- Route correction: the unresolved step is not another ideal-theoretic argument. It is the
  -- source-faithful auxiliary quotient `T` whose charts are cut out by the escaping singular
  -- element `c` and the common annihilator `λ`. The generic bridge from chart smoothness to
  -- singular-ideal membership is now available as `mem_singularIdeal_of_smoothAway`, and the
  -- product-chart composition step is isolated in `smooth_localizationAway_mul`. The remaining
  -- gap is the explicit quotient over a fixed `A`-presentation of `C`.
  letI : Algebra A C := f.toAlgebra
  letI : IsScalarTower R A C := IsScalarTower.of_algHom f
  letI : FinitePresentation A C :=
    finitePresentation_over_intermediate (R := R) (A := A) (C := C)
  let n := Algebra.Presentation.ofFinitePresentationVars A C
  let m := Algebra.Presentation.ofFinitePresentationRels A C
  let P : Algebra.Presentation A C (Fin n) (Fin m) :=
    Algebra.Presentation.ofFinitePresentation A C
  let _ := n
  let _ := m
  let _ := P
  let _ := hcomp
  let _ := hc
  let _ := hcg
  let _ := a
  let _ := haSpan
  let _ := hlam
  let _ := hkill
  -- TODO: using the fixed `A`-presentation `P`, define the textbook quotient `T`, prove the
  -- structural `z`-chart and `y_i`-charts are smooth, then pass to the product charts with
  -- `smooth_localizationAway_mul` to obtain `u ∈ H[T⁄R]` and the generator-power containment.
  sorry

-- Proof sketch: use Lemma `16.9.3` to replace the assumed local resolution at `q` by a finitely
-- presented factorization `A → C → Λ` with `𝔥_C` not contained in `q`. Because
-- `ringKrullDim (Localization.AtPrime q) = 0`, the local ring `Λ_q` is Artinian local, so some
-- power of `𝔥_A` is killed away from `q`. Adjoin variables and relations as in the textbook proof
-- to build a finitely presented `R`-algebra `B` over `A` whose target singular ideal contains
-- `𝔥_A` and still avoids `q`.
/-- Lemma 16.9.4: in Situation `16.9.1`, let `𝔭 = R ∩ 𝔮`. Assume `R` is Noetherian, `A` is
finitely presented over `R`, `𝔮` is minimal over `𝔥_A`, the localized map
`R_𝔭 → A_𝔭 → Λ_𝔮 ⊃ 𝔮 Λ_𝔮` can be resolved, and `ringKrullDim Λ_𝔮 = 0`.
Then `R → A → Λ ⊃ 𝔮` can be resolved. -/
@[stacks 07FA]
theorem resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero
    [IsNoetherianRing R] [FinitePresentation R A]
    (hq : 𝔮 ∈ (h(A⁄R, Λ)).minimalPrimes)
    (hlocal : ResolvableAtPrime Rₚ Aₚ Λ_𝔮 𝔮Λ_𝔮)
    (hdim : ringKrullDim Λ_𝔮 = 0) :
    ResolvableAtPrime R A Λ 𝔮 := by
  obtain ⟨C, hCCommRing, hCAlg, hCfp, f, g, hcomp, hnotle⟩ :=
    exists_factorization_with_singularIdeal_not_le_of_localResolutionAtMinimalPrime
      (R := R) (A := A) (Λ := Λ) q hq hlocal
  letI : CommRing C := hCCommRing
  letI : Algebra R C := hCAlg
  letI : FinitePresentation R C := hCfp
  letI : Algebra A C := f.toAlgebra
  letI : Algebra C Λ := g.toAlgebra
  letI : IsScalarTower R A C := IsScalarTower.of_algHom f
  letI : IsScalarTower R C Λ := IsScalarTower.of_algHom g
  obtain ⟨c, hc, hcg⟩ :=
    exists_mem_sourceSingularIdeal_not_mem_prime
      (R := R) (Λ := Λ) (q := q) g hnotle
  obtain ⟨r, a, haSpan, N, hNpos, lam, hlam, hkill⟩ :=
    existsFiniteSingularGenerators_and_commonAnnihilator
      (R := R) (A := A) (Λ := Λ) (q := q) hq hdim
  obtain ⟨T, hTCommRing, hTAlgR, hTAlgA, hTAlgΛ, hTowerRAT, hTowerRTΛ, hTowerATΛ, hTfp,
      t, htSing, htq, hpow⟩ :=
    existsAuxiliaryResolvedFactorization_of_sourceSingularEscape_and_commonAnnihilator
      (R := R) (A := A) (Λ := Λ) (q := q)
      (f := f) (g := g) hcomp hc hcg a haSpan (hlam := hlam) hkill
  letI : CommRing T := hTCommRing
  letI : Algebra R T := hTAlgR
  letI : Algebra A T := hTAlgA
  letI : Algebra T Λ := hTAlgΛ
  letI : IsScalarTower R A T := hTowerRAT
  letI : IsScalarTower R T Λ := hTowerRTΛ
  letI : IsScalarTower A T Λ := hTowerATΛ
  letI : FinitePresentation R T := hTfp
  have hSelfRes : ResolvableAtPrime.{u, max u v w, w} R T Λ 𝔮 := by
    -- Proof comment: the auxiliary algebra resolves itself because one of its singular elements
    -- maps outside `𝔮`.
    exact
      auxiliarySelfResolvableAtPrime
        (R := R) (Λ := Λ) (q := q) htSing htq
  have hSingLe : h(A⁄R, Λ) ≤ h(T⁄R, Λ) := by
    -- Proof comment: the generator-power containment supplied by the auxiliary construction
    -- upgrades to full containment of the original target singular ideal.
    exact
      singularIdealLe_auxiliary_ofGeneratorPowers
        (R := R) (A := A) (Λ := Λ) (T := T) (N := N) a haSpan hpow
  -- Proof comment: precompose the resolved auxiliary factorization with `A → T`.
  exact
    resolvableAtPrime_of_auxiliarySingularContainment
      (R := R) (A := A) (Λ := Λ) (q := q) (T := T) hSingLe hSelfRes

end Prime

end

end Algebra
