import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_63_1 (from Chap10) -/
universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

namespace Ideal

/-
Domain triage: this file is in commutative algebra of associated primes. The owner abstraction is
mathlib's `IsAssociatedPrime` / `associatedPrimes`, while Definition 10.63.1 is source-facing
because it remembers the exact annihilator of an element rather than only its radical. The
primitive data for that source-facing notion should therefore be the canonical annihilator ideal
`Ideal.torsionOf R M m`, with the bridge to the owner abstraction derived afterwards.
-/

/-- Definition 10.63.1: a prime ideal `𝔭` of `R` is associated to the `R`-module `M` if `𝔭`
is the annihilator ideal of some element of `M`. -/
def IsAssociatedToModule (𝔭 : Ideal R) : Prop :=
  𝔭.IsPrime ∧ ∃ m : M, 𝔭 = torsionOf R M m

theorem isAssociatedToModule_map_of_injective {M' : Type*} [AddCommGroup M'] [Module R M']
    {𝔭 : Ideal R} (h𝔭 : IsAssociatedToModule R M 𝔭) (f : M →ₗ[R] M')
    (hf : Function.Injective f) :
    IsAssociatedToModule R M' 𝔭 := by
  rcases h𝔭 with ⟨hprime, m, hm⟩
  refine ⟨hprime, f m, ?_⟩
  ext r
  rw [hm, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff, ← map_smul, map_eq_zero_iff f hf]

private theorem torsionOf_eq_bot_colon_singleton (m : M) :
    torsionOf R M m = (⊥ : Submodule R M).colon ({m} : Set M) := by
  calc
    torsionOf R M m = (Submodule.span R ({m} : Set M)).annihilator := by
      simpa [Ideal.torsionOf] using (Submodule.annihilator_span_singleton m).symm
    _ = (⊥ : Submodule R M).colon ({m} : Set M) := by
      rw [Submodule.bot_colon']

/-- Companion re-expression of `IsAssociatedToModule` using `Ideal.torsionOf`, matching the
textbook annihilator-of-an-element wording. -/
theorem isAssociatedToModule_iff_exists_torsionOf (𝔭 : Ideal R) :
    IsAssociatedToModule R M 𝔭 ↔ 𝔭.IsPrime ∧ ∃ m : M, 𝔭 = torsionOf R M m := by
  rfl

/-- A textbook-associated prime is associated in mathlib's radical-based sense. -/
theorem IsAssociatedToModule.isAssociatedPrime {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedToModule R M 𝔭) :
    IsAssociatedPrime 𝔭 M := by
  rcases h𝔭 with ⟨h𝔭, m, hm⟩
  refine ⟨h𝔭, m, ?_⟩
  calc
    𝔭 = (torsionOf R M m).radical := by
      simpa [hm] using h𝔭.radical.symm
    _ = ((⊥ : Submodule R M).colon ({m} : Set M)).radical := by
      rw [torsionOf_eq_bot_colon_singleton R M m]

theorem isAssociatedToModule_comap {S : Type*} [CommRing S] [Algebra R S]
    [Module S M] [IsScalarTower R S M] {P : Ideal S} (hP : IsAssociatedToModule S M P) :
    IsAssociatedToModule R M (Ideal.comap (algebraMap R S) P) := by
  rcases hP with ⟨hP, m, hm⟩
  refine ⟨hP.comap (algebraMap R S), m, ?_⟩
  ext r
  rw [hm, Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/-- In a Noetherian ring, the textbook notion of an associated prime agrees with mathlib's
`IsAssociatedPrime`. -/
theorem isAssociatedToModule_iff_isAssociatedPrime [IsNoetherianRing R] (𝔭 : Ideal R) :
    IsAssociatedToModule R M 𝔭 ↔ IsAssociatedPrime 𝔭 M := by
  rw [isAssociatedToModule_iff_exists_torsionOf, isAssociatedPrime_iff]
  constructor
  · rintro ⟨h𝔭, m, hm⟩
    exact ⟨h𝔭, m, hm.trans (torsionOf_eq_bot_colon_singleton R M m)⟩
  · rintro ⟨h𝔭, m, hm⟩
    exact ⟨h𝔭, m, hm.trans (torsionOf_eq_bot_colon_singleton R M m).symm⟩

end Ideal

namespace LinearEquiv

theorem isAssociatedToModule_iff {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') {𝔭 : Ideal R} :
    Ideal.IsAssociatedToModule R M 𝔭 ↔ Ideal.IsAssociatedToModule R M' 𝔭 := by
  constructor
  · intro h𝔭
    exact Ideal.isAssociatedToModule_map_of_injective R M h𝔭 e.toLinearMap e.injective
  · intro h𝔭
    exact Ideal.isAssociatedToModule_map_of_injective R M' h𝔭 e.symm.toLinearMap e.symm.injective

end LinearEquiv

/-- The set of textbook-associated primes of the `R`-module `M`. -/
def associatedPrimesOfModule : Set (Ideal R) :=
  Ideal.IsAssociatedToModule R M

/-- A prime ideal belongs to `associatedPrimesOfModule R M` exactly when it is associated to
`M` in the textbook sense. -/
@[simp] theorem mem_associatedPrimesOfModule_iff (𝔭 : Ideal R) :
    𝔭 ∈ associatedPrimesOfModule R M ↔ Ideal.IsAssociatedToModule R M 𝔭 :=
  Iff.rfl

namespace LinearEquiv

theorem associatedPrimesOfModule_eq {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') :
    associatedPrimesOfModule R M = associatedPrimesOfModule R M' := by
  ext 𝔭
  exact e.isAssociatedToModule_iff

end LinearEquiv

/-- The textbook-associated primes of `M` are contained in mathlib's owner set
`associatedPrimes R M`. -/
theorem associatedPrimesOfModule_subset_associatedPrimes :
    associatedPrimesOfModule R M ⊆ associatedPrimes R M := fun _ h ↦ h.isAssociatedPrime

/-- In a Noetherian ring, the textbook-associated primes of `M` coincide with mathlib's
`associatedPrimes R M`. -/
theorem associatedPrimesOfModule_eq_associatedPrimes [IsNoetherianRing R] :
    associatedPrimesOfModule R M = associatedPrimes R M := by
  ext 𝔭
  change Ideal.IsAssociatedToModule R M 𝔭 ↔ IsAssociatedPrime 𝔭 M
  exact Ideal.isAssociatedToModule_iff_isAssociatedPrime R M 𝔭

end

/-! ### Lemma_10_63_2 (from Chap10) -/
universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-
Domain triage: this item lies in commutative algebra of associated primes and module support.
The owner abstraction is mathlib's `IsAssociatedPrime` / `associatedPrimes R M`, while the
textbook exact-annihilator set `associatedPrimesOfModule R M` from Definition 10.63.1 is the
source-facing bridge layer.
-/

/-- A mathlib-associated prime of an `R`-module lies in its support. -/
theorem IsAssociatedPrime.mem_support {𝔭 : Ideal R} (h𝔭 : IsAssociatedPrime 𝔭 M) :
    (⟨𝔭, h𝔭.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  rcases h𝔭.eq_radical_colon with ⟨m, hm⟩
  rw [Module.mem_support_iff_exists_annihilator]
  refine ⟨m, ?_⟩
  simpa [Submodule.bot_colon', hm] using
    (Ideal.le_radical :
      (⊥ : Submodule R M).colon ({m} : Set M) ≤
        ((⊥ : Submodule R M).colon ({m} : Set M)).radical)

namespace Module

/-- Canonical owner-form of Lemma 10.63.2 for mathlib's radical-based `associatedPrimes R M`. -/
theorem associatedPrimes_subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M ⊆ support R M := by
  intro 𝔭 h𝔭
  simpa using (AssociatedPrimes.mem_iff.mp h𝔭).mem_support

/-- Lemma 10.63.2: every textbook-associated prime of an `R`-module `M` lies in the support
`Module.support R M`. -/
-- Proof sketch: if `p ∈ associatedPrimesOfModule R M`, then by Definition 10.63.1 there is
-- `m : M` with `p = Ideal.torsionOf R M m = (R ∙ m).annihilator`, and
-- `Module.mem_support_iff_exists_annihilator` puts the corresponding point of `Spec R` in
-- `Supp(M)`.
theorem associatedPrimesOfModule_subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimesOfModule R M ⊆ support R M := by
  intro 𝔭 h𝔭
  exact associatedPrimes_subset_support <|
    associatedPrimesOfModule_subset_associatedPrimes R M h𝔭

end Module

/-! ### Lemma_10_63_3 (from Chap10) -/
universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']
variable {M'' : Type x} [AddCommGroup M''] [Module R M'']
variable {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}

/- Domain triage:
- primary domain: commutative algebra of textbook associated primes of modules;
- owner abstraction: the project-level set-valued declaration `associatedPrimesOfModule R M`,
  parallel to mathlib's owner namespace `associatedPrimes`;
- sampled owner-style declarations: mathlib's `associatedPrimes.subset_of_injective`,
  `associatedPrimes.subset_union_of_exact`, `associatedPrimes.prod`, and the chapter file
  `weaklyAssociatedPrimes.subset_of_injective` in Lemma 10.66.4;
- primitive data: modules and linear maps in an injective map or exact sequence;
- derived API: inclusions and product formulas for the owner set `associatedPrimesOfModule`.
-/
namespace associatedPrimesOfModule

/-- Canonical owner-form of Lemma 10.63.3 (1): an injective linear map sends textbook-associated
primes into textbook-associated primes. -/
theorem subset_of_injective (hf : Function.Injective f) :
    associatedPrimesOfModule R M ⊆ associatedPrimesOfModule R M' := by
  intro p hp
  simpa [associatedPrimesOfModule] using Ideal.isAssociatedToModule_map_of_injective R M hp f hf

/-- Canonical owner-form of Lemma 10.63.3 (2): if `0 → M → M' → M''` is exact, then every
textbook-associated prime of `M'` lies in the union of those of `M` and `M''`. -/
theorem subset_union_of_exact (hf : Function.Injective f)
    (hfg : Function.Exact f g) :
    associatedPrimesOfModule R M' ⊆ associatedPrimesOfModule R M ∪ associatedPrimesOfModule R M'' := by
  intro p hp
  rcases hp with ⟨hp, m, hm⟩
  by_cases h : ∃ a ∈ p.primeCompl, ∃ y : M, f y = a • m
  · rcases h with ⟨a, ha, y, hy⟩
    left
    refine ⟨hp, y, le_antisymm ?_ ?_⟩
    · intro b hb
      rw [hm, Ideal.mem_torsionOf_iff] at hb
      rw [Ideal.mem_torsionOf_iff]
      exact hf <| by
        calc
          f (b • y) = b • f y := by rw [map_smul]
          _ = b • (a • m) := by rw [hy]
          _ = a • (b • m) := by simp [smul_smul, mul_comm]
          _ = 0 := by
            rw [hb, smul_zero]
          _ = f 0 := by rw [map_zero]
    · intro b hb
      rw [Ideal.mem_torsionOf_iff] at hb
      have hab : a * b ∈ p := by
        rw [hm, Ideal.mem_torsionOf_iff]
        calc
          (a * b) • m = b • (a • m) := by simp [smul_smul, mul_comm]
          _ = b • f y := by rw [hy]
          _ = f (b • y) := by rw [map_smul]
          _ = 0 := by rw [hb, map_zero]
      exact (hp.mem_or_mem hab).resolve_left <| by simpa using ha
  · right
    refine ⟨hp, g m, le_antisymm ?_ ?_⟩
    · intro b hb
      rw [hm, Ideal.mem_torsionOf_iff] at hb
      rw [Ideal.mem_torsionOf_iff]
      simpa [map_smul] using congrArg g hb
    · intro b hb
      rw [Ideal.mem_torsionOf_iff, ← map_smul, ← LinearMap.mem_ker,
        hfg.linearMap_ker_eq] at hb
      obtain ⟨y, hy⟩ := hb
      by_contra hb'
      exact h ⟨b, by simpa using hb', y, hy⟩

/-- Canonical owner-form of Lemma 10.63.3 (3): the textbook-associated primes of a binary direct
sum are exactly the union of the textbook-associated primes of the two summands. -/
theorem prod :
    associatedPrimesOfModule R (M × M') = associatedPrimesOfModule R M ∪ associatedPrimesOfModule R M' := by
  refine (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm ?_
  rw [Set.union_subset_iff]
  exact ⟨subset_of_injective LinearMap.inl_injective,
    subset_of_injective LinearMap.inr_injective⟩

end associatedPrimesOfModule

/- Lemma 10.63.3 (1): the source-facing owner theorem is
`associatedPrimesOfModule.subset_of_injective`. -/
recall associatedPrimesOfModule.subset_of_injective

/- Lemma 10.63.3 (2): the source-facing owner theorem is
`associatedPrimesOfModule.subset_union_of_exact`. -/
recall associatedPrimesOfModule.subset_union_of_exact

/- Lemma 10.63.3 (3): the source-facing owner theorem is `associatedPrimesOfModule.prod`. -/
recall associatedPrimesOfModule.prod

end

/-! ### Lemma_10_63_4 (from Chap10) -/
universe u v

open PrimeSpectrum RelSeries Submodule

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (s : PrimeCyclicFiltration R M)

/-
Domain triage:
- primary domain: commutative algebra of associated primes and prime-cyclic filtrations;
- source-facing owner: `associatedPrimesOfModule R M`;
- filtration owner: `s.primeFactors`;
- canonical Noetherian owner: mathlib's `associatedPrimes R M`;
- layer of this file: `bridge/view`, first from associated-prime points to the intrinsic filtration
  owner `s.primeFactors`, then from that owner statement to a chosen indexing `p`.
-/

/-- Helper for Lemma 10.63.4: prime factors already present in a filtration remain present after
adjoining one more prime-quotient step at the end. -/
lemma PrimeCyclicFiltration.primeFactors_subset_snoc
    {N : Submodule R M} (hrel : s.last.IsQuotientEquivQuotientPrime N) :
    s.primeFactors ⊆ PrimeCyclicFiltration.primeFactors (s.snoc N hrel) := by
  intro 𝔭 h𝔭
  rcases h𝔭 with ⟨i, hi⟩
  rcases hi with ⟨e⟩
  have hsucc : (s.snoc N hrel) (i.castSucc.succ) = s i.succ := by
    simpa using RelSeries.snoc_cast_castSucc s N hrel i.succ
  have hprev : (s.snoc N hrel) (i.castSucc.castSucc) = s i.castSucc := by
    simpa using RelSeries.snoc_cast_castSucc s N hrel i.castSucc
  let eNum : (s.snoc N hrel) (i.castSucc.succ) ≃ₗ[R] s i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      (((s.snoc N hrel) (i.castSucc.castSucc)).submoduleOf ((s.snoc N hrel) (i.castSucc.succ))).map
        (eNum : ((s.snoc N hrel) (i.castSucc.succ) →ₗ[R] s i.succ)) =
      (s i.castSucc).submoduleOf (s i.succ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eNum, hsucc, hprev] using hy
    · intro hx
      refine ⟨eNum.symm x, ?_, ?_⟩
      · simpa [eNum, hsucc, hprev] using hx
      · simpa using eNum.apply_symm_apply x
  refine ⟨i.castSucc, ?_⟩
  -- The earlier successive quotients are unchanged under `snoc`, so the old witness survives.
  exact ⟨(Submodule.Quotient.equiv _ _ eNum hmap).trans e⟩

/-- Helper for Lemma 10.63.4: the prime quotient used in the final `snoc` step is itself one of
the prime factors of the extended filtration. -/
lemma PrimeCyclicFiltration.mem_primeFactors_snoc_last
    {N : Submodule R M} {𝔭 : PrimeSpectrum R}
    (hle : s.last ≤ N)
    (h𝔭 : Nonempty ((↥N ⧸ s.last.submoduleOf N) ≃ₗ[R] R ⧸ 𝔭.asIdeal)) :
    𝔭 ∈ PrimeCyclicFiltration.primeFactors (s.snoc N ⟨hle, 𝔭, h𝔭⟩) := by
  have hstep : Nonempty ((↥N ⧸ s.last.submoduleOf N) ≃ₗ[R] R ⧸ 𝔭.asIdeal) := h𝔭
  rcases hstep with ⟨e⟩
  have hlast : (s.snoc N ⟨hle, 𝔭, h𝔭⟩).last = N := by
    simp
  have hprev : (s.snoc N ⟨hle, 𝔭, h𝔭⟩) (Fin.last s.length).castSucc = s.last := by
    simpa using RelSeries.snoc_cast_castSucc s N ⟨hle, 𝔭, h𝔭⟩ (Fin.last s.length)
  let eNum : (s.snoc N ⟨hle, 𝔭, h𝔭⟩).last ≃ₗ[R] N :=
    LinearEquiv.ofEq _ _ hlast
  have hmap :
      (((s.snoc N ⟨hle, 𝔭, h𝔭⟩) (Fin.last s.length).castSucc).submoduleOf
          ((s.snoc N ⟨hle, 𝔭, h𝔭⟩).last)).map
        (eNum : ((s.snoc N ⟨hle, 𝔭, h𝔭⟩).last →ₗ[R] N)) =
      s.last.submoduleOf N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eNum, hlast, hprev] using hy
    · intro hx
      refine ⟨eNum.symm x, ?_, ?_⟩
      · simpa [eNum, hlast, hprev] using hx
      · simpa using eNum.apply_symm_apply x
  refine ⟨Fin.last s.length, ?_⟩
  -- The last successive quotient of the extended series is exactly the new prime quotient.
  exact ⟨(Submodule.Quotient.equiv _ _ eNum hmap).trans e⟩

/-- Helper for Lemma 10.63.4: the textbook associated primes of the prime quotient `R ⧸ q` form
the singleton `{q.asIdeal}`. -/
lemma associatedPrimesOfModule_quotient_prime_eq_singleton (q : PrimeSpectrum R) :
    associatedPrimesOfModule R (R ⧸ q.asIdeal) = {q.asIdeal} := by
  ext I
  constructor
  · intro hI
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hI
    rcases hI with ⟨hprime, x, rfl⟩
    have hx_ne : x ≠ 0 := by
      intro hx
      have htop : Ideal.torsionOf R (R ⧸ q.asIdeal) x = ⊤ := by
        simpa [hx] using (Ideal.torsionOf_eq_top_iff (R := R) x).2 hx
      exact hprime.ne_top (by simpa [htop])
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha_not_mem : a ∉ q.asIdeal := by
      intro ha
      exact hx_ne ((Ideal.Quotient.eq_zero_iff_mem).2 ha)
    simp only [Set.mem_singleton_iff]
    apply Ideal.ext
    intro r
    constructor
    · intro hr
      rw [Ideal.mem_torsionOf_iff] at hr
      have hmul : r * a ∈ q.asIdeal := by
        change Ideal.Quotient.mk q.asIdeal (r * a) = 0 at hr
        exact (Ideal.Quotient.eq_zero_iff_mem).1 hr
      exact q.isPrime.mem_or_mem hmul |>.resolve_right ha_not_mem
    · intro hr
      rw [Ideal.mem_torsionOf_iff]
      change Ideal.Quotient.mk q.asIdeal (r * a) = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
        simpa [mul_comm] using q.asIdeal.mul_mem_left a hr
  · intro hI
    rw [Set.mem_singleton_iff] at hI
    subst I
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
    refine ⟨q.isPrime, (1 : R ⧸ q.asIdeal), ?_⟩
    apply Ideal.ext
    intro r
    constructor
    · intro hr
      rw [Ideal.mem_torsionOf_iff]
      change Ideal.Quotient.mk q.asIdeal (r * 1) = 0
      simpa using (Ideal.Quotient.eq_zero_iff_mem).2 hr
    · intro hr
      rw [Ideal.mem_torsionOf_iff] at hr
      change Ideal.Quotient.mk q.asIdeal (r * 1) = 0 at hr
      simpa using (Ideal.Quotient.eq_zero_iff_mem).1 hr

/-- Helper for Lemma 10.63.4: if a prime-cyclic filtration starts at `0`, then every textbook
associated prime of its final stage comes from one of its prime factors. -/
lemma associatedPrimesOfLast_subset_image_primeFactors_of_prime_quotient_filtration
    (hs₀ : s.head = ⊥) :
    associatedPrimesOfModule R s.last ⊆ PrimeSpectrum.asIdeal '' s.primeFactors := by
  -- We follow the source proof by peeling off the last quotient and recursing on the shorter
  -- filtration.
  revert hs₀
  induction s using RelSeries.inductionOn' with
  | singleton N =>
      intro hs₀ I hI
      have hN : N = ⊥ := hs₀
      subst N
      have hI' : I ∈ associatedPrimesOfModule R (⊥ : Submodule R M) := by
        simpa using hI
      rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hI'
      rcases hI' with ⟨hprime, m, hm⟩
      have hm_zero : m = 0 := Subsingleton.elim _ _
      have htop : Ideal.torsionOf R (⊥ : Submodule R M) m = ⊤ :=
        (Ideal.torsionOf_eq_top_iff (R := R) m).2 hm_zero
      have : I = ⊤ := by simpa [hm, htop]
      exact (hprime.ne_top this).elim
  | snoc s N hrel ih =>
      rcases hrel with ⟨hle, q, hq⟩
      intro hs₀ I hI
      rw [RelSeries.last_snoc] at hI
      have hI_N : I ∈ associatedPrimesOfModule R N := hI
      have hsubmodule :
          associatedPrimesOfModule R (s.last.submoduleOf N) = associatedPrimesOfModule R s.last := by
        simpa using
          (LinearEquiv.associatedPrimesOfModule_eq
            (R := R) (M := s.last.submoduleOf N) (M' := s.last)
            (Submodule.submoduleOfEquivOfLe hle))
      have hsubset :
          associatedPrimesOfModule R N ⊆
            associatedPrimesOfModule R (s.last.submoduleOf N) ∪
              associatedPrimesOfModule R (N ⧸ s.last.submoduleOf N) :=
        associatedPrimesOfModule.subset_union_of_exact
          (f := Submodule.subtype (s.last.submoduleOf N)) (g := (s.last.submoduleOf N).mkQ)
          (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _)
      have hI' := hsubset hI_N
      rcases hI' with hI' | hI'
      · -- Associated primes already coming from the penultimate stage remain prime factors after
        -- adding the last quotient.
        have hI_last : I ∈ associatedPrimesOfModule R s.last := by
          rw [← hsubmodule]
          exact hI'
        rcases ih hs₀ hI_last with ⟨𝔭, h𝔭, rfl⟩
        exact ⟨𝔭, PrimeCyclicFiltration.primeFactors_subset_snoc (s := s) ⟨hle, q, hq⟩ h𝔭, rfl⟩
      · -- The quotient term contributes only the last prime factor, since it is isomorphic to
        -- `R ⧸ q`.
        have hquot :
            associatedPrimesOfModule R (N ⧸ s.last.submoduleOf N) = {q.asIdeal} := by
          rcases hq with ⟨e⟩
          rw [LinearEquiv.associatedPrimesOfModule_eq
            (R := R) (M := N ⧸ s.last.submoduleOf N) (M' := R ⧸ q.asIdeal) e]
          exact associatedPrimesOfModule_quotient_prime_eq_singleton (R := R) q
        rw [hquot, Set.mem_singleton_iff] at hI'
        exact ⟨q, PrimeCyclicFiltration.mem_primeFactors_snoc_last (s := s) hle hq, hI'.symm⟩

/-- Owner-form companion to Lemma 10.63.4: the associated prime points of `M` lie among the prime
factors occurring in the given prime-cyclic filtration. -/
theorem associatedPrimePointsOfModule_subset_primeFactors_of_prime_quotient_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    :
    asIdeal ⁻¹' associatedPrimesOfModule R M ⊆
      s.primeFactors := by
  have hlast :
      associatedPrimesOfModule R s.last ⊆ PrimeSpectrum.asIdeal '' s.primeFactors :=
    associatedPrimesOfLast_subset_image_primeFactors_of_prime_quotient_filtration
      (R := R) (M := M) s hs₀
  have htop :
      associatedPrimesOfModule R s.last = associatedPrimesOfModule R M := by
    rw [hs_top]
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq
        (R := R) (M := (⊤ : Submodule R M)) (M' := M) Submodule.topEquiv)
  intro 𝔭 h𝔭
  have h𝔭_mem : 𝔭.asIdeal ∈ associatedPrimesOfModule R M := by
    simpa using h𝔭
  have h𝔭_last : 𝔭.asIdeal ∈ associatedPrimesOfModule R s.last := by
    rw [htop]
    exact h𝔭_mem
  rcases hlast h𝔭_last with ⟨q, hq, hq_eq⟩
  have : q = 𝔭 := PrimeSpectrum.ext hq_eq
  simpa [this] using hq

variable (p : Fin s.length → PrimeSpectrum R)

/-- Lemma 10.63.4: if `M` admits a finite filtration by submodules whose successive quotients are
isomorphic to quotients `R ⧸ p i` by prime ideals, then every textbook-associated prime of `M`
comes from one of the prime points occurring in that filtration. This ideal-valued form is the
image of the prime-spectrum owner statement under `PrimeSpectrum.asIdeal`. -/
-- Proof sketch: induct on the length of the relation series. For the last step, apply
-- the source-facing associated-prime description to the last short exact sequence
-- `0 → s.eraseLast.last → s.last → quotient → 0`; identify the associated primes of the quotient
-- with the singleton `{(p i).asIdeal}` using the chosen quotient isomorphism and the cyclic
-- description of
-- `Ass(R ⧸ p)`, then use the induction hypothesis on the truncated filtration.
theorem associatedPrimesOfModule_subset_range_of_prime_quotient_filtration
    (hp : ∀ i,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    : associatedPrimesOfModule R M ⊆ asIdeal '' Set.range p := by
  have hsubset :
      asIdeal ⁻¹' associatedPrimesOfModule R M ⊆ Set.range p := by
    simpa [s.primeFactors_eq_range p hp] using
      associatedPrimePointsOfModule_subset_primeFactors_of_prime_quotient_filtration s hs₀ hs_top
  intro I hI
  have hpoint :
      (⟨I, hI.1⟩ : PrimeSpectrum R) ∈ asIdeal ⁻¹' associatedPrimesOfModule R M := by
    simpa
  rcases hsubset hpoint with ⟨i, hi⟩
  refine ⟨p i, ⟨⟨i, rfl⟩, ?_⟩⟩
  exact congrArg asIdeal hi

/-- In the Noetherian setting, Lemma 10.63.4 can be restated using the canonical mathlib set
`associatedPrimes R M`. -/
theorem associatedPrimes_subset_range_of_prime_quotient_filtration [IsNoetherianRing R]
    (hp : ∀ i,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    : associatedPrimes R M ⊆ asIdeal '' Set.range p := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes R M] using
    associatedPrimesOfModule_subset_range_of_prime_quotient_filtration s p hp hs₀ hs_top

end

/-! ### Lemma_10_63_5 (from Chap10) -/
section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.63.5: if `R` is a Noetherian ring and `M` is a finite `R`-module, then
`associatedPrimes R M` is finite. This is exactly the owner theorem
`associatedPrimes.finite`. -/
recall associatedPrimes.finite

end

/-! ### Proposition_10_63_6 (from Chap10) -/
universe u v

open PrimeSpectrum Module.associatedPrimes

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Proposition 10.63.6: for a finite module over a Noetherian ring, a prime point `𝔭 : Spec R`
is minimal in the support of `M` if and only if its underlying ideal is minimal among the
associated primes of `M`. -/
-- Proof sketch: the inclusion `Ass(M) ⊆ Supp(M)` is Lemma `10.63.2`. Conversely, a minimal point
-- of the support is associated by the minimal-support criterion from this section. Minimality then
-- upgrades these inclusions to an equivalence on minimal primes.
theorem minimal_support_iff_minimal_associatedPrimes
    (𝔭 : PrimeSpectrum R) :
    Minimal (· ∈ Module.support R M) 𝔭 ↔
      Minimal (· ∈ associatedPrimes R M) 𝔭.asIdeal := by
  constructor
  · intro h𝔭
    refine ⟨Module.minimal_support_mem_associatedPrimes 𝔭 h𝔭, ?_⟩
    intro q hq hq𝔭
    let q' : PrimeSpectrum R := ⟨q, hq.1⟩
    have hq' : q' ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
      simpa [q'] using hq
    exact h𝔭.2 (Module.associatedPrimes_subset_support hq') hq𝔭
  · intro h𝔭
    have h𝔭' : 𝔭 ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
      simpa using h𝔭.1
    refine ⟨Module.associatedPrimes_subset_support h𝔭', ?_⟩
    intro q hq hq𝔭
    obtain ⟨r, hr, hrq⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hq)
    let r' : PrimeSpectrum R := ⟨r, hr.1.1⟩
    have hr_assoc : r ∈ associatedPrimes R M :=
      minimalPrimes_annihilator_subset_associatedPrimes R M hr
    have h𝔭r : 𝔭.asIdeal ≤ r := h𝔭.2 hr_assoc (hrq.trans hq𝔭)
    exact h𝔭r.trans hrq

omit [IsNoetherianRing R] [Module.Finite R M] in
private theorem minimal_associatedPrimePoints_iff_minimal_associatedPrimes
    (𝔭 : PrimeSpectrum R) :
    Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) 𝔭 ↔
      Minimal (· ∈ associatedPrimes R M) 𝔭.asIdeal := by
  constructor
  · intro h𝔭
    refine ⟨by simpa using h𝔭.1, ?_⟩
    intro q hq hq𝔭
    let q' : PrimeSpectrum R := ⟨q, hq.1⟩
    have hq' : q' ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
      simpa [q'] using hq
    exact h𝔭.2 hq' hq𝔭
  · intro h𝔭
    refine ⟨by simpa using h𝔭.1, ?_⟩
    intro q hq hq𝔭
    exact h𝔭.2 hq (show q.asIdeal ≤ 𝔭.asIdeal from hq𝔭)

/- Proposition 10.63.6 also identifies minimal support points with the minimal prime factors of any
prime cyclic filtration. The prime-spectrum associated-prime condition needed for the three-way TFAE
is a bridge/view of the owner theorem `minimal_support_iff_minimal_associatedPrimes`, while the
filtration comparison is exactly the owner theorem
`minimal_primeFactor_iff_minimal_support_of_prime_cyclic_filtration` from Lemma `10.62.5`. -/

/-- Proposition 10.63.6, reformulated as the equivalence of the three textbook conditions at a
fixed prime point of `Spec R`. -/
theorem minimal_support_associatedPrimes_prime_quotient_filtration_tfae
    (s : PrimeCyclicFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) (𝔭 : PrimeSpectrum R) :
    List.TFAE
      [ Minimal (· ∈ Module.support R M) 𝔭,
        Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) 𝔭,
        Minimal (· ∈ s.primeFactors) 𝔭 ] := by
  tfae_have 1 ↔ 2 := by
    rw [minimal_support_iff_minimal_associatedPrimes, ←
      minimal_associatedPrimePoints_iff_minimal_associatedPrimes 𝔭]
  tfae_have 1 ↔ 3 :=
    (minimal_primeFactor_iff_minimal_support_of_prime_cyclic_filtration s hs₀ hs_top 𝔭).symm
  tfae_finish

end

/-! ### Lemma_10_63_7 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item lies in commutative algebra of associated primes of modules.
Sampled declarations in this domain are the chapter's source-facing `associatedPrimesOfModule`,
the bridge `associatedPrimesOfModule_eq_associatedPrimes`, and mathlib's owner lemmas
`associatedPrimes.eq_empty_of_subsingleton` and `associatedPrimes.nonempty`. The numbered item is
`source-facing`, while the owner-form statement is only a derived `bridge/view` companion in the
Noetherian setting. -/

/-- Lemma 10.63.7: over a Noetherian ring, an `R`-module `M` is the zero module exactly when
its textbook set of associated primes is empty. In Lean, `M = (0)` is expressed as
`Subsingleton M`. -/
-- Proof sketch: pass from the source-facing set `associatedPrimesOfModule` to the Noetherian
-- owner set `associatedPrimes` via `associatedPrimesOfModule_eq_associatedPrimes`, then use
-- `associatedPrimes.eq_empty_of_subsingleton` and `associatedPrimes.nonempty`.
theorem subsingleton_iff_associatedPrimesOfModule_eq_empty :
    Subsingleton M ↔ associatedPrimesOfModule R M = ∅ := by
  constructor
  · intro hM
    letI := hM
    rw [associatedPrimesOfModule_eq_associatedPrimes]
    simpa using (associatedPrimes.eq_empty_of_subsingleton : associatedPrimes R M = ∅)
  · intro hAssoc
    by_contra hM
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    have hAssoc' : associatedPrimes R M = ∅ := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hAssoc
    exact (associatedPrimes.nonempty R M).ne_empty hAssoc'

/-- Noetherian owner-form companion to Lemma 10.63.7 in mathlib's `associatedPrimes` API. -/
theorem subsingleton_iff_associatedPrimes_eq_empty :
    Subsingleton M ↔ associatedPrimes R M = ∅ := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    (subsingleton_iff_associatedPrimesOfModule_eq_empty :
      Subsingleton M ↔ associatedPrimesOfModule R M = ∅)

end

/-! ### Lemma_10_63_8 (from Chap10) -/
universe u v

open PrimeSpectrum Module.associatedPrimes

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage: this item lies in commutative algebra of module support and associated primes.
The core owner abstraction is mathlib's `associatedPrimes R M`; the theorem below is a
source-facing bridge from minimal support points to membership in that owner set.
-/

namespace Module

/-- Lemma 10.63.8: if a prime point `𝔭` is minimal in the support of an `R`-module `M` over a
Noetherian ring, then its underlying ideal is an associated prime of `M`. -/
-- Proof sketch: choose `m : M` with `(R ∙ m).annihilator ≤ 𝔭.asIdeal`. The cyclic submodule
-- `R ∙ m` is finite, and minimality of `𝔭` in `Supp(M)` makes `𝔭` minimal in `Supp(R ∙ m)` as
-- well. A minimal prime of the annihilator of `R ∙ m` lying under `𝔭.asIdeal` must then equal
-- `𝔭.asIdeal`, so the canonical theorem
-- `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes` gives
-- `𝔭.asIdeal ∈ associatedPrimes R (R ∙ m)`. Finally, associated primes are preserved by the
-- owner theorem `associatedPrimes.subset_of_injective` for the injective subtype map `R ∙ m ↪ M`.
theorem minimal_support_mem_associatedPrimes
    (𝔭 : PrimeSpectrum R)
    (h𝔭 : Minimal (· ∈ support R M) 𝔭) :
    𝔭.asIdeal ∈ associatedPrimes R M := by
  obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp h𝔭.1
  let N : Submodule R M := R ∙ m
  have h𝔭_span : 𝔭 ∈ support R N := mem_support_iff_of_finite.mpr hm
  have h𝔭_span_min : Minimal (· ∈ support R N) 𝔭 := by
    refine ⟨h𝔭_span, fun q hq hq𝔭 ↦ ?_⟩
    exact h𝔭.2 (support_subset_of_injective N.subtype N.subtype_injective hq) hq𝔭
  obtain ⟨q, hq, hq𝔭⟩ := Ideal.exists_minimalPrimes_le hm
  let q' : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hq' : q' ∈ support R N := mem_support_iff_of_finite.mpr hq.1.2
  have h𝔭q : 𝔭 ≤ q' := h𝔭_span_min.2 hq' hq𝔭
  have hq_eq : q = 𝔭.asIdeal := le_antisymm hq𝔭 h𝔭q
  have h𝔭_assoc_span : 𝔭.asIdeal ∈ associatedPrimes R N := by
    have h𝔭_min : 𝔭.asIdeal ∈ (Module.annihilator R N).minimalPrimes := by
      simpa [hq_eq] using hq
    exact minimalPrimes_annihilator_subset_associatedPrimes R N h𝔭_min
  exact associatedPrimes.subset_of_injective N.subtype_injective h𝔭_assoc_span

end Module

end

/-! ### Lemma_10_63_9 (from Chap10) -/
section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- Lemma 10.63.9: for a Noetherian ring `R` and an `R`-module `M`, the union of the associated
primes of `M` is exactly the set of elements of `R` that are zerodivisors on `M`. This is the
canonical mathlib theorem `biUnion_associatedPrimes_eq_zero_divisors`. -/
recall biUnion_associatedPrimes_eq_zero_divisors

end

/-! ### Lemma_10_63_10 (from Chap10) -/
universe u v

open IsLocalRing
open scoped Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

/- Domain triage: this item is a source-facing bridge in the owner API `Module.supportDim`. The
primitive owner data is the module `M` and the canonical quotient object `QuotSMulTop f M`; the
two inequalities are derived from owner theorems rather than new primitive structure. -/

-- Proof sketch: the left inequality comes from the quotient map `M →ₗ[R] QuotSMulTop f M` via
-- `Module.supportDim_le_of_surjective`, reflecting `Supp(M / fM) ⊆ Supp(M)`. The right inequality
-- is exactly the canonical theorem `Module.supportDim_le_supportDim_quotSMulTop_succ`.
/-- Lemma 10.63.10: if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`f ∈ maximalIdeal R`, then the support dimension of `M / fM`, written canonically as
`QuotSMulTop f M`, satisfies
`supportDim R (QuotSMulTop f M) ≤ supportDim R M ∧
  supportDim R M ≤ supportDim R (QuotSMulTop f M) + 1`. -/
theorem supportDim_quotSMulTop_bounds_of_mem_maximalIdeal (f : R) (hf : f ∈ maximalIdeal R) :
    supportDim R (QuotSMulTop f M) ≤ supportDim R M ∧
      supportDim R M ≤ supportDim R (QuotSMulTop f M) + 1 := by
  constructor
  · simpa using
      supportDim_le_of_surjective (Submodule.mkQ (f • ⊤))
        (Submodule.mkQ_surjective _)
  · simpa using supportDim_le_supportDim_quotSMulTop_succ hf

/- Companion recall: if `f` avoids every minimal prime of `Module.annihilator R M`, then the right
inequality above is an equality. This is the canonical theorem
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal`. -/
recall supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal

/- Companion recall: if `f` is a nonzerodivisor on `M` and lies in the maximal ideal, then the
right inequality above is an equality. This is the canonical theorem
`Module.supportDim_quotSMulTop_succ_eq_supportDim`. -/
recall supportDim_quotSMulTop_succ_eq_supportDim

end Module

end

/-! ### Lemma_10_63_11 (from Chap10) -/
universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/- Domain triage: this item is in commutative algebra of associated primes under restriction of
scalars.
* `source-facing`: the textbook statement is about the source-facing set
  `associatedPrimesOfModule`.
* `core/canonical`: the owner abstraction in mathlib is `associatedPrimes R M`.
* `bridge/view`: the primitive contraction statement already lives upstream as
  `Ideal.isAssociatedToModule_comap` on the predicate `Ideal.IsAssociatedToModule`.
The present file should therefore stay a thin set-level bridge, with no parallel owner wrapper.
-/

/-- Lemma 10.63.11: contracting associated primes of an `S`-module `M` along `Spec(S) → Spec(R)`
lands in the associated primes of `M` viewed as an `R`-module. -/
theorem associatedPrimesOfModule_image_comap_subset :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M ⊆ associatedPrimesOfModule R M :=
  by
    rintro _ ⟨P, hP, rfl⟩
    exact Ideal.isAssociatedToModule_comap R M hP

end

/-! ### Remark_10_63_12 (from Chap10) -/
universe u

open MvPolynomial IsLocalRing

/-- The quotient ring `k[x₁, x₂, x₃, \ldots]/(x_i^2)` from the counterexample in
Stacks, Remark 10.63.12 (`05BX`). -/
abbrev infiniteSquareZeroPolynomialQuotient (k : Type u) [CommRing k] :=
  MvPolynomial ℕ k ⧸ Ideal.span (Set.range fun i : ℕ ↦ ((X i : MvPolynomial ℕ k) ^ 2))

section

variable (k : Type u) [Field k]

local notation "I∞" =>
  Ideal.span (Set.range fun i : ℕ ↦ ((X i : MvPolynomial ℕ k) ^ 2))
local notation "S∞" => infiniteSquareZeroPolynomialQuotient k

-- Keep the quotient ring's canonical self-module structure local so theorem statements elaborate
-- without exposing any extra public API.
noncomputable local instance : Module S∞ S∞ :=
  Semiring.toModule

/-- The augmentation `k[x₁, x₂, x₃, \ldots] / (x_i^2) → k` given by the constant coefficient. -/
noncomputable def infiniteSquareZeroPolynomialQuotientAugmentation : S∞ →+* k :=
  Ideal.Quotient.lift I∞ MvPolynomial.constantCoeff <| by
    intro p hp
    have hker : I∞ ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ℕ k →+* k) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    simpa [RingHom.mem_ker] using hker hp

/-- The augmentation `k[x₁, x₂, x₃, \ldots] / (x_i^2) → k` is surjective. -/
theorem infiniteSquareZeroPolynomialQuotientAugmentation_surjective :
    Function.Surjective (infiniteSquareZeroPolynomialQuotientAugmentation k) := by
  intro a
  refine ⟨Ideal.Quotient.mk I∞ (MvPolynomial.C a), ?_⟩
  simp [infiniteSquareZeroPolynomialQuotientAugmentation]

/-- Helper for Remark 10.63.12: the square-zero relation ideal is the monomial ideal generated by
the square monomials `X_i^2 = monomial (single i 2) 1`. -/
private theorem relation_ideal_eq_square_monomial_span :
    I∞ =
      Ideal.span ((fun s : ℕ →₀ ℕ ↦ MvPolynomial.monomial s (1 : k)) ''
        Set.range (fun i : ℕ ↦ Finsupp.single i 2)) := by
  change Ideal.span (Set.range fun i : ℕ ↦ (MvPolynomial.X i : MvPolynomial ℕ k) ^ 2) =
    Ideal.span ((fun s : ℕ →₀ ℕ ↦ MvPolynomial.monomial s (1 : k)) ''
      Set.range (fun i : ℕ ↦ Finsupp.single i 2))
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Finsupp.single i 2, ⟨i, rfl⟩, by simp [MvPolynomial.X_pow_eq_monomial]⟩
  · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp [MvPolynomial.X_pow_eq_monomial]⟩

/-- Helper for Remark 10.63.12: every nonconstant monomial has square in the relation ideal. -/
private theorem monomial_sq_mem_relation_ideal_of_ne_zero
    {d : ℕ →₀ ℕ} (hd : d ≠ 0) (a : k) :
    (MvPolynomial.monomial d a : MvPolynomial ℕ k) ^ 2 ∈ I∞ := by
  classical
  rw [relation_ideal_eq_square_monomial_span (k := k)]
  rw [pow_two, MvPolynomial.monomial_mul, MvPolynomial.mem_ideal_span_monomial_image_iff_dvd]
  intro xi hxi
  by_cases ha : a = 0
  · simp [ha] at hxi
  · have haa : a * a ≠ 0 := mul_ne_zero ha ha
    have hxi_eq : xi = d + d := by
      simpa [MvPolynomial.support_monomial, haa] using hxi
    subst hxi_eq
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
    have hi_pos : 1 ≤ d i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
    have hi_two : 2 ≤ (d + d) i := by
      simpa [Finsupp.add_apply] using add_le_add hi_pos hi_pos
    have hi_le : Finsupp.single i 2 ≤ d + d := by
      simpa [Finsupp.single_le_iff] using hi_two
    refine ⟨Finsupp.single i 2, ⟨i, rfl⟩, ?_⟩
    rw [MvPolynomial.monomial_dvd_monomial]
    exact ⟨Or.inr hi_le, one_dvd _⟩

/-- Helper for Remark 10.63.12: each nonconstant monomial class in the quotient is nilpotent,
indeed square-zero. -/
private theorem quotient_mk_monomial_isNilpotent_of_ne_zero
    {d : ℕ →₀ ℕ} (hd : d ≠ 0) (a : k) :
    IsNilpotent (Ideal.Quotient.mk I∞ (MvPolynomial.monomial d a) : S∞) := by
  refine ⟨2, ?_⟩
  -- The square vanishes because it lies in the defining monomial square ideal.
  simpa [map_pow] using
    (Ideal.Quotient.eq_zero_iff_mem).2
      (monomial_sq_mem_relation_ideal_of_ne_zero (k := k) hd a)

/-- Helper for Remark 10.63.12: augmentation-zero classes are nilpotent because they are finite
sums of nonconstant monomial classes. -/
private theorem quotient_mk_isNilpotent_of_constantCoeff_zero
    (p : MvPolynomial ℕ k) (hp : MvPolynomial.constantCoeff p = 0) :
    IsNilpotent (Ideal.Quotient.mk I∞ p : S∞) := by
  classical
  -- Expand the representative as a finite sum of support monomials and use nilpotence termwise.
  have hsum :
      (Ideal.Quotient.mk I∞ p : S∞) =
        ∑ d ∈ p.support, (Ideal.Quotient.mk I∞ (MvPolynomial.monomial d (p.coeff d)) : S∞) := by
    calc
      (Ideal.Quotient.mk I∞ p : S∞) =
          Ideal.Quotient.mk I∞ (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) := by
            simpa using congrArg (Ideal.Quotient.mk I∞) (MvPolynomial.as_sum p)
      _ = ∑ d ∈ p.support, (Ideal.Quotient.mk I∞ (MvPolynomial.monomial d (p.coeff d)) : S∞) := by
            rw [map_sum]
  rw [hsum]
  apply isNilpotent_sum
  intro d hd
  have hd_ne_zero : d ≠ 0 := by
    intro hd0
    have hcoeff : p.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    exact hcoeff (by simpa [MvPolynomial.constantCoeff, hd0] using hp)
  exact quotient_mk_monomial_isNilpotent_of_ne_zero (k := k) hd_ne_zero (p.coeff d)

/-- Helper for Remark 10.63.12: a nonzero class has a support monomial not divisible by any
square monomial. -/
private theorem exists_squarefree_support_of_not_mem_relation_ideal
    {p : MvPolynomial ℕ k} (hp : p ∉ I∞) :
    ∃ d ∈ p.support, ∀ j : ℕ, ¬ Finsupp.single j 2 ≤ d := by
  classical
  by_contra h
  push Not at h
  apply hp
  rw [relation_ideal_eq_square_monomial_span (k := k)]
  rw [MvPolynomial.mem_ideal_span_monomial_image]
  intro d hd
  obtain ⟨j, hj⟩ := h d hd
  exact ⟨Finsupp.single j 2, ⟨j, rfl⟩, hj⟩

/-- Helper for Remark 10.63.12: every nonzero class is multiplied nontrivially by some fresh
square-zero variable class. -/
private theorem exists_square_zero_variable_mul_ne_zero_of_ne_zero
    {p : MvPolynomial ℕ k} (hp : (Ideal.Quotient.mk I∞ p : S∞) ≠ 0) :
    ∃ i : ℕ, (Ideal.Quotient.mk I∞ (MvPolynomial.X i) : S∞) ^ 2 = 0 ∧
      (Ideal.Quotient.mk I∞ (MvPolynomial.X i) : S∞) * Ideal.Quotient.mk I∞ p ≠ 0 := by
  classical
  have hp_not_mem : p ∉ I∞ := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hp
  obtain ⟨d, hd, hd_squarefree⟩ :=
    exists_squarefree_support_of_not_mem_relation_ideal (k := k) hp_not_mem
  let i : ℕ := p.vars.sup id + 1
  have hi_not_mem_vars : i ∉ p.vars := by
    intro hi
    have hle : i ≤ p.vars.sup (fun n : ℕ => n) := by
      simpa using (Finset.le_sup (f := fun n : ℕ => n) hi)
    have hle' : p.vars.sup (fun n : ℕ => n) + 1 ≤ p.vars.sup (fun n : ℕ => n) := by
      simpa [i] using hle
    exact Nat.not_succ_le_self _ hle'
  have hdi_zero : d i = 0 := by
    by_contra hdi
    have hdi_mem : i ∈ d.support := Finsupp.mem_support_iff.mpr hdi
    have hi_mem_vars : i ∈ p.vars := (MvPolynomial.mem_vars i).2 ⟨d, hd, hdi_mem⟩
    exact hi_not_mem_vars hi_mem_vars
  have hXi_sq_zero : (Ideal.Quotient.mk I∞ (MvPolynomial.X i) : S∞) ^ 2 = 0 := by
    -- Each variable square is one of the defining relations.
    have hXi_sq_mem : (MvPolynomial.X i : MvPolynomial ℕ k) ^ 2 ∈ I∞ := by
      exact Ideal.subset_span ⟨i, rfl⟩
    simpa [map_pow] using
      (Ideal.Quotient.eq_zero_iff_mem).2 hXi_sq_mem
  let m : ℕ →₀ ℕ := Finsupp.single i 1 + d
  have hm_support : m ∈ (MvPolynomial.X i * p).support := by
    rw [MvPolynomial.mem_support_iff]
    simpa [m, MvPolynomial.coeff_X_mul] using (MvPolynomial.mem_support_iff.mp hd)
  have hm_no_square : ∀ j : ℕ, ¬ Finsupp.single j 2 ≤ m := by
    intro j hle
    by_cases hji : j = i
    · have hj_two : 2 ≤ m i := by
        simpa [m, hji, Finsupp.single_le_iff] using hle
      have : ¬ 2 ≤ m i := by
        simpa [m, Finsupp.add_apply, hdi_zero]
      exact this hj_two
    · have hj_two : 2 ≤ m j := by
        simpa [m, Finsupp.single_le_iff] using hle
      have hsingle_le : Finsupp.single j 2 ≤ d := by
        simpa [m, Finsupp.add_apply, hji, Finsupp.single_le_iff] using hj_two
      exact hd_squarefree j hsingle_le
  have hmul_not_mem : MvPolynomial.X i * p ∉ I∞ := by
    intro hmul_mem
    rw [relation_ideal_eq_square_monomial_span (k := k),
      MvPolynomial.mem_ideal_span_monomial_image] at hmul_mem
    rcases hmul_mem m hm_support with ⟨s, hs, hsle⟩
    rcases hs with ⟨j, rfl⟩
    exact hm_no_square j hsle
  refine ⟨i, hXi_sq_zero, ?_⟩
  intro hmul_zero
  apply hmul_not_mem
  exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa [map_mul] using hmul_zero)

/-- An element of the infinite square-zero polynomial quotient is a unit exactly when its
augmentation is nonzero. -/
theorem infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero (x : S∞) :
    IsUnit x ↔ infiniteSquareZeroPolynomialQuotientAugmentation k x ≠ 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    -- Units remain units under the augmentation, and units in a field are exactly the nonzero
    -- elements.
    exact isUnit_iff_ne_zero.mp <|
      RingHom.isUnit_map (infiniteSquareZeroPolynomialQuotientAugmentation k) hx
  · intro hx
    have hconst : MvPolynomial.constantCoeff p ≠ 0 := by
      simpa [infiniteSquareZeroPolynomialQuotientAugmentation] using hx
    have hnil :
        IsNilpotent
          (Ideal.Quotient.mk I∞ (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) : S∞) := by
      -- The augmentation-zero remainder is nilpotent by the monomial decomposition helper.
      apply quotient_mk_isNilpotent_of_constantCoeff_zero (k := k)
      simp [MvPolynomial.constantCoeff]
    have hconst_unit :
        IsUnit (Ideal.Quotient.mk I∞ (MvPolynomial.C (MvPolynomial.constantCoeff p)) : S∞) := by
      -- The constant term is a nonzero scalar from the base field, hence a unit.
      refine RingHom.isUnit_map (Ideal.Quotient.mk I∞) ?_
      exact RingHom.isUnit_map MvPolynomial.C (isUnit_iff_ne_zero.mpr hconst)
    -- Split into constant term plus nilpotent remainder.
    have hp_split :
        (Ideal.Quotient.mk I∞ p : S∞) =
          Ideal.Quotient.mk I∞ (MvPolynomial.C (MvPolynomial.constantCoeff p)) +
            Ideal.Quotient.mk I∞ (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) := by
      calc
        (Ideal.Quotient.mk I∞ p : S∞) =
            Ideal.Quotient.mk I∞
              (MvPolynomial.C (MvPolynomial.constantCoeff p) +
                (p - MvPolynomial.C (MvPolynomial.constantCoeff p))) := by
                  congr 1
                  simp [sub_eq_add_neg, add_left_comm]
        _ =
            Ideal.Quotient.mk I∞ (MvPolynomial.C (MvPolynomial.constantCoeff p)) +
              Ideal.Quotient.mk I∞ (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) := by
                  rw [map_add]
    rw [hp_split]
    exact hnil.isUnit_add_left_of_commute hconst_unit (Commute.all _ _)

instance : IsLocalRing S∞ := by
  letI : Nontrivial S∞ := (infiniteSquareZeroPolynomialQuotientAugmentation k).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  by_cases hx : infiniteSquareZeroPolynomialQuotientAugmentation k x = 0
  · right
    rw [infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero]
    simp [map_sub, hx]
  · left
    exact (infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero k x).2 hx

/-- The residue field of `k[x₁, x₂, x₃, \ldots] / (x_i^2)` is canonically `k`. -/
noncomputable def infiniteSquareZeroPolynomialQuotientResidueFieldEquiv :
    ResidueField S∞ ≃+* k := by
  let f := infiniteSquareZeroPolynomialQuotientAugmentation k
  letI : IsLocalHom f := IsLocalHom.of_surjective f
    (infiniteSquareZeroPolynomialQuotientAugmentation_surjective k)
  refine RingEquiv.ofBijective (IsLocalRing.ResidueField.lift f) ?_
  constructor
  · exact RingHom.injective _
  · intro a
    obtain ⟨x, rfl⟩ := infiniteSquareZeroPolynomialQuotientAugmentation_surjective k a
    refine ⟨residue S∞ x, ?_⟩
    change IsLocalRing.ResidueField.lift f (residue S∞ x) = f x
    simp [IsLocalRing.ResidueField.lift_residue_apply]

/-- In the Stacks counterexample ring `S = k[x₁, x₂, x₃, \ldots]/(x_i^2)`, the only
textbook-associated prime of `S` viewed as a `k`-module is `(0)`. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot :
    associatedPrimesOfModule k S∞ = {⊥} := by
  letI : Nontrivial S∞ := (infiniteSquareZeroPolynomialQuotientAugmentation k).domain_nontrivial
  -- Over a field, the only prime ideal is `(0)`, so nonemptiness already determines the set.
  rw [associatedPrimesOfModule_eq_associatedPrimes]
  refine Set.eq_singleton_iff_unique_mem.mpr ?_
  constructor
  · obtain ⟨p, hp⟩ := associatedPrimes.nonempty k S∞
    have hp_prime : p.IsPrime := (show IsAssociatedPrime p S∞ from hp).isPrime
    letI : p.IsPrime := hp_prime
    simpa [Ideal.eq_bot_of_prime p] using hp
  · intro p hp
    have hp_prime : p.IsPrime := (show IsAssociatedPrime p S∞ from hp).isPrime
    letI : p.IsPrime := hp_prime
    exact Ideal.eq_bot_of_prime p

/-- Noetherian-field companion to
`infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot`
in mathlib's radical-based `associatedPrimes` API. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimes_over_baseField_eq_singleton_bot :
    associatedPrimes k S∞ = {⊥} := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes k S∞]
  exact infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot
    k

/-- In the Stacks counterexample ring `S = k[x₁, x₂, x₃, \ldots]/(x_i^2)`, the textbook-associated
primes of `S` as an `S`-module are empty. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty :
    associatedPrimesOfModule S∞ S∞ = ∅ := by
  ext q
  constructor
  · intro hq
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
    rcases hq with ⟨hq_prime, x, rfl⟩
    by_cases hx : x = 0
    · -- The annihilator of `0` is the whole ring, which is never prime.
      exact hq_prime.ne_top ((Ideal.torsionOf_eq_top_iff S∞ x).2 hx)
    · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨i, hXi_sq_zero, hXi_mul_ne_zero⟩ :=
        exists_square_zero_variable_mul_ne_zero_of_ne_zero (k := k) hx
      let y : S∞ := Ideal.Quotient.mk I∞ (MvPolynomial.X i)
      have hy_sq_mem : y ^ 2 ∈ Ideal.torsionOf S∞ S∞ (Ideal.Quotient.mk I∞ p) := by
        -- The chosen variable square annihilates every element because it is already zero.
        simpa [y, Ideal.mem_torsionOf_iff, smul_eq_mul, hXi_sq_zero]
      have hy_not_mem : y ∉ Ideal.torsionOf S∞ S∞ (Ideal.Quotient.mk I∞ p) := by
        -- But the fresh variable itself does not annihilate the chosen nonzero element.
        intro hy_mem
        exact hXi_mul_ne_zero (by simpa [y, Ideal.mem_torsionOf_iff, smul_eq_mul] using hy_mem)
      have hy_mul_mem : y * y ∈ Ideal.torsionOf S∞ S∞ (Ideal.Quotient.mk I∞ p) := by
        simpa [pow_two] using hy_sq_mem
      have hy_mem : y ∈ Ideal.torsionOf S∞ S∞ (Ideal.Quotient.mk I∞ p) := by
        rcases hq_prime.mem_or_mem hy_mul_mem with hy_mem | hy_mem
        · exact hy_mem
        · exact hy_mem
      exact hy_not_mem hy_mem
  · intro hq
    simp at hq

/-- Remark 10.63.12 (Stacks, tag `05BX`): for
`S = k[x₁, x₂, x₃, \ldots]/(x_i^2)` and `M = S`, the associated primes of `M` over the base field
`k` are nonempty, while the associated primes of `S` over itself are empty. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_counterexample :
    (associatedPrimesOfModule k S∞).Nonempty ∧ associatedPrimesOfModule S∞ S∞ = ∅ := by
  refine ⟨?_, infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty k⟩
  rw [infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot k]
  exact Set.singleton_nonempty ⊥

/-- Noetherian-field companion to
`infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_counterexample` in mathlib's
`associatedPrimes` API. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimes_counterexample :
    (associatedPrimes k S∞).Nonempty ∧ associatedPrimesOfModule S∞ S∞ = ∅ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes k S∞]
  exact infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_counterexample k

/-- Remark 10.63.12 (Stacks, tag `05BX`): for the ring map
`k → k[x₁, x₂, x₃, \ldots]/(x_i^2)` with `M = S`, the image of `Ass_S(M)` in `Spec k` does not
contain `Ass_k(M)`. -/
theorem associatedPrimesOfModule_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient :
    ¬ associatedPrimesOfModule k S∞ ⊆
      Ideal.comap (algebraMap k S∞) '' associatedPrimesOfModule S∞ S∞ := by
  rw [infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot k,
    infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty k]
  simp

/-- Noetherian-field companion to
`associatedPrimesOfModule_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient` in
mathlib's radical-based `associatedPrimes` API. -/
theorem associatedPrimes_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient :
    ¬ associatedPrimes k S∞ ⊆
      Ideal.comap (algebraMap k S∞) '' associatedPrimesOfModule S∞ S∞ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes k S∞]
  exact associatedPrimesOfModule_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient k

end

/-! ### Lemma_10_63_13 (from Chap10) -/
universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Helper for Lemma 10.63.13: restricting scalars contracts the annihilator ideal of an element
of `M` over `S` to its annihilator over `R`. -/
private theorem comap_torsionOf_eq_torsionOf_restrictScalars (m : M) :
    Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m) = Ideal.torsionOf R M m := by
  -- Both sides encode the same equation `r • m = 0`, viewed through the scalar tower.
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/-- Helper for Lemma 10.63.13: the quotient `S / Ann_S(m)` embeds into `M` as the cyclic
submodule generated by `m`. -/
private theorem quotient_torsionOf_to_module_injective (m : M) :
    Function.Injective
      (((Submodule.subtype (S ∙ m)).comp
        (Ideal.quotTorsionOfEquivSpanSingleton S M m).toLinearMap) :
          (S ⧸ Ideal.torsionOf S M m) →ₗ[S] M) := by
  -- The quotient-to-span equivalence is injective, and the subtype map into `M` is injective.
  intro x y hxy
  apply (Ideal.quotTorsionOfEquivSpanSingleton S M m).injective
  exact Subtype.ext hxy

/-- Helper for Lemma 10.63.13: a prime minimal over the annihilator of `m` over `S` is associated
to `M` over `S`. -/
private theorem mem_associatedPrimes_of_mem_minimalPrimes_torsionOf [IsNoetherianRing S]
    (m : M) {q : Ideal S} (hq : q ∈ (Ideal.torsionOf S M m).minimalPrimes) :
    q ∈ associatedPrimes S M := by
  let f : (S ⧸ Ideal.torsionOf S M m) →ₗ[S] M :=
    (Submodule.subtype (S ∙ m)).comp
      (Ideal.quotTorsionOfEquivSpanSingleton S M m).toLinearMap
  have hf : Function.Injective f := quotient_torsionOf_to_module_injective (S := S) (M := M) m
  have hq_quot :
      q ∈ associatedPrimes S (S ⧸ Ideal.torsionOf S M m) := by
    -- Minimal primes over the annihilator of the quotient module are associated in the
    -- Noetherian owner API.
    have hq_ann :
        q ∈ (Module.annihilator S (S ⧸ Ideal.torsionOf S M m)).minimalPrimes := by
      simpa [Ideal.annihilator_quotient] using hq
    exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      S (S ⧸ Ideal.torsionOf S M m) hq_ann
  -- Transport the associated prime along the injective cyclic-quotient map into `M`.
  exact associatedPrimes.subset_of_injective (R := S) (M := S ⧸ Ideal.torsionOf S M m)
    (M' := M) (f := f) hf hq_quot

/-- Helper for Lemma 10.63.13: a prime minimal over the annihilator of `m` over `S` is
textbook-associated to `M`. -/
private theorem mem_associatedPrimesOfModule_of_mem_minimalPrimes_torsionOf
    [IsNoetherianRing S] (m : M) {q : Ideal S}
    (hq : q ∈ (Ideal.torsionOf S M m).minimalPrimes) :
    q ∈ associatedPrimesOfModule S M := by
  -- Over the Noetherian ring `S`, the textbook and owner associated-prime notions coincide.
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    mem_associatedPrimes_of_mem_minimalPrimes_torsionOf (S := S) (M := M) m hq

/- Domain triage: this item is in commutative algebra of associated primes under restriction of
scalars.
* `source-facing`: the textbook set `associatedPrimesOfModule R M`.
* `core/canonical`: mathlib's owner set `associatedPrimes R M`.
* `bridge/view`: contraction along `Spec(S) → Spec(R)` induced by `algebraMap R S`.
The textbook statement is source-facing, while the owner-form companion is kept as a thin
Noetherian bridge for downstream use. -/

/-- Lemma 10.63.13: if `S` is Noetherian, then contracting the textbook associated primes
`Ass_S(M)` along `Spec(S) → Spec(R)` gives exactly the textbook associated primes `Ass_R(M)`. -/
-- Proof sketch: Lemma 10.63.11 gives the inclusion from left to right. For the reverse
-- inclusion, choose `p ∈ Ass_R(M)` coming from an element `m : M`, let `I` be the annihilator of
-- `m` in `S`, and choose a prime `q` minimal over `I` that contracts to `p`. Since `S` is
-- Noetherian, minimal primes over annihilators are associated, so `q ∈ Ass_S(M)` and contracts
-- to `p`.
theorem associatedPrimesOfModule_restrictScalars_eq_image_comap [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M =
      associatedPrimesOfModule R M := by
  refine Set.Subset.antisymm associatedPrimesOfModule_image_comap_subset ?_
  intro p hp
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp
  rcases hp with ⟨hp, m, hm⟩
  -- Contract the `S`-annihilator of the same witness and lift the resulting minimal prime.
  have hminimal :
      p ∈ (Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m)).minimalPrimes := by
    refine ⟨⟨hp, ?_⟩, ?_⟩
    · rw [comap_torsionOf_eq_torsionOf_restrictScalars (R := R) (S := S) (M := M) m, hm]
    · intro J hJ hJp
      simpa [comap_torsionOf_eq_torsionOf_restrictScalars (R := R) (S := S) (M := M) m, hm] using
        hJ.2
  obtain ⟨q, hq, hq_comap⟩ :=
    Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) p hminimal
  -- The lifted minimal prime is associated to the cyclic quotient, hence to `M`.
  exact ⟨q, mem_associatedPrimesOfModule_of_mem_minimalPrimes_torsionOf
    (S := S) (M := M) m hq, hq_comap⟩

/-- Noetherian owner-form companion to Lemma 10.63.13 in mathlib's `associatedPrimes` API. -/
-- Proof sketch: the forward inclusion contracts a Noetherian `S`-associated prime to a
-- source-facing associated prime over `R`, hence to an owner associated prime over `R`. For the
-- reverse inclusion, start from an owner witness `p = radical(Ann_R(m))`, lift a minimal prime
-- over `Ann_S(m)` contracting to `p`, and then use the cyclic quotient `S / Ann_S(m) ↪ M` to show
-- that this lifted prime is associated over `S`.
theorem associatedPrimes_restrictScalars_eq_image_comap [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M =
      associatedPrimes R M := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro p ⟨q, hq, rfl⟩
    -- On the `S`-side, Noetherianity lets us pass to the textbook exact-annihilator witness.
    have hq' : q ∈ associatedPrimesOfModule S M := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq
    have hp' : Ideal.comap (algebraMap R S) q ∈ associatedPrimesOfModule R M :=
      associatedPrimesOfModule_image_comap_subset ⟨q, hq', rfl⟩
    exact (associatedPrimesOfModule_subset_associatedPrimes (R := R) (M := M)) hp'
  · intro p hp
    rcases hp with ⟨hp, m, hm⟩
    -- Rewrite the owner witness as the radical of the contracted `S`-annihilator.
    have hm_torsion : p = (Ideal.torsionOf R M m).radical := by
      calc
        p = ((⊥ : Submodule R M).colon ({m} : Set M)).radical := hm
        _ = ((Submodule.span R ({m} : Set M)).annihilator).radical := by
          rw [Submodule.bot_colon']
        _ = (Ideal.torsionOf R M m).radical := by
          simp [Ideal.torsionOf, Submodule.annihilator_span_singleton]
    have hminimal :
        p ∈ (Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m)).minimalPrimes := by
      rw [comap_torsionOf_eq_torsionOf_restrictScalars (R := R) (S := S) (M := M) m,
        hm_torsion]
      refine ⟨⟨by simpa [hm_torsion] using hp, Ideal.le_radical⟩, ?_⟩
      intro J hJ hJp
      exact hJ.1.radical_le_iff.mpr hJ.2
    obtain ⟨q, hq, hq_comap⟩ :=
      Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) p hminimal
    -- The same lifted minimal prime is associated to `M` over `S`.
    exact ⟨q, mem_associatedPrimes_of_mem_minimalPrimes_torsionOf
      (S := S) (M := M) m hq, hq_comap⟩

end

/-! ### Lemma_10_63_14 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
variable [IsScalarTower R (R ⧸ I) M]

/- Domain triage: this item lies in commutative algebra of associated primes under a quotient map.
* `source-facing`: the textbook exact-annihilator set `associatedPrimesOfModule`.
* `core/canonical`: mathlib's radical-based owner set `associatedPrimes`.
* `bridge/view`: contraction along the quotient map `Ideal.Quotient.mk I`.
The primitive data here are the annihilator ideals `Ideal.torsionOf ... m`; the quotient theorem is
derived from their canonical map/comap behavior, so the file keeps no extra public helper API.
-/

private lemma quotient_comap_torsionOf_eq_torsionOf (m : M) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.torsionOf (R ⧸ I) M m) = Ideal.torsionOf R M m := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff,
    ← algebraMap_smul (R ⧸ I) r m]
  simp [Ideal.Quotient.algebraMap_eq]

private lemma quotient_comap_bot_le_torsionOf (m : M) :
    Ideal.comap (Ideal.Quotient.mk I) ⊥ ≤ Ideal.torsionOf R M m := by
  intro r hr
  rw [Ideal.mem_torsionOf_iff]
  rw [Ideal.mem_comap, Ideal.mem_bot] at hr
  rw [← algebraMap_smul (R ⧸ I) r m]
  change (Ideal.Quotient.mk I) r • m = 0
  simpa using congrArg (fun x : R ⧸ I ↦ x • m) hr

/-- Lemma 10.63.14: the textbook associated primes `Ass(M)` of an `R ⧸ I`-module `M`, viewed in
`Spec(R)` by contraction along `R → R ⧸ I`, are exactly the associated primes of `M` as an
`R`-module. Here the `R`-action on `M` is the one coming from restriction of scalars along the
quotient map. -/
theorem associatedPrimesOfModule_quotient_image_comap_eq :
    Ideal.comap (Ideal.Quotient.mk I) '' associatedPrimesOfModule (R ⧸ I) M =
      associatedPrimesOfModule R M := by
  refine Set.Subset.antisymm ?_ ?_
  · simpa [Ideal.Quotient.algebraMap_eq] using
      (associatedPrimesOfModule_image_comap_subset :
        Ideal.comap (algebraMap R (R ⧸ I)) '' associatedPrimesOfModule (R ⧸ I) M ⊆
          associatedPrimesOfModule R M)
  · intro p hp
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp
    rcases hp with ⟨hp, m, hm⟩
    have hIp : I ≤ p := by
      have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ p := by
        simpa [hm, RingHom.ker_eq_comap_bot] using quotient_comap_bot_le_torsionOf I m
      simpa [Ideal.mk_ker] using hker
    refine ⟨p.map (Ideal.Quotient.mk I), ?_, Ideal.comap_map_mk hIp⟩
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
    refine ⟨Ideal.isPrime_map_quotientMk_of_isPrime hIp, m, ?_⟩
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [Ideal.comap_map_mk hIp, quotient_comap_torsionOf_eq_torsionOf I m, hm]

end
