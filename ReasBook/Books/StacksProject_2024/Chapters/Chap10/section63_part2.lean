import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_63_15 (from Chap10) -/
universe u v

section

open IsLocalRing

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item is in commutative algebra of associated primes under localization.
The owner abstraction in mathlib is `Module.associatedPrimes`, but the chapter's public notion in
this section is the source-facing exact-annihilator predicate `Ideal.IsAssociatedToModule` and the
derived set `associatedPrimesOfModule`. This file therefore stays at the `source-facing` layer and
uses the owner-style localization argument only as an internal bridge. Primitive data: a prime
ideal `p`, its localization `Localization.AtPrime p`, and the localized module
`LocalizedModule.AtPrime p M`. Derived API: the set-membership reformulations below. -/

namespace Ideal

/-- Lemma 10.63.15 (1), predicate form: if `p` is associated to `M` in the textbook
exact-annihilator sense, then the maximal ideal of `R_p` is associated to `M_p` in the same
exact-annihilator sense. -/
theorem isAssociatedToModule_maximalIdeal_atPrime
    {p : Ideal R} [p.IsPrime] (hp : IsAssociatedToModule R M p) :
    IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
      (maximalIdeal (Localization.AtPrime p)) := by
  rw [isAssociatedToModule_iff_exists_torsionOf] at hp ⊢
  rcases hp with ⟨hp, m, hm⟩
  let f : M →ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
  refine ⟨(maximalIdeal.isMaximal _).isPrime, f m, ?_⟩
  ext t
  rcases IsLocalization.exists_mk'_eq p.primeCompl t with ⟨r, s, rfl⟩
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p) p]
  constructor
  · intro hr
    have hrm : r • m = 0 := by
      simpa [Ideal.mem_torsionOf_iff] using (show r ∈ Ideal.torsionOf R M m from hm.symm ▸ hr)
    rw [Ideal.mem_torsionOf_iff, ← IsLocalizedModule.mk'_one p.primeCompl f,
      IsLocalizedModule.mk'_smul_mk', mul_one, hrm, IsLocalizedModule.mk'_zero]
  · intro ht
    rw [Ideal.mem_torsionOf_iff, ← IsLocalizedModule.mk'_one p.primeCompl f,
      IsLocalizedModule.mk'_smul_mk', mul_one, IsLocalizedModule.mk'_eq_zero'] at ht
    rcases ht with ⟨s', hs'⟩
    have hs'r_zero : (r * (s' : R)) • m = 0 := by
      calc
        (r * (s' : R)) • m = (s' : R) • (r • m) := by
          simp [smul_smul, mul_comm]
        _ = 0 := hs'
    have hs'r_torsion : (r * (s' : R)) ∈ Ideal.torsionOf R M m := by
      simpa [Ideal.mem_torsionOf_iff] using hs'r_zero
    have hs'r : r * (s' : R) ∈ p := by
      exact hm.symm ▸ hs'r_torsion
    exact (hp.mem_or_mem hs'r).resolve_right s'.2

/-- Lemma 10.63.15 (2), predicate form: if `p` is finitely generated and the maximal ideal of
`R_p` is associated to `M_p` in the textbook exact-annihilator sense, then `p` is associated to
`M`. -/
theorem isAssociatedToModule_of_isAssociatedToModule_maximalIdeal_atPrime_of_fg
    {p : Ideal R} [p.IsPrime]
    (hp :
      IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
        (maximalIdeal (Localization.AtPrime p)))
    (hfg : p.FG) :
    IsAssociatedToModule R M p := by
  rw [isAssociatedToModule_iff_exists_torsionOf] at hp ⊢
  rcases hp with ⟨hpmax, x, hx⟩
  rcases hfg with ⟨T, hT⟩
  let f : M →ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
  rcases IsLocalizedModule.mk'_surjective p.primeCompl f x with ⟨⟨m, s⟩, rfl⟩
  simp only [Function.uncurry_apply_pair] at hx
  have mem (a : T) : algebraMap R (Localization.AtPrime p) a ∈ maximalIdeal (Localization.AtPrime p) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p a).2 <|
      by simpa [← hT] using Ideal.subset_span a.2
  simp only [hx, Ideal.mem_torsionOf_iff, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
    IsLocalizedModule.mk'_eq_zero' f] at mem
  choose g hg using mem
  let G : p.primeCompl := ∏ a, g a
  refine ⟨‹p.IsPrime›, G.1 • m, le_antisymm ?_ ?_⟩
  · have hspan : Ideal.span ↑T ≤ Ideal.torsionOf R M (G.1 • m) := by
      rw [Ideal.span_le]
      intro a ha
      let aT : T := ⟨a, ha⟩
      obtain ⟨u, hu⟩ : g aT ∣ G := by
        apply Finset.dvd_prod_of_mem g
        exact Finset.mem_univ aT
      change a ∈ Ideal.torsionOf R M (G.1 • m)
      rw [Ideal.mem_torsionOf_iff]
      have hga : ((g aT).1 * a) • m = 0 := by
        calc
          ((g aT).1 * a) • m = (g aT).1 • (a • m) := by
            simp [smul_smul]
          _ = 0 := by simpa [aT] using hg aT
      calc
        a • (G.1 • m) = u.1 • (((g aT).1 * a) • m) := by
          rw [show G = g aT * u by exact hu, Submonoid.coe_mul]
          simp [smul_smul, mul_comm, mul_left_comm]
        _ = 0 := by rw [hga, smul_zero]
    simpa [hT] using hspan
  · intro r hr
    have hr0 : (r * G.1) • m = 0 := by
      simpa [G, Ideal.mem_torsionOf_iff, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hr
    have hrG_loc : algebraMap R (Localization.AtPrime p) (r * G.1) ∈ maximalIdeal (Localization.AtPrime p) := by
      rw [hx, Ideal.mem_torsionOf_iff, algebraMap_smul, ← IsLocalizedModule.mk'_smul, hr0,
        IsLocalizedModule.mk'_zero]
    have hrG : r * G.1 ∈ p :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p (r * G.1)).1 hrG_loc
    exact (‹p.IsPrime›.mem_or_mem hrG).resolve_right G.2

end Ideal

/-- Lemma 10.63.15 (1): if `p` is associated to `M` in the textbook exact-annihilator sense, then
the maximal ideal of `R_p` is associated to `M_p` in the same exact-annihilator sense. -/
theorem mem_associatedPrimesOfModule_atPrime_of_mem_associatedPrimesOfModule
    {p : Ideal R} [p.IsPrime] (hp : p ∈ associatedPrimesOfModule R M) :
    maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
  rw [mem_associatedPrimesOfModule_iff] at hp ⊢
  exact Ideal.isAssociatedToModule_maximalIdeal_atPrime hp

/-- Lemma 10.63.15 (2): if `p` is finitely generated and the maximal ideal of `R_p` is associated
to `M_p` in the textbook exact-annihilator sense, then `p` is associated to `M`. -/
theorem mem_associatedPrimesOfModule_of_mem_associatedPrimesOfModule_atPrime_of_fg
    {p : Ideal R} [p.IsPrime]
    (hp :
      maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M))
    (hfg : p.FG) :
    p ∈ associatedPrimesOfModule R M := by
  rw [mem_associatedPrimesOfModule_iff] at hp ⊢
  exact Ideal.isAssociatedToModule_of_isAssociatedToModule_maximalIdeal_atPrime_of_fg hp hfg

end

/-! ### Lemma_10_63_16 (from Chap10) -/
universe u v

section

open Module.associatedPrimes

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "Rₛ" => Localization S
local notation "Mₛ" => LocalizedModule S M

private lemma mem_range_comap_iff_disjoint_of_isPrime {p : Ideal R} (hp : p.IsPrime) :
    p ∈ Set.range (Ideal.comap (algebraMap R Rₛ)) ↔
      Disjoint (S : Set R) (p : Set R) := by
  constructor
  · rintro ⟨J, rfl⟩
    rw [IsLocalization.disjoint_comap_iff S Rₛ]
    simpa using hp.ne_top
  · intro hpS
    exact ⟨Ideal.map (algebraMap R Rₛ) p,
      IsLocalization.comap_map_of_isPrime_disjoint S Rₛ hp hpS⟩

/-- Lemma 10.63.16 (1): under the canonical injection
`Spec(Rₛ) → Spec(R)`, the textbook associated primes `Ass(Mₛ)` over `Rₛ` are exactly the
textbook associated primes of the same localized module viewed over `R`. -/
-- Proof sketch: contract associated primes of `LocalizedModule S M` along `R → Localization S`
-- to get one inclusion. For the reverse inclusion, an associated prime of `LocalizedModule S M`
-- over `R` is disjoint from `S`, hence comes from a unique prime of `Localization S`; the same
-- localized element exhibits that prime as associated over the localization ring.
theorem associatedPrimesOfModule_localizedModule_eq_image_comap :
    Ideal.comap (algebraMap R Rₛ) '' associatedPrimesOfModule Rₛ Mₛ =
      associatedPrimesOfModule R Mₛ := by
  refine Set.Subset.antisymm associatedPrimesOfModule_image_comap_subset ?_
  intro p hp
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp
  rcases hp with ⟨hp, m, hm⟩
  let q : Ideal Rₛ := Ideal.torsionOf Rₛ Mₛ m
  have hcomap : Ideal.comap (algebraMap R Rₛ) q = p := by
    ext r
    rw [hm, Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    simp [algebraMap_smul]
  have hq_ne_top : q ≠ ⊤ := by
    intro hq_top
    apply hp.ne_top
    simpa [hq_top] using hcomap.symm
  have hq : q.IsPrime := by
    refine (IsLocalization.isPrime_iff_isPrime_disjoint S Rₛ q).2 ?_
    refine ⟨by simpa [hcomap] using hp, ?_⟩
    simpa [hcomap] using (IsLocalization.disjoint_comap_iff S Rₛ q).2 hq_ne_top
  refine ⟨q, ?_, hcomap⟩
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
  exact ⟨hq, m, rfl⟩

/-- Lemma 10.63.16 (2): an associated prime of `M` that is disjoint from `S` remains an
associated prime after localizing. This is the source-facing exact-annihilator statement from
Definition 10.63.1. -/
-- Proof sketch: let `p ∈ associatedPrimesOfModule R M` come from an element `m : M`, and assume
-- `p` is disjoint from `S`. Then the image of `m` in `LocalizedModule S M` has annihilator still
-- equal to `p`, showing that `p` is associated to the localized module over `R` in the textbook
-- sense.
theorem associatedPrimesOfModule_inter_disjoint_subset_localizedModule :
    associatedPrimesOfModule R M ∩ { p : Ideal R | Disjoint (S : Set R) (p : Set R) } ⊆
      associatedPrimesOfModule R Mₛ := by
  let f : M →ₗ[R] Mₛ := LocalizedModule.mkLinearMap S M
  rintro p ⟨hp, hpS⟩
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp ⊢
  rcases hp with ⟨hp, m, hm⟩
  refine ⟨hp, f m, ?_⟩
  ext r
  rw [hm, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro hr
    simpa [f.map_smul] using congrArg f hr
  · intro hr
    have hfr : f (r • m) = f 0 := by
      simpa [f.map_smul] using hr
    rcases (IsLocalizedModule.eq_iff_exists S f).1 hfr with ⟨s, hs⟩
    have hmul : r * (s : R) ∈ p := by
      rw [hm, Ideal.mem_torsionOf_iff]
      calc
        (r * (s : R)) • m = (s : R) • (r • m) := by
          simp [smul_smul, mul_comm]
        _ = 0 := by simpa using hs
    have hsnot : (s : R) ∉ p := by
      intro hs'
      exact Set.disjoint_left.1 hpS s.2 hs'
    have hrp : r ∈ p := (hp.mem_or_mem hmul).resolve_right hsnot
    simpa [hm, Ideal.mem_torsionOf_iff] using hrp

/-- Textbook reformulation of Lemma 10.63.16 (2) using the image of
`Spec(Localization S) → Spec(R)`. -/
-- Proof sketch: identify the image of `Spec(Localization S) → Spec(R)` with the prime ideals of
-- `R` disjoint from `S`, then apply
-- `associatedPrimesOfModule_inter_disjoint_subset_localizedModule`.
theorem associatedPrimesOfModule_inter_localization_range_subset :
    associatedPrimesOfModule R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) ⊆
      associatedPrimesOfModule R Mₛ := by
  rintro p ⟨hp, hp_range⟩
  exact associatedPrimesOfModule_inter_disjoint_subset_localizedModule S
    ⟨hp, (mem_range_comap_iff_disjoint_of_isPrime S hp.1).1 hp_range⟩

/-- Noetherian owner-form of Lemma 10.63.16 (3): for mathlib's `associatedPrimes`, localizing at
`S` keeps exactly the primes in the image of `Spec(Localization S) → Spec(R)`. -/
theorem associatedPrimes_inter_localization_range_eq [IsNoetherianRing R] :
    associatedPrimes R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) =
      associatedPrimes R Mₛ := by
  let f : M →ₗ[R] Mₛ := LocalizedModule.mkLinearMap S M
  have hpreimage :
      (Ideal.comap (algebraMap R Rₛ)) ⁻¹' associatedPrimes R M =
        associatedPrimes Rₛ Mₛ := by
    simpa using
      (preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
        S Rₛ f)
  calc
    associatedPrimes R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) =
        Ideal.comap (algebraMap R Rₛ) '' associatedPrimes Rₛ Mₛ := by
          rw [← hpreimage]
          ext p
          constructor
          · rintro ⟨hp, ⟨q, rfl⟩⟩
            exact ⟨q, hp, rfl⟩
          · rintro ⟨q, hq, rfl⟩
            exact ⟨hq, ⟨q, rfl⟩⟩
    _ = associatedPrimes R Mₛ := associatedPrimes_restrictScalars_eq_image_comap

/-- Textbook reformulation of Lemma 10.63.16 (3) using the image of
`Spec(Localization S) → Spec(R)`. -/
-- Proof sketch: rewrite the source-facing associated-prime set to mathlib's owner set in the
-- Noetherian case, then apply the owner-form localization theorem above.
theorem associatedPrimesOfModule_inter_localization_range_eq [IsNoetherianRing R] :
    associatedPrimesOfModule R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) =
      associatedPrimesOfModule R Mₛ := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    associatedPrimes_inter_localization_range_eq S

/-- Lemma 10.63.16 (3): if `R` is Noetherian, then the associated primes of `M` disjoint from `S`
are exactly the associated primes of `LocalizedModule S M` viewed over `R`, in the textbook
exact-annihilator sense. -/
-- Proof sketch: the inclusion from `(2)` is always available. For the converse, use the
-- Noetherian localization theorem for textbook associated primes to identify the associated
-- primes of the localized module with those primes of `R` coming from associated primes of `M`,
-- then rewrite the image condition as disjointness from `S`.
theorem associatedPrimesOfModule_inter_disjoint_eq_localizedModule [IsNoetherianRing R] :
    associatedPrimesOfModule R M ∩ { p : Ideal R | Disjoint (S : Set R) (p : Set R) } =
      associatedPrimesOfModule R Mₛ := by
  calc
    associatedPrimesOfModule R M ∩ { p : Ideal R | Disjoint (S : Set R) (p : Set R) } =
        associatedPrimesOfModule R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) := by
          ext p
          constructor
          · rintro ⟨hp, hpS⟩
            exact ⟨hp, (mem_range_comap_iff_disjoint_of_isPrime S hp.1).2 hpS⟩
          · rintro ⟨hp, hp_range⟩
            exact ⟨hp, (mem_range_comap_iff_disjoint_of_isPrime S hp.1).1 hp_range⟩
    _ = associatedPrimesOfModule R Mₛ := by
          simpa [associatedPrimesOfModule_eq_associatedPrimes] using
            associatedPrimes_inter_localization_range_eq S

/-- Noetherian companion to Lemma 10.63.16 (2) in mathlib's radical-based `associatedPrimes`
API. -/
theorem associatedPrimes_inter_disjoint_subset_localizedModule [IsNoetherianRing R] :
    associatedPrimes R M ∩ { p : Ideal R | Disjoint (S : Set R) (p : Set R) } ⊆
      associatedPrimes R Mₛ := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    associatedPrimesOfModule_inter_disjoint_subset_localizedModule S

/-- Noetherian companion to the range reformulation of Lemma 10.63.16 (2) in mathlib's
`associatedPrimes` API. -/
theorem associatedPrimes_inter_localization_range_subset [IsNoetherianRing R] :
    associatedPrimes R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) ⊆
      associatedPrimes R Mₛ := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    associatedPrimesOfModule_inter_localization_range_subset S

/-- Noetherian companion to Lemma 10.63.16 (3) in mathlib's radical-based `associatedPrimes`
API. -/
theorem associatedPrimes_inter_disjoint_eq_localizedModule [IsNoetherianRing R] :
    associatedPrimes R M ∩ { p : Ideal R | Disjoint (S : Set R) (p : Set R) } =
      associatedPrimes R Mₛ := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    associatedPrimesOfModule_inter_disjoint_eq_localizedModule S

end

/-! ### Lemma_10_63_17 (from Chap10) -/
universe u v

section

open Module.associatedPrimes IsLocalizedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

local notation "Mₛ" => LocalizedModule S M

/- Domain triage:
- primary domain: commutative algebra of associated primes under localization;
- `source-facing`: the textbook exact-annihilator set `associatedPrimesOfModule R M`;
- `core/canonical`: mathlib's radical-based owner set `associatedPrimes R M` in the Noetherian
  case;
- primitive data: the canonical localization map `LocalizedModule.mkLinearMap S M` together with
  regularity of the `S`-action on `M`;
- derived API: equalities of the associated-prime sets. This file should stay a thin source-facing
  theorem plus its Noetherian owner companion, with no extra wrapper layer.
-/

/-- Lemma 10.63.17: if every element of the multiplicative set `S` is a nonzerodivisor on the
`R`-module `M`, then the associated primes of `M` agree with those of the localized module
`S⁻¹M` viewed as an `R`-module. -/
-- Proof sketch: the hypothesis is exactly the injectivity criterion for the canonical localization
-- map `M → S⁻¹M`, so the annihilator of `m` agrees with the annihilator of its image. For the
-- reverse inclusion, write a localized witness as `m / s`; if `r (m / s) = 0`, then after
-- clearing denominators some `s' ∈ S` kills `r m`, and regularity of `s'` forces `r m = 0`.
@[stacks 05C0]
theorem associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule
    (hS : ∀ s : S, IsSMulRegular M s) :
    associatedPrimesOfModule R M = associatedPrimesOfModule R Mₛ := by
  let f : M →ₗ[R] Mₛ := LocalizedModule.mkLinearMap S M
  refine Set.Subset.antisymm ?_ ?_
  · intro p hp
    have hf : Function.Injective f := (injective_iff_isRegular S f).2 hS
    simpa [associatedPrimesOfModule] using Ideal.isAssociatedToModule_map_of_injective R M hp f hf
  · intro p hp
    rcases hp with ⟨hp, x, hx⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := mk'_surjective S f x
    simp only [Function.uncurry_apply_pair] at hx
    refine ⟨hp, m, ?_⟩
    ext r
    rw [hx, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    constructor
    · intro hr
      have hs : mk' f (r • m) s = 0 := by
        simpa [mk'_smul] using hr
      rcases (mk'_eq_zero' f s).mp hs with ⟨s', hs'⟩
      exact (hS s').right_eq_zero_of_smul hs'
    · intro hr
      rw [← mk'_smul, hr, mk'_zero]

/-- In the Noetherian case, Lemma 10.63.17 specializes to the canonical mathlib set
`associatedPrimes`. -/
theorem associatedPrimes_eq_associatedPrimes_localizedModule [IsNoetherianRing R]
    (hS : ∀ s : S, IsSMulRegular M s) :
    associatedPrimes R M = associatedPrimes R Mₛ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes R M,
    ← associatedPrimesOfModule_eq_associatedPrimes R Mₛ]
  exact associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule S hS

end

/-! ### Lemma_10_63_18 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (I : Ideal R)

/- Domain triage:
- `source-facing`: the textbook criterion for when an ideal contains an `M`-regular element.
- `core/canonical`: mathlib's owner set `associatedPrimes R M`.
- `bridge/view`: `biUnion_associatedPrimes_eq_compl_regular`, identifying the regular locus with the
  complement of the union of the owner set.

Sampled owner declarations in this domain:
- `associatedPrimes R M`
- `associatedPrimes.finite`
- `biUnion_associatedPrimes_eq_compl_regular`
- `Ideal.subset_union_prime_finite`

Primitive data are only the ideal `I` and the owner set `associatedPrimes R M`; the regularity
criterion is derived API, so no extra wrapper or packaged data belongs in the public surface. -/

/-- Lemma 10.63.18: let `R` be a Noetherian local ring, let `M` be a finite `R`-module, and let
`I ⊆ maximalIdeal R` be an ideal. Then `I` contains an element that is a nonzerodivisor on `M` if
and only if `I` is not contained in any associated prime of `M`.

The local hypothesis `I ≤ maximalIdeal R` is mathematically redundant for this criterion, so the
refined owner-based statement omits it. -/
-- Proof sketch: if `x ∈ I` is `M`-regular, then `x` avoids every associated prime by the
-- owner theorem `biUnion_associatedPrimes_eq_compl_regular`. Conversely, finiteness of
-- `associatedPrimes R M` and prime avoidance yield `x ∈ I` outside every associated prime when
-- `I` is contained in none of them; the same owner theorem then shows `x` is
-- `M`-regular.
theorem exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes :
    (∃ x ∈ I, IsSMulRegular M x) ↔
      ∀ 𝔮 ∈ associatedPrimes R M, ¬ I ≤ 𝔮 := by
  let U : Set R := ⋃ p ∈ associatedPrimes R M, (p : Set R)
  constructor
  · rintro ⟨x, hxI, hxreg⟩ 𝔮 h𝔮 hI𝔮
    have hxnot : x ∉ U := by
      simpa [U, Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hxreg
    exact hxnot <| Set.mem_iUnion.2 ⟨𝔮, Set.mem_iUnion.2 ⟨h𝔮, hI𝔮 hxI⟩⟩
  · intro hI
    have hnot_subset : ¬ (I : Set R) ⊆ U := by
      intro hsubset
      obtain ⟨𝔮, h𝔮, hI𝔮⟩ :=
        (I.subset_union_prime_finite (associatedPrimes.finite R M) I I
          fun 𝔮 h𝔮 _ _ ↦ (AssociatedPrimes.mem_iff.mp h𝔮).isPrime).mp hsubset
      exact hI 𝔮 h𝔮 hI𝔮
    obtain ⟨x, hxI, hxnot⟩ := Set.not_subset.mp hnot_subset
    refine ⟨x, hxI, ?_⟩
    simpa [U, Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hxnot

end

/-! ### Lemma_10_63_19 (from Chap10) -/
universe u v

open LocalizedModule

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
* `source-facing`: this item is the associated-prime-indexed localization map from the Stacks
  statement.
* `core/canonical`: the canonical family of localization maps is `LocalizedModule.mkLinearMap`,
  assembled over an index set by `LinearMap.pi`.
* `bridge/view`: this theorem reindexes the weakly-associated-prime statement from
  `Lemma_10_66_17` along `associatedPrimes_eq_weaklyAssociatedPrimes`, so it should stay a thin
  bridge rather than introducing a parallel map definition. -/

/-- Lemma 10.63.19: if `R` is Noetherian, then the canonical map from `M` to the product of its
localizations at the associated primes of `M` is injective. -/
-- Proof sketch: if `x : M` maps to zero in every localization `M_𝔭` for `𝔭 ∈ associatedPrimes R M`,
-- then any associated prime of the cyclic submodule `R ∙ x` also lies in `associatedPrimes R M`
-- by Lemma 10.63.3, but localization at that prime would keep `R ∙ x` nonzero. Hence
-- `associatedPrimes R (R ∙ x) = ∅`, so Lemma 10.63.7 forces `R ∙ x = 0`, and therefore `x = 0`.
theorem to_pi_localization_at_associated_primes_injective :
    Function.Injective
      (LinearMap.pi fun p : associatedPrimes R M ↦
        mkLinearMap p.1.primeCompl M) :=
  by
    let reindex :
        ((p : associatedPrimes R M) → LocalizedModule.AtPrime (p : Ideal R) M) ≃ₗ[R]
          ((p : weaklyAssociatedPrimes R M) → LocalizedModule.AtPrime (p : Ideal R) M) :=
      LinearEquiv.piCongrLeft R
        (fun p : weaklyAssociatedPrimes R M ↦ LocalizedModule.AtPrime (p : Ideal R) M)
        (Equiv.setCongr associatedPrimes_eq_weaklyAssociatedPrimes)
    have hcomp :
        reindex.toLinearMap.comp
            (LinearMap.pi fun p : associatedPrimes R M ↦ mkLinearMap p.1.primeCompl M) =
          LinearMap.pi fun p : weaklyAssociatedPrimes R M ↦ mkLinearMap p.1.primeCompl M := by
      ext x p
      rfl
    have hinj :
        Function.Injective
          ⇑(reindex.toLinearMap.comp
            (LinearMap.pi fun p : associatedPrimes R M ↦ mkLinearMap p.1.primeCompl M)) := by
      simpa [hcomp] using
        (weaklyAssociatedPrimes_localizationMap_injective :
          Function.Injective
            ⇑(LinearMap.pi fun p : weaklyAssociatedPrimes R M ↦ mkLinearMap p.1.primeCompl M))
    intro x y hxy
    exact hinj <| by simpa using congrArg reindex hxy

end

/-! ### Lemma_10_63_20 (from Chap10) -/
universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S]

include k

/-- Lemma 10.63.20: if `S` is a finite type `k`-algebra of positive Krull dimension, then `S`
contains an element that is a nonzerodivisor and not a unit.

Canonical Lean form: for an element of a ring, "is a nonzerodivisor" is expressed by membership
in the canonical submonoid `nonZeroDivisors S`, rather than by the module-specialized predicate
`IsSMulRegular S`. -/
-- Proof sketch: `S` is Noetherian, so `associatedPrimes S S` is finite by Lemma `10.63.5`.
-- Positive Krull dimension rules out the zero-dimensional case from Lemma `10.61.3`, so `S` has
-- infinitely many maximal ideals and one can choose a maximal ideal not among the associated
-- primes. Lemma `10.63.18` then yields an element of that maximal ideal that is regular on `S`,
-- hence a nonzerodivisor. Membership in a proper maximal ideal shows it is not a unit.
theorem exists_nonzerodivisor_nonunit_of_finiteType_over_field_of_pos_ringKrullDim
    (hdim : 0 < ringKrullDim S) :
    ∃ f : S, f ∈ nonZeroDivisors S ∧ ¬ IsUnit f := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  haveI : Nontrivial S := by
    by_contra hS
    haveI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    simp [ringKrullDim_eq_bot_of_subsingleton] at hdim
  have htfae :
      List.TFAE
        [ Ring.KrullDimLE 0 S
        , Finite (PrimeSpectrum S)
        , Finite (MaximalSpectrum S)
        , T2Space (PrimeSpectrum S)
        , FiniteDimensional k S
        , IsArtinianRing S
        , DiscreteTopology (PrimeSpectrum S)
        ] :=
    finiteTypeAlgebra_over_field_zeroDimensional_tfae
  have hnot_finite : ¬ Finite (MaximalSpectrum S) := by
    intro hfinite
    have hle0 : Ring.KrullDimLE 0 S := (htfae.out 0 2 rfl rfl).mpr hfinite
    have hzero : ringKrullDim S = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle0
    exact not_lt_of_ge hzero.le hdim
  haveI : Infinite (MaximalSpectrum S) := by
    by_contra hfinite
    exact hnot_finite (not_infinite_iff_finite.mp hfinite)
  classical
  have hassoc_finite : (associatedPrimes S S).Finite := associatedPrimes.finite S S
  have hmax_assoc_finite :
      { m : MaximalSpectrum S | m.asIdeal ∈ associatedPrimes S S }.Finite := by
    let e : MaximalSpectrum S ↪ Ideal S :=
      ⟨MaximalSpectrum.asIdeal, fun m n h ↦ by
        cases m
        cases n
        cases h
        rfl⟩
    simpa [e] using Set.Finite.preimage_embedding e hassoc_finite
  obtain ⟨m, hm_assoc⟩ : ∃ m : MaximalSpectrum S, m.asIdeal ∉ associatedPrimes S S := by
    simpa using hmax_assoc_finite.infinite_compl.nonempty
  have hm_not_le_assoc : ∀ q ∈ associatedPrimes S S, ¬ m.asIdeal ≤ q := by
    intro q hq_assoc hle
    have hmq : m.asIdeal = q :=
      m.isMaximal.eq_of_le (IsAssociatedPrime.isPrime <| AssociatedPrimes.mem_iff.mp hq_assoc).ne_top
        hle
    exact hm_assoc (hmq ▸ hq_assoc)
  obtain ⟨f, hfm, hf_reg⟩ :
      ∃ f ∈ m.asIdeal, IsSMulRegular S f :=
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes m.asIdeal).2 hm_not_le_assoc
  have hf_mem : f ∈ nonZeroDivisors S := by
    simpa [nonZeroDivisorsLeft_eq_nonZeroDivisors] using
      hf_reg.isLeftRegular.mem_nonZeroDivisorsLeft
  refine ⟨f, hf_mem, ?_⟩
  intro hf_unit
  exact m.isMaximal.ne_top <| m.asIdeal.eq_top_of_isUnit_mem hfm hf_unit

end
