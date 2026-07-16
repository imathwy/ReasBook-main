import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import stacks_proof.stacks_project.Chap10.Lemma_10_63_13
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 05BZ]
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
@[stacks 05BZ]
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
@[stacks 05BZ]
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
