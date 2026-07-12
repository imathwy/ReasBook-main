import StacksProject_2024.Chap10.Definition_10_67_1
import StacksProject_2024.Chap10.Lemma_10_63_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Pointwise

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "I" => Module.annihilator R M
local notation "A" => R ⧸ Module.annihilator R M

-- Source/core/bridge triage:
-- * source-facing layer: the statement is about embedded primes of the faithful quotient
--   `R ⧸ Ann_R(M)`.
-- * core/canonical owner layer: `associatedPrimes`, `Module.annihilator`, and contraction along
--   `R → R ⧸ Ann_R(M)`.
-- * bridge/view layer: `embeddedAssociatedPrimes` remains the source-facing wrapper, but the proof
--   is carried entirely by the owner theorems `associatedPrimes_restrictScalars_eq_image_comap`,
--   `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`, and
--   `IsAssociatedPrime.map_of_injective`.
/-- Lemma 10.67.4: if the finite `R`-module `M` has no embedded associated primes, then the quotient
ring `R ⧸ Ann_R(M)` has no embedded primes. -/
-- Proof sketch: replace `R` by `R ⧸ Ann_R(M)` so that `M` is faithful. By Lemma 10.40.5, the
-- support of `M` is then all of `Spec R`. If `R` had an embedded prime `𝔭`, choose an element of
-- `R` whose annihilator is `𝔭` and consider the nonzero submodule obtained by multiplying `M` by
-- that element. Any associated prime of this submodule is also an associated prime of `M` lying
-- above `𝔭`, hence would be embedded, contradicting the hypothesis.
theorem quotient_annihilator_has_no_embedded_primes_of_no_embedded_associated_primes
    (hM : embeddedAssociatedPrimes R M = ∅) :
    embeddedPrimes A = ∅ := by
  letI : Module A M := Module.quotientAnnihilator
  letI : IsScalarTower R A M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  letI : IsNoetherianRing A := Ideal.Quotient.isNoetherianRing I
  letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite R A M
  have hrestrict : Ideal.comap (algebraMap R A) '' associatedPrimes A M = associatedPrimes R M :=
    associatedPrimes_restrictScalars_eq_image_comap
  have hsurj_mk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (algebraMap R A) := by
    simpa [Ideal.Quotient.algebraMap_eq] using hsurj_mk
  have hM_min : ∀ p : Ideal R, p ∈ associatedPrimes R M → Minimal (· ∈ associatedPrimes R M) p := by
    let hiff :
        embeddedAssociatedPrimes R M = ∅ ↔
          ∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p :=
      embeddedAssociatedPrimes_eq_empty_iff R M
    exact hiff.1 hM
  have hA_M_min : ∀ p : Ideal A, p ∈ associatedPrimes A M → Minimal (· ∈ associatedPrimes A M) p := by
    intro p hp
    have hpR : Ideal.comap (algebraMap R A) p ∈ associatedPrimes R M := by
      rw [← hrestrict]
      exact ⟨p, hp, rfl⟩
    have hpR_min : Minimal (· ∈ associatedPrimes R M) (Ideal.comap (algebraMap R A) p) :=
      hM_min _ hpR
    refine ⟨hp, fun q hq hqp ↦ ?_⟩
    have hqR : Ideal.comap (algebraMap R A) q ∈ associatedPrimes R M := by
      rw [← hrestrict]
      exact ⟨q, hq, rfl⟩
    have hcomap_eq : Ideal.comap (algebraMap R A) p = Ideal.comap (algebraMap R A) q := by
      refine le_antisymm ?_ ?_
      · exact hpR_min.2 hqR (Ideal.comap_mono hqp)
      · exact Ideal.comap_mono hqp
    exact (Ideal.comap_injective_of_surjective (algebraMap R A) hsurj hcomap_eq).le
  have hfaithful : Module.annihilator A M = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨r, rfl⟩ := hsurj_mk x
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    change r ∈ Module.annihilator R M
    rw [Module.mem_annihilator] at hx ⊢
    intro m
    simpa [Module.IsTorsionBySet.mk_smul (Module.isTorsionBySet_annihilator R M) r m] using hx m
  have hA_ring_subset_module : associatedPrimes A A ⊆ associatedPrimes A M := by
    intro p hp
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
    rcases hp with ⟨hp_prime, a, ha⟩
    let N : Submodule A M := a • (⊤ : Submodule A M)
    have hN_ann : N.annihilator = p := by
      ext r
      rw [Submodule.mem_annihilator, ha, Submodule.mem_colon_singleton, Submodule.mem_bot]
      constructor
      · intro hr
        have hra : r * a ∈ Module.annihilator A M := by
          rw [Module.mem_annihilator]
          intro m
          have ham : a • m ∈ N := by
            exact Submodule.smul_mem_pointwise_smul m a ⊤ (by simp)
          simpa [N, smul_smul] using hr (a • m) ham
        simpa [hfaithful, Algebra.smul_def] using hra
      · intro hr n hn
        rcases Submodule.mem_smul_pointwise_iff_exists n a (⊤ : Submodule A M) |>.mp
            (by simpa [N] using hn) with
          ⟨m, -, rfl⟩
        simpa [smul_smul] using congrArg (fun x ↦ x • m) hr
    have hp_min : p ∈ N.annihilator.minimalPrimes := by
      simpa [hN_ann] using
        (show p ∈ p.minimalPrimes by
          rw [Ideal.minimalPrimes_eq_subsingleton_self]
          simp)
    have hp_assoc_N : p ∈ associatedPrimes A N := by
      simpa [Submodule.annihilator] using
        Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A N hp_min
    exact associatedPrimes.subset_of_injective N.subtype_injective hp_assoc_N
  have hA_ring_min : ∀ p ∈ associatedPrimes A A, Minimal (· ∈ associatedPrimes A A) p := by
    intro p hp
    refine ⟨hp, fun q hq hqp ↦ ?_⟩
    exact (hA_M_min p (hA_ring_subset_module hp)).2 (hA_ring_subset_module hq) hqp
  exact (embeddedPrimes_eq_empty_iff A).2 hA_ring_min

end
