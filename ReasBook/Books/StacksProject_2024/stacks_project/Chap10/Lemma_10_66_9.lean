import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_63_15
import StacksProject_2024.stacks_project.Chap10.Lemma_10_66_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_66_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
* `source-facing`: Stacks Lemma 10.66.9 compares the chapter predicate
  `Ideal.IsAssociatedToModule` with `Ideal.IsWeaklyAssociatedToModule` for a finitely generated
  prime ideal.
* `core/canonical`: mathlib's owner abstraction is `IsAssociatedPrime`.
* `bridge/view`: the owner-level equivalence and owner-set equality are derived from the
  source-facing theorem below. Primitive data: none. -/

private theorem isAssociatedToModule_maximalIdeal_of_fg_of_isWeaklyAssociatedToModule
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hfg : (maximalIdeal A).FG)
    (h : Ideal.IsWeaklyAssociatedToModule A N (maximalIdeal A)) :
    Ideal.IsAssociatedToModule A N (maximalIdeal A) := by
  rcases h with ⟨x, hx⟩
  have hminimal : (Ideal.torsionOf A N x).minimalPrimes = {maximalIdeal A} := by
    ext q
    constructor
    · intro hq
      have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.1.ne_top
      exact Set.mem_singleton_iff.mpr <| le_antisymm hq_le (hx.2 hq.1 hq_le)
    · rintro rfl
      exact hx
  have hrad : (Ideal.torsionOf A N x).radical = maximalIdeal A := by
    rw [← Ideal.sInf_minimalPrimes, hminimal, sInf_singleton]
  have htorsion_ne_top : Ideal.torsionOf A N x ≠ ⊤ := by
    intro htop
    exact (maximalIdeal.isMaximal A).ne_top <| by
      simpa [htop, Ideal.radical_top] using hrad.symm
  have hpow : ∃ n : ℕ, maximalIdeal A ^ n ≤ Ideal.torsionOf A N x := by
    exact
      Ideal.exists_pow_le_of_le_radical_of_fg
        (by simp [hrad]) hfg
  classical
  let n := Nat.find hpow
  have hn : maximalIdeal A ^ n ≤ Ideal.torsionOf A N x := Nat.find_spec hpow
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    exact htorsion_ne_top <| top_le_iff.mp <| by simpa [n, hn_zero] using hn
  have hnot : ¬ maximalIdeal A ^ (n - 1) ≤ Ideal.torsionOf A N x := by
    intro hle
    have hfind : n ≤ n - 1 := Nat.find_min' hpow hle
    omega
  rw [Ideal.isAssociatedToModule_iff_exists_torsionOf]
  rw [SetLike.not_le_iff_exists] at hnot
  rcases hnot with ⟨a, ha_mem, ha_not_mem⟩
  refine ⟨(maximalIdeal.isMaximal A).isPrime, a • x, ?_⟩
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_torsionOf_iff, smul_smul]
    have hba : b * a ∈ maximalIdeal A ^ n := by
      have hba' : b * a ∈ maximalIdeal A ^ (n - 1) * maximalIdeal A := by
        simpa [mul_comm] using Ideal.mul_mem_mul_rev ha_mem hb
      have hba'' : b * a ∈ maximalIdeal A ^ (n - 1 + 1) := by
        simpa [pow_succ] using hba'
      have hn_eq : n - 1 + 1 = n := by
        exact Nat.sub_add_cancel <| Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
      simpa [hn_eq] using hba''
    simpa [Ideal.mem_torsionOf_iff, mul_comm, mul_left_comm, mul_assoc] using hn hba
  · have hproper : Ideal.torsionOf A N (a • x) ≠ ⊤ := by
      intro htop
      have ha_zero : a • x = 0 := by
        simpa [Ideal.mem_torsionOf_iff, one_smul] using
          (show (1 : A) ∈ Ideal.torsionOf A N (a • x) by simp [htop])
      exact ha_not_mem <| by simp [Ideal.mem_torsionOf_iff, ha_zero]
    exact IsLocalRing.le_maximalIdeal hproper

/-- Lemma 10.66.9: for a finitely generated ideal `𝔭`, textbook-associated and weakly associated
primes of `M` coincide. -/
theorem isAssociatedToModule_iff_isWeaklyAssociatedToModule_of_fg
    (𝔭 : Ideal R) (h𝔭fg : 𝔭.FG) :
    Ideal.IsAssociatedToModule R M 𝔭 ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
  constructor
  · intro h
    exact h.isWeaklyAssociatedToModule
  · intro h
    by_cases h𝔭prime : 𝔭.IsPrime
    · letI : 𝔭.IsPrime := h𝔭prime
      have hloc :
          Ideal.IsAssociatedToModule (Localization.AtPrime 𝔭) (LocalizedModule.AtPrime 𝔭 M)
            (maximalIdeal (Localization.AtPrime 𝔭)) := by
        exact
          isAssociatedToModule_maximalIdeal_of_fg_of_isWeaklyAssociatedToModule
            (by simpa [Localization.AtPrime.map_eq_maximalIdeal] using h𝔭fg.map (algebraMap R (Localization.AtPrime 𝔭)))
            ((isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime 𝔭).mp h)
      exact Ideal.isAssociatedToModule_of_isAssociatedToModule_maximalIdeal_atPrime_of_fg hloc h𝔭fg
    · exact (h𝔭prime h.isPrime).elim

/-- Companion owner-form of Lemma 10.66.9: for a finitely generated ideal `𝔭`, the mathlib
predicate `IsAssociatedPrime 𝔭 M` is equivalent to weak association. -/
theorem isAssociatedPrime_iff_isWeaklyAssociatedToModule_of_fg
    (𝔭 : Ideal R) (h𝔭fg : 𝔭.FG) :
    IsAssociatedPrime 𝔭 M ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
  constructor
  · intro h
    exact h.isWeaklyAssociatedToModule
  · intro h
    exact
      ((isAssociatedToModule_iff_isWeaklyAssociatedToModule_of_fg 𝔭 h𝔭fg).mpr h).isAssociatedPrime

/-- In a Noetherian ring, textbook-associated primes and weakly associated primes of a module
coincide in mathlib's owner API. -/
theorem associatedPrimes_eq_weaklyAssociatedPrimes [IsNoetherianRing R] :
    associatedPrimes R M = weaklyAssociatedPrimes R M := by
  ext 𝔭
  rw [AssociatedPrimes.mem_iff, mem_weaklyAssociatedPrimes_iff]
  exact
    isAssociatedPrime_iff_isWeaklyAssociatedToModule_of_fg 𝔭
      (Ideal.fg_of_isNoetherianRing 𝔭)

end
