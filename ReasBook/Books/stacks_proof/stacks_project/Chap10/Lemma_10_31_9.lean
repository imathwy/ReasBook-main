import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Localization
open IsLocalRing
open scoped BigOperators

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p

private theorem awayElement_isUnit_atPrime (f : p.primeCompl) :
    IsUnit (algebraMap R Rₚ f.1) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff Rₚ p f.1).2 f.2

private theorem awayLift_injective_of_kernel_killed (f : p.primeCompl)
    (H : ∀ a, algebraMap R Rₚ a = 0 → ∃ n, f.1 ^ n * a = 0) :
    Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  letI : IsLocalization.Away (algebraMap R Rₚ f.1) Rₚ :=
    IsLocalization.away_of_isUnit_of_bijective Rₚ (awayElement_isUnit_atPrime p f)
      Function.bijective_id
  simpa [Localization.awayLift] using
    (show Function.Injective
        (IsLocalization.Away.map (Localization.Away f.1) Rₚ (algebraMap R Rₚ) f.1) by
      rw [IsLocalization.Away.map_injective_iff]
      exact H)

private theorem exists_injective_awayLift_atPrime_of_isNoetherianRing [IsNoetherianRing R] :
    ∃ f : p.primeCompl,
      Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  classical
  have hfg : (RingHom.ker (algebraMap R Rₚ)).FG :=
    Ideal.FG.of_isNoetherianRing (RingHom.ker (algebraMap R Rₚ))
  rcases hfg with ⟨t, ht⟩
  have hx0 : ∀ x : t, ∃ s : p.primeCompl, s.1 * x.1 = 0 := by
    intro x
    have hxker : x.1 ∈ RingHom.ker (algebraMap R Rₚ) := by
      rw [← ht]
      exact Ideal.subset_span x.2
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rₚ x.1).mp <| by
      simpa [RingHom.mem_ker] using hxker
    exact ⟨s, hs⟩
  choose m hm using hx0
  let f : p.primeCompl := ⟨∏ x : t, (m x).1, by
    classical
    show (∏ x ∈ (Finset.univ : Finset t), (m x).1) ∈ p.primeCompl
    refine Finset.induction ?_ ?_ Finset.univ
    · simp
    · intro x s hx hs
      simpa [hx] using p.primeCompl.mul_mem (m x).2 hs⟩
  refine ⟨f, awayLift_injective_of_kernel_killed p f ?_⟩
  intro a ha
  have haK : a ∈ Ideal.span (t : Set R) := by
    rw [ht]
    exact ha
  have hf_mul : ∀ x : t, f.1 * x.1 = 0 := by
    intro x
    have hprod : f.1 = (m x).1 * ∏ y ∈ ({x}ᶜ : Set t), (m y).1 := by
      simpa [f] using Fintype.prod_eq_mul_prod_compl x (fun y : t ↦ (m y).1)
    calc
      f.1 * x.1 = ((m x).1 * ∏ y ∈ ({x}ᶜ : Set t), (m y).1) * x.1 := by rw [hprod]
      _ = (∏ y ∈ ({x}ᶜ : Set t), (m y).1) * ((m x).1 * x.1) := by ring
      _ = 0 := by simp [hm x]
  have hspan : ∀ b ∈ Ideal.span (t : Set R), f.1 * b = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | zero => simp
    | mem x hx => exact hf_mul ⟨x, hx⟩
    | add x y _ _ hx hy => simp [mul_add, hx, hy]
    | smul c x _ hx =>
        simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ c * z) hx
  exact ⟨1, by simpa using hspan a haK⟩

private theorem exists_injective_awayLift_atPrime_of_isReduced_finiteMinimalPrimes [IsReduced R]
    (hfinite : (minimalPrimes R).Finite) :
    ∃ f : p.primeCompl,
      Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  classical
  let bad : Finset (Ideal R) := hfinite.toFinset.filter fun q ↦ ¬ q ≤ p
  let I : Ideal R := ∏ q ∈ bad, q
  have hI_not_le : ¬ I ≤ p := by
    intro hIp
    obtain ⟨q, hqbad, hqp⟩ :=
      (inferInstance : p.IsPrime).prod_le.mp (show (∏ q ∈ bad, q) ≤ p by simpa [I] using hIp)
    exact (Finset.mem_filter.mp hqbad).2 hqp
  obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp (show ¬ (I : Set R) ⊆ p by simpa using hI_not_le)
  let f' : p.primeCompl := ⟨f, hfp⟩
  refine ⟨f', awayLift_injective_of_kernel_killed p f' ?_⟩
  intro a ha
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rₚ a).mp ha
  have hfa : f * a ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro q hq
    haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
    by_cases hqp : q ≤ p
    · have hsq : (s : R) ∉ q := fun hsq ↦ s.2 (hqp hsq)
      have hsa : s * a ∈ q := by simp [hs]
      have haq : a ∈ q := (Ideal.IsPrime.mem_or_mem inferInstance hsa).resolve_left hsq
      exact q.mul_mem_left f haq
    · have hqbad : q ∈ bad := Finset.mem_filter.mpr ⟨by simpa using hq, hqp⟩
      have hfq : f ∈ q := (Ideal.prod_le_inf.trans (Finset.inf_le hqbad)) hfI
      exact q.mul_mem_right a hfq
  have hsInf : sInf (minimalPrimes R) = (⊥ : Ideal R) := by
    have hsInf' : sInf ((⊥ : Ideal R).minimalPrimes) = (⊥ : Ideal R).radical :=
      Ideal.sInf_minimalPrimes
    have hrad : (⊥ : Ideal R).radical = (⊥ : Ideal R) := by
      simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R
    simpa [minimalPrimes] using hsInf'.trans hrad
  refine ⟨1, ?_⟩
  rw [pow_one, ← Ideal.mem_bot, ← hsInf]
  exact hfa

/-- Lemma 10.31.9: if `R` is Noetherian, or reduced with finitely many minimal primes, then there
exists `f ∉ p` such that the canonical map `R_f → R_𝔭` is injective. In mathlib, this map is the
canonical lift `Localization.awayLift` of `R → Localization.AtPrime p`, using that every `f ∉ p`
becomes a unit in `R_𝔭`. The domain case from the source is redundant here, since a domain is
reduced and has the unique minimal prime `(0)`. -/
-- Proof sketch: in the Noetherian case, kill the finitely generated kernel of `R → R_𝔭` after
-- localizing away from a suitable `f ∉ p`; the owner existence theorem for this step is
-- `Localization.exists_awayMap_injective_of_localRingHom_injective`. In the reduced case with
-- finitely many minimal primes, choose `f` in the product of the minimal primes not contained in
-- `p` but outside `p`; then any element of the kernel of `R → R_𝔭` is annihilated by `f`, since
-- it already vanishes at the minimal primes contained in `p` and `f` vanishes at the others.
@[stacks 0BX1]
theorem exists_injective_awayMap_atPrime_of_noetherian_or_reduced_finiteMinimalPrimes
    (h : IsNoetherianRing R ∨ (IsReduced R ∧ (minimalPrimes R).Finite)) :
    ∃ f : p.primeCompl,
      Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  rcases h with hnoeth | ⟨hred, hfinite⟩
  · letI := hnoeth
    exact exists_injective_awayLift_atPrime_of_isNoetherianRing p
  · classical
    letI := hred
    exact exists_injective_awayLift_atPrime_of_isReduced_finiteMinimalPrimes p hfinite

end
