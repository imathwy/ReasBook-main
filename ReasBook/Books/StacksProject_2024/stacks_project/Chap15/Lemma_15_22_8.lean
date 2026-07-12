import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Proposition_10_63_6
import StacksProject_2024.Chap10.Lemma_10_157_2
import StacksProject_2024.Chap15.Definition_15_22_1
import StacksProject_2024.Chap15.Lemma_15_22_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: commutative algebra of finite modules over Noetherian domains, with owner-level
  notions `Module.IsTorsionFree R M`, `associatedPrimes R M`,
  `Module.SerreConditionS R M 1`, and `embeddedAssociatedPrimes R M`;
- sampled owner declarations:
  `isTorsionFree_iff_exists_injective_to_fin_fun`,
  `Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
  `embeddedAssociatedPrimes_eq_empty_iff`,
  `Module.associatedPrimes_subset_support`,
  `minimal_support_iff_minimal_associatedPrimes`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`;
- best owner abstraction: `Module.SerreConditionS R M 1` for the `(S₁)` clause and
  `embeddedAssociatedPrimes R M` for the no-embedded-associated-primes clause;
- primitive data vs derived API: the owner predicates above are primitive/canonical, while the two
  deleted public pairwise equivalence theorems were bridge-level API that added no new owner data.

Source/core/bridge triage:
- `source-facing`: the five-way TFAE from Stacks, whose fourth and fifth clauses still need the
  extra generic-point-in-support conjunct from the source;
- `core/canonical`: `Module.IsTorsionFree`, `associatedPrimes`, `Module.SerreConditionS`,
  `embeddedAssociatedPrimes`;
- `bridge/view`: the source-facing conjunctions pairing the generic-point support clause with the
  canonical owner predicates.
-/

section

open Module

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: combine Lemma `15.22.7` for the equivalence of torsion-freeness with embeddability
-- into a finite free module, Lemma `10.157.2` for `(S_1)` versus absence of embedded associated
-- primes, and the standard implications relating associated primes and support over a domain.
variable [Nontrivial M]

/-- Lemma 15.22.8: for a nonzero finite module over a Noetherian domain, the following are
equivalent: `M` is torsion free, `M` embeds into a finite free module, `(0)` is the only
associated prime of `M`, `(0)` lies in the support of `M` and `M` satisfies Serre's condition
`(S_1)`, and `(0)` lies in the support of `M` and `M` has no embedded associated prime. -/
theorem torsionFree_tfae_associatedPrimes_support_serreS1 :
    List.TFAE
      [ IsTorsionFree R M,
        ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f,
        associatedPrimes R M = {⊥},
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1,
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ ] := by
  have htors :
      IsTorsionFree R M ↔ associatedPrimes R M = {⊥} := by
    constructor
    · intro htors
      letI := htors
      have hprime_eq_bot : ∀ ⦃p : Ideal R⦄, p ∈ associatedPrimes R M → p = ⊥ := by
        intro p hp
        by_contra hpbot
        exact not_mem_associatedPrimes_of_ne_bot hpbot hp
      have hbot_assoc : (⊥ : Ideal R) ∈ associatedPrimes R M := by
        obtain ⟨p, hp⟩ := associatedPrimes.nonempty R M
        simpa [hprime_eq_bot hp] using hp
      ext p
      constructor
      · intro hp
        simpa [hprime_eq_bot hp]
      · intro hp
        simpa [Set.mem_singleton_iff.mp hp] using hbot_assoc
    · intro hassoc
      rw [Submodule.isTorsionFree_iff_torsion_eq_bot]
      refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
      by_contra hx0
      rw [Submodule.mem_torsion_iff] at hx
      rcases hx with ⟨⟨r, hr0⟩, hrx⟩
      have hr0' : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr0
      have hr_mem : r ∈ ⋃ p ∈ associatedPrimes R M, p := by
        rw [biUnion_associatedPrimes_eq_zero_divisors R M]
        exact ⟨x, hx0, hrx⟩
      rw [Set.mem_iUnion] at hr_mem
      obtain ⟨p, hp_mem⟩ := hr_mem
      rw [Set.mem_iUnion] at hp_mem
      obtain ⟨hp, hrp⟩ := hp_mem
      have hpbot : p = ⊥ := by
        simpa [hassoc] using hp
      exact hr0' (by simpa [hpbot] using hrp)
  have hassoc :
      associatedPrimes R M = {⊥} ↔
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ := by
    constructor
    · intro hassoc
      refine ⟨?_, ?_⟩
      · exact associatedPrimes_subset_support <| by
          simpa [hassoc]
      · exact (embeddedAssociatedPrimes_eq_empty_iff R M).2 <|
          fun p hp ↦ by
            refine ⟨hp, ?_⟩
            intro q hq hqp
            have hpbot : p = ⊥ := by
              simpa [hassoc] using hp
            have hqbot : q = ⊥ := by
              simpa [hassoc] using hq
            simpa [hpbot, hqbot]
    · rintro ⟨hbot_support, hembedded⟩
      have hminimal_assoc := (embeddedAssociatedPrimes_eq_empty_iff R M).mp hembedded
      have hbot_assoc : Minimal (· ∈ associatedPrimes R M) (⊥ : Ideal R) := by
        have hminimal_support_bot : Minimal (· ∈ support R M) (⊥ : PrimeSpectrum R) := by
          refine ⟨hbot_support, ?_⟩
          intro q hq hqbot
          exact bot_le
        exact (minimal_support_iff_minimal_associatedPrimes (⊥ : PrimeSpectrum R)).1
          hminimal_support_bot
      ext p
      constructor
      · intro hp
        have hp_min := hminimal_assoc p hp
        have hpbot : p = ⊥ := by
          exact le_antisymm (hp_min.2 hbot_assoc.1 bot_le) bot_le
        simpa [hpbot]
      · intro hp
        simpa [Set.mem_singleton_iff.mp hp] using hbot_assoc.1
  have hserre :
      (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1 ↔
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ := by
    constructor
    · rintro ⟨hsupport, hserre⟩
      exact ⟨hsupport, embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one.2 hserre⟩
    · rintro ⟨hsupport, hembedded⟩
      exact ⟨hsupport, embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one.1 hembedded⟩
  refine List.tfae_of_forall (IsTorsionFree R M) _ ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  rcases ha with rfl | ha
  · exact (isTorsionFree_iff_exists_injective_to_fin_fun).symm
  rcases ha with rfl | ha
  · exact htors.symm
  rcases ha with rfl | ha
  · calc
      (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1 ↔
          (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ :=
        hserre
      _ ↔ associatedPrimes R M = {⊥} :=
        hassoc.symm
      _ ↔ IsTorsionFree R M :=
        htors.symm
  rcases ha with rfl | ha
  · calc
      (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ ↔
          associatedPrimes R M = {⊥} :=
        hassoc.symm
      _ ↔ IsTorsionFree R M :=
        htors.symm
  · simpa using ha

end
