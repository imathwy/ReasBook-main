import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

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
