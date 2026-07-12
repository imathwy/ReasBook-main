import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 00LL]
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
