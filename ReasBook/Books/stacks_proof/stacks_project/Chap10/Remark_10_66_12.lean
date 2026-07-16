import stacks_proof.stacks_project.Chap10.Lemma_10_63_11
import stacks_proof.stacks_project.Chap10.Lemma_10_66_6
import stacks_proof.stacks_project.Chap10.Lemma_10_66_11
import stacks_proof.stacks_project.Chap10.Lemma_10_66_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Remark 10.66.12: under the map `Spec S → Spec R`, the image of `Ass_S(M)` is contained in
`Ass_R(M)`, which is contained in `WeakAss_R(M)`, which is contained in the image of
`WeakAss_S(M)`. -/
-- Proof sketch: combine the restriction-of-scalars inclusion for textbook associated primes, the
-- inclusion `Ass_R(M) ⊆ WeakAss_R(M)`, and the restriction-of-scalars inclusion for weakly
-- associated primes.
@[stacks 05C7]
theorem restrictScalars_associatedPrimes_weaklyAssociatedPrimes_chain :
    List.IsChain (· ⊆ ·)
      [ Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M,
        associatedPrimesOfModule R M,
        weaklyAssociatedPrimes R M,
        Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M ] := by
  refine List.IsChain.cons_cons ?_ ?_
  · simpa using associatedPrimesOfModule_image_comap_subset
  · refine List.IsChain.cons_cons ?_ ?_
    · simpa using associatedPrimesOfModule.subset_weaklyAssociatedPrimes
    · simpa [List.isChain_pair] using weaklyAssociatedPrimes.subset_comap_image

/-- If `S` is Noetherian, then all inclusions in the restriction-of-scalars chain for associated
and weakly associated primes are equalities. -/
-- Proof sketch: if `S` is Noetherian, then `associatedPrimesOfModule S M = weaklyAssociatedPrimes
-- S M`. The first theorem gives a chain of inclusions whose outer two terms are therefore equal,
-- forcing all adjacent inclusions to be equalities.
theorem restrictScalars_associatedPrimes_weaklyAssociatedPrimes_eq_chain_of_isNoetherianRing
    [IsNoetherianRing S] :
    List.IsChain (· = ·)
      [ Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M,
        associatedPrimesOfModule R M,
        weaklyAssociatedPrimes R M,
        Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M ] := by
  let A : Set (Ideal R) := Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M
  let B : Set (Ideal R) := associatedPrimesOfModule R M
  let C : Set (Ideal R) := weaklyAssociatedPrimes R M
  let D : Set (Ideal R) := Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M
  change List.IsChain (· = ·) [A, B, C, D]
  have hAB : A ⊆ B := by
    simpa [A, B] using associatedPrimesOfModule_image_comap_subset
  have hBC : B ⊆ C := by
    simpa [B, C] using associatedPrimesOfModule.subset_weaklyAssociatedPrimes
  have hCD : C ⊆ D := by
    simpa [C, D] using weaklyAssociatedPrimes.subset_comap_image
  have hAD : A = D := by
    simp [A, D, associatedPrimesOfModule_eq_associatedPrimes, associatedPrimes_eq_weaklyAssociatedPrimes]
  have hAB_eq : A = B := Set.Subset.antisymm hAB fun p hp ↦ hAD.symm ▸ hCD (hBC hp)
  have hBC_eq : B = C := Set.Subset.antisymm hBC fun p hp ↦ hAB_eq ▸ (hAD.symm ▸ hCD hp)
  have hCD_eq : C = D := Set.Subset.antisymm hCD fun p hp ↦ hBC (hAB_eq ▸ (hAD.symm ▸ hp))
  refine List.IsChain.cons_cons hAB_eq ?_
  refine List.IsChain.cons_cons hBC_eq ?_
  simpa [List.isChain_pair] using hCD_eq

end
