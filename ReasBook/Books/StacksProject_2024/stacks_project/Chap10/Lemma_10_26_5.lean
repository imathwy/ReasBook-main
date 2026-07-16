import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap05.Lemma_5_23_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set PrimeSpectrum TopologicalSpace

section

variable {R : Type u} [CommRing R]

private theorem isClosed_of_isCompact_open_of_basicOpen_closed
    (hbasic : ∀ f : R, IsClosed ((basicOpen f : Set (PrimeSpectrum R)))) :
    ∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U := by
  intro U hU hUcompact
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hUcompact, hU⟩
  have hUeq : U = ⋃ f ∈ t, (basicOpen f : Set (PrimeSpectrum R)) := by
    rw [← ht]
    ext x
    simp [basicOpen_eq_zeroLocus_compl, mem_zeroLocus, Set.not_subset]
  rw [hUeq]
  exact isClosed_biUnion_finset fun f _ ↦ hbasic f

/-- In `Spec R`, being the generic point of its irreducible component is equivalent to `p`
corresponding to a minimal prime ideal of `R`; this is the source-facing companion to the
canonical irreducible-component/minimal-prime correspondence on `Spec R`. -/
theorem isGenericPoint_irreducibleComponent_iff_mem_minimalPrimes (p : PrimeSpectrum R) :
    IsGenericPoint p (irreducibleComponent p) ↔ p.asIdeal ∈ minimalPrimes R := by
  rw [isGenericPoint_def]
  constructor
  · intro hp
    have hcomponent :
        closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) :=
      hp ▸ irreducibleComponent_mem_irreducibleComponents p
    rw [← vanishingIdeal_singleton]
    exact vanishingIdeal_mem_minimalPrimes.mpr hcomponent
  · intro hp
    have hcomponent :
        closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) := by
      rw [← vanishingIdeal_singleton] at hp
      exact vanishingIdeal_mem_minimalPrimes.mp hp
    have hsubset :
        closure ({p} : Set (PrimeSpectrum R)) ⊆ irreducibleComponent p := by
      exact closure_minimal (singleton_subset_iff.mpr mem_irreducibleComponent)
        isClosed_irreducibleComponent
    exact Set.Subset.antisymm hsubset <|
      hcomponent.2 isIrreducible_irreducibleComponent hsubset

/-- Lemma 10.26.5: for a commutative ring `R`, the following equivalent conditions on `Spec R`
use the canonical topological predicates from Chapter 5, together with the spectrum-specific basic
open criterion. The textbook ring-theoretic clauses are recovered from these by
`PrimeSpectrum.le_iff_specializes`, `PrimeSpectrum.isClosed_singleton_iff_isMaximal`, and
`isGenericPoint_irreducibleComponent_iff_mem_minimalPrimes`. -/
-- Proof sketch: specialize `spectralSpace_profinite_criteria` to `PrimeSpectrum R`, using Lemma
-- `10.26.2` for spectrality. The only additional clause is closedness of basic opens, which is
-- equivalent to closedness of all quasi-compact opens by quasi-compactness of `D(f)` and Lemma
-- `10.26.4`.
theorem primeSpectrum_profinite_tfae :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (PrimeSpectrum R ≃ₜ P),
        T2Space (PrimeSpectrum R),
        TotallyDisconnectedSpace (PrimeSpectrum R),
        ∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U,
        ∀ ⦃p q : PrimeSpectrum R⦄, p ⤳ q → p = q,
        ∀ p : PrimeSpectrum R, IsClosed ({p} : Set (PrimeSpectrum R)),
        ∀ p : PrimeSpectrum R, IsGenericPoint p (irreducibleComponent p),
        ∀ f : R, IsClosed ((basicOpen f : Set (PrimeSpectrum R))) ] := by
  classical
  let howner := spectralSpace_profinite_criteria (PrimeSpectrum R)
  tfae_have 1 → 2 := by
    intro h
    exact (howner.out 0 1).mp h
  tfae_have 2 → 3 := by
    intro h
    exact (howner.out 1 2).mp h
  tfae_have 3 → 4 := by
    intro h
    exact (howner.out 2 3).mp h
  tfae_have 4 → 5 := by
    intro h
    exact (howner.out 3 4).mp h
  tfae_have 5 → 6 := by
    intro h
    exact (howner.out 4 5).mp h
  tfae_have 6 → 7 := by
    intro h
    exact (howner.out 5 6).mp h
  tfae_have 7 → 8 := by
    intro h p
    have hclosed :
        ∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U :=
      (howner.out 6 3).mp h
    exact hclosed _ isOpen_basicOpen (isCompact_basicOpen p)
  tfae_have 8 → 1 := by
    intro h
    exact (howner.out 3 0).mp (isClosed_of_isCompact_open_of_basicOpen_closed h)
  tfae_finish

end
