import Mathlib
import stacks_project.Chap10.Lemma_10_118_5

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

-- Proof sketch: by Lemma `10.118.5`, for each `i` the localized good locus on `Spec(R_{f i})`
-- identifies with the restriction of `goodLocus R S M` to `D(f i)`. Thus the hypothesis is that
-- the complement of `goodLocus R S M` is nowhere dense on every member of a dense standard-open
-- cover. Apply Topology, Lemma `5.21.4` to that complement and use density of the union of the
-- cover members.
/-- Lemma 10.118.6: if a dense union of basic opens `⋃ i, D(fᵢ)` has the property that the
restriction of `U(R → S, M)` to each `D(fᵢ)` is dense, then `U(R → S, M)` is dense in
`Spec(R)`. -/
theorem dense_goodLocus_of_dense_standardOpen_cover
    {ι : Type x} (f : ι → R)
    (hcover : Dense (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum R))))
    (hdense :
      ∀ i, Dense (((↑) : PrimeSpectrum.basicOpen (f i) → PrimeSpectrum R) ⁻¹' goodLocus R S M)) :
    Dense (goodLocus R S M) := sorry

end GenericFlatness

end
