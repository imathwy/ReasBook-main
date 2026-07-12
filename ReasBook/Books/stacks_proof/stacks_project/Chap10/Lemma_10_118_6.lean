import Mathlib
import StacksProject_2024.Chap10.Lemma_10_118_5

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/-- Helper for Lemma 10.118.6: the good locus is open because it is a union of basic opens. -/
lemma isOpen_goodLocus_aux :
    IsOpen (goodLocus R S M) := by
  -- Expand the defining union and use that every basic open in `Spec(R)` is open.
  rw [goodLocus_eq_iUnion]
  exact isOpen_iUnion fun g => PrimeSpectrum.isOpen_basicOpen

-- Proof sketch: by Lemma `10.118.5`, for each `i` the localized good locus on `Spec(R_{f i})`
-- identifies with the restriction of `goodLocus R S M` to `D(f i)`. Thus the hypothesis is that
-- the complement of `goodLocus R S M` is nowhere dense on every member of a dense standard-open
-- cover. Apply Topology, Lemma `5.21.4` to that complement and use density of the union of the
-- cover members.
/-- Lemma 10.118.6: if a dense union of basic opens `⋃ i, D(fᵢ)` has the property that the
restriction of `U(R → S, M)` to each `D(fᵢ)` is dense, then `U(R → S, M)` is dense in
`Spec(R)`. -/
@[stacks 051Y]
theorem dense_goodLocus_of_dense_standardOpen_cover
    {ι : Type x} (f : ι → R)
    (hcover : Dense (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum R))))
    (hdense :
      ∀ i, Dense (((↑) : PrimeSpectrum.basicOpen (f i) → PrimeSpectrum R) ⁻¹' goodLocus R S M)) :
    Dense (goodLocus R S M) := by
  let V : Set (PrimeSpectrum R) := ⋃ i, (basicOpen (f i) : Set (PrimeSpectrum R))
  have hDenseOnV : Dense (((↑) : V → PrimeSpectrum R) ⁻¹' goodLocus R S M) := by
    rw [dense_iff_inter_open]
    intro W hWopen hWnonempty
    rcases hWnonempty with ⟨x, hxW⟩
    rcases Set.mem_iUnion.mp x.2 with ⟨i, hxi⟩
    let includeToV : PrimeSpectrum.basicOpen (f i) → Subtype V :=
      fun y ↦ ⟨y.1, Set.mem_iUnion.mpr ⟨i, y.2⟩⟩
    have hIncludeToV : Continuous includeToV := by
      -- The chosen basic open sits inside the ambient union `V`, so its inclusion is continuous.
      exact Continuous.subtype_mk
        (p := V)
        (f := fun y : PrimeSpectrum.basicOpen (f i) ↦ (y : PrimeSpectrum R))
        continuous_subtype_val
        (fun y ↦ Set.mem_iUnion.mpr ⟨i, y.2⟩)
    let Wi : Set (PrimeSpectrum.basicOpen (f i)) := includeToV ⁻¹' W
    have hWi_open : IsOpen Wi := hWopen.preimage hIncludeToV
    have hxWi : (⟨x.1, hxi⟩ : PrimeSpectrum.basicOpen (f i)) ∈ Wi := by
      simpa [Wi, includeToV] using hxW
    have hWi_nonempty : Wi.Nonempty := ⟨⟨x.1, hxi⟩, hxWi⟩
    rcases (hdense i).inter_open_nonempty Wi hWi_open hWi_nonempty with ⟨y, hyW, hyGood⟩
    refine ⟨includeToV y, ?_⟩
    constructor
    · simpa [Wi, includeToV] using hyW
    · simpa [includeToV] using hyGood
  have hV_subset_closure :
      V ⊆ closure (goodLocus R S M) := by
    rw [Subtype.dense_iff] at hDenseOnV
    intro x hxV
    have hxImage :
        x ∈ closure
          (((↑) : V → PrimeSpectrum R) '' (((↑) : V → PrimeSpectrum R) ⁻¹' goodLocus R S M)) :=
      hDenseOnV hxV
    -- The image of the restricted good locus in the subtype is contained in the ambient good locus.
    exact closure_mono
      (fun y hy ↦ by
        rcases hy with ⟨z, hz, rfl⟩
        exact hz)
      hxImage
  -- Density on the dense open union `V` forces density in the whole spectrum.
  intro x
  simpa [closure_closure] using closure_mono hV_subset_closure (hcover x)

end GenericFlatness

end
