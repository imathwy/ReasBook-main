import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.137.10: the source-facing Stacks condition that `R → S` is smooth at the prime
`q`, meaning that some basic open neighborhood `S_g` with `g ∉ q` is smooth over `R`. -/
@[stacks 00TB]
def SmoothAtPrime (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Smooth R (Localization.Away g)

-- Proof sketch: if `S_g` is smooth over `R` for some `g ∉ q`, then localizing further at the
-- prime corresponding to `q` gives `S_q`, so `S_q` is formally smooth over `R`. Conversely, for a
-- finitely presented `R`-algebra, mathlib's theorem `Algebra.IsSmoothAt.exists_notMem_smooth`
-- produces such a neighborhood from the formal smoothness of `S_q`.
/-- Chap10 Definition 10 137 10: for finitely presented algebras, the source-facing condition
`SmoothAtPrime R S q` is equivalent to the canonical owner predicate `IsSmoothAt R q.asIdeal`. -/
theorem smoothAtPrime_iff_isSmoothAt [FinitePresentation R S] (q : PrimeSpectrum S) :
    SmoothAtPrime R S q ↔ IsSmoothAt R q.asIdeal := by
  constructor
  · -- A smooth basic open neighborhood of `q` places `q` in the canonical smooth locus.
    rintro ⟨g, hgq, hgSmooth⟩
    have hsubset : ↑(PrimeSpectrum.basicOpen g) ⊆ smoothLocus R S := by
      rw [basicOpen_subset_smoothLocus_iff_smooth]
      exact hgSmooth
    have hqbasic : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgq
    have hqLocus : q ∈ smoothLocus R S := hsubset hqbasic
    simpa [smoothLocus] using hqLocus
  · -- The canonical local predicate gives a smooth basic open witness avoiding `q.asIdeal`.
    intro hq
    letI : IsSmoothAt R q.asIdeal := hq
    exact IsSmoothAt.exists_notMem_smooth R q.asIdeal

end Algebra
