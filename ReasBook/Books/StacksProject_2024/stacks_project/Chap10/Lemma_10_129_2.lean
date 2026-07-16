import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_10_5
import StacksProject_2024.stacks_project.Chap10.Definition_10_17_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_104_6
import StacksProject_2024.stacks_project.Chap10.Definition_10_125_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open PrimeSpectrum
open RingTheory Sequence
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-
Domain-style sampling:
* primary domain: regular-sequence loci on the canonical fiber local rings over `Spec R`;
* sampled owner declarations of the same kind:
  `fiberLocalRingAt`,
  `toFiberLocalRingAt`,
  `PrimeSpectrum.IsRegularInFiberLocalRing`,
  `PrimeSpectrum.zeroLocus`,
  `RingTheory.Sequence.IsRegular`;
* best owner abstraction: the source-facing locus should live directly on the closed subspace
  `V(Ideal.ofList fs)`, because containment of `Ideal.ofList fs` is primitive data in the source
  statement; the pointwise regular-sequence owner on a prime `q` should be the bridge
  `q.IsRegularInFiberLocalRing R fs`, whose canonical content is regularity of the image of `fs`
  in the owner fiber local ring `fiberLocalRingAt R S q`;
* primitive data: the list `fs`, the point `q : V(Ideal.ofList fs)`, and regularity of the image
  of `fs` in the owner fiber local ring at `q.1`;
* derived API: the named regular-sequence locus on `V(Ideal.ofList fs)` and the openness theorem
  below.

Source/core/bridge triage:
* `source-facing`: the regular-sequence locus inside `V(Ideal.ofList fs)` and its openness;
* `core/canonical`: `fiberLocalRingAt`, `toFiberLocalRingAt`, and `Sequence.IsRegular`;
* `bridge/view`: `PrimeSpectrum.IsRegularInFiberLocalRing`, the subtype-valued locus, and its
  point-membership lemma.
-/

/-- The locus in `V(Ideal.ofList fs)` where the images of `fs` form a regular sequence in the
local fiber ring. -/
def fiberLocalRingRegularSequenceLocus (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (fs : List S) :
    Set (V((Ideal.ofList fs : Set S))) :=
  { q | q.1.IsRegularInFiberLocalRing R fs }

/-- A point of `V(Ideal.ofList fs)` lies in `fiberLocalRingRegularSequenceLocus` exactly when the
images of `fs` form a regular sequence in the corresponding local fiber ring. -/
theorem mem_fiberLocalRingRegularSequenceLocus_iff
    (fs : List S) (q : V((Ideal.ofList fs : Set S))) :
    q ∈ fiberLocalRingRegularSequenceLocus R S fs ↔
      q.1.IsRegularInFiberLocalRing R fs := by
  rfl

variable [Algebra.FiniteType R S]

-- Proof sketch: for `q` in the locus, pass to the quotient `S ⧸ Ideal.ofList fs`. The fiber over
-- `q ∩ R` stays Cohen--Macaulay and equidimensional, and `hConstDim` identifies its Krull
-- dimension with that of every other fiber. Regularity of `fs` in the local fiber ring gives the
-- expected dimension drop by `fs.length` for the quotient fiber. Lemma `10.125.6` then yields an
-- open neighborhood on which all quotient fibers have relative dimension bounded by this common
-- fiber dimension minus `fs.length`, and Lemma `10.129.1` upgrades that bound to regularity of the
-- localized sequence at every nearby point. Hence the locus is open inside `V(fs)`.
/-- Lemma 10.129.2: let `R → S` be a finite type ring map, and let `fs` be a finite list of
elements of `S`. Assume every fiber `κ(𝔭) ⊗[R] S` is Cohen--Macaulay and equidimensional, and
that these fibers all have the same Krull dimension. Then the primes `q` of `S` containing
`Ideal.ofList fs` for which the images of `fs` form a regular sequence in the local fiber ring at
`q` form an open subset of `V(Ideal.ofList fs)`. -/
theorem isOpen_fiberLocalRingRegularSequenceLocusWithinZeroLocus_of_fiberwise_cohenMacaulay_equidimensional
    (fs : List S)
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S))
    (hEqdim : ∀ p : PrimeSpectrum R,
      TopologicalSpace.EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber S)))
    (hConstDim : ∀ p p' : PrimeSpectrum R,
      ringKrullDim (p.asIdeal.Fiber S) = ringKrullDim (p'.asIdeal.Fiber S)) :
    IsOpen (fiberLocalRingRegularSequenceLocus R S fs) := sorry

end
