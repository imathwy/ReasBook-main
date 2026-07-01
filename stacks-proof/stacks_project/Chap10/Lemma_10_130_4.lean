import Mathlib
import stacks_project.Chap10.Definition_10_104_1
import stacks_project.Chap10.Definition_10_125_1
import stacks_project.Chap10.Lemma_10_130_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace PrimeSpectrum

/- 
Domain-style sampling:
- primary domain: source-facing loci on `Spec(S)` cut out by properties of the fiber local ring
  and the relative fiber dimension;
- sampled owner declarations of the same kind:
  `fiberLocalRingAt`,
  `Module.CohenMacaulay`,
  `PrimeSpectrum.cohenMacaulayLocus`,
  `PrimeSpectrum.normalLocus`,
  `PrimeSpectrum.dimensionStratum`,
  `relativeDimensionAtLELocus`;
- best owner abstraction: the Cohen-Macaulay fiber condition should be owned by a named locus on
  `PrimeSpectrum S`, with pointwise membership owned by the canonical local self-module predicate
  `Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)`; the
  relative-dimension-`d` refinement in Lemma `10.130.4` remains a theorem-level condition built
  from that owner and `relativeDimensionAt`;
- primitive data: the prime `q : PrimeSpectrum S` together with the core owners
  `fiberLocalRingAt R S q` and `relativeDimensionAt R S q`;
- derived API: the named Cohen-Macaulay fiber locus and the bridge identifying it with the
  Cohen-Macaulay locus of the fiber ring at `fiberPrimeAt R S q`.

Source/core/bridge triage:
- `source-facing`: `PrimeSpectrum.cohenMacaulayFiberLocus R S`;
- `core/canonical`: `fiberLocalRingAt R S q` and
  `Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)`;
- `bridge/view`: the comparison with `PrimeSpectrum.cohenMacaulayLocus` on the fiber ring and the
  theorem-level intersection with the exact relative-dimension condition in Lemma `10.130.4`.
-/

/-- The locus in `Spec(S)` where the fiber local ring of `S/R` is Cohen-Macaulay. -/
def cohenMacaulayFiberLocus (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] :
    Set (PrimeSpectrum S) :=
  { q | Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) }

/-- Membership in `PrimeSpectrum.cohenMacaulayFiberLocus R S` means that the corresponding fiber
local ring is Cohen-Macaulay. -/
@[simp] theorem mem_cohenMacaulayFiberLocus (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) :
    q ∈ cohenMacaulayFiberLocus R S ↔
      Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) :=
  Iff.rfl

/-- The source-facing fiber-local-ring formulation is equivalent to the fiber-ring
Cohen-Macaulay-locus formulation at the canonical fiber prime. -/
theorem mem_cohenMacaulayFiberLocus_iff_mem_cohenMacaulayLocus
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (q : PrimeSpectrum S) :
    q ∈ cohenMacaulayFiberLocus R S ↔
      fiberPrimeAt R S q ∈ PrimeSpectrum.cohenMacaulayLocus ((q.asIdeal.under R).Fiber S) := by
  rw [mem_cohenMacaulayFiberLocus]
  rw [PrimeSpectrum.mem_cohenMacaulayLocus ((q.asIdeal.under R).Fiber S) (fiberPrimeAt R S q)]
  rfl

end PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S] [Module.Flat R S]

-- Proof sketch: for a prime `q` in the locus, use Lemma `10.125.2` after shrinking around `q`
-- to obtain a quasi-finite map `R[t₁, …, t_d] → S_g` with `d = relativeDimensionAt R S q`.
-- Lemma `10.130.1` identifies the Cohen-Macaulay plus relative-dimension-`d` condition with
-- flatness over that polynomial ring, Lemma `10.128.8` upgrades the fiberwise flatness to
-- flatness of the local map, and Theorem `10.129.4` then shows the corresponding flatness locus
-- is open. Shrinking once more, every nearby prime satisfies the same fiberwise criterion.
/-- Lemma 10.130.4: if `R → S` is flat and of finite presentation, then for each `d : ℕ` the
subset of primes `q : Spec(S)` such that the local fiber ring at `q` is Cohen-Macaulay and the
relative dimension of `S/R` at `q` is `d` is open in `Spec(S)`. -/
theorem isOpen_cohenMacaulayFiber_and_relativeDimensionAt_eq_of_finitePresentation_flat
    (d : ℕ) :
    IsOpen
      ((PrimeSpectrum.cohenMacaulayFiberLocus R S) ∩
        { q : PrimeSpectrum S | relativeDimensionAt R S q = (d : WithBot ℕ∞) }) := sorry

end
