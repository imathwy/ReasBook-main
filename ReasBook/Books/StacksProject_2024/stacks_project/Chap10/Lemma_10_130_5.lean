import Mathlib
import StacksProject_2024.Chap10.Lemma_10_130_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S] [Module.Flat R S]

/- 
Domain-style sampling:
- primary domain: source-facing loci on `Spec(S)` cut out by the Cohen-Macaulay condition on the
  fiber local ring, together with the induced topology on each set-theoretic fiber of
  `PrimeSpectrum.comap (algebraMap R S)`;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.cohenMacaulayFiberLocus`,
  `PrimeSpectrum.mem_cohenMacaulayFiberLocus_iff_mem_cohenMacaulayLocus`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `dense_cohenMacaulayLocus_of_finiteType`;
- best owner abstraction: the source-facing owner remains the named locus
  `PrimeSpectrum.cohenMacaulayFiberLocus R S`; the set-theoretic fiber should use the canonical
  subtype `PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}` rather than a one-off local alias;
- primitive data: the finitely presented flat map `R → S`, the locus owner
  `PrimeSpectrum.cohenMacaulayFiberLocus R S`, and a base prime `p : PrimeSpectrum R`;
- derived API: the separate openness theorem and the fiberwise density theorem, both extracted from
  the source-facing conjunction.

Source/core/bridge triage:
- `source-facing`: openness of `PrimeSpectrum.cohenMacaulayFiberLocus R S` together with density on
  each fiber of `Spec(S) → Spec(R)`;
- `core/canonical`: `PrimeSpectrum.cohenMacaulayFiberLocus R S` and the canonical subtype fiber
  `PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}`;
- `bridge/view`: `PrimeSpectrum.preimageHomeomorphFiber R S p`, relating the set-theoretic fiber to
  `Spec (κ(p) ⊗[R] S)`.
-/

-- Proof sketch: apply Lemma `10.130.4` to see that the Cohen--Macaulay fiber locus is open in
-- `Spec(S)`. For a fixed `p : Spec(R)`, identify the fiber over `p` with `Spec(κ(p) ⊗[R] S)`; the
-- induced subset is exactly the Cohen--Macaulay locus of that finite type algebra over the field
-- `κ(p)`, so Lemma `10.130.3` gives density in the fiber.
/-- Lemma 10.130.5: if `R → S` is flat and of finite presentation, then the set of primes
`q : Spec(S)` for which the local fiber ring
`S_q ⊗[R] κ(q ∩ R)`, formalized as `fiberLocalRingAt R S q`, is Cohen-Macaulay is open in
`Spec(S)` and its induced subset on every fiber of `Spec(S) → Spec(R)` is dense. -/
theorem isOpen_and_fiberwiseDense_cohenMacaulayFiberLocus_of_finitePresentation_flat :
    IsOpen (cohenMacaulayFiberLocus R S) ∧
      ∀ p : PrimeSpectrum R,
        Dense
          (((↑) : comap (algebraMap R S) ⁻¹' {p} → PrimeSpectrum S) ⁻¹'
            cohenMacaulayFiberLocus R S) := sorry

/-- The Cohen-Macaulay fiber locus of a flat finitely presented map is open. -/
theorem isOpen_cohenMacaulayFiberLocus_of_finitePresentation_flat :
    IsOpen (cohenMacaulayFiberLocus R S) :=
  isOpen_and_fiberwiseDense_cohenMacaulayFiberLocus_of_finitePresentation_flat.1

end

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- On the fiber over `p : Spec(R)`, if the fiber ring `κ(p) ⊗[R] S` is finite type over
`κ(p)`, then the induced Cohen-Macaulay fiber locus is dense. -/
theorem dense_preimage_cohenMacaulayFiberLocus_of_fiberFiniteType
    (p : PrimeSpectrum R) [Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S)] :
    Dense
      (((↑) : comap (algebraMap R S) ⁻¹' {p} → PrimeSpectrum S) ⁻¹'
        cohenMacaulayFiberLocus R S) := sorry

end
