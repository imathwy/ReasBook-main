import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import stacks_project.Chap05.Lemma_5_8_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for the affine irreducibility criterion:
* primary domain: irreducibility of prime spectra under an open spectral map, with fibers described
  by fiber rings `κ(p) ⊗[R] S`;
* sampled owner declarations:
  `IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`.

Layer triage:
* `source-facing`: the affine-spectrum form of the Stacks irreducibility criterion;
* `core/canonical`: the topological owner theorem
  `IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber`;
* `bridge/view`: `PrimeSpectrum.preimageHomeomorphFiber`, identifying the set-theoretic fiber of
  `PrimeSpectrum.comap (algebraMap R S)` over `p` with `PrimeSpectrum (p.asIdeal.Fiber S)`.

Primitive data is the open-map hypothesis on `Spec S → Spec R` together with dense irreducibility
of the fiber spectra `Spec(κ(p) ⊗[R] S)`. The irreducibility of `Spec S` is derived API obtained
by transporting the fiber condition across the canonical homeomorphism and applying the owner
theorem.
-/

-- Auxiliary generalization: this is the affine-spectrum specialization of
-- `IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber`. For each
-- `p : PrimeSpectrum R`, identify the set-theoretic fiber of `PrimeSpectrum.comap (algebraMap R S)`
-- over `p` with `PrimeSpectrum (p.asIdeal.Fiber S)` via `PrimeSpectrum.preimageHomeomorphFiber`.
theorem irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hopen : IsOpenMap (comap (algebraMap R S)))
    (hdense : Dense { p : PrimeSpectrum R | IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber S)) }) :
    IrreducibleSpace (PrimeSpectrum S) := by
  refine IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber hopen hR ?_
  refine hdense.mono fun p hp ↦ ?_
  simpa [isIrreducible_iff_irreducibleSpace] using
    (preimageHomeomorphFiber R S p).irreducibleSpace_iff.mpr hp

-- Proof sketch: flat algebras satisfy going down, so
-- `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation` applies; then use the
-- open-map generalization above.
/-- Lemma 10.47.1: if `Spec R` is irreducible, `R → S` is flat and of finite presentation, and
the fiber spectra `Spec(κ(p) ⊗[R] S)` are irreducible for a dense set of primes `p` of `R`, then
`Spec S` is irreducible. -/
theorem irreducibleSpace_primeSpectrum_of_flat_finitePresentation_of_dense_irreducible_fibers
    (hR : IrreducibleSpace (PrimeSpectrum R))
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (hdense : Dense { p : PrimeSpectrum R | IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber S)) }) :
    IrreducibleSpace (PrimeSpectrum S) := by
  exact irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    hR isOpenMap_comap_of_hasGoingDown_of_finitePresentation hdense

end
