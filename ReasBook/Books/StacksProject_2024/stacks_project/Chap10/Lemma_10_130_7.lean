import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_130_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R'] [Algebra.FiniteType R S]

/- 
Domain-style sampling:
- primary domain: base change on `PrimeSpectrum` for loci cut out by a fiber-local ring property;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.cohenMacaulayFiberLocus`,
  `fiberLocalRingAt`,
  `Module.CohenMacaulay`,
  `relativeDimensionAt_le_preimage_eq_baseChange`,
  `smoothLocus_baseChange_preimage_eq`;
- best owner abstraction: the upstream named locus owner
  `PrimeSpectrum.cohenMacaulayFiberLocus R S`, whose membership is defined through the canonical
  fiber-local-ring owner `fiberLocalRingAt R S q` and the local self-module predicate
  `Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)`;
- primitive data: the finite type map `R → S`, the arbitrary base change `R → R'`, and the
  induced map `Spec(R' ⊗[R] S) → Spec(S)`;
- derived API: the base-change equality for the inverse image of that locus owner.

Source/core/bridge triage:
* `source-facing`: the Cohen-Macaulay fiber locus of `Spec(S)`;
* `core/canonical`: `fiberLocalRingAt` and `Module.CohenMacaulay` on the fiber local self-module;
* `bridge/view`: inverse image along `PrimeSpectrum.comap includeRight.toRingHom`.
-/

-- Proof sketch: for `q' : Spec(R' ⊗[R] S)`, let `q` be its image in `Spec(S)`. The local fiber
-- ring of `S'/R'` at `q'` is the base change of the local fiber ring of `S/R` at `q` along the
-- residue-field extension `κ(q ∩ R) → κ(q' ∩ R')`. Apply Lemma `10.130.6` to that field extension
-- and then unwind the definitions of the two loci.
/-- Lemma 10.130.7: for a finite type ring map `R → S`, an arbitrary base change `R → R'`, and
`S' = R' ⊗[R] S`, the locus of primes of `S'` where the local fiber ring of `S'/R'` is
Cohen-Macaulay is exactly the inverse image of the corresponding locus of `S/R` under
`Spec(S') → Spec(S)`. -/
theorem cohenMacaulayFiberLocus_baseChange_preimage_eq :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        PrimeSpectrum.cohenMacaulayFiberLocus R S =
      PrimeSpectrum.cohenMacaulayFiberLocus R' (R' ⊗[R] S) := sorry

end
