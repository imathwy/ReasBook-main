import Mathlib
import stacks_project.Chap10.Lemma_10_125_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- 
Domain-style sampling:
- primary domain: base change of source-facing loci on `PrimeSpectrum` defined by a local fiber
  invariant attached to a ring map;
- sampled owner declarations of the same kind:
  `relativeDimensionAtLELocus`,
  `smoothLocus_baseChange_preimage_eq`,
  `cohenMacaulayFiberLocus_baseChange_preimage_eq`;
- best owner abstraction: the upstream named locus owner `relativeDimensionAtLELocus`, with the
  base-change theorem stated as equality for that owner rather than as a raw set-builder identity;
- primitive data: the algebra `R → S`, the base change `R → R'`, and the bound `n`;
- derived API: the preimage formula for the named locus.

Source/core/bridge triage:
* `source-facing`: the locus where the relative dimension of `S/R` is at most `n`;
* `core/canonical`: `relativeDimensionAt` and the upstream owner `relativeDimensionAtLELocus`;
* `bridge/view`: inverse image along `Spec(R' ⊗[R] S) → Spec(S)` induced by `includeRight`.
-/

variable [Algebra.FiniteType R S]

-- Proof sketch: for `q' : Spec(R' ⊗[R] S)`, let `q` be its image in `Spec(S)`. The fiber of
-- `Spec(S') → Spec(R')` at `q' ∩ R'` is canonically the same finite type algebra over the same
-- residue field as the fiber of `Spec(S) → Spec(R)` at `q ∩ R`; equivalently, the corresponding
-- local fiber rings have equal Krull dimension. Apply Lemma `10.116.6` to this residue-field base
-- change of fibers and then extensionality of inverse images.
/-- Lemma 10.125.7: for a finite type ring map `R → S`, an arbitrary base change `R → R'`, and
`S' = R' ⊗[R] S`, the inverse image in `Spec(S')` of the locus where the relative dimension
`dim_q(S/R)` is at most `n` is exactly the locus where the relative dimension
`dim_q(S'/R')` is at most `n`. -/
theorem relativeDimensionAt_le_preimage_eq_baseChange (n : ℕ) :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        relativeDimensionAtLELocus R S n =
      relativeDimensionAtLELocus R' (R' ⊗[R] S) n := sorry

end
