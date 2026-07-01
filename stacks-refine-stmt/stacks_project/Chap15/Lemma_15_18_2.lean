import stacks_project.Chap15.Lemma_15_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable {I : Ideal R} {I' : Ideal R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- Domain-style sampling for Lemma 15.18.2:
- primary domain: flatness loci of modules on closed subsets of `Spec` under tensor-product base
  change and descent in commutative algebra;
- sampled owner declarations:
  `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange`,
  `zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends`;
- best owner abstraction: the canonical owner is `Module.flatOverBaseLocus`, while the chapter
  owner-level descent bridge is
  `zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends`;
- primitive data: the ideal comparison `IR' ≤ I'`, surjectivity of `V(I') → V(I)`, the local
  flatness locus condition on `Spec R'`, and the tensor-base-changed flatness-locus inclusion on
  `Spec (S ⊗[R] R')`;
- derived API: this file's source-facing specialization theorem, obtained by instantiating the
  later descent bridge with `R' := R`, `S' := S`, `R'' := R'`, and
  `M'' := (S ⊗[R] R') ⊗[S] M`.

Source/core/bridge triage:
- `source-facing`: the Stacks tensor-base-change descent statement for `(R → S, R → R', I, I')`;
- `core/canonical`: `Module.flatOverBaseLocus`;
- `bridge/view`: the later chapter theorem
  `zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends`, which this file specializes
  to the tensor-product base-change interface. -/

/-- Lemma 15.18.2: if the canonical closed-subset inclusion
`V(I'(S ⊗[R] R')) ⊆ Module.flatOverBaseLocus R' (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M)` holds after the
tensor-product base change `R → R'`, then the corresponding inclusion
`V(IS) ⊆ Module.flatOverBaseLocus R S M` already holds over `R`, provided `IR' ≤ I'`, the induced
map `V(I') → V(I)` is surjective, and `I'` has flat-over-`R` zero locus on `Spec R'`. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_tensorBaseChange_descends
    (hI' : Ideal.map (algebraMap R R') I ≤ I')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R R'))
      (zeroLocus (I' : Set R')) (zeroLocus (I : Set R)))
    (hlocFlat : zeroLocus (I' : Set R') ⊆ Module.flatOverBaseLocus R R' R')
    (hbase :
      zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') ⊆
        Module.flatOverBaseLocus R' S' M') :
    zeroLocus (Ideal.map (algebraMap R S) I : Set S) ⊆ Module.flatOverBaseLocus R S M :=
  zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends hI' hsurj hlocFlat hbase

end
