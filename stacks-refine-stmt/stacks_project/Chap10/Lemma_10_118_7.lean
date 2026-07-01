import stacks_project.Chap10.Lemma_10_118_3
import stacks_project.Chap10.Lemma_10_118_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/- Domain triage:
* primary domain: the generic-flatness good locus on `Spec(R)`;
* source-facing owner: `goodLocus R S M` from `10_118_3_2`;
* core/canonical topological owners: `IsOpen` and `Dense` for subsets of `Spec(R)`;
* bridge/view target of this file: openness comes directly from the owner description
  `goodLocus_eq_iUnion`, while density under `[IsReduced R]` is the source-facing consequence
  obtained by combining the domain case `Lemma_10_118_3` with the dense-standard-open bridge
  `dense_goodLocus_of_dense_standardOpen_cover` from `Lemma_10_118_6`. -/

/-- The generic-flatness good locus `U(R → S, M)` is open in `Spec(R)`. -/
-- Proof sketch: `goodLocus R S M` is defined as a union of basic opens `D(f)`, and each basic
-- open is open in `Spec(R)`.
theorem isOpen_goodLocus :
    IsOpen (goodLocus R S M) := sorry

/-- Lemma 10.118.7: if `R → S` is of finite type, `M` is a finite `S`-module, and `R` is
reduced, then the generic-flatness good locus `U(R → S, M)` is dense in `Spec(R)`. This is the
canonical reformulation of the textbook statement asserting the existence of an open dense subset
on which, Zariski-locally, `S_f` is a finitely presented free `R_f`-algebra and `M_f` is a
finitely presented free `S_f`-module over `R_f`. -/
-- Proof sketch: this is the density statement proved in the text for the good locus
-- `U(R → S, M)`, first for polynomial algebras by induction and Noether normalization and then in
-- general by passing to a polynomial presentation of `S`.
theorem dense_goodLocus_of_finiteType_finiteModule_reduced
    [Algebra.FiniteType R S] [Module.Finite S M] [IsReduced R] :
    Dense (goodLocus R S M) := sorry

end GenericFlatness

end
