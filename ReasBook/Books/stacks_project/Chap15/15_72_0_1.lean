import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex.HomComplex.CohomologyClass

noncomputable section

universe u

section

variable {R : Type u} [Ring R]
variable (L M : CochainComplex (ModuleCat R) ℤ) (n : ℤ)

/- Domain-style sampling for 15.72.0.1:
- primary domain: cohomology of Hom complexes and morphisms in the homotopy category of cochain
  complexes of modules;
- sampled owner declarations:
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.toHom`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.toHom_mk`;
- best owner abstraction: the canonical owner layer is the cohomology-class API for the Hom
  complex, with the source statement expressed by the upstream composite
  `(CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv`;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(Hom^•(L^•, M^•)) ≃ Hom_{K(R)}(L^•, M^•[n])`;
  `core/canonical`: `CochainComplex.HomComplex.CohomologyClass` together with
  `homologyAddEquiv` and `homAddEquiv`;
  `bridge/view`: the composite equivalence giving the source statement directly.

This file targets the `bridge/view` layer. The complexes `L`, `M`, and the degree `n` are the
only primitive inputs; the intermediate cohomology-class quotient and both equivalences are already
canonical upstream. A local wrapper definition with the same interface would therefore be duplicate
derived API and should be deleted in favor of direct canonical recall/use.
-/

/- 15.72.0.1: the canonical equivalence from the degree-`n` homology of `Hom^•(L^•, M^•)` to
`Hom_{K(R)}(L^•, M^•[n])` is the direct upstream composite of the standard homology-to-cohomology-
class equivalence with the standard cohomology-class-to-homotopy-morphism equivalence. -/
#check (CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv

end
