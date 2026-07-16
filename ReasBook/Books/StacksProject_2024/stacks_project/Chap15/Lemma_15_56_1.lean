import Mathlib
import StacksProject_2024.stacks_project.Chap12.Remark_12_29_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open ModuleCat

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: change of rings for module-valued cochain complexes and preservation of
  `CochainComplex.IsKInjective`.
- inspected owner declarations:
  `CochainComplex.IsKInjective`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`,
  `ModuleCat.extendRestrictScalarsAdj`,
  `extendScalars_exact_of_flat`.
- source/core/bridge triage:
  `source-facing`: the flat restriction-of-scalars specialization for K-injective cochain
    complexes;
  `core/canonical`: `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
  `bridge/view`: `extendRestrictScalarsAdj f` and `extendScalars_exact_of_flat f hf`.
- primitive data: the ring map `f` and its flatness.
- derived API: K-injectivity of the restricted complex.
- owner decision: this file should keep the flat specialization as a source-facing bridge, not
  introduce a second owner parallel to the Chapter 13 theorem.
-/

-- Proof sketch: `extendScalars f ⊣ restrictScalars f` is the canonical change-of-rings adjunction,
-- and flatness makes the left adjoint exact by `extendScalars_exact_of_flat`. The theorem is then
-- exactly the Chapter 13 owner theorem specialized to this adjunction.
/-- Lemma 15.56.1: for a flat ring map `f : R →+* S`, a K-injective cochain complex of
`S`-modules remains K-injective when regarded as a cochain complex of `R`-modules via restriction
of scalars. -/
theorem restrictScalars_isKInjective_of_flat
    (f : R →+* S) (hf : f.Flat) (I : CochainComplex (ModuleCat.{u} S) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj I) := by
  simpa using
    right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (restrictScalars.{u} f) (extendScalars.{u, u, u} f) (extendRestrictScalarsAdj f)
      (extendScalars_exact_of_flat f hf) I

end
