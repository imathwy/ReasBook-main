import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap13.Lemma_13_31_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open ModuleCat

universe u

section

variable {R S : Type u} [Ring R] [Ring S]

/- Domain-style sampling for Lemma 15.56.3:
- primary domain: change of rings for module-valued cochain complexes and preservation of
  `CochainComplex.IsKInjective` under adjunctions;
- inspected owner declarations:
  `ModuleCat.restrictCoextendScalarsAdj`,
  `restrictScalars_exact`,
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`,
  `CochainComplex.IsKInjective`;
- best owner abstraction:
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`.

Source/core/bridge triage:
- `source-facing`: coextension of scalars along a ring map sends K-injective cochain complexes to
  K-injective cochain complexes;
- `core/canonical`: `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: the canonical adjunction `restrictScalars f ⊣ coextendScalars f` together with
  the exactness theorem `restrictScalars_exact f`.

The source statement is a source-facing bridge specialization of that owner theorem to the
canonical adjunction `restrictScalars f ⊣ coextendScalars f`; it should stay as a thin bridge
rather than a duplicate local owner.
-/

-- Proof sketch: `restrictScalars f ⊣ coextendScalars f` is the canonical change-of-rings
-- adjunction, and `restrictScalars f` is exact by Remark `12.29.2`. The result is the Chapter 13
-- owner theorem specialized to this adjunction.
/-- Lemma 15.56.3: for a ring homomorphism `f : R →+* S`, coextension of scalars sends
K-injective cochain complexes of `R`-modules to K-injective cochain complexes of `S`-modules. -/
@[stacks 0917]
theorem coextendScalars_isKInjective
    (f : R →+* S) (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((coextendScalars f).mapHomologicalComplex (up ℤ)).obj I) := by
  exact
    (right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (coextendScalars f) (restrictScalars f) (restrictCoextendScalarsAdj f)
      (restrictScalars_exact f) I :
        CochainComplex.IsKInjective (((coextendScalars f).mapHomologicalComplex (up ℤ)).obj I))

end
