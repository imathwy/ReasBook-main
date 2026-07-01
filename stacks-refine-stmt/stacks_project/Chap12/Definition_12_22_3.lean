import stacks_project.Chap12.Definition_12_22_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling for Definition 12.22.3:
- primary domain: homology of differential objects in an abelian category, realized in this
  chapter as one-object homological complexes;
- sampled canonical declarations in the local/mathlib owner ecosystem:
  `HomologicalComplex.homology`,
  `HomologicalComplex.homologyFunctor`,
  `HomologicalComplex.homologyMap`,
  `ShortComplex.homology`;
- best owner abstraction: the one-object specialization of `HomologicalComplex.homology` at
  `PUnit.unit`;
- primitive data: the ambient abelian category and a one-object homological complex `A`;
- derived API: functoriality via
  `HomologicalComplex.homologyFunctor C (ComplexShape.refl PUnit.{1}) PUnit.unit` and the induced
  map `HomologicalComplex.homologyMap φ PUnit.unit`;
- source/core/bridge triage:
  `source-facing`: the homology object `H(A,d) = ker d / im d` of a differential object;
  `core/canonical`: `HomologicalComplex.homology`;
  `bridge/view`: Definition 12.22.1, which identifies differential objects with one-object
    homological complexes, together with evaluation of the owner construction at `PUnit.unit`.

This item is therefore a source-facing bridge/view on the canonical owner: the public surface
should expose the one-object specialization `H(A)` rather than only the fully general owner
`HomologicalComplex.homology`, without introducing a second public owner alias. -/

scoped notation "H(" A ")" => HomologicalComplex.homology A PUnit.unit

variable (A : HomologicalComplex C (ComplexShape.refl PUnit.{1}))

/- Definition 12.22.3: for a differential object `A`, the source-facing homology object is
`H(A)`, i.e. the one-object specialization of `HomologicalComplex.homology` at `PUnit.unit`. -/
#check H(A)

/- Companion recall: the source-facing homology of differential objects is functorial via the
one-object specialization of `HomologicalComplex.homologyFunctor`. -/
#check (HomologicalComplex.homologyFunctor C (ComplexShape.refl PUnit.{1}) PUnit.unit)

end CategoryTheory
