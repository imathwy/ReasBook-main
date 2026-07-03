import StacksProject_2024.Chap12.Definition_12_22_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling for Lemma 12.22.2:
- primary domain: differential objects in an abelian category, realized in this chapter as
  one-object homological complexes;
- sampled owner declarations in the local/canonical ecosystem:
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
  `HomologicalComplex.instAbelian`,
  `HomologicalComplex.d_comp_d`,
  `HomologicalComplex.Hom.comm`;
- best owner abstraction: the chapter owner
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`;
- primitive data: for this lemma, only the ambient abelian category and the owner category of
  one-object complexes;
- derived API: the abelian-category instance supplied canonically by
  `HomologicalComplex.instAbelian`;
- source/core/bridge triage:
  `source-facing`: the differential-object language introduced in Definition 12.22.1;
  `core/canonical`: the instance `HomologicalComplex.instAbelian` specialized to the one-object
    shape;
  `bridge/view`: Definition 12.22.1, which identifies the source notion with the owner
    `HomologicalComplex C (ComplexShape.refl PUnit.{1})`.

This file is therefore a pure core/canonical recall, not a place for any new wrapper API. -/
/- Lemma 12.22.2: the category of differential objects of `C`, identified in
Definition 12.22.1 with the category of one-object homological complexes in `C`,
is an abelian category. This is the one-object specialization of the canonical
owner instance `HomologicalComplex.instAbelian`. -/
recall HomologicalComplex.instAbelian

end CategoryTheory
