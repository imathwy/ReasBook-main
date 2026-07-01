import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap12.Definition_12_19_1

open CategoryTheory.Limits
open scoped CategoryTheory

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/- Domain-style sampling for Definition 12.23.1:
- primary domain: filtered differential objects in a category with zero morphisms,
  obtained by specializing the differential-object owner from Definition 12.22.1 to the category
  of filtered objects from Definition 12.19.1;
- sampled core/canonical declarations in this domain:
  `HomologicalComplex (Fil(C)) (ComplexShape.refl PUnit.{1})`,
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
  `FilteredObject.Hom.preserves`,
  `HomologicalComplex.d_comp_d`;
- best owner abstraction: the one-object homological-complex owner
  `HomologicalComplex (Fil(C)) (ComplexShape.refl PUnit.{1})`;
- primitive data: a filtered object together with its unique differential, which is automatically
  filtration-preserving because it is a morphism in `Fil(C)`;
- derived API: preservation of each filtration stage via `FilteredObject.Hom.preserves`,
  square-zero of the differential via `HomologicalComplex.d_comp_d`, and commutation of morphisms
  with differentials via `HomologicalComplex.Hom.comm`;
- source/core/bridge triage:
  `source-facing`: a filtered object equipped with a filtration-preserving endomorphism squaring
    to zero;
  `core/canonical`: the one-object complex owner in `Fil(C)`;
  `bridge/view`: the forgetful view to Definition `12.22.1`, obtained by forgetting the
    filtration.

This item adds no new public data beyond the existing owner, so the refined file keeps a direct
canonical recall/check rather than introducing a parallel alias such as
`FilteredDifferentialObject`. -/
/- Definition 12.23.1: this is the `Fil(C)` specialization of the chapter's owner
declaration for differential objects from Definition 12.22.1. In the source's abelian setting,
this means a filtered differential object is canonically a one-object homological complex in the
category of filtered objects, equivalently a filtered object equipped with an endomorphism
preserving each filtration stage and squaring to zero. The owner recall itself only needs zero
morphisms on `C`. -/
#check (HomologicalComplex (Fil(C)) (ComplexShape.refl PUnit.{1}))

/- Companion recall: the unique differential of a one-object filtered complex preserves each
filtration stage because it is a morphism in `Fil(C)`. -/
recall FilteredObject.Hom.preserves

/- Companion recall: the unique differential of a one-object filtered complex squares to zero by
specializing `HomologicalComplex.d_comp_d`. -/
recall HomologicalComplex.d_comp_d

/- Companion recall: morphisms of one-object filtered complexes commute with the distinguished
differentials by `HomologicalComplex.Hom.comm`. -/
recall HomologicalComplex.Hom.comm

end CategoryTheory
