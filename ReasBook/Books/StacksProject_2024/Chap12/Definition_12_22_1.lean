import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/- Domain-style sampling for Definition 12.22.1:
- primary domain: differential objects in a category with zero morphisms, expressed here in the
  chapter's one-object homological-complex language;
- sampled core/canonical declarations:
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
  `HomologicalComplex.d_comp_d`,
  `HomologicalComplex.Hom.comm`,
  `ExactCouple.page`;
- sampled more general upstream declaration:
  `CategoryTheory.DifferentialObject`, which packages a shifted differential
  `X ⟶ X⟦(1 : S)⟧` and therefore lives at a different owner level from the source's unshifted
  endomorphism-squared-zero notion;
- best owner abstraction for this item:
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`;
- primitive data: the single object together with the unique differential of the one-object
  complex;
- derived API: square-zero of that differential via `HomologicalComplex.d_comp_d`, and
  commutation of morphisms with it via `HomologicalComplex.Hom.comm`;
- source/core/bridge triage:
  `source-facing`: the textbook differential object, i.e. an object with an endomorphism whose
    square is zero;
  `core/canonical`: the one-object homological-complex owner
    `HomologicalComplex C (ComplexShape.refl PUnit.{1})`;
  `bridge/view`: source-facing unpacking into the unique component and differential, as used by
    `ExactCouple.page`.

No local wrapper is needed: in this chapter the source notion is already canonically owned by the
one-object `HomologicalComplex` specialization. -/
/- Definition 12.22.1: in the abelian-category setting of the chapter, a differential object is
canonically the one-object homological complex `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
equivalently an object equipped with an endomorphism whose square is zero; morphisms are the chain
maps, i.e. the maps commuting with the distinguished endomorphisms. -/
#check (HomologicalComplex C (ComplexShape.refl PUnit.{1}))

/- Companion recall: the unique differential of a one-object homological complex squares to zero by
specializing the owner lemma `HomologicalComplex.d_comp_d`. -/
recall HomologicalComplex.d_comp_d

/- Companion recall: a morphism of one-object homological complexes commutes with the unique
differential by the owner lemma `HomologicalComplex.Hom.comm`. -/
recall HomologicalComplex.Hom.comm

end CategoryTheory
