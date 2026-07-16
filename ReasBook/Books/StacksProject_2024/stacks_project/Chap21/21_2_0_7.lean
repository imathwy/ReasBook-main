import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.SiteHigherDirectImageCore

open CategoryTheory
open scoped CategoryTheory.Sheaf

noncomputable section

universe v u

/- Domain-style sampling for 21.2.0.7:
- primary domain: higher direct images of sheaves as right derived objects of sheaf pushforward;
- sampled owner API:
  `CategoryTheory.Sheaf.higherDirectImageFunctor`,
  `CategoryTheory.Sheaf.higherDirectImage`,
  `CategoryTheory.Functor.sheafPushforwardContinuous`,
  `CategoryTheory.Functor.rightDerived`,
  `CategoryTheory.InjectiveResolution`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstraction: the source-facing site owner `higherDirectImage` and its functor-level
  companion `higherDirectImageFunctor u i`, with the injective-resolution computation supplied by
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- primitive data: a continuous functor `u : D ⥤ C`, a sheaf `F : Sheaf JC AddCommGrpCat`,
  a chosen injective resolution `I : CategoryTheory.InjectiveResolution F`, and a degree `i : ℕ`;
- derived API: the canonical comparison computing the right-derived value from the pushed-forward
  injective cocomplex.

Source/core/bridge triage:
- `source-facing`: the higher direct image of a sheaf along a morphism of sites;
- `core/canonical`: `CategoryTheory.Sheaf.higherDirectImageFunctor`,
  `CategoryTheory.Sheaf.higherDirectImage`, and
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: the injective-resolution computation theorem for the owner `higherDirectImage`.

This item is the companion theorem layer for the owner-level site specialization introduced in
`SiteHigherDirectImageCore`: the source-facing site-theoretic surface is the reusable owner
`higherDirectImage`, while `InjectiveResolution.isoRightDerivedObj` remains the computation theorem
used to identify it with the pushed-forward injective cocomplex. Since that comparison already has
the exact source-facing isomorphism type here, this file should keep only the tagged
`IsIsomorphic` companion theorem rather than a duplicate local isomorphism wrapper.
-/

namespace CategoryTheory
namespace Sheaf

/- 21.2.0.7: the higher direct image of a sheaf is computed by the degree-`i` homology of the
pushforward of an injective resolution. This is exactly the specialization of
`InjectiveResolution.isoRightDerivedObj` to the sheaf-pushforward functor. -/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [Functor.IsContinuous u JD JC]
variable [HasSheafify JC AddCommGrpCat.{v}] [HasSheafify JD AddCommGrpCat.{v}]
variable [HasInjectiveResolutions (Sheaf JC AddCommGrpCat.{v})]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC)]

/-- 21.2.0.7, source-facing companion: the canonical isomorphism above gives the usual
`IsIsomorphic` statement for the `i`-th higher direct image. -/
@[stacks 071I]
theorem higherDirectImage_isomorphic_to_homology_of_injectiveResolution
    (F : Sheaf JC AddCommGrpCat.{v}) (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic (R^{i}_[u](F))
      ((HomologicalComplex.homologyFunctor (Sheaf JD AddCommGrpCat.{v})
          (ComplexShape.up ℕ) i).obj
        (((u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) :=
  ⟨I.isoRightDerivedObj (u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC) i⟩

end

end Sheaf
end CategoryTheory
