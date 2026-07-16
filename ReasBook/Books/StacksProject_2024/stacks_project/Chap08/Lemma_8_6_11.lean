import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_42_5
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_1
import StacksProject_2024.stacks_project.Chap08.Definition_8_6_1
import StacksProject_2024.stacks_project.Chap08.Lemma_8_6_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X T : FibredInGroupoidsOver C}
variable [IsStackInGroupoids J T.p]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

/- Domain-style sampling for Lemma 8.6.11:
- primary domain: stacks in groupoids over a site and the slice-pair presheaf attached to a
  morphism of categories fibred in groupoids;
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `IsStackInSetoids`,
  `FibredInGroupoidsMor.faithful_iff_fiberwise`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `isStackInSetoids_iff_isoClassPresheaf_isSheaf`;
- best owner abstraction: the source-facing conclusion remains the owner predicate
  `IsStackInGroupoids J X.p`, while the faithfulness hypothesis should use the canonical owner
  predicate `F.toBasedFunctor.Faithful` rather than duplicating its fiberwise reformulation; the
  slice hypothesis should be stated directly for the canonical slice base change
  `F.sliceTwoFibreProduct G`, with the owner-level stack-in-setoids reformulation on its
  projection kept as derived API;
- primitive data: the morphism `F : X ⟶ T` and the sheaf condition on the canonical
  iso-class presheaf of the canonical slice base change for each slice morphism `G : C/U ⟶ T`;
- derived API: the companion owner-level hypothesis
  `IsStackInSetoids (J.over U) (F.sliceTwoFibreProduct G).p` via Lemma `8.6.3`, and the
  resulting stack-in-groupoids structure on `X`, whose groupoid part is already ambient because
  `X : FibredInGroupoidsOver C`.

Source/core/bridge triage:
- `source-facing`: Lemma 8.6.11 itself;
- `core/canonical`: `IsStackInGroupoids J X.p`, `F.toBasedFunctor.Faithful`, and
  `IsStackInSetoids (J.over U) ((F.sliceTwoFibreProduct G).p)`;
- `bridge/view`: the textbook fibrewise-faithful hypothesis, recovered from
  `FibredInGroupoidsMor.faithful_iff_fiberwise`, together with the sheaf reformulation on
  `fiberIsoClassPresheaf ((F.sliceTwoFibreProduct G).p)` supplied by Lemma `8.6.3`. -/

-- Proof sketch: for each object `U`, use the faithful morphism `F : X ⟶ T` and the sheaf
-- condition on the canonical slice iso-class presheaf of `F.sliceTwoFibreProduct G` to show that
-- descent data in `X` is effective and morphisms descend uniquely after applying `F`. The stack
-- condition for `T` supplies the compatible target-side object and comparison isomorphisms, which
-- the sheaf hypothesis lifts back to `X`, yielding the stack condition on `X`.
/-- Lemma 8.6.11: let `F : X ⟶ T` be a morphism of categories fibred in groupoids over the
site `(C, J)`. Assume that `T` is a stack in groupoids, that the underlying based functor
`F.toBasedFunctor` is faithful (equivalently, faithful on every fiber by Lemma `4.35.9`), and
that for every `U : C` and every slice morphism `G : C/U ⟶ T`, the canonical iso-class presheaf
of the slice base change `F.sliceTwoFibreProduct G` is a sheaf. Via Yoneda on `T_U`, this is the
source presheaf of isomorphism classes of pairs `(x, F(x) ≅ f^* y)`. Then `X` is a stack in
groupoids over `(C, J)`. -/
theorem isStackInGroupoids_of_faithful_and_sliceTwoFibreProductIsoClassPresheaf_isSheaf
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hSheaf :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ T),
        Presheaf.IsSheaf (J.over U) ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf)) :
    IsStackInGroupoids J X.p := sorry

/-- Companion owner-level reformulation: it is enough to assume that each canonical slice base
change is a stack in setoids over the slice site. The source-facing sheaf hypothesis of Lemma
`8.6.11` is then recovered from Lemma `8.6.3`. -/
theorem isStackInGroupoids_of_faithful_and_sliceTwoFibreProduct_isStackInSetoids
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hStack :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ T),
        IsStackInSetoids (J.over U) ((F.sliceTwoFibreProduct G).p)) :
    IsStackInGroupoids J X.p := by
  refine isStackInGroupoids_of_faithful_and_sliceTwoFibreProductIsoClassPresheaf_isSheaf
    F hFaithful ?_
  intro U G
  exact
    (isStackInSetoids_iff_isoClassPresheaf_isSheaf (J.over U) (F.sliceTwoFibreProduct G).p).1
      (hStack G)

end FibredInGroupoidsMor

end

end CategoryTheory
