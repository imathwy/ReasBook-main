import Mathlib
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Lemma_8_10_3

-- Declarations for this item will be appended below by the statement pipeline.

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryOver
open FibredCategoryMor
open StackInGroupoidsOver.Hom

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Y : FibredCategoryOver C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.10.5:
- primary domain: stacks in groupoids over sites and the inherited topology on the total category
  of a fibred category over the base site;
- inspected owner-level declarations:
  `StackOver`,
  `StackInGroupoidsOver`,
  `SubTwoCategory.Hom.toHom`,
  `StackInGroupoidsOver.Hom.G`,
  `FibredCategoryOver.inheritedTopology`,
  `IsStackOnSite`,
  `IsStackInGroupoids`;
- best owner abstraction: the new mathematical content is the canonical owner-level theorem
  `IsStackOnSite (inheritedTopology J Y) (G F)` for an ambient owner hom
  `F : FibredCategoryMor X.toFibredCategoryOver Y`; the stronger
  source/target groupoid hypotheses belong only to the source-facing specialization. The
  source-facing owner-hom specialization
  `IsStackInGroupoids (inheritedTopology J Yₛ) (G F)` is then derived from the
  existing owner-level constructor for stacks in groupoids;
- primitive data: a stack `X : StackOver J`, a target fibred category `Y : FibredCategoryOver C`,
  an ambient owner hom `F : FibredCategoryMor X.toFibredCategoryOver Y`, and the extra
  hypothesis `[IsFibredInGroupoids F.toFunctor]`;
- derived API: the source-facing theorem below reuses the canonical
  `[IsFibredInGroupoids _] [IsStackOnSite _ _]` to `IsStackInGroupoids _ _` instance rather than
  packaging a parallel local owner.

Source/core/bridge triage:
- `source-facing`: `isStackInGroupoidsOverInheritedTopology_of_isFibredInGroupoids`;
- `core/canonical`: `isStackOnSiteOverInheritedTopology_of_isFibredInGroupoids`;
- `bridge/view`: the existing chapter bridge `toFibredCategoryMor F`,
  together with the derived `IsStackInGroupoids (inheritedTopology J Yₛ) F.toFunctor`
  conclusion obtained by `inferInstance`. -/

-- Proof sketch: equip `Y` with the inherited topology from Lemma `8.10.3`. By hypothesis
-- `F.toFunctor` is fibred in groupoids over `Y`, and since `X` is already
-- a stack over the base site `(C, J)`, the argument of the Stacks Project lemma transports
-- descent data along the inherited topology on `Y`.
/-- The owner-level inherited-topology stack statement behind Lemma 8.10.5, at the canonical
ambient hom layer over a stack source and an arbitrary target fibred category. -/
theorem isStackOnSiteOverInheritedTopology_of_isFibredInGroupoids
    (X : StackOver J) (F : FibredCategoryMor X.toFibredCategoryOver Y)
    [IsFibredInGroupoids (toFunctor F)] :
    IsStackOnSite (inheritedTopology J Y) (toFunctor F) := sorry

-- Proof sketch: apply the owner-level inherited-topology stack statement to the ambient fibred
-- category morphism underlying `F : Xₛ ⟶ Yₛ`, then combine it with the assumed
-- fibred-in-groupoids structure on `G F` and the canonical constructor
-- `[IsFibredInGroupoids _] [IsStackOnSite _ _] → IsStackInGroupoids _ _`.
/-- Lemma 8.10.5: let `Xₛ` and `Yₛ` be stacks in groupoids over the site `(C, J)`, and let
`F : Xₛ ⟶ Yₛ` be a `1`-morphism of stacks in groupoids over `(C, J)`. If the underlying functor
`F.G` makes the total category of `Xₛ` into a category fibred in groupoids over the total
category of `Yₛ`, then `F.G` is a stack in groupoids for the topology on `Yₛ` inherited from
`(C, J)`. -/
theorem isStackInGroupoidsOverInheritedTopology_of_isFibredInGroupoids
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)] :
    IsStackInGroupoids (inheritedTopology J Yₛ) (G F) := sorry

end

end CategoryTheory
