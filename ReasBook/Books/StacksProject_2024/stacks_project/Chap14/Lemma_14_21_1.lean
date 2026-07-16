import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap14.Lemma_14_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory SimplexCategory.Truncated
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 14.21.1:
- primary domain: simplicial objects obtained by pointwise left Kan extension along the truncated
  simplex inclusion;
- sampled owner declarations:
  `Truncated.sk`,
  `Functor.leftKanExtensionObjIsoColimit`,
  `Functor.ι_leftKanExtensionObjIsoColimit_inv`,
  `Functor.ι_leftKanExtensionObjIsoColimit_hom`;
- best owner abstraction: the chapter-level owner for the source notion `i_{m!} U` is
  `Truncated.sk m`; the pointwise colimit comparison and its cocone-leg formulas
  are derived API from the canonical Kan-extension owner, so this file should reuse those owners
  directly rather than keep parallel local wrappers;
- primitive data: the truncated simplicial object `U` and the simplex `Δ`;
- derived API: the value of `((Truncated.sk m).obj U)` at `Δ`, together with the
  formulas describing how each indexing simplex contributes through the simplicial transition maps.

Source/core/bridge triage:
- `source-facing`: the Chapter 14 description of `i_{m!} U` by its degree objects and the maps
  induced by simplicial operators;
- `core/canonical`: the skeleton functor owner `Truncated.sk m`;
- `bridge/view`: the specialization of the pointwise Kan-extension colimit API to that owner. -/

variable {C : Type u} [Category.{v} C]
variable (m : ℕ)
variable [HasFiniteColimits C]

/- Companion owner recall: the pointwise description of a left Kan extension as a colimit is the
canonical declaration `Functor.leftKanExtensionObjIsoColimit`. -/
recall Functor.leftKanExtensionObjIsoColimit

variable (U : SimplicialObject.Truncated C m) (Δ : SimplexCategory)

/- Lemma 14.21.1: the value of the simplicial `m`-skeleton `i_{m!} U` at `Δ` is the canonical
colimit computing the left Kan extension along the truncated simplex inclusion. -/
#check
  ((Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Δ) :
    ((Truncated.sk m).obj U).obj (op Δ) ≅
      colimit (CostructuredArrow.proj (Truncated.inclusion m).op (op Δ) ⋙ U))

variable
    (g : CostructuredArrow (SimplexCategory.Truncated.inclusion m).op (op Δ))

/- Companion bridge recall: each cocone leg into that colimit is identified by the canonical
inverse comparison formula. -/
#check
  (((Truncated.inclusion m).op.ι_leftKanExtensionObjIsoColimit_inv U (op Δ) g) :
    colimit.ι (CostructuredArrow.proj (Truncated.inclusion m).op (op Δ) ⋙ U) g ≫
      ((Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Δ)).inv =
        (((Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left) ≫
          ((Truncated.sk m).obj U).map g.hom)

/- The forward cocone-leg formula is the corresponding canonical `hom` statement. -/
#check
  (((Truncated.inclusion m).op.ι_leftKanExtensionObjIsoColimit_hom U (op Δ) g) :
    (((Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left) ≫
        ((Truncated.sk m).obj U).map g.hom ≫
          ((Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Δ)).hom =
      colimit.ι (CostructuredArrow.proj (Truncated.inclusion m).op (op Δ) ⋙ U) g)

end

end CategoryTheory
