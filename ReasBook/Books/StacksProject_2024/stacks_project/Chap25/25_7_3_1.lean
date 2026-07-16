import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap14.Example_14_5_6
import StacksProject_2024.stacks_project.Chap14.Definition_14_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for 25.7.3.1:
- primary domain: the simplicial presheaf `Hom(C[k], T)` and the `n`-coskeleton unit on simplicial
  objects;
- sampled owner API:
  `homFromCosimplicialSet`,
  `truncation`,
  `Truncated.cosk`,
  `coskAdj`;
- source/core/bridge triage:
  `source-facing`: the displayed morphism
    `Hom(C[k], T)_{n + 1} ⟶ (cosk_n sk_n Hom(C[k], T))_{n + 1}`;
  `core/canonical`: the unit natural transformation of the adjunction
    `truncation n ⊣ Truncated.cosk n`;
  `bridge/view`: evaluating that unit at the source-facing owner `homFromCosimplicialSet C[k] T`
    and simplicial degree `n + 1`.

This item adds no new owner beyond that canonical component, so the refined file keeps the direct
recall/check surface rather than an exact-interface wrapper definition. -/

variable {C : Type u} [Category.{v} C]
variable (k n : ℕ)
variable
  [∀ Δ : SimplexCategory,
    HasProductsOfShape ((C[k] : CosimplicialObject (Type)).obj Δ) C]
variable
  [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

recall homFromCosimplicialSet
recall coskAdj

variable (T : SimplicialObject C)

/- 25.7.3.1: for a simplicial object `T`, the displayed morphism
`Hom(C[k], T)_{n + 1} ⟶ (cosk_n sk_n Hom(C[k], T))_{n + 1}` is exactly the degree-`n + 1`
component of the canonical unit map from `Hom(C[k], T)` to the `n`-coskeleton of its
`n`-truncation. -/
#check
  (((coskAdj n).unit.app (homFromCosimplicialSet C[k] T)).app (op ⦋n + 1⦌) :
    (homFromCosimplicialSet C[k] T).obj (op ⦋n + 1⦌) ⟶
      ((SimplicialObject.cosk n).obj (homFromCosimplicialSet C[k] T)).obj (op ⦋n + 1⦌))

end CategoryTheory
