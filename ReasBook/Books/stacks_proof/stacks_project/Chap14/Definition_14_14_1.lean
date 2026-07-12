import Mathlib
import StacksProject_2024.Chap14.Definition_14_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : SSet)
variable [∀ Δ : SimplexCategoryᵒᵖ, HasProductsOfShape (U.obj Δ) C]

/-
Domain-style sampling for Definition 14.14.1:
- primary domain: the simplicial-set cotensor of a cosimplicial object, obtained degreewise as the
  product of copies of `V_n` indexed by `U_n`;
- inspected owner declarations:
  `CategoryTheory.homFromCosimplicialSet`,
  `CategoryTheory.homFromCosimplicialSet_map_π`,
  `CategoryTheory.Limits.piObj`,
  `CategoryTheory.Limits.Pi.map'`;
  the best owner abstraction is the source-facing specialization of the chapter owner
  `homFromCosimplicialSet` from arbitrary `D ⥤ Type` / `Dᵒᵖ ⥤ C` data to
  simplicial-set / cosimplicial-object data;
- primitive-vs-derived split:
  primitive data are the simplicial set `U`, the cosimplicial object `V`, and the product-shape
  hypotheses `[HasProductsOfShape (U.obj Δ) C]`;
  the degreewise product objects and their reindexing maps are derived from
  `homFromCosimplicialSet`, `piObj`, `Pi.map'`, the canonical double-opposite equivalence on
  `SimplexCategory`, and the specialized comparison square below.

Source/core/bridge triage:
- `source-facing`: the cosimplicial cotensor `homFromSimplicialSet U V`;
- `core/canonical`: `homFromCosimplicialSet U ((opOpEquivalence SimplexCategory).functor ⋙ V)`;
- `bridge/view`: transport of that core owner across
  `(opOpEquivalence SimplexCategory).inverse`, together with the specialized projection square
  `homFromSimplicialSet_map_π`.
-/

/-- Definition 14.14.1. Assuming the products indexed by the simplices of `U` exist degreewise in
`C`, `homFromSimplicialSet U V` is the source-facing simplicial-set cotensor obtained by
transporting the canonical owner `homFromCosimplicialSet` across the standard double-opposite
equivalence on `SimplexCategory`. -/
@[stacks 019V]
abbrev homFromSimplicialSet (V : CosimplicialObject C) : CosimplicialObject C :=
  (opOpEquivalence SimplexCategory).inverse ⋙
    homFromCosimplicialSet U ((opOpEquivalence SimplexCategory).functor ⋙ V)

/-- Helper for Definition 14.14.1: the structure map of `homFromSimplicialSet U V` and the
corresponding projections form the canonical commutative square induced by reindexing on `U` and
the cosimplicial structure map on `V`. -/
theorem homFromSimplicialSet_map_π
    (V : CosimplicialObject C)
    {m n : SimplexCategory} (f : n ⟶ m) (u : U.obj (op m)) :
    CommSq
      ((homFromSimplicialSet U V).map f)
      (Pi.π (fun _ : U.obj (op n) ↦ V.obj n) (U.map f.op u))
      (Pi.π (fun _ : U.obj (op m) ↦ V.obj m) u)
      (V.map f) := by
  simpa using
    (homFromCosimplicialSet_map_π
      U
      ((opOpEquivalence SimplexCategory).functor ⋙ V)
      f.op.op
      u)

/-- Helper for Definition 14.14.1: a morphism into `homFromSimplicialSet U V` is componentwise
natural with respect to the cosimplicial structure maps. -/
theorem homFromSimplicialSet_hom_naturality
    {X : CosimplicialObject C}
    (V : CosimplicialObject C)
    (h : X ⟶ homFromSimplicialSet U V)
    {m n : SimplexCategory} (f : n ⟶ m) (u : U.obj (op m)) :
    CommSq
      (X.map f)
      (h.app n ≫ Pi.π (fun _ : U.obj (op n) ↦ V.obj n) (U.map f.op u))
      (h.app m ≫ Pi.π (fun _ : U.obj (op m) ↦ V.obj m) u)
      (V.map f) := by
  simpa using
    (CommSq.vert_comp
      (CommSq.mk (h.naturality f))
      (homFromSimplicialSet_map_π U V f u))

end CategoryTheory
