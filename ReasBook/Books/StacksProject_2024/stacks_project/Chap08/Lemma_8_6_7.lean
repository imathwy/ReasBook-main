import Mathlib
import StacksProject_2024.Chap08.Definition_8_4_5
import StacksProject_2024.Chap08.Definition_8_6_1
import StacksProject_2024.Chap08.Lemma_8_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredCategoryOver

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {T R S : StackOver J}

namespace WideSubcategory

private abbrev toFibredCategoryMor {T S : StackOver J} (f : T ⟶ S) :=
  InducedCategory.Hom.toFibredCategoryMor f

private abbrev toBasedFunctor {T S : StackOver J} (f : T ⟶ S) :=
  InducedCategory.Hom.toBasedFunctor f

end WideSubcategory

/- Domain-style sampling for Lemma 8.6.7:
- primary domain: stacks over a site, organized around the explicit `2`-fibre product of the
  underlying fibred categories and owner predicates on its projection functor;
- inspected owner-level declarations:
  `IsStackInSetoids`,
  `IsFibredInSetoids`,
  the canonical hom bridge owners `InducedCategory.Hom.toBasedFunctor` and
  `InducedCategory.Hom.toFibredCategoryMor`, used below through the short object-prefix spellings
  `f.toBasedFunctor` and `f.toFibredCategoryMor`,
  `twoFibreProduct`,
  `StackOver.ofProjection`;
- best owner abstraction: the canonical core is the projection
  `(twoFibreProduct f.toFibredCategoryMor
    g.toFibredCategoryMor).p`, while
  `StackOver.ofProjection J
    (twoFibreProduct f.toFibredCategoryMor
      g.toFibredCategoryMor).p` is
  only the bundled stack-level view;
- primitive data: the morphisms `f : T ⟶ S`, `g : R ⟶ S`, the faithfulness hypothesis on the
  owner based functor `f.toBasedFunctor`, and the ambient
  stack/groupoid/setoid instances on the three factors;
- derived API: the internal `IsFibredInSetoids` closure on the explicit `2`-fibre-product
  projection, used only to support the source-facing stack-in-setoids conclusion.

Source/core/bridge triage:
- `source-facing`: `stackTwoFibreProduct_isStackInSetoids_of_leftFaithful`;
- `core/canonical`: `IsFibredInSetoids` and `IsStackInSetoids` on
  `(twoFibreProduct f.toFibredCategoryMor
    g.toFibredCategoryMor).p`;
- `bridge/view`: the bundled stack
  `StackOver.ofProjection J
    (twoFibreProduct f.toFibredCategoryMor
      g.toFibredCategoryMor).p`. -/

section

variable [IsFibredInGroupoids T.p]
variable [IsStackInSetoids J R.p]
variable [IsFibredInGroupoids S.p]
variable (f : T ⟶ S) (g : R ⟶ S)

-- Proof sketch: by Lemma `4.35.9`, faithfulness of the left morphism restricts to faithfulness on
-- each fiber. In the explicit fiber description from Lemma `4.32.3`, a morphism is then uniquely
-- determined by its component in the setoid fiber of `R`, so every fiber of the `2`-fibre product
-- is thin, hence again a setoid `1`-category.
/-- If the left leg of the explicit `2`-fibre product of stacks is faithful and the right stack is
in setoids, then every fiber of the explicit `2`-fibre product is a setoid `1`-category. -/
private theorem twoFibreProduct_fiber_isThin_of_leftFaithful
    (hf : f.toBasedFunctor.Faithful) (U : C) :
    Quiver.IsThin
      ((twoFibreProduct f.toFibredCategoryMor
        g.toFibredCategoryMor).p.Fiber U) := sorry

-- Proof sketch: the previous theorem supplies exactly the thin-fiber data required by
-- `IsFibredInSetoids`, while Lemma `4.35.7` already gives the ambient fibred-in-groupoids
-- structure on the explicit `2`-fibre-product projection.
/-- If the left leg of the explicit `2`-fibre product of stacks is faithful and the right stack is
in setoids, then the explicit `2`-fibre-product projection is fibred in setoids. -/
private theorem twoFibreProduct_isFibredInSetoids_of_leftFaithful
    (hf : f.toBasedFunctor.Faithful) :
    IsFibredInSetoids
      (twoFibreProduct f.toFibredCategoryMor
        g.toFibredCategoryMor).p := by
  let P := twoFibreProduct f.toFibredCategoryMor g.toFibredCategoryMor
  letI : ∀ U : C, Quiver.IsThin (P.p.Fiber U) :=
    twoFibreProduct_fiber_isThin_of_leftFaithful f g hf
  change IsFibredInSetoids P.p
  infer_instance

-- Proof sketch: apply Lemma `8.4.6` to get a descent theory making the explicit
-- `2`-fibre-product projection a stack. The previous theorem supplies the fiberwise thinness, and
-- the generic instance from Definition `4.39.2` then upgrades the canonical projection to a
-- category fibred in setoids.
/-- Lemma 8.6.7: if `T` and `S` are stacks in groupoids over `(C, J)`, `R` is a stack in setoids
over `(C, J)`, `f : T ⟶ S` is faithful, and `g : R ⟶ S` is a morphism of stacks, then the
`2`-fibre product `T ×[S] R` is again a stack in setoids over `(C, J)`. -/
theorem stackTwoFibreProduct_isStackInSetoids_of_leftFaithful
    (hf : f.toBasedFunctor.Faithful) :
    IsStackInSetoids J (twoFibreProduct f.toFibredCategoryMor
      g.toFibredCategoryMor).p := by
  let P := twoFibreProduct f.toFibredCategoryMor g.toFibredCategoryMor
  letI : IsFibredInSetoids P.p := twoFibreProduct_isFibredInSetoids_of_leftFaithful f g hf
  letI : IsStackOnSite J P.p := stackTwoFibreProduct_isStack
    f.toFibredCategoryMor g.toFibredCategoryMor
  change IsStackInSetoids J P.p
  infer_instance

end

end CategoryTheory
