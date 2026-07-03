import Mathlib
import StacksProject_2024.Chap04.Lemma_4_35_9
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

/-- Helper for Lemma 8.6.7: a faithful functor into a thin category has a thin source. -/
private theorem isThin_of_faithful
    {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) [G.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A := by
  -- A faithful functor reflects equality of morphisms, and the target has only one morphism.
  intro a b
  refine ⟨?_⟩
  intro φ ψ
  exact G.map_injective (Subsingleton.elim _ _)

/-- Helper for Lemma 8.6.7: in a categorical pullback, the right projection is faithful once the
left leg is faithful. -/
private theorem categorical_pullback_rightProjection_faithful_of_leftFaithful
    {A B T : Type*} [Category A] [Category B] [Category T]
    (L : A ⥤ T) (R : B ⥤ T) [L.Faithful] :
    (Limits.CategoricalPullback.π₂ L R).Faithful where
  map_injective {x y} φ ψ h := by
    -- The right components agree by assumption; the pullback commutativity then forces the left
    -- components to have the same image in `T`, hence faithfulness of `L` identifies them.
    have hsnd : φ.snd = ψ.snd := by
      simpa using h
    apply Limits.CategoricalPullback.hom_ext
    · apply L.map_injective
      have hcomp : L.map φ.fst ≫ y.iso.hom = L.map ψ.fst ≫ y.iso.hom := by
        calc
          L.map φ.fst ≫ y.iso.hom = x.iso.hom ≫ R.map φ.snd := φ.w
          _ = x.iso.hom ≫ R.map ψ.snd := by simp [hsnd]
          _ = L.map ψ.fst ≫ y.iso.hom := ψ.w.symm
      exact (Iso.cancel_iso_hom_right _ _ y.iso).1 hcomp
    · exact hsnd

/-- Helper for Lemma 8.6.7: the categorical pullback of a faithful left functor and a thin right
source category is thin. -/
private theorem categorical_pullback_isThin_of_leftFaithful_rightThin
    {A B T : Type*} [Category A] [Category B] [Category T]
    (L : A ⥤ T) (R : B ⥤ T) [L.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin (Limits.CategoricalPullback L R) := by
  -- First show the right projection is faithful, then reflect thinness from the thin right source.
  letI : (Limits.CategoricalPullback.π₂ L R).Faithful :=
    categorical_pullback_rightProjection_faithful_of_leftFaithful L R
  exact isThin_of_faithful (Limits.CategoricalPullback.π₂ L R)

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
        g.toFibredCategoryMor).p.Fiber U) := by
  let e := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    f.toBasedFunctor g.toBasedFunctor U
  have hFiberFaithful : (f.toBasedFunctor.fiberFunctor U).Faithful := by
    -- Lemma `4.35.9` transfers total faithfulness of `f` to the fiber over `U`.
    simpa using
      ((FibredCategoryMor.faithful_iff_fiberwise
        (F := f.toFibredCategoryMor)).1 hf U)
  letI : (f.toBasedFunctor.fiberFunctor U).Faithful := hFiberFaithful
  letI :
      Quiver.IsThin ((BasedCategory.ofFunctor R.toFibredCategoryOver.1.p).p.Fiber U) := by
    -- The right factor is already a stack in setoids, so its fiber over `U` is thin.
    simpa using (inferInstance : Quiver.IsThin (R.p.Fiber U))
  letI :
      Quiver.IsThin
        (Limits.CategoricalPullback
          (f.toBasedFunctor.fiberFunctor U)
          (g.toBasedFunctor.fiberFunctor U)) :=
    categorical_pullback_isThin_of_leftFaithful_rightThin
      (f.toBasedFunctor.fiberFunctor U)
      (g.toBasedFunctor.fiberFunctor U)
  -- Transport thinness back across the canonical equivalence from the fiber of the explicit
  -- `2`-fibre product to the pullback of the two fibers.
  exact isThin_of_faithful e.functor

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
