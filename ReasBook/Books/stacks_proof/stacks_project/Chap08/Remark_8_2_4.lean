import Mathlib
import stacks_proof.stacks_project.Chap04.Definition_4_35_1
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open FibredCategoryMor

variable {C : Type u} [Category.{v} C]

/-- Helper for Remark 8.2.4: a category fibred in groupoids over `C` is a fibred category over
`C` whose projection functor is fibred in groupoids. -/
structure FibredInGroupoidsOver (C : Type u) [Category.{v} C] where
  toFibredCategoryOver : FibredCategoryOver.{u, v, uS, vS} C
  fibredInGroupoids : IsFibredInGroupoids toFibredCategoryOver.p

namespace FibredInGroupoidsOver

/-- Helper for Remark 8.2.4: the projection functor of a category fibred in groupoids over
`C`. -/
abbrev p (X : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver.p

/-- Helper for Remark 8.2.4: forget a category fibred in groupoids to its underlying fibred
category over `C`. -/
instance : CoeOut (FibredInGroupoidsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Helper for Remark 8.2.4: the projection of a category fibred in groupoids is again fibred in
groupoids. -/
instance (X : FibredInGroupoidsOver C) : IsFibredInGroupoids X.p :=
  X.fibredInGroupoids

end FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}

/-- Helper for Remark 8.2.4: a morphism of categories fibred in groupoids is the underlying
morphism of fibred categories between the ambient fibred-category objects. -/
abbrev FibredInGroupoidsMor (X Y : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver

namespace FibredInGroupoidsMor

/-- Helper for Remark 8.2.4: the underlying based functor of a morphism of categories fibred in
groupoids over `C`. -/
abbrev toBasedFunctor
    (F : FibredInGroupoidsMor X Y) :
    X.toFibredCategoryOver.toBasedCategory ⥤ᵇ Y.toFibredCategoryOver.toBasedCategory :=
  F.toHom

/-- Helper for Remark 8.2.4: equivalence over the base for a morphism of categories fibred in
groupoids is the ambient equivalence-over-base condition on the underlying based functor. -/
abbrev IsEquivalenceOverBase (F : FibredInGroupoidsMor X Y) : Prop :=
  BasedFunctor.IsEquivalenceOverBase F.toBasedFunctor

/- Domain-style sampling for Remark 8.2.4:
- primary domain: morphisms of categories fibred in groupoids over a fixed base and the induced
  canonical Hom-presheaf morphisms on fibers;
- sampled owner-level declarations:
  `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedFunctor.isEquivalence_of_isEquivalenceOverBase`,
  `Functor.FullyFaithful.ofFullyFaithful`,
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful`;
- best owner abstraction: the owner morphism `F : FibredInGroupoidsMor X Y`, with the
  equivalence-over-base predicate as primitive data; the Hom-presheaf isomorphism is derived API
  obtained by upgrading `F.toBasedFunctor` to an equivalence, then to the canonical fully
  faithful owner witness, and finally routing through the ambient
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful` theorem;
- primitive data: only `F` together with `hF : F.IsEquivalenceOverBase`;
- derived API: `F.toBasedFunctor.IsEquivalence`, the resulting canonical fully faithful witness,
  and finally the `IsIso` statement for the comparison morphism `F.fibredMorphismPresheafMap x y`.

Source/core/bridge triage:
- `source-facing`: the remark-level conclusion that an equivalence over the base preserves the
  presheaves `Mor(x, y)`;
- `core/canonical`: `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedFunctor.isEquivalence_of_isEquivalenceOverBase`,
  `Functor.FullyFaithful.ofFullyFaithful`, and
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful`;
- `bridge/view`: the theorem below, which derives the source-facing conclusion from those owner
  abstractions without introducing a parallel presheaf API. -/

/-- Remark 8.2.4, in canonical form: for an equivalence over the base category `C`, the canonical
Hom-presheaf morphism from Lemma `8.2.3` is an isomorphism. Combined with
Lemma `4.37.3`, this is the source-faithful observation that one may replace a category fibred in
groupoids by an equivalent split model without changing the presheaves `Mor(x, y)`. -/
-- Proof sketch: upgrade the equivalence-over-base hypothesis to a fully faithful underlying based
-- functor, then apply the Chapter 8 isomorphism criterion for the canonical Hom-presheaf map.
@[stacks 02ZA]
theorem fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase
    (F : FibredInGroupoidsMor X Y) (hF : F.IsEquivalenceOverBase)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (fibredMorphismPresheafMap
      (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) x y) := by
  -- Reinterpret the equivalence-over-base hypothesis as full faithfulness for the underlying
  -- based functor on total categories.
  have hFF : Nonempty F.toBasedFunctor.FullyFaithful := by
    let _ : F.toBasedFunctor.IsEquivalence :=
      BasedFunctor.isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF
    exact ⟨Functor.FullyFaithful.ofFullyFaithful F.toBasedFunctor.toFunctor⟩
  -- Each component is conjugation by the pullback-comparison isomorphisms around the map induced
  -- by the fiber functor, hence bijective.
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  rw [isIso_iff_bijective]
  let xW := W.unop.hom ^*[canonicalPullbackChoice X.toFibredCategoryOver.p] x
  let yW := W.unop.hom ^*[canonicalPullbackChoice X.toFibredCategoryOver.p] y
  let FxW := (F.toBasedFunctor.fiberFunctor W.unop.left).obj xW
  let FyW := (F.toBasedFunctor.fiberFunctor W.unop.left).obj yW
  let ex := FibredCategoryMor.pullbackComparison F W.unop.hom x
  let ey := FibredCategoryMor.pullbackComparison F W.unop.hom y
  have hFiberFF :
      Nonempty ((F.toBasedFunctor.fiberFunctor W.unop.left).FullyFaithful) := by
    let _ : (F.toBasedFunctor.fiberFunctor W.unop.left).IsEquivalence :=
      BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
        F.toBasedFunctor hF W.unop.left
    exact ⟨Functor.FullyFaithful.ofFullyFaithful (F.toBasedFunctor.fiberFunctor W.unop.left)⟩
  have hFiberMapBijective :
      ∀ a b : X.toFibredCategoryOver.p.Fiber W.unop.left,
        Function.Bijective
          ((F.toBasedFunctor.fiberFunctor W.unop.left).map : (a ⟶ b) →
            ((F.toBasedFunctor.fiberFunctor W.unop.left).obj a ⟶
              (F.toBasedFunctor.fiberFunctor W.unop.left).obj b)) := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective] at hFiberFF
    exact hFiberFF
  have hMap :
      Function.Bijective ((F.toBasedFunctor.fiberFunctor W.unop.left).map : (xW ⟶ yW) → (FxW ⟶ FyW)) := by
    simpa [xW, yW, FxW, FyW] using hFiberMapBijective xW yW
  let eCongr :
      (FxW ⟶ FyW) ≃
        ((canonicalFiberPseudofunctor Y.toFibredCategoryOver.p).presheafHom
          ((F.toHom.fiberFunctor U).obj x)
          ((F.toHom.fiberFunctor U).obj y)).obj W :=
    Iso.homCongr ex.symm ey.symm
  have hApp :
      (fibredMorphismPresheafMap
        (F := (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver)) x y).app W =
        fun δ : xW ⟶ yW ↦ eCongr ((F.toBasedFunctor.fiberFunctor W.unop.left).map δ) := by
    funext δ
    rfl
  rw [hApp]
  constructor
  · intro δ₁ δ₂ hδ
    apply hMap.1
    apply eCongr.injective
    simpa using hδ
  · intro θ
    rcases eCongr.surjective θ with ⟨θ', rfl⟩
    rcases hMap.2 θ' with ⟨δ, rfl⟩
    exact ⟨δ, rfl⟩

end FibredInGroupoidsMor

end CategoryTheory
