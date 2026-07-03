import Mathlib
import StacksProject_2024.Chap13.Definition_13_14_10

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']

/- Domain-style sampling for Lemma 13.14.14:
- primary domain: global pointwise existence of derived functors from source-facing computation
  objects connected by morphisms in the localization class;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctor`,
  `Functor.HasPointwiseLeftDerivedFunctor`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the core/canonical owners are
  `Functor.HasPointwiseRightDerivedFunctor` and `Functor.HasPointwiseLeftDerivedFunctor`; the
  source-facing hypotheses use `ComputesRightDerivedAt` and `ComputesLeftDerivedAt`, whose only
  primitive data relevant here is the inherited pointwise-definedness owner at the chosen object,
  and transport along a morphism in `S` should therefore reuse the canonical owner theorems
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem` and
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem` rather than a chapter-local wrapper;
- primitive data: for each object `X`, an `S`-morphism connecting `X` to an object `X'` together
  with a proof that `X'` computes the corresponding derived functor;
- derived API: the everywhere-definedness predicates on `F`.

Source/core/bridge triage:
- `source-facing`: the Stacks existential hypotheses with objects computing the right or left
  derived functor;
- `core/canonical`: `Functor.HasPointwiseRightDerivedFunctor`,
  `Functor.HasPointwiseLeftDerivedFunctor`, and the owner transport equivalences
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem` and
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`;
- `bridge/view`: the two theorems in this file, which should remain thin existential-to-owner
  bridges.
-/

-- Proof sketch: for each `X`, choose `s : X ⟶ X'` in `S` with `X'` computing the right derived
-- functor. The computation hypothesis restricts to the core pointwise right-derived owner at `X'`,
-- and
-- `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem` transports this property along `s` back
-- to `X`.
/-- Lemma 13.14.14 (1): if every object admits a morphism in `S` to an object computing the
pointwise right derived functor of `F`, then the right derived functor is everywhere defined. -/
theorem hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) [S.ContainsIdentities]
    (h :
      ∀ X : 𝒟, ∃ (X' : 𝒟) (s : X ⟶ X'), S s ∧ F.ComputesRightDerivedAt S X') :
    F.HasPointwiseRightDerivedFunctor S := sorry

-- Proof sketch: for each `X`, choose `s : X' ⟶ X` in `S` with `X'` computing the left derived
-- functor. The computation hypothesis restricts to the core pointwise left-derived owner at `X'`,
-- and
-- `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem` transports this property along `s` to
-- `X`.
/-- Lemma 13.14.14 (2): if every object receives a morphism in `S` from an object computing the
pointwise left derived functor of `F`, then the left derived functor is everywhere defined. -/
theorem hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) [S.ContainsIdentities]
    (h :
      ∀ X : 𝒟, ∃ (X' : 𝒟) (s : X' ⟶ X), S s ∧ F.ComputesLeftDerivedAt S X') :
    F.HasPointwiseLeftDerivedFunctor S := sorry

end

end Functor

end CategoryTheory
