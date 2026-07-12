import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.Tactic.Recall

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂} [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
variable (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) (X : 𝒟)

/-
Domain-style sampling for Definition 13.14.2:
- primary domain: pointwise derived functors with respect to a localization morphism property;
- relevant owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff`;
- best owner abstraction: the pointwise derived-functor existence predicates already owned by
  mathlib, not a parallel local alias;
- primitive data: the Prop-valued owner saying the pointwise derived functor is defined at `X`;
- derived API: the upstream colimit/limit characterizations of the corresponding comma diagrams.

Source/core/bridge triage:
- `source-facing`: the source statement that the right or left derived functor is defined at `X`;
- `core/canonical`: `Functor.HasPointwiseRightDerivedFunctorAt` and
  `Functor.HasPointwiseLeftDerivedFunctorAt`;
- `bridge/view`: `Functor.hasPointwiseRightDerivedFunctorAt_iff` and
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff`.
-/

/- Definition 13.14.2 (1): saying that the right derived functor of `F : 𝒟 ⥤ 𝒟'` with respect
to `S` is defined at `X` is exactly the canonical owner
`F.HasPointwiseRightDerivedFunctorAt S X`. -/
recall HasPointwiseRightDerivedFunctorAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) (X : 𝒟) : Prop

/- Definition 13.14.2 (2): saying that the left derived functor of `F : 𝒟 ⥤ 𝒟'` with respect
to `S` is defined at `X` is exactly the canonical owner
`F.HasPointwiseLeftDerivedFunctorAt S X`. -/
recall HasPointwiseLeftDerivedFunctorAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) (X : 𝒟) : Prop

end

end Functor

end CategoryTheory
