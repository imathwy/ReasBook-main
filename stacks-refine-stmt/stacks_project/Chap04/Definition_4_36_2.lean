import Mathlib
import stacks_project.Chap04.Definition_4_32_1
import stacks_project.Chap04.Lemma_4_33_8

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open BasedFunctor
open Opposite
open scoped CategoryTheory.Bicategory
open scoped BasedFunctor
variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

open Pseudofunctor

/- Domain-style sampling for Definition 4.36.2:
- primary domain: fibred categories over a fixed base and split models coming from contravariant
  `Cat`-valued functors via the co-Grothendieck construction.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.toPseudofunctor'`,
  `CoGrothendieck.forget`,
  `BasedCategory.ofFunctor`,
  `BasedFunctor.IsEquivalenceOverBase`.
- best owner abstraction: the source-facing predicate `Functor.IsSplitFibredCategory p`, built
  directly from the canonical co-Grothendieck model and the canonical category-over-base owner
  `BasedCategory`, with the comparison expressed as an isomorphism in `Cat/C`.
- primitive data: the functor `p : S ⥤ C` together with a contravariant functor
  `F : Cᵒᵖ ⥤ Cat` and an isomorphism over `C` from `p` to the associated co-Grothendieck model.
- derived API: the induced fibredness of `p`, transported from the canonical fibredness instance on
  `Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')` via the isomorphism's induced
  equivalence-over-base.

Source/core/bridge triage:
- `source-facing`: `Functor.IsSplitFibredCategory p`.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: `Functor.toPseudofunctor'`, `Pseudofunctor.CoGrothendieck.forget`, and the
  canonical isomorphism in `Cat/C`, together with the transport theorem
  `BasedFunctor.isFibered_iff_of_equivalence_over_base` applied to its forward morphism. -/

/-- Definition 4.36.2: a functor `p : S ⥤ C` is a split fibred category if it is isomorphic over
`C` to the co-Grothendieck construction attached to a contravariant category-valued functor on
`C`; the fibredness of `p` is then derived from this model. -/
class IsSplitFibredCategory (p : S ⥤ C) : Prop where
  existsCoGrothendieckModel :
    ∃ (F : Cᵒᵖ ⥤ Cat.{v₂, u₂})
      (e : BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))
      (eInv : BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')) ⥤ᵇ
        BasedCategory.ofFunctor p),
      e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
        eInv ⋙ e = 𝟙 (BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))

namespace IsSplitFibredCategory

theorem isFibered {p : S ⥤ C} (hp : Functor.IsSplitFibredCategory p) : p.IsFibered := by
  rcases hp.existsCoGrothendieckModel with ⟨F, e, eInv, hη, hε⟩
  let he : e.IsEquivalenceOverBase :=
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      eInv
      (eqToIso hη.symm)
      (eqToIso hε)
  exact
    (isFibered_iff_of_equivalence_over_base e he).2
      (inferInstance : (CoGrothendieck.forget (F.toPseudofunctor')).IsFibered)

end IsSplitFibredCategory

instance (p : S ⥤ C) [Functor.IsSplitFibredCategory p] : p.IsFibered :=
  IsSplitFibredCategory.isFibered inferInstance

end Functor

end CategoryTheory
