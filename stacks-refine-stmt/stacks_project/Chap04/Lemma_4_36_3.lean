import Mathlib
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap04.Definition_4_36_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Fiber
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/- Domain-style sampling for Lemma 4.36.3:
- primary domain: split fibred categories, chosen pullback systems on standard fibers, and the
  canonical pseudofunctor/co-Grothendieck bridge.
- inspected owner-level declarations:
  `PullbackChoice`,
  `PullbackChoice.pullbackFunctor`,
  `PullbackChoice.pullbackCompIso`,
  `PullbackChoice.pullbackIdIso`,
  `Functor.IsSplitFibredCategory`.
- best owner abstraction: the source-facing data is a chosen pullback system `hc : PullbackChoice p`
  together with strict composition for its pullback functors; the split side is owned by the
  canonical predicate `p.IsSplitFibredCategory`.
- primitive data: the chosen pullback system `hc : PullbackChoice p`.
- derived API: the composition-on-the-nose equations
  `hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g`, and separately the
  optional strict unit normalization `hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U)`.

Source/core/bridge triage:
- `source-facing`: the composition-only criterion in
  `Functor.isSplit_iff_exists_pullbackChoice`.
- `core/canonical`: `p.IsSplitFibredCategory`.
- `bridge/view`: a normalized strict-unit pullback system, recorded only in the companion theorem
  `Functor.isSplit_iff_exists_pullbackChoice_strict`. -/

-- Proof sketch: if `p` is split in the sense of Definition 4.36.2, use the owner method
-- `Functor.IsSplitFibredCategory.existsCoGrothendieckModel` to identify it over `C` with the
-- co-Grothendieck construction attached to a strict functor `F : Cᵒᵖ ⥤ Cat`, whose pullback
-- functors satisfy strict composition by ordinary functoriality. Conversely, a chosen pullback
-- system with strict composition determines the source-facing contravariant action on the fibers,
-- and hence a split model over `C`.
/-- Lemma 4.36.3: a functor `p : S ⥤ C` is split in the sense of Definition 4.36.2 if and only if
there is a choice of pullbacks for which pullback along a composite `g ≫ f` is exactly the
composite of the pullback functors along `f` and `g`. -/
theorem Functor.isSplit_iff_exists_pullbackChoice
    (p : S ⥤ C) :
    p.IsSplitFibredCategory ↔
      ∃ hc : PullbackChoice p,
        ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
          hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g := sorry

-- Proof sketch: the stronger strict-unit normalization is a harmless companion sharpening of the
-- source-facing composition criterion above. It is useful when one wants an honest functor
-- `Cᵒᵖ ⥤ Cat` rather than only the source-level split structure.
/-- Companion normalization: the pullback system in Lemma 4.36.3 may moreover be chosen so that
pullback along identities is exactly the identity functor on each standard fiber. -/
theorem Functor.isSplit_iff_exists_pullbackChoice_strict
    (p : S ⥤ C) :
    p.IsSplitFibredCategory ↔
      ∃ hc : PullbackChoice p,
        (∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U)) ∧
        ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
          hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g := sorry

end CategoryTheory
