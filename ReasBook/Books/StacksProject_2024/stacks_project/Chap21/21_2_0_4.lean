import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.SiteHigherDirectImageCore

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped CategoryTheory.Sheaf

noncomputable section

universe v u

namespace CategoryTheory
namespace Sheaf

/- Domain-style sampling for 21.2.0.4:
- primary domain: higher direct images of abelian sheaves along a continuous functor of sites;
- sampled owner API:
  `CategoryTheory.Sheaf.higherDirectImageFunctor`,
  `CategoryTheory.Sheaf.higherDirectImage`,
  `CategoryTheory.Functor.sheafPushforwardContinuous`,
  `CategoryTheory.Functor.rightDerived`,
  `CategoryTheory.Functor.Additive`;
- best owner abstraction: `CategoryTheory.Sheaf.higherDirectImage`, with functor-level companion
  `CategoryTheory.Sheaf.higherDirectImageFunctor`;
- primitive data: a continuous functor of sites `u : D ⥤ C`, an abelian sheaf
  `F : Sheaf JC AddCommGrpCat`, and a degree `i : ℕ`;
- derived API: the source-facing notation `R^{i}_[u](F)` for the right-derived pushforward object,
  together with its functor-level owner `higherDirectImageFunctor u i`.

Source/core/bridge triage:
- `source-facing`: the higher direct image of an abelian sheaf along a morphism of sites;
- `core/canonical`: `CategoryTheory.Sheaf.higherDirectImageFunctor` and
  `CategoryTheory.Sheaf.higherDirectImage`;
- `bridge/view`: the notation `R^{i}_[u](F)` and the underlying identification with the
  right-derived pushforward functor.

This item adds no new mathematical data beyond the canonical Chapter 21 higher-direct-image owner
already introduced in `SiteHigherDirectImageCore`. The refined entry should therefore recall that
owner directly instead of duplicating the later injective-resolution comparison theorem from
`21_2_0_7`. -/

/- 21.2.0.4: for a continuous functor of sites `u : D ⥤ C`, the `i`-th higher direct image of an
abelian sheaf `F` is the right-derived pushforward object `R^{i}_[u](F)`, canonically owned by
`CategoryTheory.Sheaf.higherDirectImage`. -/
recall CategoryTheory.Sheaf.higherDirectImage

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [Functor.IsContinuous u JD JC]
variable [HasSheafify JC AddCommGrpCat.{v}] [HasSheafify JD AddCommGrpCat.{v}]
variable [HasInjectiveResolutions (Sheaf JC AddCommGrpCat.{v})]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC)]
variable (F : Sheaf JC AddCommGrpCat.{v}) (i : ℕ)

/- Functor-level companion: the `i`-th higher direct image is the right-derived pushforward
functor on abelian sheaves. -/
#check
  (higherDirectImageFunctor u i :
    Sheaf JC AddCommGrpCat.{v} ⥤ Sheaf JD AddCommGrpCat.{v})

/- Source-facing specialization: the notation `R^{i}_[u](F)` exposes the higher direct image as
the object of the corresponding derived pushforward functor. -/
#check (R^{i}_[u](F) : Sheaf JD AddCommGrpCat.{v})

end

end Sheaf
end CategoryTheory
