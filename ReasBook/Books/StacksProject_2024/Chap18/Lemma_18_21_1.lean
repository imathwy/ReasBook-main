import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v w

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Lemma 18.21.1:
- primary domain: localization of a topos at an object via the slice adjunction, together with the
  induced adjunction on sheaves of modules in the representable localization case;
- sampled owner declarations:
  `Over.forgetAdjStar`,
  `Over.star_obj_left`,
  `Over.star_obj_hom`,
  `SheafOfModules.overPushforwardOverAdj`;
- best owner abstraction: `Over.forgetAdjStar` for the topos-level localization and
  `SheafOfModules.overPushforwardOverAdj` for the module-level representable localization;
- primitive data: a sheaf `ℱ` for the slice-localization owner;
- derived API: the forgetful functor `Over.forget ℱ` and the objectwise descriptions
  `Over.star_obj_left ℱ`, `Over.star_obj_hom ℱ`.

Source/core/bridge triage:
- `source-facing`: the textbook identification of localization at `ℱ` with the slice topos;
- `core/canonical`: `Over.forgetAdjStar`;
- `bridge/view`: `Over.forget ℱ`, `Over.star_obj_left ℱ`, and `Over.star_obj_hom ℱ`.
-/

/- Lemma 18.21.1: localization of the topos `Sh(C)` at a sheaf `ℱ` is the slice topos
`Sh(C)/ℱ`, and the canonical localization morphism has inverse-image functor `Over.star ℱ`
and lower-shriek functor `Over.forget ℱ`. This is the canonical topos-level localization used for
the ringed-topos statement. -/
recall Over.forgetAdjStar

/- Companion recall: on sheaves of sets, the functor `j_{ℱ!}` is the slice forgetful functor
`Sh(C)/ℱ ⥤ Sh(C)`. -/
#check Over.forget ℱ

/- Companion recall: the inverse-image functor sends a sheaf `ℋ` to the slice object over `ℱ`
whose underlying sheaf is `ℱ ⨯ ℋ`, matching the textbook notation `ℋ_ℱ`. -/
#check Over.star_obj_left ℱ

/- Companion recall: the structure morphism of `ℋ_ℱ` is the projection `ℱ ⨯ ℋ ⟶ ℱ`. -/
#check Over.star_obj_hom ℱ

end

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (x : C)

/- Domain-style sampling for the representable localization companion:
- primary domain: sheaves of modules over the localized slice site `J.over x`;
- sampled owner declarations:
  `SheafOfModules.pushforwardOver`,
  `SheafOfModules.overPushforwardOverAdj`,
  the left-adjoint instance on `SheafOfModules.pushforward (𝟙 (R.over x))`;
- best owner abstraction: `SheafOfModules.overPushforwardOverAdj`;
- primitive data: the ring sheaf `R` and the object `x : C`;
- derived API: the left-adjoint instance on `SheafOfModules.pushforward (𝟙 (R.over x))`.

Source/core/bridge triage:
- `source-facing`: the representable module-localization adjunction used to compare with the slice
  localization of `Lemma 18.21.1`;
- `core/canonical`: `SheafOfModules.overPushforwardOverAdj`;
- `bridge/view`: the induced `IsLeftAdjoint` instance.
-/

/- Companion recall: in the representable localization case used in the proof, the module-level
localization adjunction is the standard adjunction for sheaves of modules over `R.over x`. -/
recall SheafOfModules.overPushforwardOverAdj

/- Companion recall: equivalently, the corresponding module-theoretic inverse-image functor is a
left adjoint in the representable case. -/
#check (inferInstance : (SheafOfModules.pushforward (𝟙 (R.over x))).IsLeftAdjoint)

end
