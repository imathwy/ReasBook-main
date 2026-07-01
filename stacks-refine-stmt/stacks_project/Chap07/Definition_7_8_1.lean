import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap07.Definition_7_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe w₁ v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SemiRepresentableFamily
namespace Over

/- Domain-style sampling for Definition 7.8.1:
- primary domain: families of arrows with fixed target, modeled by semi-representable families in
  slice categories and transported along `Over.map`;
- inspected owner declarations:
  `Definition_7_6_1`'s owner recall `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `SemiRepresentableFamily.Hom`,
  `SemiRepresentableFamily.map`,
  `Over.map`;
- best owner abstraction: the chapter owner `SemiRepresentableFamily.Over U`, together with its
  canonical indexed-arrow constructor `SemiRepresentableFamily.Over.ofArrows` and the induced
  functor `SemiRepresentableFamily.map (Over.map f)` on families when the target changes along
  `f`;
- primitive data: an indexed family of arrows into a fixed target, packaged as an object of
  `SemiRepresentableFamily.Over U`;
- derived API: same-target refinement as existence of a canonical owner morphism, and the
  cross-target change-of-target morphism type obtained directly from
  `SemiRepresentableFamily.map (Over.map f)`.

Source/core/bridge triage:
- `source-facing`: `Refines`;
- `core/canonical`: `SemiRepresentableFamily.Hom`, `SemiRepresentableFamily.Over`, and
  `SemiRepresentableFamily.map`;
- `bridge/view`: the upstream constructor `SemiRepresentableFamily.Over.ofArrows`, turning an
  indexed family of arrows into the owner object `SemiRepresentableFamily.Over U`.
-/

/- Companion owner recall: same-target refinement is governed by the canonical componentwise
morphism object on semi-representable families; the indexed-arrow presentation remains only the
upstream bridge `SemiRepresentableFamily.Over.ofArrows`. -/
recall SemiRepresentableFamily.Hom

/- Definition 7.8.1, cross-target owner recall: for `f : U ⟶ V`, a morphism of fixed-target
families from `𝒰 : SemiRepresentableFamily.Over U` to `𝒱 : SemiRepresentableFamily.Over V` is
canonically a morphism `((map (Over.map f)).obj 𝒰 ⟶ 𝒱)` in
`SemiRepresentableFamily (CategoryTheory.Over V)`. -/
section

variable {U V : C} (f : U ⟶ V) (𝒰 : Over U) (𝒱 : Over V)

#check ((map (Over.map f)).obj 𝒰 ⟶ 𝒱)

end

/-- Definition 7.8.1: a family `𝒰` refines `𝒱` when there is a morphism in the canonical category
`SemiRepresentableFamily.Over U` from `𝒰` to `𝒱`. -/
abbrev Refines {U : C} (𝒰 𝒱 : Over U) : Prop :=
  Nonempty (𝒰 ⟶ 𝒱)

-- Proof sketch: unfold `Refines`; this is the defining equivalence for the abbreviation.
/-- Refinement is exactly the existence of a morphism between the corresponding fixed-target
families. -/
theorem refines_iff_nonempty_hom {U : C} {𝒰 𝒱 : Over U} :
    Refines 𝒰 𝒱 ↔ Nonempty (𝒰 ⟶ 𝒱) := sorry

end Over
end SemiRepresentableFamily

end CategoryTheory
