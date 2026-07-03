import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory
namespace Presheaf

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/- Domain-style sampling for 18.44.1.1:
- primary domain: localization of commutative-ring-valued presheaves on a Grothendieck site;
- sampled owner declarations:
  `TopCat.Presheaf.SubmonoidPresheaf`,
  `TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf`,
  `TopCat.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf`,
  `CategoryTheory.Presheaf.IsSheaf`;
- best owner abstraction: the presheaf-level core owner should be a site-level
  `Presheaf.SubmonoidPresheaf`, with localization and its canonical comparison morphism derived
  from that owner;
- primitive data: a commutative-ring-valued presheaf `𝒪` and, for each object, a multiplicative
  submonoid compatible with restriction;
- derived API: the localization presheaf `𝒮.localizationPresheaf` and the canonical map
  `𝒮.toLocalizationPresheaf`.

Source/core/bridge triage:
- `source-facing`: the objectwise localized presheaf `𝒮⁻¹𝒪`;
- `core/canonical`: the owner `Presheaf.SubmonoidPresheaf 𝒪`;
- `bridge/view`: later sheafification constructions built from `𝒮.localizationPresheaf`.

This file therefore owns the presheaf-level localization data; downstream sheaf files should reuse
it instead of redefining the same owner inside a sheaf namespace. -/

/-- A multiplicative subpresheaf of a presheaf of commutative rings on a site. -/
structure SubmonoidPresheaf (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) where
  /-- The multiplicative subset chosen in each object of the site. -/
  obj : ∀ U : Cᵒᵖ, Submonoid (𝒪.obj U)
  /-- Restriction maps preserve the chosen multiplicative subsets. -/
  map : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V),
    obj U ≤ (obj V).comap (𝒪.map f).hom

namespace SubmonoidPresheaf

variable (𝒮 : SubmonoidPresheaf 𝒪)

/-- The objectwise localization presheaf `𝒮⁻¹𝒪`. -/
protected noncomputable def localizationPresheaf : Cᵒᵖ ⥤ CommRingCat.{max u v} where
  obj U := CommRingCat.of <| Localization (𝒮.obj U)
  map {_ _} f := CommRingCat.ofHom <| IsLocalization.map _ (𝒪.map f).hom (𝒮.map f)
  map_id U := by
    simp_rw [𝒪.map_id]
    ext x
    exact IsLocalization.map_id x
  map_comp {U V W} f g := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [𝒪.map_comp]
    ext : 1
    dsimp
    rw [IsLocalization.map_comp_map]

set_option quotPrecheck false in
set_option linter.unusedVariables false in
local notation:max 𝒮 "⁻¹ " 𝒪 => 𝒮.localizationPresheaf

instance (U : Cᵒᵖ) : Algebra (𝒪.obj U) ((𝒮⁻¹ 𝒪).obj U) :=
  inferInstanceAs <| Algebra (𝒪.obj U) (Localization (𝒮.obj U))

instance (U : Cᵒᵖ) : IsLocalization (𝒮.obj U) ((𝒮⁻¹ 𝒪).obj U) :=
  inferInstanceAs <| IsLocalization (𝒮.obj U) (Localization (𝒮.obj U))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism from `𝒪` to the localization presheaf `𝒮⁻¹𝒪`. -/
def toLocalizationPresheaf : 𝒪 ⟶ 𝒮⁻¹ 𝒪 where
  app U := CommRingCat.ofHom <| algebraMap (𝒪.obj U) (Localization <| 𝒮.obj U)
  naturality {_ _} f := CommRingCat.hom_ext <| (IsLocalization.map_comp (𝒮.map f)).symm

end SubmonoidPresheaf

end Presheaf
end CategoryTheory

namespace LocalizedPresheaf

/- Textbook notation for the localization presheaf `𝒮⁻¹𝒪`. -/
scoped macro:max 𝒮:term noWs "⁻¹" 𝒪:term : term => do
  let _ := 𝒪
  `(CategoryTheory.Presheaf.SubmonoidPresheaf.localizationPresheaf $𝒮)

end LocalizedPresheaf
