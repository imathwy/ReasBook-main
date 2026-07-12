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

/-- A morphism of commutative-ring-valued presheaves out of `𝒪` sends every section of `𝒮` to a
unit. -/
def SectionsMapToUnits {𝒜 : Cᵒᵖ ⥤ CommRingCat.{max u v}} (η : 𝒪 ⟶ 𝒜) : Prop :=
  ∀ ⦃U : Cᵒᵖ⦄ (s : 𝒮.obj U), IsUnit ((η.app U).hom s.1)

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

/-- The canonical localization morphism sends every distinguished section of `𝒮` to a unit. -/
theorem toLocalizationPresheaf_sectionsMapToUnits :
    𝒮.SectionsMapToUnits 𝒮.toLocalizationPresheaf := by
  intro U s
  change IsUnit ((algebraMap (𝒪.obj U) (𝒮.localizationPresheaf.obj U)) s.1)
  simpa using IsLocalization.map_units (𝒮.localizationPresheaf.obj U) s

private noncomputable def localizationPresheafLift {𝒜 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.SectionsMapToUnits η) :
    𝒮.localizationPresheaf ⟶ 𝒜 where
  app U :=
    let g := (η.app U).hom
    let hg : ∀ s : 𝒮.obj U, IsUnit (g s.1) := fun s ↦ hη s
    CommRingCat.ofHom (IsLocalization.lift hg)
  naturality {U V} f := by
    let gU := (η.app U).hom
    let hgU : ∀ s : 𝒮.obj U, IsUnit (gU s.1) := fun s ↦ hη s
    let gV := (η.app V).hom
    let hgV : ∀ s : 𝒮.obj V, IsUnit (gV s.1) := fun s ↦ hη s
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (𝒮.obj U)
    apply RingHom.ext
    intro x
    change IsLocalization.lift hgV
        (((𝒮.localizationPresheaf.map f).hom)
          ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x)) =
      (𝒜.map f).hom
        ((IsLocalization.lift hgU) ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x))
    let _ : Algebra (𝒪.obj U) (𝒮.localizationPresheaf.obj U) := by
      change Algebra (𝒪.obj U) (Localization (𝒮.obj U))
      infer_instance
    let _ : IsLocalization (𝒮.obj U) (𝒮.localizationPresheaf.obj U) := by
      change IsLocalization (𝒮.obj U) (Localization (𝒮.obj U))
      infer_instance
    let _ : Algebra (𝒪.obj V) (𝒮.localizationPresheaf.obj V) := by
      change Algebra (𝒪.obj V) (Localization (𝒮.obj V))
      infer_instance
    let _ : IsLocalization (𝒮.obj V) (𝒮.localizationPresheaf.obj V) := by
      change IsLocalization (𝒮.obj V) (Localization (𝒮.obj V))
      infer_instance
    have hmap :
        ((𝒮.localizationPresheaf.map f).hom
          ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x)) =
        (algebraMap (𝒪.obj V) (Localization (𝒮.obj V))) ((𝒪.map f).hom x) := by
      change IsLocalization.map (Localization (𝒮.obj V)) (𝒪.map f).hom (𝒮.map f)
          ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x) =
        (algebraMap (𝒪.obj V) (Localization (𝒮.obj V))) ((𝒪.map f).hom x)
      simpa using
        congrArg
          (fun α : 𝒪.obj U →+* Localization (𝒮.obj V) ↦ α x)
          (IsLocalization.map_comp (𝒮.map f))
    rw [hmap]
    have hleft :
        (IsLocalization.lift hgV)
            ((algebraMap (𝒪.obj V) (Localization (𝒮.obj V))) ((𝒪.map f).hom x)) =
          gV ((𝒪.map f).hom x) :=
      IsLocalization.lift_eq hgV ((𝒪.map f).hom x)
    have hright :
        (IsLocalization.lift hgU)
            ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x) =
          gU x :=
      IsLocalization.lift_eq hgU x
    have hnat : gV ((𝒪.map f).hom x) = (𝒜.map f).hom (gU x) := by
      simpa [gU, gV] using congrArg (fun α : 𝒪.obj U ⟶ 𝒜.obj V ↦ α.hom x) (η.naturality f)
    calc
      (IsLocalization.lift hgV)
          ((algebraMap (𝒪.obj V) (Localization (𝒮.obj V))) ((𝒪.map f).hom x)) =
        gV ((𝒪.map f).hom x) := hleft
      _ = (𝒜.map f).hom (gU x) := hnat
      _ = (𝒜.map f).hom ((IsLocalization.lift hgU)
            ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x)) := by
          rw [hright]

/-- Any morphism of commutative-ring-valued presheaves out of `𝒪` that inverts `𝒮` factors
uniquely through the canonical localization map. -/
theorem existsUnique_localizationPresheafLift
    {𝒜 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.SectionsMapToUnits η) :
    ∃! γ : 𝒮.localizationPresheaf ⟶ 𝒜,
      𝒮.toLocalizationPresheaf ≫ γ = η := by
  refine ⟨localizationPresheafLift 𝒮 η hη, ?_, ?_⟩
  · ext U x
    let g := (η.app U).hom
    let hg : ∀ s : 𝒮.obj U, IsUnit (g s.1) := fun s ↦ hη s
    change IsLocalization.lift hg
        ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x) = g x
    exact IsLocalization.lift_eq hg x
  · intro γ hγ
    ext U y
    have hγU :
        (γ.app U).hom = ((localizationPresheafLift 𝒮 η hη).app U).hom := by
      apply IsLocalization.ringHom_ext (𝒮.obj U)
      apply RingHom.ext
      intro x
      have hx := congrArg (fun α : 𝒪 ⟶ 𝒜 ↦ ((α.app U).hom) x) hγ
      change (γ.app U).hom (((𝒮.toLocalizationPresheaf.app U).hom) x) = ((η.app U).hom) x at hx
      refine hx.trans ?_
      let g := (η.app U).hom
      let hg : ∀ s : 𝒮.obj U, IsUnit (g s.1) := fun s ↦ hη s
      change g x = IsLocalization.lift hg ((algebraMap (𝒪.obj U) (Localization (𝒮.obj U))) x)
      simpa [g] using (IsLocalization.lift_eq hg x).symm
    simpa using congrArg (fun δ : Localization (𝒮.obj U) →+* 𝒜.obj U ↦ δ y) hγU

end SubmonoidPresheaf

end Presheaf
end CategoryTheory

namespace LocalizedPresheaf

/- Textbook notation for the localization presheaf `𝒮⁻¹𝒪`. -/
scoped macro:max 𝒮:term noWs "⁻¹" 𝒪:term : term => do
  let _ := 𝒪
  `(CategoryTheory.Presheaf.SubmonoidPresheaf.localizationPresheaf $𝒮)

end LocalizedPresheaf
