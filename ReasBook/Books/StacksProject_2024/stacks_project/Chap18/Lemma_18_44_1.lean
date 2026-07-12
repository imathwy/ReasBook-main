import Mathlib
import StacksProject_2024.Chap18.«18_44_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped LocalizedPresheaf

noncomputable section

universe u v

namespace LocalizedPresheaf

/- Textbook notation for sheafification of a commutative-ring-valued presheaf on a site. In
particular, it gives the source-facing sheafified localization notation `(𝒮⁻¹𝒪)^#[J]`. Since
the site is not inferable from the presheaf, we keep it explicit in `𝒪^#[J]`. -/
set_option quotPrecheck false in
scoped macro:max 𝒪:term noWs "^#[" J:term "]" : term => do
  `((CategoryTheory.presheafToSheaf $J CommRingCat).obj $𝒪)

end LocalizedPresheaf

namespace CategoryTheory
namespace Presheaf
namespace SubmonoidPresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.44.1:
- primary domain: localization of presheaves and sheaves of commutative rings on a Grothendieck
  site;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizationPresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf`,
  `presheafToSheaf`,
  `sheafifyMap`,
  `sheafificationIso`,
  `sheafifyLift`,
  `toSheafify_sheafifyLift`,
  `sheafifyLift_unique`,
  `IsLocalization.lift`;
- best owner abstraction: on the source-facing side, the public owner should be the
  submonoid-presheaf together with its localization presheaf and canonical map; on the sheaf side,
  the canonical owner is `(presheafToSheaf J CommRingCat.{max u v}).obj`, with the source-facing
  notation `(𝒮⁻¹𝒪)^#[J]`; `sheafificationIso` supplies the canonical comparison from the given
  sheaf into the sheafification stage, `IsLocalization.lift` supplies the objectwise localized
  presheaf map, and `sheafifyLift` is the canonical sheafified lift;
- primitive data: a presheaf of commutative rings and a compatible multiplicative subset on each
  object of the site;
- derived API: the localization presheaf, the canonical map into it, the notation
  `(𝒮⁻¹𝒪)^#[J]`, and the sheafified universal-property lift together with its factorization and
  uniqueness theorems.

Source/core/bridge triage:
- `source-facing`: the site-level localization presheaf and the universal property of its
  sheafification;
  - `core/canonical`: the owner pair `Presheaf.SubmonoidPresheaf.localizationPresheaf` and
  `Presheaf.SubmonoidPresheaf.toLocalizationPresheaf`, together with
  `(presheafToSheaf J CommRingCat.{max u v}).obj`, `sheafifyLift`, and `IsLocalization.lift`;
- `bridge/view`: the canonical morphism from the given sheaf `𝒪` to the sheafification of
  `𝒮.localizationPresheaf`, and the induced canonical lift into any sheaf that inverts `𝒮`.

This file is therefore now purely the sheafification bridge: the presheaf-level owner lives in
`CategoryTheory.Presheaf.SubmonoidPresheaf`, and the declarations here extend that owner by the
sheafified canonical map and its universal-property lift API. -/

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒮 : SubmonoidPresheaf 𝒪.obj)

/-- The canonical morphism of sheaves of commutative rings from `𝒪` to the sheafification of
`𝒮⁻¹𝒪`, written `(𝒮⁻¹𝒪)^#[J]`. -/
noncomputable def toSheafifiedLocalizationPresheaf :
    𝒪 ⟶ (𝒮⁻¹𝒪)^#[J] :=
  (sheafificationIso 𝒪).hom ≫
    (presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf

/-- Bridge/view: a morphism of sheaves of commutative rings out of `𝒪` inverts `𝒮` when its
underlying presheaf morphism sends every local section of `𝒮` to a unit. -/
abbrev Inverts {𝒜 : Sheaf J CommRingCat.{max u v}} (η : 𝒪 ⟶ 𝒜) : Prop :=
  𝒮.SectionsMapToUnits η.hom

private noncomputable def localizationPresheafLift {𝒜 : Sheaf J CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.Inverts η) :
    𝒮.localizationPresheaf ⟶ 𝒜.obj where
  app U :=
    let g := (η.hom.app U).hom
    let hg : ∀ s : 𝒮.obj U, IsUnit (g s.1) := fun s ↦ hη s
    CommRingCat.ofHom (IsLocalization.lift hg)
  naturality {U V} f := by
    -- Compare the two ring homomorphisms after restricting to the original sections.
    let gU := (η.hom.app U).hom
    let hgU : ∀ s : 𝒮.obj U, IsUnit (gU s.1) := fun s ↦ hη s
    let gV := (η.hom.app V).hom
    let hgV : ∀ s : 𝒮.obj V, IsUnit (gV s.1) := fun s ↦ hη s
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (𝒮.obj U)
    apply RingHom.ext
    intro x
    change IsLocalization.lift hgV
        (((𝒮.localizationPresheaf.map f).hom)
          ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) x)) =
      (𝒜.obj.map f).hom
        ((IsLocalization.lift hgU) ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) x))
    let _ : Algebra (𝒪.obj.obj U) (𝒮.localizationPresheaf.obj U) := by
      change Algebra (𝒪.obj.obj U) (Localization (𝒮.obj U))
      infer_instance
    let _ : IsLocalization (𝒮.obj U) (𝒮.localizationPresheaf.obj U) := by
      change IsLocalization (𝒮.obj U) (Localization (𝒮.obj U))
      infer_instance
    let _ : Algebra (𝒪.obj.obj V) (𝒮.localizationPresheaf.obj V) := by
      change Algebra (𝒪.obj.obj V) (Localization (𝒮.obj V))
      infer_instance
    let _ : IsLocalization (𝒮.obj V) (𝒮.localizationPresheaf.obj V) := by
      change IsLocalization (𝒮.obj V) (Localization (𝒮.obj V))
      infer_instance
    have hmap :
        ((𝒮.localizationPresheaf.map f).hom
          ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) x)) =
        (algebraMap (𝒪.obj.obj V) (Localization (𝒮.obj V))) ((𝒪.obj.map f).hom x) := by
      change IsLocalization.map (Localization (𝒮.obj V)) (𝒪.obj.map f).hom (𝒮.map f)
          ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) x) =
        (algebraMap (𝒪.obj.obj V) (Localization (𝒮.obj V))) ((𝒪.obj.map f).hom x)
      simpa using
        congrArg
          (fun α : 𝒪.obj.obj U →+* Localization (𝒮.obj V) ↦ α x)
          (IsLocalization.map_comp (𝒮.map f))
    rw [hmap]
    have hleft :
        (IsLocalization.lift hgV)
            ((algebraMap (𝒪.obj.obj V) (Localization (𝒮.obj V))) ((𝒪.obj.map f).hom x)) =
          gV ((𝒪.obj.map f).hom x) :=
      IsLocalization.lift_eq hgV ((𝒪.obj.map f).hom x)
    have hright :
        (IsLocalization.lift hgU)
            ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) x) =
          gU x :=
      IsLocalization.lift_eq hgU x
    have hnat : gV ((𝒪.obj.map f).hom x) = (𝒜.obj.map f).hom (gU x) := by
      simpa [gU, gV] using congrArg
        (fun α : 𝒪.obj.obj U ⟶ 𝒜.obj.obj V ↦ α.hom x) (η.hom.naturality f)
    calc
      (IsLocalization.lift hgV)
          ((algebraMap (𝒪.obj.obj V) (Localization (𝒮.obj V))) ((𝒪.obj.map f).hom x)) =
        gV ((𝒪.obj.map f).hom x) := hleft
      _ = (𝒜.obj.map f).hom (gU x) := hnat
      _ = (𝒜.obj.map f).hom ((IsLocalization.lift hgU)
            ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) x)) := by
          rw [hright]

@[reassoc]
private theorem toLocalizationPresheaf_comp_localizationPresheafLift
    {𝒜 : Sheaf J CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.Inverts η) :
    𝒮.toLocalizationPresheaf ≫ 𝒮.localizationPresheafLift η hη = η.hom := by
  ext U x
  let g := (η.hom.app U).hom
  let hg : ∀ s : 𝒮.obj U, IsUnit (g s.1) := fun s ↦ hη s
  change
    IsLocalization.lift hg ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) x) = g x
  exact IsLocalization.lift_eq hg x

private theorem localizationPresheafLift_unique
    {𝒜 : Sheaf J CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.Inverts η)
    (δ : 𝒮.localizationPresheaf ⟶ 𝒜.obj)
    (hδ : 𝒮.toLocalizationPresheaf ≫ δ = η.hom) :
    δ = 𝒮.localizationPresheafLift η hη := by
  ext U y
  have hδU :
      (δ.app U).hom = ((𝒮.localizationPresheafLift η hη).app U).hom := by
    apply IsLocalization.ringHom_ext (𝒮.obj U)
    ext z
    have hz := congrArg (fun f : 𝒪.obj ⟶ 𝒜.obj ↦ ((f.app U).hom) z) hδ
    change ((δ.app U).hom) (((𝒮.toLocalizationPresheaf.app U).hom) z) = ((η.hom.app U).hom) z at hz
    refine hz.trans ?_
    let g := (η.hom.app U).hom
    let hg : ∀ s : 𝒮.obj U, IsUnit (g s.1) := fun s ↦ hη s
    change g z = (IsLocalization.lift hg) ((algebraMap (𝒪.obj.obj U) (Localization (𝒮.obj U))) z)
    simpa [g] using (IsLocalization.lift_eq hg z).symm
  simpa using congrArg (fun f ↦ f y) hδU

/-- Helper for Lemma 18.44.1: the underlying presheaf map of the canonical sheafified
localization morphism is the sheafification unit followed by the sheafified localization map. -/
private theorem toSheafifiedLocalizationPresheaf_hom :
    𝒮.toSheafifiedLocalizationPresheaf.hom =
      CategoryTheory.toSheafify J 𝒪.obj ≫ CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf :=
  rfl

-- Proof sketch: the canonical map `𝒪 ⟶ 𝒮⁻¹𝒪` inverts every section of `𝒮` objectwise; after
-- sheafification, the sheafification adjunction turns objectwise factorization through the
-- localization into a unique sheaf morphism from the sheafification of `𝒮⁻¹𝒪`.
/-- The canonical sheafified localization morphism sends every local section of `𝒮` to a unit. -/
theorem toSheafifiedLocalizationPresheaf_sectionsMapToUnits :
    𝒮.Inverts 𝒮.toSheafifiedLocalizationPresheaf := by
  intro U s
  -- Rewrite the underlying map through the sheafification unit on `𝒮.localizationPresheaf`.
  rw [toSheafifiedLocalizationPresheaf_hom]
  rw [← CategoryTheory.toSheafify_naturality J 𝒮.toLocalizationPresheaf]
  change
    IsUnit
      (((CategoryTheory.toSheafify J 𝒮.localizationPresheaf).app U).hom
        (((𝒮.toLocalizationPresheaf).app U).hom s.1))
  exact IsUnit.map ((CategoryTheory.toSheafify J 𝒮.localizationPresheaf).app U).hom
    (toLocalizationPresheaf_sectionsMapToUnits (𝒮 := 𝒮) s)

/-- The canonical morphism induced by a sheaf map `η : 𝒪 ⟶ 𝒜` that inverts every section of
`𝒮`. -/
noncomputable def sheafifiedLocalizationPresheafLift {𝒜 : Sheaf J CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.Inverts η) :
    (𝒮⁻¹𝒪)^#[J] ⟶ 𝒜 :=
  ⟨sheafifyLift J (𝒮.localizationPresheafLift η hη) 𝒜.property⟩

/-- The canonical sheafified localization lift factors `η` through
`𝒪 ⟶ (𝒮⁻¹𝒪)^#[J]`. -/
theorem toSheafifiedLocalizationPresheaf_comp_sheafifiedLocalizationPresheafLift
    {𝒜 : Sheaf J CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.Inverts η) :
    𝒮.toSheafifiedLocalizationPresheaf ≫ 𝒮.sheafifiedLocalizationPresheafLift η hη = η := by
  -- Compare both maps after transporting them across the sheafification equivalence of `𝒪`.
  rw [toSheafifiedLocalizationPresheaf, Category.assoc]
  have hcomp :
      CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫
          CategoryTheory.sheafifyLift J (𝒮.localizationPresheafLift η hη) 𝒜.property =
        CategoryTheory.sheafifyLift J η.hom 𝒜.property := by
    -- The presheaf factorization through localization sheafifies to the desired lift out of `𝒪`.
    apply CategoryTheory.sheafifyLift_unique J η.hom 𝒜.property
    calc
      CategoryTheory.toSheafify J 𝒪.obj ≫
          CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫
            CategoryTheory.sheafifyLift J (𝒮.localizationPresheafLift η hη) 𝒜.property =
        𝒮.toLocalizationPresheaf ≫
          CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫
            CategoryTheory.sheafifyLift J (𝒮.localizationPresheafLift η hη) 𝒜.property := by
              simpa [Category.assoc] using
                congrArg
                  (fun f : 𝒪.obj ⟶ (presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf ↦
                    f ≫ CategoryTheory.sheafifyLift J (𝒮.localizationPresheafLift η hη)
                      𝒜.property)
                  (CategoryTheory.toSheafify_naturality J 𝒮.toLocalizationPresheaf).symm
      _ = 𝒮.toLocalizationPresheaf ≫ 𝒮.localizationPresheafLift η hη := by
            rw [CategoryTheory.toSheafify_sheafifyLift]
      _ = η.hom := by
            simpa using 𝒮.toLocalizationPresheaf_comp_localizationPresheafLift η hη
  have hη_lift :
      ((sheafificationIso 𝒪).inv ≫ η).hom = CategoryTheory.sheafifyLift J η.hom 𝒜.property := by
    -- The inverse sheafification comparison is the unique map whose pullback is `η.hom`.
    apply CategoryTheory.sheafifyLift_unique J η.hom 𝒜.property
    simpa using congrArg Sheaf.Hom.hom ((sheafificationIso 𝒪).hom_inv_id_assoc η)
  have hpresheaf_hom :
      (((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf) ≫
          𝒮.sheafifiedLocalizationPresheafLift η hη).hom =
        ((sheafificationIso 𝒪).inv ≫ η).hom := by
    -- The sheaf equality is already proved on underlying presheaves.
    simpa [CategoryTheory.sheafifyMap, sheafifiedLocalizationPresheafLift] using
      (hcomp.trans hη_lift.symm)
  have hpresheaf :
      ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf) ≫
          𝒮.sheafifiedLocalizationPresheafLift η hη =
        (sheafificationIso 𝒪).inv ≫ η := by
    ext U x
    exact congrArg (fun f ↦ ((f.app U).hom) x) hpresheaf_hom
  calc
    (sheafificationIso 𝒪).hom ≫
        (((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf) ≫
          𝒮.sheafifiedLocalizationPresheafLift η hη) =
      (sheafificationIso 𝒪).hom ≫ ((sheafificationIso 𝒪).inv ≫ η) := by
          rw [hpresheaf]
    _ = η := by
          simpa [Category.assoc] using (sheafificationIso 𝒪).hom_inv_id_assoc η

/-- Any factorization of `η` through `𝒪 ⟶ (𝒮⁻¹𝒪)^#[J]` agrees with the canonical sheafified
localization lift. -/
theorem sheafifiedLocalizationPresheafLift_unique
    {𝒜 : Sheaf J CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.Inverts η)
    (γ : (𝒮⁻¹𝒪)^#[J] ⟶ 𝒜)
    (hγ : 𝒮.toSheafifiedLocalizationPresheaf ≫ γ = η) :
    γ = 𝒮.sheafifiedLocalizationPresheafLift η hη := by
  have hγ_hom :
      𝒮.toSheafifiedLocalizationPresheaf.hom ≫ γ.hom = η.hom := by
    simpa [Category.assoc] using congrArg (fun f ↦ f.hom) hγ
  have hδγ :
      CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫ γ.hom =
        𝒮.localizationPresheafLift η hη := by
    -- Recover the presheaf-level factorization through `𝒮.localizationPresheaf`.
    apply 𝒮.localizationPresheafLift_unique η hη
    calc
      𝒮.toLocalizationPresheaf ≫
          CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫ γ.hom =
        CategoryTheory.toSheafify J 𝒪.obj ≫
          CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫ γ.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun f : 𝒪.obj ⟶ (presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf ↦
                  f ≫ γ.hom)
                (CategoryTheory.toSheafify_naturality J 𝒮.toLocalizationPresheaf)
      _ = η.hom := by
            simpa [toSheafifiedLocalizationPresheaf_hom, Category.assoc] using hγ_hom
  -- The sheafification lift is unique once its pullback to the presheaf level is fixed.
  ext U x
  simpa [sheafifiedLocalizationPresheafLift] using
    congrArg (fun f ↦ ((f.app U).hom) x)
      (CategoryTheory.sheafifyLift_unique J
        (𝒮.localizationPresheafLift η hη) 𝒜.property γ.hom hδγ)

/-- Lemma 18.44.1: any morphism of sheaves of commutative rings out of `𝒪` that inverts `𝒮`
factors uniquely through the canonical sheafified localization map. -/
theorem existsUnique_sheafifiedLocalizationPresheafLift
    {𝒜 : Sheaf J CommRingCat.{max u v}}
    (η : 𝒪 ⟶ 𝒜)
    (hη : 𝒮.Inverts η) :
    ∃! γ : (𝒮⁻¹𝒪)^#[J] ⟶ 𝒜,
      𝒮.toSheafifiedLocalizationPresheaf ≫ γ = η := by
  refine ⟨𝒮.sheafifiedLocalizationPresheafLift η hη, ?_, ?_⟩
  · exact 𝒮.toSheafifiedLocalizationPresheaf_comp_sheafifiedLocalizationPresheafLift η hη
  · intro γ hγ
    exact 𝒮.sheafifiedLocalizationPresheafLift_unique η hη γ hγ

end SubmonoidPresheaf
end Presheaf
end CategoryTheory
