import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_7_1 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

private abbrev localizedRestriction
    (𝒪 : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules 𝒪 ⥤ SheafOfModules (𝒪.over U) :=
  SheafOfModules.pushforward (𝟙 (𝒪.over U))

-- Proof sketch: restriction to the localized ringed site is right adjoint to extension by zero,
-- and extension by zero is exact; apply the standard adjunction criterion that a right adjoint to
-- an exact functor preserves injective objects.
/-- Lemma 21.7.1 (1): if `ℐ` is an injective `\mathcal O`-module on a ringed site
`(\mathcal C, \mathcal O)`, then its restriction to the localized ringed site
`(\mathcal C/U, \mathcal O_U)` is an injective `\mathcal O_U`-module. -/
theorem ringedSite_localizationModuleRestriction_injective
    (𝒪 : Sheaf J RingCat.{w}) (U : C) (ℐ : SheafOfModules 𝒪)
    (hℐ : Injective ℐ) :
    Injective ((localizedRestriction 𝒪 U).obj ℐ) := sorry

-- Proof sketch: choose an injective resolution of `ℱ` in `Mod(\mathcal O)`, restrict it to the
-- localized ringed site using part (1), and compute both sides by the homology of the same
-- sections complex; sections of `ℱ` over `U` agree with global sections of `ℱ|_U` on `X/U`.
/-- Lemma 21.7.1 (2): for an `\mathcal O`-module `ℱ` on a ringed site
`(\mathcal C, \mathcal O)` and an object `U : \mathcal C`, the cohomology of `ℱ` over `U`
agrees with the cohomology of the restricted module on the localized ringed site
`(\mathcal C/U, \mathcal O_U)`. -/
theorem ringedSite_localizationModuleRestriction_cohomologyOver_eq
    (𝒪 : Sheaf J RingCat.{w}) (U : C)
    [HasSheafify J AddCommGrpCat]
    [HasExt (Sheaf J AddCommGrpCat)]
    [HasSheafify (J.over U) AddCommGrpCat]
    [HasExt (Sheaf (J.over U) AddCommGrpCat)]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p U) =
      AddCommGrpCat.of
        (((SheafOfModules.toSheaf (𝒪.over U)).obj
          ((localizedRestriction 𝒪 U).obj ℱ)).H p) := sorry

/-! ### Lemma_21_7_2 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [u.Full] [u.Faithful] [u.IsContinuous J K] [u.IsCocontinuous J K]
variable [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]

-- Proof sketch: apply Homology, Lemma `12.29.1` to the adjunction
-- `u.sheafPullback AddCommGrpCat J K ⊣ u.sheafPushforwardContinuous AddCommGrpCat J K`.
-- The left adjoint is exact under the site hypotheses from Lemma `7.21.8`, so the right adjoint
-- preserves injective abelian sheaves. Compute cohomology over `U` by injective resolutions on
-- the slice sites `C/U` and `D/u(U)`.
/-- Lemma 21.7.2: if `u : C ⥤ D` satisfies the hypotheses of Sites, Lemma `7.21.8`, then for any
abelian sheaf `F` on `D`, any degree `p`, and any object `U` of `C`, the cohomology of the
inverse image `g⁻¹ F`, formalized as
`(u.sheafPushforwardContinuous AddCommGrpCat J K).obj F`, over `U` is canonically isomorphic to
the cohomology of `F` over `u(U)`. -/
theorem inverseImage_site_cohomology_over_obj_iso
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) (U : C) :
    IsIsomorphic (((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F).H' p U)
      (F.H' p (u.obj U)) := sorry

variable [HasGlobalSectionsFunctor J AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor K AddCommGrpCat.{u}]

-- Proof sketch: this is the global-sections case of the same injective-resolution argument.
-- Since `u.sheafPushforwardContinuous AddCommGrpCat J K` preserves injective objects, the right
-- derived functors of global sections identify on `g⁻¹ F` and on `F`.
/-- For the inverse-image functor attached to `u`, global site cohomology agrees with the global
cohomology of the original sheaf on `D`. -/
theorem inverseImage_site_global_cohomology_iso
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F).H p))
      (AddCommGrpCat.of (F.H p)) := sorry

end

end Sheaf
end CategoryTheory

/-! ### Lemma_21_7_3 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u v

/-- Lemma 21.7.3: for a sheaf of modules on a ringed site, every positive-degree cohomology class
becomes zero after restricting to a suitable covering of the base object. -/
-- Proof sketch: view `ℱ` as an abelian sheaf via `SheafOfModules.toSheaf 𝒪`, represent `ξ` by a
-- cocycle in an injective resolution, and use exactness in positive degree together with the local
-- surjectivity characterization of exactness for sheaves to refine to a cover on which the cocycle
-- is locally a coboundary.
theorem exists_cover_restrict_eq_zero_of_positive_cohomology_class
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat] [HasExt (Sheaf J AddCommGrpCat)]
    {𝒪 : Sheaf J RingCat.{max u v}} (ℱ : SheafOfModules 𝒪) {U : C} {n : ℕ}
    (hn : 0 < n) (ξ : ((SheafOfModules.toSheaf 𝒪).obj ℱ).H' n U) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ((((SheafOfModules.toSheaf 𝒪).obj ℱ).cohomologyPresheaf n).map I.f.op) ξ = 0 := sorry

/-! ### Lemma_21_7_4 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u v

namespace RingedSite.Hom

/-- The direct-image functor on sheaves of modules attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The `i`-th higher direct image of a sheaf of modules along a morphism of ringed sites. -/
abbrev higherDirectImageModule {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [Functor.Additive f.modulePushforward]
    [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
    (ℱ : SheafOfModules X.structureSheaf) (i : ℕ) :
    SheafOfModules Y.structureSheaf :=
  (f.modulePushforward.rightDerived i).obj ℱ

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
variable [Functor.Additive f.modulePushforward]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt.{max u v} (Sheaf X.siteTopology AddCommGrpCat.{max u v})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 21.7.4:
- primary domain: higher direct images of sheaves of modules on a morphism of ringed sites and
  the comparison with objectwise cohomology of the underlying abelian sheaf;
- sampled owner declarations:
  `RingedSite.Hom.modulePushforward`,
  `RingedSite.Hom.higherDirectImageModule`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the source-facing higher direct image owner
  `higherDirectImageModule f ℱ i`, built from the bundled morphism `f : RingedSite.Hom X Y`;
- primitive data: the bundled morphism `f`, an `\mathcal O_X`-module
  `ℱ : SheafOfModules X.structureSheaf`, and the degree `i`;
- derived API: the underlying abelian sheaf functor `SheafOfModules.toSheaf`, the right derived
  direct image owner `higherDirectImageModule f ℱ i`, and the sheafification of the objectwise
  cohomology presheaf on `Y`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement identifying the underlying abelian sheaf of
  `R^i f_* \mathcal F` with the sheaf associated to `V ↦ H^i(f^{-1}(V), \mathcal F)`;
- `core/canonical`: the chapter owners `RingedSite.Hom.modulePushforward` and
  `RingedSite.Hom.higherDirectImageModule`;
- `bridge/view`: forgetting module structure via `SheafOfModules.toSheaf` and expressing the
  target as a sheafification of the presheaf `f.base.op ⋙ ... .cohomologyPresheaf i`.

This theorem depends only on the owner-level ringed-site data, not on a particular presentation by
commutative ringed sites. The former local aliases for the source and target commutative ringed
sites were presentation-only duplicate scaffolding and are removed.
-/

-- Proof sketch: compute `R^i f_* ℱ` from an injective resolution of `ℱ` via the right-derived
-- functor of `f.modulePushforward`. After forgetting the module
-- structure, the resulting degree-`i` cohomology sheaf is the sheafification of the presheaf of
-- sectionwise cohomology of the same pushed-forward complex, and evaluating the direct image on
-- `V` identifies that presheaf with `V ↦ H^i(f^{-1}(V), ℱ)`.
/-- Lemma 21.7.4, owner form: for a morphism of ringed sites `f : X ⟶ Y`, the underlying abelian
sheaf of `R^i f_* \mathcal F`, formalized here as `higherDirectImageModule f ℱ i`, is
canonically isomorphic to the sheaf associated to the presheaf
`V ↦ H^i(f^{-1}(V), \mathcal F)`. In the Stacks commutative setting, this applies to ringed sites
arising from `RingedSite.ofCommRingSheaf`. -/
theorem higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology
    (ℱ : SheafOfModules X.structureSheaf) (i : ℕ) :
    IsIsomorphic
      ((SheafOfModules.toSheaf Y.structureSheaf).obj (higherDirectImageModule f ℱ i))
      ((presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}).obj
        (f.base.op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf
          (J := X.siteTopology) ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ) i)) := sorry

end RingedSite.Hom
