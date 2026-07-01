import stacks_project.Chap06.Lemma_6_30_10
import stacks_project.Chap06.Lemma_6_30_12
import stacks_project.Chap06.Definition_6_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {B : Set (Opens X)} (hB : Opens.IsBasis B)

local notation "BasisRingSheaf" => BasisSiteSheaf RingCat B hB

private instance basisOpenInclusion_isContinuous :
    Functor.IsContinuous (basisOpenInclusion B)
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)
      (basisOpenInclusion B)
      (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
        (Opens.grothendieckTopology X))

/- Domain-style sampling for Lemma 6.30.13:
- primary domain: sheaves of modules over ring-valued sheaves on a dense basis subsite;
- sampled owner declarations:
  `(basisOpenInclusion B).sheafPushforwardContinuous`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `SheafOfModules.pushforward`,
  `basisModuleSheafExtension`;
- best owner abstraction: the dense-subsite restriction functor on sheaves, together with the
  induced module-sheaf pushforward along the identity map of the restricted ring sheaf;
- primitive data: the basis inclusion `basisOpenInclusion B`, the induced topology
  `basisGrothendieckTopology B hB`, and the sheaf of rings `𝒪`;
- derived API: restriction of `𝒪`-modules to the basis and the extension construction from
  `Lemma_6_30_12`, expressed through the canonical functor
  `SheafOfModules.pushforward (𝟙 _)`;
- source/core/bridge triage:
  `source-facing`: restriction of `𝒪`-modules to basis opens;
  `core/canonical`: `(basisOpenInclusion B).sheafPushforwardContinuous` and
    `SheafOfModules.pushforward`;
  `bridge/view`: `basisModuleSheafExtension`, which supplies the inverse-direction module
    structure on the extension back to `X`.
-/

variable (𝒪 : TopCat.Sheaf RingCat.{u} X)

/-- Helper for Lemma 6.30.13: the restricted ring sheaf on the basis site attached to `B`. -/
private abbrev restrictedRingSheaf :
    BasisSiteSheaf RingCat B hB :=
  ((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
    (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪

/-- Helper for Lemma 6.30.13: the dense-subsite comparison equivalence for `RingCat`-valued sheaves
between the basis site and all opens of `X`. -/
private noncomputable abbrev ringRestrictionEquiv :
    BasisSiteSheaf RingCat B hB ≌ TopCat.Sheaf RingCat X := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  change Sheaf (basisGrothendieckTopology B hB) RingCat ≌ TopCat.Sheaf RingCat X
  exact
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) RingCat

/-- Helper for Lemma 6.30.13: the dense-subsite comparison equivalence for additive sheaves on the
basis and on all opens of `X`. -/
private noncomputable abbrev addRestrictionEquiv :
    BasisSiteSheaf AddCommGrpCat B hB ≌ TopCat.Sheaf AddCommGrpCat X := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  change Sheaf (basisGrothendieckTopology B hB) AddCommGrpCat ≌ TopCat.Sheaf AddCommGrpCat X
  exact
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) AddCommGrpCat

/-- Helper for Lemma 6.30.13: extending the restricted ring sheaf back to `X` recovers `𝒪`
through the counit of the dense-subsite comparison equivalence. -/
private noncomputable abbrev restrictedRingCounitIso :
    (restrictedRingSheaf hB 𝒪).extend ≅ 𝒪 :=
  (ringRestrictionEquiv hB).counitIso.app 𝒪

/-- Helper for Lemma 6.30.13: on a basis open, restricting the inverse counit
`𝒪 ⟶ (𝒪|_B).extend` agrees with the canonical `restrictExtend` comparison map. -/
private theorem restrictedCounitInv_app_eq_restrictExtendComponentHom
    (U : (BasisOpen B)ᵒᵖ) :
    ((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).map
          (restrictedRingCounitIso hB 𝒪).inv).hom.app U) =
      BasisSiteSheaf.restrictExtendComponentHom (restrictedRingSheaf hB 𝒪) U := by
  -- The inverse counit becomes the unit after restricting back to the basis.
  simpa [restrictedRingSheaf, restrictedRingCounitIso, BasisSiteSheaf.presheaf,
    BasisSiteSheaf.extend] using
    congrArg (fun f => f.hom.app U)
      ((ringRestrictionEquiv hB).unit_app_inverse 𝒪).symm

/-- Helper for Lemma 6.30.13: on a basis open, restricting the counit
`(𝒪|_B).extend ⟶ 𝒪` agrees with the inverse `restrictExtend` comparison map. -/
private theorem restrictedCounitHom_app_eq_restrictExtendComponentInv
    (U : (BasisOpen B)ᵒᵖ) :
    ((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).map
          (restrictedRingCounitIso hB 𝒪).hom).hom.app U) =
      BasisSiteSheaf.restrictExtendComponentInv (restrictedRingSheaf hB 𝒪) U := by
  -- The counit itself restricts to the inverse unit comparison on the basis site.
  simpa [restrictedRingSheaf, restrictedRingCounitIso, BasisSiteSheaf.presheaf,
    BasisSiteSheaf.extend] using
    congrArg (fun f => f.hom.app U)
      ((ringRestrictionEquiv hB).unitInv_app_inverse 𝒪).symm

/- The restriction functor in Lemma 6.30.13 is not a new owner: it is the canonical module
pushforward functor along the identity map of the restricted ring sheaf on the basis site. On the
source-facing surface, it has type `Mod(𝒪) ⥤ Mod(𝒪|_B)`. -/
#check
  (SheafOfModules.pushforward
      (𝟙 (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)) :
    Mod(𝒪) ⥤
      Mod((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)))

-- Proof sketch: use Lemma 6.30.10 for the equivalence between sheaves on `X` and sheaves on the
-- basis site, and Lemma 6.30.12 to equip the extended additive sheaf with the canonical module
-- structure over the extended ring sheaf. Together these identify restriction to the basis as an
-- equivalence on module sheaves.
/-- Helper for Lemma 6.30.13: the canonical restriction functor from `𝒪`-modules on `X` to
modules over the restricted ring sheaf on the basis site. -/
private abbrev basisModuleRestrictionFunctor :
    Mod(𝒪) ⥤ Mod(restrictedRingSheaf hB 𝒪) :=
  SheafOfModules.pushforward (𝟙 (restrictedRingSheaf hB 𝒪))

/-- Helper for Lemma 6.30.13: the basis-open comparison map from a basis sheaf to the restriction
of its extension is injective on sections. -/
private theorem restrictExtendComponentHom_injective
    (F : BasisSiteSheaf AddCommGrpCat B hB)
    (U : (BasisOpen B)ᵒᵖ) :
    Function.Injective (BasisSiteSheaf.restrictExtendComponentHom F U) := by
  -- Apply the inverse comparison map to both sides and simplify the triangular identity.
  intro s t hst
  calc
    s =
      BasisSiteSheaf.restrictExtendComponentInv F U
        (BasisSiteSheaf.restrictExtendComponentHom F U s) := by
          symm
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_hom_inv_id F U) s
    _ =
      BasisSiteSheaf.restrictExtendComponentInv F U
        (BasisSiteSheaf.restrictExtendComponentHom F U t) := by
          simpa using congrArg (BasisSiteSheaf.restrictExtendComponentInv F U) hst
    _ = t := by
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_hom_inv_id F U) t

/-- Helper for Lemma 6.30.13: the underlying additive map of the extension of a basis-module
morphism is the image of that morphism under the additive dense-subsite equivalence. -/
private noncomputable abbrev basisModuleSheafExtensionUnderlyingMap
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules 𝒪}
    (f : ℱ ⟶ 𝒢) :
    BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ) ⟶
      BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj 𝒢) :=
  (addRestrictionEquiv hB).functor.map ((SheafOfModules.toSheaf 𝒪).map f)

/-- Helper for Lemma 6.30.13: on a basis open, the additive extension of a module morphism agrees
with the original basis-open map after identifying both extensions with the restricted sheaves. -/
private theorem basisModuleSheafExtensionUnderlyingMap_restrictExtend_app
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules 𝒪}
    (f : ℱ ⟶ 𝒢)
    (U : (BasisOpen B)ᵒᵖ)
    (m : ℱ.val.obj U) :
    (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app
        ((basisOpenInclusion B).op.obj U)
        (BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) U m) =
      BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj 𝒢) U
        ((((SheafOfModules.toSheaf 𝒪).map f).hom.app U) m) := by
  -- The unit comparison of the dense-subsite equivalence is natural in the additive sheaf map.
  change
    (ConcreteCategory.hom
          (((addRestrictionEquiv hB).functor.map
                ((SheafOfModules.toSheaf 𝒪).map f)).hom.app
            ((basisOpenInclusion B).op.obj U)))
        ((((addRestrictionEquiv hB).unitIso.app
              ((SheafOfModules.toSheaf 𝒪).obj ℱ)).hom.hom.app U) m) =
      (((addRestrictionEquiv hB).unitIso.app
            ((SheafOfModules.toSheaf 𝒪).obj 𝒢)).hom.hom.app U)
        ((((SheafOfModules.toSheaf 𝒪).map f).hom.app U) m)
  have hnat :=
    congrArg (fun τ => (ConcreteCategory.hom (τ.hom.app U)) m)
      ((addRestrictionEquiv hB).unitIso.hom.naturality
        ((SheafOfModules.toSheaf 𝒪).map f))
  change
    (fun τ => (ConcreteCategory.hom (τ.hom.app U)) m)
        ((addRestrictionEquiv hB).unitIso.hom.app ((SheafOfModules.toSheaf 𝒪).obj ℱ) ≫
          ((addRestrictionEquiv hB).functor ⋙ (addRestrictionEquiv hB).inverse).map
            ((SheafOfModules.toSheaf 𝒪).map f)) =
      (fun τ => (ConcreteCategory.hom (τ.hom.app U)) m)
        ((𝟭 (BasisSiteSheaf AddCommGrpCat B hB)).map ((SheafOfModules.toSheaf 𝒪).map f) ≫
          (addRestrictionEquiv hB).unitIso.hom.app ((SheafOfModules.toSheaf 𝒪).obj 𝒢))
  exact hnat.symm

/-- Helper for Lemma 6.30.13: a morphism of basis-module sheaves extends to a morphism of the
corresponding sheaves of modules on `X`. -/
private noncomputable def basisModuleSheafExtensionMap
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules 𝒪}
    (f : ℱ ⟶ 𝒢) :
    basisModuleSheafExtension 𝒪 ℱ ⟶ basisModuleSheafExtension 𝒪 𝒢 :=
  -- TODO: package the additive extension map as a module morphism by checking linearity on basis
  -- neighborhoods via `BasisSiteSheaf.restrictExtendIso` and the basis-open compatibility lemma.
  sorry

/-- Helper for Lemma 6.30.13: the extension construction from Lemma 6.30.12 should be upgraded to
a functor from basis-module sheaves to module sheaves over the extended restricted ring sheaf. -/
private noncomputable def basisModuleSheafExtensionFunctor :
    Mod(restrictedRingSheaf hB 𝒪) ⥤ Mod((restrictedRingSheaf hB 𝒪).extend) :=
  -- TODO: use `basisModuleSheafExtensionMap` as the map part and prove `map_id`/`map_comp`
  -- through the additive dense-subsite equivalence.
  sorry

/-- Helper for Lemma 6.30.13: the extension construction from Lemma 6.30.12 should be upgraded to
a functor back to `𝒪`-modules by extending a basis-module sheaf and then restricting scalars along
the counit isomorphism `𝒪 ≅ (𝒪|_B).extend`. -/
private noncomputable def basisModuleExtensionFunctor :
    Mod(restrictedRingSheaf hB 𝒪) ⥤ Mod(𝒪) :=
  -- Extend the basis-module sheaf first, then transport scalars back to `𝒪` via the counit.
  basisModuleSheafExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
    SheafOfModules.pushforward (F := 𝟭 _) ((restrictedRingCounitIso hB 𝒪).inv)

/-- Helper for Lemma 6.30.13: once the extension functor is available on morphisms, the global-side
unit isomorphism comes from the dense-subsite counit on the underlying additive sheaf. -/
private noncomputable def basisModuleRestrictionUnitIso :
    𝟭 (Mod(𝒪)) ≅
      basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) :=
  -- TODO: use the inverse dense-subsite counit on the underlying additive sheaf after rewriting
  -- `toSheaf` of the extension functor object through `basisModuleSheafExtension_toSheaf`.
  sorry

/-- Helper for Lemma 6.30.13: once the extension functor is available on morphisms, the basis-side
counit isomorphism comes from `BasisSiteSheaf.restrictExtendIso` on the underlying additive sheaf,
upgraded to module morphisms using the restricted counit bridge lemmas. -/
private noncomputable def basisModuleRestrictionCounitIso :
    basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪) ≅
      𝟭 (Mod(restrictedRingSheaf hB 𝒪)) :=
  -- TODO: identify the component maps with `restrictExtendComponentHom` and
  -- `restrictExtendComponentInv`, then prove linearity using the restricted counit bridge lemmas.
  sorry

/-- Lemma 6.30.13: restricting a sheaf of `\mathcal O`-modules on `X` to the members of the basis
`\mathcal B` defines an equivalence between `Mod(\mathcal O)` and
`Mod(\mathcal O|_\mathcal B)`. -/
theorem restrictSheafOfModulesToBasis_isEquivalence
    (𝒪 : TopCat.Sheaf RingCat.{u} X) :
    Functor.IsEquivalence
      (SheafOfModules.pushforward
          (𝟙 (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)) :
        Mod(𝒪) ⥤
          Mod((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪))) := by
  -- Route correction: package the restriction functor with the intended extension quasi-inverse
  -- so the remaining work is reduced to functoriality of extension and the two standard
  -- comparison isomorphisms.
  change Functor.IsEquivalence (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪))
  exact
    Functor.IsEquivalence.mk'
      (basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪))
      (basisModuleRestrictionUnitIso (hB := hB) (𝒪 := 𝒪))
      (basisModuleRestrictionCounitIso (hB := hB) (𝒪 := 𝒪))

end
