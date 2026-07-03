import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_19_1 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u v

namespace RingedSite

variable (X : RingedSite.{u, v}) (U : X)

/-- Definition 18.19.1: the localization of a ringed site `(\\mathcal C, \\mathcal O)` at an
object `U` is the slice ringed site `(\\mathcal C/U, \\mathcal O_U)`. -/
def localization : RingedSite.{max u v, v} where
  carrier := Over U
  str := inferInstance
  siteTopology := X.siteTopology.over U
  structureSheaf := X.structureSheaf.over U

-- Proof sketch: `localization X U` is defined by specifying its carrier to be `Over U`, so
-- this is the corresponding definitional identification recorded as a theorem-level API.
/-- The underlying category of the localized ringed site `X.localization U` is the slice
category `Over U`. -/
theorem localization_carrier :
    (X.localization U).carrier = Over U := rfl

-- Proof sketch: `localization X U` is defined using the restricted structure sheaf
-- `X.structureSheaf.over U`, so this is the defining description of its structure sheaf.
/-- The structure sheaf on `X.localization U` is the restricted sheaf `\mathcal O_U`. -/
theorem localization_structureSheaf :
    (X.localization U).structureSheaf = X.structureSheaf.over U := rfl

/- Companion recall: restriction of `\mathcal O_X`-modules to the slice ringed site
`X.localization U` is the canonical pushforward along the identity on `X.structureSheaf.over U`.
The right adjoint back to `X` and the adjunction itself are the canonical mathlib constructions
`SheafOfModules.pushforwardOver U` and `SheafOfModules.overPushforwardOverAdj U`. -/

end RingedSite

/-! ### Lemma_18_19_2 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on a ringed
site. -/
abbrev ringedSiteModuleCategory {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

section

variable {C : Type u} [Category.{u} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.19.2:
- primary domain: pullback/pushforward of sheaves of modules on localized ringed sites;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  the presheaf analogue `PresheafOfModules.pullbackPushforwardAdjunction` from Remark `18.19.7`;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- primitive data: the ringed site `(\mathcal C, J, \mathcal O)` and the object `U : C`;
- derived API: any localized restriction/extension-by-zero functor expression and the Hom-set
  bijection obtained from `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the adjunction `j_{U!} ⊣ j_U^*` on the localized ringed site;
- `core/canonical`: the specialized owner adjunction below;
- `bridge/view`: any later use of `.homEquiv`, exactness, or derived-category consequences.

This file keeps only the reusable owner alias `ringedSiteModuleCategory`. The localized functors
themselves are used through the canonical `SheafOfModules.pullback` / `SheafOfModules.pushforward`
API rather than through parallel public wrappers. -/

/- Lemma 18.19.2: on the localized ringed site `(C/U, J.over U, \mathcal O_U)`, extension by
zero is left adjoint to restriction. In Lean this is exactly the specialized owner adjunction
`SheafOfModules.pullbackPushforwardAdjunction` for the identity morphism of the localized
structure sheaf `\mathcal O_U = \mathcal O.over U`. -/
#check
  (SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)))

end

/-! ### Lemma_18_19_3 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/-
Domain-style sampling for Lemma 18.19.3:
- primary domain: exactness of extension by zero for sheaves of modules on the localized ringed
  site `(C/U, J.over U, 𝒪.over U)`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `exactFunctor`;
- best owner abstraction:
  `SheafOfModules.pullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- primitive data: only `J`, `𝒪`, and `U`;
- derived API: the exactness statement for the source-facing localized extension-by-zero functor
  `j_{U!}`.

Source/core/bridge triage:
- `source-facing`: exactness of `j_{U!}` for the chosen object `U`;
- `core/canonical`: the identity-structure-map pullback owner on sheaves of modules;
- `bridge/view`: the source notation `j_{U!}` for this canonical owner.

This file should therefore keep the specialized exactness theorem, but express it directly in terms
of the canonical pullback owner and the upstream module-category alias from `Lemma_18.19.2`.
-/

-- Proof sketch: `ringedSiteLocalizedExtensionByZero J 𝒪 U` is the lower shriek `j_{U!}` from
-- the localized ringed site, i.e. the pullback functor for the identity map on `𝒪_U`, hence a
-- left adjoint to restriction and therefore right exact. For left exactness, compute sections
-- objectwise as the direct sum over morphisms into `U`, which sends monomorphisms to
-- monomorphisms, and then use exactness of sheafification as in Lemma `18.11.2`.
/-- Lemma 18.19.3: for a ringed site `(\mathcal C, \mathcal O)` and an object `U : \mathcal C`,
the extension-by-zero functor
`j_{U!} : \mathrm{Mod}(\mathcal O_U) ⥤ \mathrm{Mod}(\mathcal O)` is exact. In canonical
mathlib form, this is the exactness of the pullback functor on sheaves of modules induced by the
identity map of the localized ringed site `(C/U, J.over U, \mathcal O_U)`. -/
lemma ringedSiteLocalizedExtensionByZero_exact :
    exactFunctor
      (ringedSiteModuleCategory (J.over U) (𝒪.over U))
      (ringedSiteModuleCategory J 𝒪)
      (SheafOfModules.pullback
        (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))) := sorry

end

/-! ### Lemma_18_19_4 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.19.4:
- primary domain: exactness reflection for extension by zero from the localized ringed site
  `(C/U, J.over U, 𝒪_U)` to `(C, J, 𝒪)`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `ringedSiteLocalizedExtensionByZero_exact`;
- best owner abstraction:
  `let 𝒪_U := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U;
   SheafOfModules.pullback (𝟙 𝒪_U)`, the canonical
  lower-shriek extension-by-zero owner `j_{U!}`;
- primitive data: only the site `(C, J)`, the structure sheaf `𝒪`, and the object `U : C`;
- derived API: the source-facing exactness comparison for short complexes under `j_{U!}`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a short complex over `𝒪_U` is exact iff its
  extension by zero is exact over `𝒪`;
- `core/canonical`: the mathlib owner
  `let 𝒪_U := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U;
   SheafOfModules.pullback (𝟙 𝒪_U)` for localization extension by zero;
- `bridge/view`: the exactness comparison theorem below.

This lemma is a bridge/view statement: the source-facing `j_{U!}` is the canonical pullback owner
above, so the file should reuse that owner directly instead of introducing the opposite direct
image `j_{U,*}` or extra local wrapper/instance noise. -/

-- Proof sketch: Lemma `18.19.3` identifies the forward implication with exactness of the
-- canonical extension-by-zero owner `j_{U!}`. The converse is the source-facing reflection
-- statement for the same owner on localized `\mathcal O_U`-modules.
/-- Lemma 18.19.4: a short complex of `\mathcal O_U`-modules on the localized ringed site
`(\mathcal C/U, \mathcal O_U)` is exact if and only if its image under extension by zero
`j_{U!} : \mathrm{Mod}(\mathcal O_U) ⥤ \mathrm{Mod}(\mathcal O)` is exact. In canonical mathlib
form, `j_{U!}` is the pullback functor on sheaves of modules induced by the identity morphism of
the localized structure sheaf `\mathcal O_U`. -/
theorem ringedSiteLocalizedExtensionByZero_exact_iff
    (S : ShortComplex (ringedSiteModuleCategory (J.over U) (𝒪.over U))) :
    let 𝒪_U := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U
    S.Exact ↔ (S.map (SheafOfModules.pullback (𝟙 𝒪_U))).Exact :=
  sorry

end

/-! ### Lemma_18_19_5 (from Chap18) -/
open CategoryTheory Opposite

universe u v w

noncomputable section

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.19.5:
- primary domain: relocalization of a ringed site along a map `f : V ⟶ U` and the induced
  comparison on sheaf inverse/direct images over slice sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `Functor.sheafPushforwardCocontinuousComp'`,
  `GrothendieckTopology.overPullback`,
  `GrothendieckTopology.overMapPullback`;
- source/core/bridge triage:
  `source-facing`: the localization triangle for `(Sh(C), 𝒪)` and its relocalization at `f`;
  `core/canonical`: the slice-site comparison owners already recorded in Chapter 7;
  `bridge/view`: the structure-sheaf identification obtained by evaluating the inverse-image
  comparison at `𝒪`.

Primitive data are only `J`, `𝒪`, and `f`. The inverse-image and direct-image comparisons are
already canonically owned by the Chapter 7 slice-site comparison machinery, and the
structure-sheaf comparison is derived by applying that owner isomorphism to `𝒪`, so this file
should remain a direct recall/use file rather than introduce chapter-local wrappers.
-/

/- Lemma 18.19.5: on inverse-image functors, the relocalization triangle
`j_U⁻¹ ⋙ j⁻¹ ≅ j_V⁻¹` is exactly the canonical slice-site comparison attached to
`Over.mapForget f`. -/
recall Functor.sheafPushforwardContinuousComp'

section InverseImage

variable (𝒪 : Sheaf J RingCat.{v}) {U V : C} (f : V ⟶ U)

#check
  (Functor.sheafPushforwardContinuousComp' (Over.mapForget f) (Type w) (J.over V) (J.over U) J :
    J.overPullback (Type w) U ⋙ J.overMapPullback (Type w) f ≅ J.overPullback (Type w) V)

/- Applying the inverse-image comparison to the structure sheaf gives the canonical
identification `j^{-1}(𝒪_U) ≅ 𝒪_V`. -/
#check
  ((Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
      RingCat.{v} (J.over V) (J.over U) J).app 𝒪 :
    (J.overMapPullback RingCat.{v} f).obj (𝒪.over U) ≅ 𝒪.over V)

end InverseImage

/- The direct-image comparison in the same triangle is the cocontinuous owner isomorphism for
`Over.map f ⋙ Over.forget U ≅ Over.forget V`; no extra Chapter 18 owner is needed. -/
recall Functor.sheafPushforwardCocontinuousComp'

section DirectImage

variable {U V : C} (f : V ⟶ U)
variable [∀ F : (Over V)ᵒᵖ ⥤ RingCat.{v}, (Over.map f).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ RingCat.{v}, (Over.forget U).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ RingCat.{v}, (Over.forget V).op.HasPointwiseRightKanExtension F]

#check
  (Functor.sheafPushforwardCocontinuousComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
      (Over.map f).sheafPushforwardCocontinuous RingCat.{v} (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPushforwardCocontinuous RingCat.{v} (J.over U) J ≅
        (Over.forget V).sheafPushforwardCocontinuous RingCat.{v} (J.over V) J)

end DirectImage

end

end GrothendieckTopology
end CategoryTheory

/-! ### Remark_18_19_6 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C]

private abbrev localizedStructureMap (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    Sheaf (J.over U) RingCat.{u} :=
  (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)

/- Domain-style sampling for Remark 18.19.6:
- primary domain: localized extension-by-zero for sheaves of modules on a ringed site, and its
  compatibility with passage to the underlying sheaf of abelian groups;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.toSheaf`,
  `SheafOfModules.sheafificationCompPullback`,
  `(Over.forget U).sheafPushforwardContinuous`;
- best owner abstraction: the canonical lower-shriek owner
  `SheafOfModules.pullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`
  together with the canonical pullback/sheafification comparison
  `SheafOfModules.sheafificationCompPullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- primitive data: the ringed site `(\mathcal C, J, \mathcal O)` and the object `U : C`;
- derived API: the restriction-side definitional equality with `toSheaf`.

Source/core/bridge triage:
- `source-facing`: the `j_{U!}` square saying that extension by zero on `\mathcal O_U`-modules is
  compatible with forgetting to the underlying abelian sheaf;
- `core/canonical`: `SheafOfModules.pullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`,
  `SheafOfModules.sheafificationCompPullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`,
  `SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`, and
  `(Over.forget U).sheafPushforwardContinuous AddCommGrpCat (J.over U) J`;
- `bridge/view`: the restriction-side equality below, which is the right-adjoint mate of the
  source-facing left-adjoint square.

This remark therefore should present the lower-shriek square through the upstream owner
`SheafOfModules.sheafificationCompPullback`, specialized to the identity map of `\mathcal O_U`,
and keep the restriction compatibility only as a companion. -/

section ExtensionByZeroSide

variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Remark 18.19.6: the extension-by-zero square for `j_{U!}` on sheaves of modules is exactly the
canonical pullback/sheafification comparison specialized to the identity morphism of
`\mathcal O_U`; equivalently, localized extension by zero commutes with forgetting to the
underlying sheaf of abelian groups. -/
recall SheafOfModules.sheafificationCompPullback

-- Proof sketch: the upstream owner
-- `SheafOfModules.sheafificationCompPullback
--   (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`
-- identifies module-valued extension by zero with presheaf extension by zero followed by
-- sheafification. Forgetting module structure turns that presheaf pullback into the abelian lower
-- shriek along `Over.forget U`, yielding the source-facing `j_{U!}` square.
/- Applying the recalled natural isomorphism above to an `\mathcal O_U`-module `\mathcal F`
recovers the source-facing comparison
`(j_{U!}\mathcal F)_{\mathrm{ab}} \cong j_{U!}(\mathcal F_{\mathrm{ab}})`.
We keep `SheafOfModules.sheafificationCompPullback` itself as the public entry, rather than a
parallel objectwise wrapper. -/

end ExtensionByZeroSide

section RestrictionSide

variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

-- Proof sketch: localized restriction is `SheafOfModules.pushforward` for the identity map on
-- `\mathcal O_U`. Forgetting module structure turns this pushforward into the usual sheaf
-- pushforward along `Over.forget U`, so the two composites are definitionally equal.
/-- Companion to Remark 18.19.6: localized restriction commutes definitionally with forgetting to
the underlying sheaf of abelian groups. This is the right-adjoint mate of the main
extension-by-zero square above. -/
theorem ringedSiteLocalizedRestriction_toSheaf :
    SheafOfModules.pushforward (𝟙 (localizedStructureMap J 𝒪 U)) ⋙
        SheafOfModules.toSheaf (localizedStructureMap J 𝒪 U) =
      SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) ⋙
        (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over U) J :=
  rfl

end RestrictionSide

end SheafOfModules.RingedSite

/-! ### Remark_18_19_7 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section PresheafLevel

variable {C : Type u} [Category.{u} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (U : C)

/- Domain-style sampling for Remark 18.19.7:
- primary domain: localization of presheaves of modules via restriction and its two Kan-extension
  adjoints along `Over.forget U`;
- sampled owner declarations:
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `Adjunction.ofIsLeftAdjoint`,
  `Functor.rightAdjoint`,
  `SheafOfModules.sheafificationCompPullback`,
  `Functor.ranAdjunction`;
- best owner abstraction:
  `PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪))`;
- primitive data: the ring presheaf `𝒪` on `C` and the localization object `U : C`;
- derived API: the presheaf right adjoint `j_{U*}`, the objectwise coproduct formula for
  `j_{U!}` as a canonical isomorphism, the exactness of this presheaf-level lower shriek, and,
  in the sheaf case below, the comparison showing that sheaf-level extension by zero is obtained
  by sheafifying presheaf-level extension by zero.

Source/core/bridge triage:
- `source-facing`: the presheaf localization adjoints `j_{U!} ⊣ j_U^* ⊣ j_{U*}`, the exactness
  of `j_{U!}`, and the objectwise formula for `j_{U!}`;
- `core/canonical`:
  `PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪))`;
- `bridge/view`: the coproduct formula and the sheafification comparison from the presheaf owner
  to the sheaf owner.

This file should therefore recall the canonical presheaf lower-shriek adjunction directly, record
the missing right adjunction for restriction, add the source-facing exactness statement for the
same owner, keep the coproduct formula as a canonical isomorphism, and use the upstream
sheafification/pullback comparison instead of a chapter-local wrapper square.
-/

/- Remark 18.19.7: for a presheaf of rings `𝒪` on `C` and an object `U : C`, restriction to the
slice category `C/U` is the canonical pushforward
`PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))`, and its left adjoint
`j_{U!}` is exactly the owner adjunction
`PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪))`. -/
recall PresheafOfModules.pullbackPushforwardAdjunction

-- Proof sketch: the restriction functor is induced by precomposition with `(Over.forget U).op`,
-- so its right adjoint is the presheaf-module right Kan extension along `(Over.forget U).op`,
-- i.e. the presheaf-level `j_{U*}` from the source remark.
/-- Remark 18.19.7 also records that the restriction functor `j_U^*` on presheaves of modules is a
left adjoint, so its chosen right adjoint is the presheaf direct image `j_{U*}`. -/
instance presheafLocalizedRestriction_isLeftAdjoint :
    (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))).IsLeftAdjoint := sorry

/-- The source remark's presheaf direct image `j_{U*}` is the right adjoint of restriction, hence
the canonical adjunction below packages the source-facing statement `j_U^* ⊣ j_{U*}` directly. -/
noncomputable abbrev presheafLocalizedRestrictionRightAdjunction :
    PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪)) ⊣
      (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪))).rightAdjoint :=
  Adjunction.ofIsLeftAdjoint
    (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ 𝒪)))

-- Proof sketch: this is exactly Lemma `18.19.3` for the chaotic topology, where every presheaf is
-- already a sheaf. Equivalently, `j_{U!}` is the canonical pullback owner for the identity map on
-- the localized ring presheaf, and the source remark records that this lower shriek is exact.
/-- Remark 18.19.7 also records that the presheaf-level extension-by-zero functor
`j_{U!} = PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))` is exact. -/
theorem presheafLocalizedExtensionByZero_exact :
    exactFunctor
      (PresheafOfModules ((Over.forget U).op ⋙ 𝒪))
      (PresheafOfModules 𝒪)
      (PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))) := by
  sorry

-- Proof sketch: compute the objectwise left Kan extension defining `j_{U!}` along
-- `(Over.forget U).op`; as in Remark `7.25.10`, the indexing category over `V` is final over the
-- discrete family of arrows `φ : V ⟶ U`, so the value at `V` is the coproduct of the fibers
-- `𝒢(V \xrightarrow{φ} U)`.
/-- The value of presheaf extension by zero at `V` is canonically the coproduct of the fibers over
all arrows `V ⟶ U`. This is the module-valued counterpart of the Chapter 7 left-Kan-extension
formula for localization. -/
noncomputable def presheafLocalizedExtensionByZero_objIsoSigma
    (𝒢 : PresheafOfModules ((Over.forget U).op ⋙ 𝒪)) (V : C) :
    (((PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ 𝒪))).obj 𝒢).obj (op V)) ≅
      (∐ fun φ : V ⟶ U ↦ 𝒢.obj (op (Over.mk φ))) := by
  sorry

end PresheafLevel

section SheafComparison

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J RingCat.{u}) (U : C)

/- The comparison square in Remark 18.19.7 is exactly the upstream pullback/sheafification
comparison specialized to the identity map of the localized ring sheaf `𝒪_U`. -/
recall SheafOfModules.sheafificationCompPullback

end SheafComparison

/-! ### Lemma_18_19_8 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 18.19.8:
- primary domain: unit and counit isomorphisms for the localization adjunctions on abelian sheaves
  over the slice site `C/U`;
- sampled owner declarations:
  `overForget_full_of_subsingletonHom`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`,
  `counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful`;
- best owner abstraction: the adjunction owners
  `(Over.forget U).sheafAdjunctionContinuous AddCommGrpCat (J.over U) J` and
  `(Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat (J.over U) J`;
- primitive data: the site `J`, the object `U`, and the source hypothesis
  `hU : ∀ X, Subsingleton (X ⟶ U)`;
- derived API: the `IsIso` facts for the unit and counit components of those owners.

Source/core/bridge triage:
- `source-facing`: the two source statements for abelian sheaves on `C/U`;
- `core/canonical`: the unit and counit morphisms of the localization adjunction owners;
- `bridge/view`: the fullness of `Over.forget U` supplied by
  `overForget_full_of_subsingletonHom`.

This file should therefore keep the two specialized source-facing theorem names, but derive them
directly from the canonical owner instances instead of carrying parallel local proof data.
-/

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (U : C)

-- Proof sketch: the hypothesis implies that `Over.forget U` is fully faithful, so Lemma 18.16.4
-- applies to the adjunction `j_{U!} ⊣ j_U⁻¹` coming from the canonical pullback functor on abelian
-- sheaves.
/-- Lemma 18.19.8 (1): if every object of `C` has at most one morphism to `U`, then for every
abelian sheaf `ℱ` on the localized site `C/U` the canonical map
`ℱ ⟶ j_U⁻¹(j_{U!} ℱ)` is an isomorphism. -/
theorem localization_lowerShriek_unit_app_isIso_of_subsingletonHom
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v}, (Over.forget U).op.HasLeftKanExtension F]
    (ℱ : Sheaf (J.over U) AddCommGrpCat.{max u v}) :
    IsIso (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{max u v} (J.over U) J).unit.app
      ℱ) := by
  refine (fun hU ↦ ?_) hU
  letI : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  infer_instance

-- Proof sketch: the same full-faithfulness input reduces the statement to Lemma 18.16.4 for the
-- adjunction `j_U⁻¹ ⊣ j_{U*}`, where `j_{U*}` is the cocontinuous pushforward on abelian sheaves.
/-- Lemma 18.19.8 (2): if every object of `C` has at most one morphism to `U`, then for every
abelian sheaf `ℱ` on the localized site `C/U` the canonical map
`j_U⁻¹(j_{U*} ℱ) ⟶ ℱ` is an isomorphism. -/
theorem localization_inverseImage_pushforward_app_isIso_of_subsingletonHom
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (Over.forget U).op.HasPointwiseRightKanExtension F]
    (ℱ : Sheaf (J.over U) AddCommGrpCat.{max u v}) :
    IsIso (((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{max u v} (J.over U) J).counit.app
      ℱ) := by
  refine (fun hU ↦ ?_) hU
  letI : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  infer_instance

end CategoryTheory
