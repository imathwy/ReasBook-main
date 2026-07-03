import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_21_1 (from Chap18) -/
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

/-! ### Definition_18_21_2 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

namespace RingedSite

section

variable {C : Type (max u v)} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Sheaf J (Type v))

/- Domain-style sampling for Definition 18.21.2:
- primary domain: localization of a ringed topos at an arbitrary object of the underlying topos,
  using the category-of-elements site presentation of the slice topos;
- sampled owner declarations:
  `localizationProjection`,
  `localizationTopology`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `sheafCategoryOfElementsEquivOver`,
  `Over.forgetAdjStar`;
- best owner abstraction: the source-facing localized ringed site is the `RingedSite` on the
  category of elements of `ℱ`, with topology `localizationTopology ℱ` and structure sheaf pulled
  back along `localizationProjection ℱ`; the correctly oriented localization morphism
  `j_ℱ : Sh(localizationTopology ℱ) ⟶ Sh(C, J)` is canonically owned by
  `(localizationProjection ℱ).morphismOfTopoiInOfCocontinuous (localizationTopology ℱ) J` and,
  under the slice equivalence, by `Over.forgetAdjStar ℱ`;
- primitive data: the structure sheaf `𝒪` and the sheaf `ℱ`;
- derived API: the localized ringed site `localizationAtSheaf 𝒪 ℱ`, the pushforward-form
  structure map `localizationAtSheafStructureMap 𝒪 ℱ`, the equivalence with the slice topos
  `Over ℱ`, the induced inverse-image comparison with `Over.star ℱ`, and the representable bridge
  to `𝒪.over U` and `SheafOfModules.pushforwardOver U`.

Source/core/bridge triage:
- `source-facing`: `localizationAtSheaf 𝒪 ℱ` and `localizationAtSheafStructureMap 𝒪 ℱ`,
  presenting `(Sh(C, J) / ℱ, 𝒪_ℱ)` and the ringed structure map `j_ℱ^♯`;
- `core/canonical`: the category-of-elements localization owners `localizationProjection ℱ` and
  `localizationTopology ℱ`, together with
  `(localizationProjection ℱ).morphismOfTopoiInOfCocontinuous (localizationTopology ℱ) J` and
  the slice-topos adjunction `Over.forgetAdjStar ℱ`;
- `bridge/view`: `sheafCategoryOfElementsEquivOver ℱ`,
  `sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ`, and the representable
  comparison API from Lemma `18.21.3`.
-/

/-- Definition 18.21.2: the localization of the ringed topos `(Sh(C, J), 𝒪)` at a sheaf `ℱ`
is the ringed site on the category of elements of `ℱ`, with the induced topology and the
inverse-image structure sheaf. This is the source-facing ringed presentation of
`(Sh(C, J) / ℱ, 𝒪_ℱ)`. -/
def localizationAtSheaf (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Sheaf J (Type v)) :
    RingedSite where
  carrier := ℱ.obj.Elementsᵒᵖ
  str := inferInstance
  siteTopology := localizationTopology ℱ
  structureSheaf :=
    ((localizationProjection ℱ).sheafPushforwardContinuous
      RingCat.{max u v} (localizationTopology ℱ) J).obj 𝒪

/-- The structure sheaf of `localizationAtSheaf 𝒪 ℱ` is the pullback of `𝒪` along the canonical
projection from the category of elements of `ℱ`. -/
theorem localizationAtSheaf_structureSheaf
    (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Sheaf J (Type v)) :
    (localizationAtSheaf 𝒪 ℱ).structureSheaf =
      ((localizationProjection ℱ).sheafPushforwardContinuous
        RingCat.{max u v} (localizationTopology ℱ) J).obj 𝒪 :=
  rfl

/- The correctly oriented localization morphism
`j_ℱ : Sh(localizationTopology ℱ) ⟶ Sh(C, J)` is already canonically owned by the cocontinuous
projection from the category of elements. Under `sheafCategoryOfElementsEquivOver ℱ`, this agrees
with the slice localization morphism from `Over.forgetAdjStar ℱ`. -/
#check
  ((localizationProjection ℱ).morphismOfTopoiInOfCocontinuous
    (localizationTopology ℱ) J : MorphismOfTopoiIn J (localizationTopology ℱ))

/-- The canonical pushforward-form structure-sheaf map
`j_ℱ^♯ : 𝒪 ⟶ j_{ℱ,*} 𝒪_ℱ`, obtained by adjunction from the identity
`j_ℱ^{-1} 𝒪 = 𝒪_ℱ`. -/
abbrev localizationAtSheafStructureMap
    (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Sheaf J (Type v)) :
    𝒪 ⟶
      ((localizationProjection ℱ).sheafPushforwardCocontinuous
          RingCat.{max u v} (localizationTopology ℱ) J).obj
        (localizationAtSheaf 𝒪 ℱ).structureSheaf :=
  ((localizationProjection ℱ).sheafAdjunctionCocontinuous
    RingCat.{max u v} (localizationTopology ℱ) J).homEquiv 𝒪
      (localizationAtSheaf 𝒪 ℱ).structureSheaf
      (show
        ((localizationProjection ℱ).sheafPushforwardContinuous
            RingCat.{max u v} (localizationTopology ℱ) J).obj 𝒪 ⟶
          (localizationAtSheaf 𝒪 ℱ).structureSheaf from
        𝟙 _)

/- Companion bridge: the underlying topos of `localizationAtSheaf 𝒪 ℱ` is canonically
equivalent to the slice topos `Sh(C, J) / ℱ`. -/
#check sheafCategoryOfElementsEquivOver ℱ

/- Companion bridge: under this equivalence, the inverse-image functor induced by the projection
from the category of elements of `ℱ` identifies with the canonical slice inverse image
`Over.star ℱ`. -/
#check sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ

/- Companion recall: the underlying localization morphism of topoi is the canonical slice
adjunction `Over.forgetAdjStar ℱ`. -/
recall Over.forgetAdjStar

end

section

variable {C : Type u} [Category.{v} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v}) (U : C)

/- Companion bridge: in the representable localization at `U`, the localized structure sheaf
`𝒪_U` is the canonical restricted sheaf `𝒪.over U` on the slice site `C / U`. -/
#check (𝒪.over U)

/- Companion bridge: in the representable case, the structure-map part `j_U^♯` is the canonical
owner `SheafOfModules.pushforwardOver U`. -/
#check (SheafOfModules.pushforwardOver U)

/- Companion bridge: the module-level adjunction for the representable localization is the
canonical owner `SheafOfModules.overPushforwardOverAdj U`. -/
recall SheafOfModules.overPushforwardOverAdj

end

end RingedSite

/-! ### Lemma_18_21_3 (from Chap18) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open scoped SheafifiedRepresentable

universe w

noncomputable section

section

variable {C : Type w} [Category.{w} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type w)]
variable (𝒪 : Sheaf J RingCat.{w}) (U : C)

/- Domain-style sampling for Lemma 18.21.3:
- primary domain: representable localization of a ringed topos, expressed through the bridge from
  the general localization-at-a-sheaf construction to the slice-site localization at `U`;
- sampled owner declarations:
  `RingedSite.localizationAtSheaf`,
  `RingedSite.localizationAtSheafStructureMap`,
  `RingedSite.localization`,
  `SheafOfModules.pushforwardOver`,
  `GrothendieckTopology.representableLocalizationComparison_forget`,
  `SheafOfModules.overPushforwardOverAdj`;
- best owner abstraction: the source-facing owner is
  `RingedSite.localizationAtSheaf`, with bridge data carried by
  `RingedSite.localizationAtSheafStructureMap` and the comparison
  `J.representableLocalizationComparison_forget U`;
- primitive data: the site `(C, J)`, the ring sheaf `𝒪`, and the object `U : C`;
- derived API: the representable localized structure sheaf `𝒪.over U`, the canonical structure
  morphism `SheafOfModules.pushforwardOver U`, and the module adjunction
  `SheafOfModules.overPushforwardOverAdj U`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.localizationAtSheaf` and
  `RingedSite.localizationAtSheafStructureMap`, specialized here to the representable case;
- `core/canonical`: `RingedSite.localization`, `SheafOfModules.pushforwardOver`, and
  `SheafOfModules.overPushforwardOverAdj`;
- `bridge/view`: `J.representableLocalizationComparison_forget U`, identifying the underlying
  localization functor at `h_U^#` with the representable localization at `U`.
-/

/- Lemma 18.21.3: for the representable sheaf `ℱ = h[U]^#[J]`, the general localization-at-a-sheaf
owner is definitionally the slice-site localization at `U`. -/
theorem localizationAtSheaf_sheafifiedRepresentable_eq_localization :
    RingedSite.localizationAtSheaf 𝒪 h[U]^#[J] =
      RingedSite.localization { carrier := C, siteTopology := J, structureSheaf := 𝒪 } U :=
  by
    sorry

/- Companion recall: on underlying topoi, the equivalence of Lemma `7.25.4` identifies the
localization morphism `j_U` with the slice forgetful functor over `h[U]^#[J]`, as recorded in
Lemma `7.30.5`. -/
#check (J.representableLocalizationComparison_forget U)

/- Companion recall: the module-level adjunction encoding the representable ringed localization is
the canonical owner `SheafOfModules.overPushforwardOverAdj U`. -/
recall SheafOfModules.overPushforwardOverAdj

end

/-! ### Lemma_18_21_4 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits

universe u v w

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒢 ℱ : Sheaf J (Type w)} (s : 𝒢 ⟶ ℱ)

/- Domain-style sampling for Lemma 18.21.4:
- primary domain: relocalization of localizations of a ringed topos, with the canonical slice-topos
  comparison on the underlying topoi and the induced comparison on localized structure sheaves;
- sampled owner declarations:
  `Over.forgetAdjStar`,
  `Over.star`,
  `Over.pullback`,
  `Over.starPullbackIsoStar`,
  `sheafCompose`;
- best owner abstraction: the underlying relocalization comparison is already owned by the
  canonical slice base-change isomorphism `Over.starPullbackIsoStar`, and the ringed refinement is
  the specialization of that same owner to the forgotten structure sheaf;
- primitive data: a morphism of sheaves `s : 𝒢 ⟶ ℱ`;
- derived API: the localization inverse-image functors `Over.star ℱ`, `Over.star 𝒢`, the
  pullback functor `Over.pullback s`, and the induced comparison on localized structure sheaves
  after forgetting ring structure.

Source/core/bridge triage:
- `source-facing`: the commutative triangle of localization morphisms of ringed topoi attached to
  `s`, including compatibility of the structure-sheaf maps;
- `core/canonical`: `Over.starPullbackIsoStar`;
- `bridge/view`: the explicit source and target functors `Over.star ℱ ⋙ Over.pullback s` and
  `Over.star 𝒢`, and the specialization of their comparison to the forgotten structure sheaf.

Primitive data and derived API separate cleanly here: the owner only needs the sheaf map `s`,
while the ringed statement is obtained by applying that owner to the underlying structure sheaf.
This file should therefore reuse `Over.starPullbackIsoStar` directly as the main entry and expose
the structure-sheaf compatibility only as its thin derived companion.
-/
/- Lemma 18.21.4: for a morphism of sheaves `s : 𝒢 ⟶ ℱ` on a ringed topos
`(\mathit{Sh}(\mathcal C), \mathcal O)`, the natural commutative triangle of localization
morphisms of the underlying topoi is the canonical relocalization comparison
`Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢`. This is the topos-level part of the ringed-topos
diagram, and the ringed refinement is obtained by transporting the structure sheaf along this
localization square. -/
recall Over.starPullbackIsoStar

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒢 ℱ : Sheaf J (Type (max u v))} (s : 𝒢 ⟶ ℱ)
variable (𝒪 : Sheaf J RingCat.{max u v})

/- Companion bridge: applying the canonical relocalization isomorphism to the forgotten
structure sheaf gives the comparison on localized structure sheaves. This is the underlying
sheaf-level content of the statement that `j_𝒢^♯` is obtained from `j_ℱ^♯` by relocalization. -/
#check
  ((Over.starPullbackIsoStar s).app
    ((sheafCompose J (forget RingCat.{max u v})).obj 𝒪))

/- Companion view: the morphism on the underlying sheaves of sets is the map appearing in the
commutative ringed-topos triangle. -/
#check
  (((Over.starPullbackIsoStar s).app
      ((sheafCompose J (forget RingCat.{max u v})).obj 𝒪)).hom.left)

end

end

/-! ### Lemma_18_21_5 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

/- Lemma 18.21.5: after identifying the representable localizations
`(j_ℱ, j_ℱ^♯) = (j_U, j_U^♯)` and `(j_𝒢, j_𝒢^♯) = (j_V, j_V^♯)` from Lemma 18.21.3, the
inverse-image square of Lemma 18.21.4 is the same canonical pullback square as in Lemma 18.19.5.
The underlying topos-level comparison is the standard slice-topos isomorphism
`Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢`. -/
recall Over.starPullbackIsoStar

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v}) (U : C)

/- Companion recall: under the identifications of Lemma 18.21.3, the structure-sheaf component
`j_U^♯` is the canonical representable localization map on sheaves of rings. This is the `j^♯`
appearing in the ringed refinement of Lemma 18.21.5. -/
#check (SheafOfModules.pushforwardOver (R := 𝒪) U)

end
