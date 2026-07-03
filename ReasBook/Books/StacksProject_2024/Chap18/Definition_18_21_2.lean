import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_21_1
import StacksProject_2024.Chap07.Lemma_7_30_3
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

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
