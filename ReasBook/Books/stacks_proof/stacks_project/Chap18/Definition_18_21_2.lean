import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Lemma_7_21_1
import stacks_proof.stacks_project.Chap07.Lemma_7_30_3
import stacks_proof.stacks_project.Chap18.Definition_18_6_1

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
  to `𝒪.over U` and `representableLocalizationStructureMap 𝒪 U`.

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
@[stacks 04J2]
abbrev localizationAtSheaf (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Sheaf J (Type v)) :
    RingedSite :=
  ofRingSheaf (localizationTopology ℱ)
    (((localizationProjection ℱ).sheafPushforwardContinuous
      RingCat.{max u v} (localizationTopology ℱ) J).obj 𝒪)

/- Companion recall: the source-facing localization morphism is the canonical morphism of topoi
owned by the localization projection. -/
#check ((localizationProjection ℱ).morphismOfTopoiInOfCocontinuous (localizationTopology ℱ) J :
  MorphismOfTopoiIn J (localizationTopology ℱ))

/- Companion recall: the localized topos is equivalent to the slice topos `Sh(C, J) / ℱ`. -/
recall sheafCategoryOfElementsEquivOver

/- Companion recall: under this equivalence, the localized inverse-image functor matches
`Over.star ℱ`. -/
recall sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar

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
      (𝟙 _)

end

section

variable {C : Type u} [Category.{v} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v}) (U : C)

/- Companion recall: in the representable case, the localized structure sheaf is the usual
restriction of `𝒪` to the slice site. -/
#check 𝒪.over U

/-- Companion bridge: in the representable localization at `U`, the structure-map part `j_U^♯`
specialized to the ring sheaf `𝒪` is the canonical representable localization map on sheaves of
rings. This source-facing bridge fixes the ambient structure-sheaf parameter that is not
recoverable from `U` alone, while still reusing the core owner `SheafOfModules.pushforwardOver`.
-/
abbrev representableLocalizationStructureMap :
    𝒪 ⟶ ((Over.star U).sheafPushforwardContinuous RingCat.{max u v} J (J.over U)).obj
      (𝒪.over U) :=
  SheafOfModules.pushforwardOver U

/- Companion recall: this representable localization map is the source-facing owner for the
structure map in the slice-site model. -/
#check representableLocalizationStructureMap 𝒪 U

end

end RingedSite
