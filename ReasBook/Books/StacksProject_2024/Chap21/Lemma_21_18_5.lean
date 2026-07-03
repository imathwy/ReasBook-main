import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : D ⥤ C)
variable [Functor.IsContinuous F JD JC]
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify JC CommRingCat.{max u v}]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify JD CommRingCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
variable (𝒪 : Sheaf JC CommRingCat.{max u v}) (𝒪' : Sheaf JD CommRingCat.{max u v})
variable [Abelian (ringedSiteModuleCategory JC 𝒪)]
variable [Abelian (ringedSiteModuleCategory JD 𝒪')]
variable
  [Abelian
    (ringedSiteModuleCategory
      JC
      ((F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪'))]

local notation "DModC" => DerivedCategory (ringedSiteModuleCategory JC 𝒪)
local notation "DModD" => DerivedCategory (ringedSiteModuleCategory JD 𝒪')
local notation "DModPull" =>
  DerivedCategory
    (ringedSiteModuleCategory
      JC
      ((F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪'))

variable
  (derivedTensorSource : DModC ⥤ DModC ⥤ DModC)
  (derivedTensorPulled : DModPull ⥤ DModC ⥤ DModC)
  (leftDerivedPullback : DModD ⥤ DModC)
  (inverseImageDerived : DModD ⥤ DModPull)

-- Proof sketch: at the abelian level, `f^*` is extension of scalars
-- `\mathcal O \otimes_{f^{-1}\mathcal O'} f^{-1}(-)`. Replace the two derived tensor products by
-- K-flat or projective resolutions, identify the underived comparison on the chosen resolutions,
-- and descend the resulting quasi-isomorphism to the derived categories. The canonical
-- bifunctoriality is encoded as a natural isomorphism in the functor category
-- `D(\mathcal O') ⥤ D(\mathcal O) ⥤ D(\mathcal O)`.
/-- Lemma 21.18.5: for a morphism of ringed topoi presented by a continuous functor of sites and a
structure-sheaf map `f^{-1}\mathcal O' \to \mathcal O`, the canonical bifunctorial isomorphism
`\mathcal F^\bullet \otimes_\mathcal O^{\mathbf L} Lf^* \mathcal G^\bullet \cong
\mathcal F^\bullet \otimes_{f^{-1}\mathcal O'}^{\mathbf L} f^{-1}\mathcal G^\bullet`
is expressed canonically as a natural isomorphism of functors
`D(\mathcal O') ⥤ D(\mathcal O) ⥤ D(\mathcal O)`. -/
theorem derivedTensor_leftDerivedPullback_iso :
    leftDerivedPullback ⋙ derivedTensorSource ≅
      inverseImageDerived ⋙ derivedTensorPulled := sorry

end

end SheafOfModules.RingedSite
