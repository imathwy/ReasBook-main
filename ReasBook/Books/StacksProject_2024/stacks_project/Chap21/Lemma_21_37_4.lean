import StacksProject_2024.Chap21.Lemma_21_14_1
import StacksProject_2024.Chap21.Lemma_21_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable {𝒪D : Sheaf JD RingCat.{u}}

local notation "𝒪C" => inverseImageRingSheaf JC JD u 𝒪D
local notation "g⁻¹Mod" =>
  RingedSite.Hom.modulePushforward (moduleInverseImageHom JC JD u 𝒪D)

/- Domain-style sampling for Lemma 21.37.4:
- primary domain: inverse-image functors on sheaves of modules over the ringed-site morphism
  attached to a continuous functor of sites, with the acyclicity conclusion expressed through the
  underlying abelian-sheaf owner `CategoryTheory.Sheaf.IsTotallyAcyclicOne`;
- sampled owner declarations:
  `inverseImageRingSheaf`,
  `moduleInverseImageHom`,
  `RingedSite.Hom.modulePushforward`,
  `CategoryTheory.Sheaf.IsTotallyAcyclicOne`,
  `RingedSite.Hom.modulePushforward_isTotallyAcyclicOne_of_injective`;
- best owner abstraction:
  `source-facing`: the inverse image of an injective module sheaf along the site morphism attached
    to `u`;
  `core/canonical`: `RingedSite.Hom.modulePushforward_isTotallyAcyclicOne_of_injective`;
  `bridge/view`: specialize that canonical owner to `moduleInverseImageHom JC JD u 𝒪D`.

This item is a source-facing specialization of the general ringed-site result
`RingedSite.Hom.modulePushforward_isTotallyAcyclicOne_of_injective`. The cocontinuity and
pullback-preservation hypotheses from the textbook proof are therefore omitted from the exported
API: once the inverse-image ringed-site morphism `moduleInverseImageHom JC JD u 𝒪D` is fixed,
they are proof-route data rather than owner data. -/

/-- Lemma 21.37.4: let `u : 𝒞 ⥤ 𝒟` be continuous, let `𝒪D` be a sheaf of rings on `𝒟`, and let
`ℐ` be an injective `𝒪D`-module. Then the inverse image `g⁻¹ ℐ`, formalized by
`RingedSite.Hom.modulePushforward (moduleInverseImageHom JC JD u 𝒪D)`, has totally acyclic
underlying abelian sheaf. This is the source-facing specialization of
`RingedSite.Hom.modulePushforward_isTotallyAcyclicOne_of_injective` to the inverse-image
ringed-site morphism attached to `u`. -/
@[stacks 0D6Y]
instance moduleInverseImage_isTotallyAcyclicOne_of_injective
    (ℐ : SheafOfModules 𝒪D) [Injective ℐ] :
    IsTotallyAcyclicOne ((SheafOfModules.toSheaf 𝒪C).obj ((g⁻¹Mod).obj ℐ)) := by
  simpa using
    RingedSite.Hom.modulePushforward_isTotallyAcyclicOne_of_injective
      (moduleInverseImageHom JC JD u 𝒪D) ℐ

end

end CategoryTheory
