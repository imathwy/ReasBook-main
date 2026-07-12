import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open RingedSite.Hom (ModuleDerived)

open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v

namespace RingedSite.Hom

section

variable {C : Type v} [Category.{v} C]
variable {D : Type v} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD]
variable (𝒪D : Sheaf JD CommRingCat.{v})

variable [Abelian (ModuleCat (RingedSite.ofRingSheaf JC
  (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D))))]
variable [CategoryWithHomology (ModuleCat (RingedSite.ofRingSheaf JC
  (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D))))]
variable [Abelian (ModuleCat (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)))]
variable [CategoryWithHomology (ModuleCat (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)))]
variable [((moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D))^*).Additive]
variable [((moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D))^*).IsRightAdjoint]
variable [Functor.Additive (modulePushforward (moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)))
  (ModuleQis (RingedSite.ofRingSheaf JC
    (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D))))]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)))
  (ModuleQis (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)))]

variable
  (K : ModuleDerived (RingedSite.ofRingSheaf JC
    (inverseImageRingSheaf JC JD u (ringSheaf JD 𝒪D))))
  (L : ModuleDerived (RingedSite.ofRingSheaf JD (ringSheaf JD 𝒪D)))

local notation "g" => moduleInverseImageHom JC JD u (ringSheaf JD 𝒪D)

/- Domain-style sampling for 21.37.2.1:
- primary domain: the Hom-set equivalence induced by the canonical Chapter 21 derived adjunction
  for the inverse-image morphism of ringed sites attached to `u`;
- sampled owner declarations:
  `moduleInverseImageHom`,
  `modulePullbackDerived_pushforward_adjunction`,
  `Adjunction.homEquiv`;
- best owner abstraction:
  `source-facing`: the textbook equivalence
    `Hom_{D(g^{-1}\mathcal O_\mathcal D)}(K, R(g)_* L) ≃
      Hom_{D(\mathcal O_\mathcal D)}(L(g)^* K, L)`;
  `core/canonical`: the Chapter 21 adjunction owner
    `modulePullbackDerived_pushforward_adjunction g : L(g)^* ⊣ R(g)_*`;
  `bridge/view`: the source orientation is the symmetric form of the owner equivalence
    `Adjunction.homEquiv`.

Primitive data are only the site functor `u`, the structure sheaf `𝒪D`, the associated ringed-site
morphism `g`, and the objects `K`, `L`. No new wrapper is needed here: once the canonical derived
adjunction owner is available, the source bijection is exactly its specialized `homEquiv`.
-/

/- 21.37.2.1 is specialized to the Chapter 21 derived adjunction
`modulePullbackDerived_pushforward_adjunction g : L(g)^* ⊣ R(g)_*`. -/
recall modulePullbackDerived_pushforward_adjunction

/- 21.37.2.1: morphisms `K ⟶ R(g)_* L` correspond canonically to morphisms
`L(g)^* K ⟶ L`. This is exactly the symmetric form of the Hom-set equivalence attached to the
canonical derived adjunction owner above. -/
#check
  (((modulePullbackDerived_pushforward_adjunction g).homEquiv K L).symm :
    (K ⟶ (R(g)_*).obj L) ≃ ((L(g)^*).obj K ⟶ L))

end

end RingedSite.Hom
