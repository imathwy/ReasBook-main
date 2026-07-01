import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪D : Sheaf JC RingCat.{max u v}} {𝒪C : Sheaf JD RingCat.{max u v}}
variable (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a ringed site with
structure sheaf `\mathcal O`. -/
private abbrev RingedSiteModules
    {E : Type u} [Category.{v} E] (J : GrothendieckTopology E)
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  SheafOfModules 𝒪

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules. -/
private abbrev RingedSiteDerived
    {E : Type u} [Category.{v} E] (J : GrothendieckTopology E)
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of
`\mathcal O`-modules. -/
private abbrev RingedSiteQis
    {E : Type u} [Category.{v} E] (J : GrothendieckTopology E)
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

/-- The pullback functor on module sheaves attached to the site-presented morphism of ringed
sites determined by `φ`. -/
private abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
    [(SheafOfModules.pushforward φ).IsRightAdjoint] :
    RingedSiteModules JC 𝒪D ⥤ RingedSiteModules JD 𝒪C :=
  SheafOfModules.pullback φ

/-- The functor on homotopy categories induced by pullback on module sheaves. -/
private abbrev mapHomotopyCategoryToDerived
    {A B : Type _} [Category A] [Preadditive A] [Category B] [Abelian B] (G : A ⥤ B)
    [G.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory B :=
  G.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The functor on homotopy categories induced by pullback on module sheaves. -/
private abbrev pullbackToDerived
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(pullbackFunctor F φ).Additive] :=
  mapHomotopyCategoryToDerived (pullbackFunctor F φ)

/-- The unbounded derived pullback functor `Lf^* : D(\mathcal O_\mathcal D) \to
D(\mathcal O_\mathcal C)`. -/
private noncomputable abbrev pullbackDerived
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(pullbackFunctor F φ).Additive]
    [Functor.HasLeftDerivedFunctor (pullbackToDerived F φ) (RingedSiteQis JC 𝒪D)] :
    RingedSiteDerived JC 𝒪D ⥤ RingedSiteDerived JD 𝒪C :=
  Functor.totalLeftDerived (pullbackToDerived F φ)
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSiteModules JC 𝒪D) (up ℤ) ⥤
        RingedSiteDerived JC 𝒪D)
    (RingedSiteQis JC 𝒪D)

-- Proof sketch: choose a representative complex for `E` together with local strictly perfect
-- approximations realizing `m`-pseudo-coherence. Pull those approximations back along `f`,
-- localize to reduce to the final-object case, preserve strict perfectness under pullback, and
-- use the cone-vanishing argument for left derived functors to keep the cohomological control in
-- degrees `> m` and degree `m`.
/-- Lemma 21.45.3: for a site-presented morphism of ringed sites determined by `φ`, if
`E ∈ D(\mathcal O_\mathcal D)` is `m`-pseudo-coherent, then the derived pullback `Lf^*E` is
`m`-pseudo-coherent in `D(\mathcal O_\mathcal C)`. -/
theorem pullbackDerived_isMPseudoCoherent
    (sourceIsMPseudoCoherent : RingedSiteDerived JC 𝒪D → ℤ → Prop)
    (targetIsMPseudoCoherent : RingedSiteDerived JD 𝒪C → ℤ → Prop)
    [(pullbackFunctor F φ).Additive]
    [Functor.HasLeftDerivedFunctor (pullbackToDerived F φ) (RingedSiteQis JC 𝒪D)]
    (E : RingedSiteDerived JC 𝒪D) (m : ℤ)
    (hE : sourceIsMPseudoCoherent E m) :
    targetIsMPseudoCoherent ((pullbackDerived F φ).obj E) m := sorry

end

end RingedSite.Hom
