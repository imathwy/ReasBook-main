import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J' AddCommGrpCat.{u}]
variable [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}} {𝒪' : Sheaf J' CommRingCat.{u}}
variable [MonoidalCategory (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalCategory (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪'))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪'))]

/-- A cochain complex of `\mathcal O`-modules on a ringed site is K-flat when tensoring it with
any acyclic cochain complex preserves acyclicity. -/
def IsKFlat
    (K : CochainComplex
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ) : Prop :=
  ∀ ⦃F : CochainComplex
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ⦄
      [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
    (HomologicalComplex.tensorObj F K).Acyclic

-- Proof sketch: this is the defining condition for K-flatness on the ringed site written out
-- explicitly in terms of preservation of acyclic complexes under total tensor product.
/-- Unfolding `IsKFlat` says exactly that total tensoring with the fixed complex preserves acyclic
cochain complexes of `\mathcal O`-modules. -/
theorem isKFlat_iff
    (K : CochainComplex
      (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ) :
    IsKFlat K ↔
      ∀ ⦃F : CochainComplex
          (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ⦄
          [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
        (HomologicalComplex.tensorObj F K).Acyclic := sorry

variable (F : C' ⥤ C) [Functor.IsContinuous F J' J]
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J' J).obj 𝒪)

/-- The `RingCat`-valued structure map attached to the site-presented morphism of ringed topoi
determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap :
    (sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} J' J).obj
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose J' (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [(SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).PreservesZeroMorphisms]

-- Proof sketch: use Lemma `21.18.6` to reduce K-flatness on the source ringed site to K-flatness
-- of all stalk complexes, which is valid because `(\mathcal C, J)` has enough points. For a
-- source point, identify the stalk of the pulled-back complex with extension of scalars of the
-- corresponding target stalk via Lemma `18.36.4`, and then apply the module-theoretic extension
-- of scalars preservation of K-flatness from Lemma `15.59.3` to the stalkwise K-flatness coming
-- from the target complex.
/-- Lemma 21.18.7: if the source site of a site-presented morphism of ringed topoi has enough
points, then the pullback of a K-flat complex of `\mathcal O'`-modules is a K-flat complex of
`\mathcal O`-modules. -/
theorem pullback_isKFlat_of_isKFlat_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (K : CochainComplex
      (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪')) ℤ)
    (hK : IsKFlat K) :
    IsKFlat
      (((SheafOfModules.pullback
          (ringedSiteUnderlyingStructureMap F φ)).mapHomologicalComplex
            (up ℤ)).obj K) := sorry

end

end SheafOfModules.RingedSite
