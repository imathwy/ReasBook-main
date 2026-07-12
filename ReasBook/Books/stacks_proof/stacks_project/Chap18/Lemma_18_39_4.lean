import Mathlib
import StacksProject_2024.Chap18.Lemma_18_39_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪')

/-- The underlying `RingCat`-valued structure map attached to a morphism of sheaves of
commutative rings over a continuous functor of sites. -/
abbrev ringedSiteUnderlyingStructureMap :
    ringSheaf JC 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj (ringSheaf JD 𝒪') :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

-- Proof sketch: apply exactness of the inverse-image functor to obtain a short exact sequence of
-- `f⁻¹𝒪`-modules, use Lemma `18.39.1` to see that the pulled-back quotient remains flat over
-- `f⁻¹𝒪`, and then apply the short-exactness preservation under tensoring with a flat quotient from
-- Lemma `18.28.9` to the extension-of-scalars description of `f^*`.
/-- Lemma 18.39.4: for a site-presented morphism of ringed topoi or ringed sites, pulling back a
short exact sequence of `\mathcal O`-modules along `f^*` preserves short exactness provided the
quotient term is flat. -/
@[stacks 0G6R]
theorem pullback_shortExact_of_flat_quotient
    (S : ShortComplex (SheafOfModules (ringSheaf JC 𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ))).ShortExact := by
  -- Proof comment: first pull back the flat quotient term itself; Lemma `18.39.1` supplies the
  -- resulting flatness over the target structure sheaf.
  letI :
      IsFlat 𝒪'
        ((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj S.X₃) :=
    _root_.pullback_isFlat_of_isFlat (F := F) (φ := φ) (ℱ := S.X₃)
  -- Proof comment: once the quotient stays flat after pullback, the target short exactness is
  -- exactly the canonical preservation theorem for pullback along a morphism of ringed sites.
  infer_instance

end
