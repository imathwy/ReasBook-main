import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪')

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
private abbrev ringedSiteUnderlyingStructureMap :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪') :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [MonoidalCategory (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalCategory (SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪'))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪'))]

-- Proof sketch: apply Lemma `18.39.1` degreewise to obtain flatness of every pulled-back term.
-- For K-flatness, follow the textbook resolution argument: replace `K` by the sequential
-- bounded-above flat resolution tower from Lemma `21.17.10`, pull that tower back termwise,
-- use Lemmas `21.17.8` and `21.17.9` to keep the pulled-back colimit K-flat, and then apply the
-- short-exact-sequence criterion of Lemma `21.17.7` after pulling back the comparison short exact
-- sequence via Lemma `18.39.4`.
/-- Lemma 21.18.1: for a site-presented morphism of ringed topoi, pulling back a K-flat cochain
complex of `\mathcal O`-modules whose terms are flat yields a K-flat cochain complex of
`\mathcal O'`-modules whose terms are flat. -/
theorem pullback_isKFlat_and_termwiseFlat_of_isKFlat_and_termwiseFlat
    (K : CochainComplex
      (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪)) ℤ)
    (hKFlat : IsKFlat K)
    (hFlat : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    IsKFlat
      (((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)
          ).mapHomologicalComplex (up ℤ)).obj K) ∧
    ∀ n : ℤ,
      IsFlat 𝒪'
        ((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj (K.X n)) := sorry

end

end SheafOfModules.RingedSite
