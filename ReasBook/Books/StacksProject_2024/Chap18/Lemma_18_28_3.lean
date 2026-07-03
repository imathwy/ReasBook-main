import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite MonoidalCategory Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

-- Proof sketch: flatness of `ℱ` means that tensoring with `ℱ` is an exact endofunctor on
-- presheaves of modules. Module sheafification is exact, and the tensor-sheafification
-- comparison identifies tensoring with `ℱ^#` over `𝒪^#` with sheafifying tensoring with `ℱ`;
-- therefore the sheafification `ℱ^#` is flat over the sheafified structure sheaf `𝒪^#`.
/-- Lemma 18.28.3: if a presheaf of `\mathcal O`-modules `\mathcal F` on a site is flat, then its
sheafification `\mathcal F^\#` is a flat `\mathcal O^\#`-module in the chapter's canonical
sheaf-level flatness owner. -/
theorem sheafification_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat ℱ] :
    SheafOfModules.RingedSite.IsFlat (commRingSheafification J 𝒪)
      ((moduleSheafification J 𝒪).obj ℱ) := sorry

/-- The sheafification of a flat presheaf carries its canonical flatness instance. -/
instance
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat ℱ] :
    SheafOfModules.RingedSite.IsFlat (commRingSheafification J 𝒪)
      ((moduleSheafification J 𝒪).obj ℱ) :=
  sheafification_isFlat J 𝒪 ℱ

end PresheafOfModules
