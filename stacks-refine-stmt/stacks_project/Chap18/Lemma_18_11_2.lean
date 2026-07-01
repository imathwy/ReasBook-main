import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J RingCat.{u}]
variable [J.WEqualsLocallyBijective RingCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

/- Lemma 18.11.2: for a presheaf of rings `𝒪` on a site `(C, J)`, the sheafification functor
`PMod(𝒪) ⥤ Mod(𝒪^\#)` is exact. The canonical owner-level form is the bundled exact functor
`ExactFunctor.of (PresheafOfModules.sheafification (toSheafify J 𝒪))`. -/
#check
  (ExactFunctor.of (PresheafOfModules.sheafification (toSheafify J 𝒪)) :
    PresheafOfModules 𝒪 ⥤ₑ
      SheafOfModules ((presheafToSheaf J RingCat.{u}).obj 𝒪))

end
