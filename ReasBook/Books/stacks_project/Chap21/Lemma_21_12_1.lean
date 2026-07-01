import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

/-- Lemma 21.12.1: an injective sheaf of modules on a ringed site is injective as an object of
`PMod(𝒪)`, i.e. of the category `PresheafOfModules 𝒪.obj` of presheaves of `𝒪`-modules. -/
-- Proof sketch: apply Lemma `12.29.1` to the adjunction
-- `PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)`. The left adjoint is exact because
-- module sheafification preserves finite limits, so the right adjoint `SheafOfModules.forget 𝒪`
-- preserves injective objects.
theorem injective_as_presheaf_of_modules
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    (F : SheafOfModules.{v} 𝒪) (hF : Injective F) :
    Injective ((SheafOfModules.forget 𝒪).obj F) := sorry

end CategoryTheory
