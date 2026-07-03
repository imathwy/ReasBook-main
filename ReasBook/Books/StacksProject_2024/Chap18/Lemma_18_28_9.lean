import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Tensoring presheaves of modules on the right by a fixed module preserves zero morphisms. -/
instance tensorRight_preservesZeroMorphisms
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪)) :
    (tensorRight 𝒢).PreservesZeroMorphisms := sorry

-- Proof sketch: resolve the right tensor factor by a short exact sequence with flat middle term,
-- apply the exactness built into flatness of `S.X₃`, and conclude with the snake lemma exactly as
-- in the textbook.
/-- Lemma 18.28.9 (1): if `0 ⟶ \mathcal F'' ⟶ \mathcal F' ⟶ \mathcal F ⟶ 0` is a short exact
sequence of presheaves of `\mathcal O`-modules and `\mathcal F` is flat, then tensoring on the
right by any presheaf `\mathcal G` preserves short exactness. -/
theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- Tensoring sheaves of modules on the right by a fixed module preserves zero morphisms. -/
instance sheafModuleTensorRightFunctor_preservesZeroMorphisms
    (𝒢 : SheafOfModules (ringSheaf J 𝒪)) :
    (sheafModuleTensorRightFunctor 𝒢).PreservesZeroMorphisms := sorry

-- Proof sketch: argue exactly as in the presheaf case, replacing the presheaf tensor product by
-- the sheaf tensor product and using flatness of `S.X₃` as a sheaf of modules.
/-- Lemma 18.28.9 (2): if `(\mathcal C, J)` is a site, `0 ⟶ \mathcal F'' ⟶ \mathcal F' ⟶
\mathcal F ⟶ 0` is a short exact sequence of sheaves of `\mathcal O`-modules, and `\mathcal F`
is flat, then tensoring on the right by any sheaf `\mathcal G` preserves short exactness. -/
theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : SheafOfModules (ringSheaf J 𝒪))
    (S : ShortComplex (SheafOfModules (ringSheaf J 𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (sheafModuleTensorRightFunctor 𝒢)).ShortExact := sorry

end SheafOfModules.RingedSite
