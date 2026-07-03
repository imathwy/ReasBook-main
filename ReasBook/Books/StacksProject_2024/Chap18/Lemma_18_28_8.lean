import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_28_5
import StacksProject_2024.Chap18.Lemma_18_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

-- Proof sketch: for each pair `(U, s)` with `U : C` and `s ∈ ℱ(U)`, the adjunction defining
-- `j_{U!}` gives a morphism `j_{U!}\mathcal O_U ⟶ ℱ` sending `1` to `s`. Taking the coproduct over
-- all such pairs yields a morphism whose components generate every section objectwise, hence an
-- epimorphism.
/-- Lemma 18.28.8 (1): any presheaf of `\mathcal O`-modules is the quotient of a direct sum of
lower-shriek modules `j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_localizedStructureModuleExtensionByZero
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ), Epi φ := sorry

-- Proof sketch: apply part `(1)` to obtain an epimorphism from a coproduct of the modules
-- `j_{U_i!}\mathcal O_{U_i}`. Each summand is flat by Lemma `18.28.7 (1)`, and the coproduct is
-- flat by Lemma `18.28.5 (2)`, giving a flat source surjecting onto `ℱ`.
/-- Lemma 18.28.8 (2): any presheaf of `\mathcal O`-modules is the quotient of a flat presheaf of
`\mathcal O`-modules. -/
theorem exists_epi_from_flat
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    ∃ (𝒢 : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))
      (_h𝒢 : IsFlat 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

-- Proof sketch: repeat the presheaf argument in the sheaf category, or apply the presheaf result
-- and then sheafify. For each local section over `U`, adjunction produces a map
-- `j_{U!}\mathcal O_U ⟶ ℱ`; the induced coproduct map is epimorphic.
/-- Lemma 18.28.8 (3): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of rings, then
any sheaf of `\mathcal O`-modules is the quotient of a direct sum of lower-shriek modules
`j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_localizedStructureModuleExtensionByZero
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ), Epi φ := sorry

-- Proof sketch: combine part `(3)` with Lemma `18.28.7 (2)` for flatness of each
-- `j_{U_i!}\mathcal O_{U_i}`, then use direct sums of flat sheaves to obtain a flat sheaf
-- surjecting onto `ℱ`.
/-- Lemma 18.28.8 (4): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of rings, then
any sheaf of `\mathcal O`-modules is the quotient of a flat sheaf of `\mathcal O`-modules. -/
theorem exists_epi_from_flat
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (𝒢 : SheafOfModules (ringSheaf J 𝒪))
      (_h𝒢 : IsFlat 𝒪 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

end SheafOfModules.RingedSite
