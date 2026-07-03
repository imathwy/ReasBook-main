import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules.RingedSite
variable {𝒪 : Sheaf J CommRingCat.{u}}

-- Proof sketch: flatness is owned by the exact tensor functor
-- `SheafOfModules.RingedSite.IsFlat`. Tensoring with `𝒢 ⊗ 𝓕` is the composite of
-- tensoring first with `𝓕` and then with `𝒢`, so exactness follows from exactness of the two
-- flat tensor functors and stability of exactness under composition.
/-- Lemma 18.28.12: for a ringed site `(\mathcal C, \mathcal O)`, if `\mathcal G` and
`\mathcal F` are flat `\mathcal O`-modules, then their tensor product
`\mathcal G \otimes_\mathcal O \mathcal F`, formalized here as `𝒢 ⊗ 𝓕`, is again a flat
`\mathcal O`-module. -/
theorem isFlat_tensor
    (𝒢 𝓕 : SheafOfModules (ringSheaf J 𝒪))
    [IsFlat 𝒪 𝒢] [IsFlat 𝒪 𝓕] :
    IsFlat 𝒪 (𝒢 ⊗ 𝓕) := by
  sorry

end SheafOfModules.RingedSite
