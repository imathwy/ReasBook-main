import Mathlib
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}

-- Proof sketch: if `S.X₁` is flat, apply Lemma `18.28.9` to see that tensoring `S` on the right
-- preserves short exactness, hence the exact tensor functor criterion gives flatness of `S.X₂`.
-- Conversely, if `S.X₂` is flat, use the exactness of tensoring with `S.X₂` and the snake-lemma
-- argument from the textbook to recover exactness after tensoring with `S.X₁`.
/-- Lemma 18.28.10: for a short exact sequence
`0 ⟶ \mathcal F_2 ⟶ \mathcal F_1 ⟶ \mathcal F_0 ⟶ 0` of presheaves of
`\mathcal O`-modules, if `\mathcal F_0` is flat then `\mathcal F_2` is flat if and only if
`\mathcal F_1` is flat. -/
theorem flat_iff_flat_of_shortExact
    (hS : S.ShortExact) [IsFlat S.X₃] :
    IsFlat S.X₁ ↔ IsFlat S.X₂ := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable {S : ShortComplex (SheafOfModules (ringSheaf J 𝒪))}

-- Proof sketch: repeat the presheaf argument in `Mod(\mathcal O)`, using the sheaf version of
-- Lemma `18.28.9` to preserve short exactness under tensor product and the same snake-lemma
-- two-out-of-three argument for flatness.
/-- On a ringed site, if the right term of a short exact sequence of sheaves of
`\mathcal O`-modules is flat, then the left term is flat if and only if the middle term is flat. -/
theorem flat_iff_flat_of_shortExact
    (hS : S.ShortExact) [IsFlat 𝒪 S.X₃] :
    IsFlat 𝒪 S.X₁ ↔ IsFlat 𝒪 S.X₂ := sorry

end SheafOfModules.RingedSite
