import Mathlib
import StacksProject_2024.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

variable {K L : Cpx}

-- Proof sketch: unfold `CochainComplex.IsStrictlyPerfect`. The cone of `f` is still bounded
-- because mapping cones of bounded cochain complexes are bounded, and each degree of
-- `CochainComplex.mappingCone f` is the biproduct of a term of `L` with a shifted term of `K`.
-- Combining the given retract presentations by finite free modules for those two terms yields the
-- corresponding retract presentation for each cone term.
/-- Lemma 21.44.2: the cone on a morphism of strictly perfect complexes of `\mathcal O`-modules on
a ringed site is strictly perfect. -/
theorem mappingCone_isStrictlyPerfect (f : K ⟶ L)
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (mappingCone f) := sorry

end

end SheafOfModules.RingedSite
