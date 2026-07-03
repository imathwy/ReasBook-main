import Mathlib
import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap07.Definition_7_17_1
import StacksProject_2024.Chap07.Lemma_7_40_1
import StacksProject_2024.Chap18.Lemma_18_28_7
import StacksProject_2024.Chap21.Lemma_21_52_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "DMod" => DerivedCategory Mod

-- Proof sketch: apply Lemma `21.52.5` to the degree-zero derived object attached to
-- `j_{U!}\mathcal O_U`. Weak contractibility gives vanishing of higher cohomology over `U` via
-- Lemma `21.51.1`, while quasi-compactness gives direct-sum compatibility of sections over `U`
-- via Modules on Sites, Lemma `18.30.3`.
/-- Lemma 21.52.6: if `U` is quasi-compact and weakly contractible in a ringed site
`(\mathcal C, \mathcal O)`, then the degree-zero derived object attached to
`j_{U!}\mathcal O_U` is a compact object of `D(\mathcal O)`. -/
theorem localizedStructureModuleExtensionByZero_degreeZero_isCompactObject_of_quasiCompact_weaklyContractible
    (U : C) (hUqc : J.QuasiCompactObject U) [J.IsWeaklyContractible U] :
    IsCompactObject (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U) := sorry

end

end SheafOfModules.RingedSite
