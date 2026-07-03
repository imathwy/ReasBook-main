import Mathlib
import StacksProject_2024.Chap18.Lemma_18_30_7
import StacksProject_2024.Chap18.Lemma_18_30_8
import StacksProject_2024.Chap18.Situation_18_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open _root_.SheafOfModules.RingedSite (HasFiniteBasisConstructibleModuleCokernelPresentation)

noncomputable section

universe u

namespace CategoryTheory.ShortComplex

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable {S : ShortComplex Mod}

-- Proof sketch: choose explicit `18.30.7.2` presentations for `S.X₁` and `S.X₃`. Lift the
-- generators of the right presentation through the epimorphism `S.g` after a finite basis
-- refinement using Lemma `18.30.9`, then compare kernels via the snake lemma and refine the
-- resulting kernel presentation using Lemma `18.30.2`. This produces a finite basis presentation
-- of the middle term `S.X₂`.
/-- Lemma 18.30.10: in Situation `18.30.5`, extensions of `\mathcal O`-modules admitting finite
basis cokernel presentations as in `18.30.7.2` again admit such a presentation. -/
theorem ringedSite_hasFiniteBasisConstructibleModuleCokernelPresentation_X2_of_shortExact
    (hS : S.ShortExact)
    (hX₁ : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₁)
    (hX₃ : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₃) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₂ := sorry

end

end CategoryTheory.ShortComplex
