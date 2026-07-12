import Mathlib.Tactic.Recall
import StacksProject_2024.Chap24.PushforwardInternalHomHomotopyFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape

noncomputable section

universe uB vB uA' vA'

namespace DifferentialGradedModule

section

variable {ModB : Type uB} [Category.{vB} ModB] [Preadditive ModB]
variable {ModAprime : Type uA'} [Category.{vA'} ModAprime] [Preadditive ModAprime]
variable (internalHomWithN : ModAprime ⥤ ModAprime) [internalHomWithN.Additive]
variable (pushforward : ModAprime ⥤ ModB) [pushforward.Additive]

local notation "KModAprime" => HomotopyCategory ModAprime (up ℤ)
local notation "KModB" => HomotopyCategory ModB (up ℤ)

/- 24.29.4.1: the homotopy-category functor
`K(\textit{Mod}(\mathcal A', d)) ⥤ K(\textit{Mod}(\mathcal B, d))`,
`\mathcal M \mapsto f_*\mathcal{H}\!\mathit{om}^{dg}_{\mathcal A'}(\mathcal N, \mathcal M)`,
is the source-facing Chapter 24 owner `pushforwardInternalHomHomotopyFunctor`. -/
recall pushforwardInternalHomHomotopyFunctor

/- Source-facing specialization: for the chosen internal-Hom-with-`\mathcal N` endofunctor and
pushforward functor, the recalled owner has source `K(\textit{Mod}(\mathcal A', d))` and target
`K(\textit{Mod}(\mathcal B, d))`. -/
#check (pushforwardInternalHomHomotopyFunctor internalHomWithN pushforward : KModAprime ⥤ KModB)

/- Companion recall: unfolding the source-facing owner recovers the canonical composite of the
homotopy-category lifts of the chosen internal-Hom and pushforward functors. -/
recall pushforwardInternalHomHomotopyFunctor_def

end

end DifferentialGradedModule
