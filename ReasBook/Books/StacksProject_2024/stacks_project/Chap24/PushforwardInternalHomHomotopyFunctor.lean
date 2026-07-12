import Mathlib

open CategoryTheory ComplexShape

noncomputable section

universe uB vB uA' vA'

namespace DifferentialGradedModule

section

variable {ModB : Type uB} [Category.{vB} ModB] [Preadditive ModB]
variable {ModAprime : Type uA'} [Category.{vA'} ModAprime] [Preadditive ModAprime]

local notation "KModAprime" => HomotopyCategory ModAprime (up ℤ)
local notation "KModB" => HomotopyCategory ModB (up ℤ)

/-- The homotopy-category functor
`K(\textit{Mod}(\mathcal A', d)) ⥤ K(\textit{Mod}(\mathcal B, d))`,
`\mathcal M ↦ f_*\mathcal{H}\!\mathit{om}^{dg}_{\mathcal A'}(\mathcal N, \mathcal M)`,
attached to a chosen internal-Hom-with-`\mathcal N` endofunctor and a chosen pushforward
functor. -/
abbrev pushforwardInternalHomHomotopyFunctor
    (internalHomWithN : ModAprime ⥤ ModAprime) [internalHomWithN.Additive]
    (pushforward : ModAprime ⥤ ModB) [pushforward.Additive] :
    KModAprime ⥤ KModB :=
  internalHomWithN.mapHomotopyCategory (up ℤ) ⋙ pushforward.mapHomotopyCategory (up ℤ)

/-- Unfolding `pushforwardInternalHomHomotopyFunctor` gives the canonical composite of the
homotopy-category lifts of the chosen internal-Hom and pushforward functors. -/
theorem pushforwardInternalHomHomotopyFunctor_def
    (internalHomWithN : ModAprime ⥤ ModAprime) [internalHomWithN.Additive]
    (pushforward : ModAprime ⥤ ModB) [pushforward.Additive] :
    pushforwardInternalHomHomotopyFunctor internalHomWithN pushforward =
      internalHomWithN.mapHomotopyCategory (up ℤ) ⋙
        pushforward.mapHomotopyCategory (up ℤ) :=
  rfl

end

end DifferentialGradedModule
