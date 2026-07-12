import StacksProject_2024.Chap24.Definition_24_29_2
import StacksProject_2024.Chap24.PushforwardInternalHomHomotopyFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uB vB uA' vA'

namespace DifferentialGradedModule

section

variable {DGModB : Type uB} [Category.{vB} DGModB] [Abelian DGModB]
variable [CategoryWithHomology DGModB]
variable {DGModAprime : Type uA'} [Category.{vA'} DGModAprime] [Abelian DGModAprime]
variable [CategoryWithHomology DGModAprime]
variable (internalHomWithN : DGModAprime ⥤ DGModAprime)
variable (pushforward : DGModAprime ⥤ DGModB)
variable [internalHomWithN.Additive] [pushforward.Additive]

local notation "KAprime" => HomotopyCategory DGModAprime (up ℤ)
local notation "KB" => HomotopyCategory DGModB (up ℤ)
local notation "DAprime" => DerivedCategory DGModAprime
local notation "DB" => DerivedCategory DGModB
local notation "QhAprime" => (DerivedCategory.Qh : KAprime ⥤ DAprime)
local notation "QhB" => (DerivedCategory.Qh : KB ⥤ DB)
local notation "QisAprime" => HomotopyCategory.quasiIso DGModAprime (up ℤ)

-- Semantic search note: `lean_leansearch` recalled the canonical `Functor.totalRightDerived`
-- owner for right derived extensions. `PushforwardInternalHomHomotopyFunctor` supplies the
-- importable owner for the homotopy-category functor from `24.29.4.1`, while
-- `Definition_24_29_2` supplies `derivedInternalHom` and `derivedPushforward`.

/-- Lemma 24.29.5: in the situation above, if `RT` denotes the right derived extension of the
homotopy-category functor (24.29.4.1),
`\mathcal M \mapsto f_*\mathcal{H}\!\mathit{om}(\mathcal N,\mathcal M)`, then functorially in
`\mathcal M` it agrees with
`Rf_* R\mathcal{H}\!\mathit{om}(\mathcal N,\mathcal M)`. -/
@[stacks 0FTT]
theorem pushforwardInternalHomRightDerived_eq_derivedInternalHom_comp_derivedPushforward
    [Functor.HasRightDerivedFunctor
      (pushforwardInternalHomHomotopyFunctor internalHomWithN pushforward ⋙ QhB) QisAprime]
    [Functor.HasRightDerivedFunctor
      (internalHomWithN.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModAprime (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (pushforward.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModAprime (up ℤ))] :
    (pushforwardInternalHomHomotopyFunctor internalHomWithN pushforward ⋙
        QhB).totalRightDerived QhAprime QisAprime =
      derivedInternalHom internalHomWithN ⋙ derivedPushforward pushforward := sorry

end

end DifferentialGradedModule
