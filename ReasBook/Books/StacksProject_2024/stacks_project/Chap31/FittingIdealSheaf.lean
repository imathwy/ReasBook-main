import StacksProject_2024.stacks_project.Chap15.Definition_15_8_3
import StacksProject_2024.stacks_project.Chap17.Lemma_17_11_2

open AlgebraicGeometry
open scoped FittingIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The `i`th Fitting ideal sheaf of a finite type quasi-coherent module is obtained by taking the
`i`th Fitting ideal of its module of sections on each affine open. -/
def fittingIdealSheaf
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (i : ℕ) :
    S.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    Fit[Γ(S, U)]_(i)(Γ(ℱ, (U : S.Opens)))

/-- The affine-open ideals of `fittingIdealSheaf` are the corresponding affine-open Fitting
ideals. -/
@[simp] theorem fittingIdealSheaf_ideal
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (i : ℕ) (U : S.affineOpens) :
    (fittingIdealSheaf ℱ i).ideal U =
      Fit[Γ(S, U)]_(i)(Γ(ℱ, (U : S.Opens))) := sorry

end AlgebraicGeometry.Scheme
