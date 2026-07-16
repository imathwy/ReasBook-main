import StacksProject_2024.stacks_project.Chap18.Lemma_18_23_4
import StacksProject_2024.stacks_project.Chap31.FittingIdealSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace
open scoped FittingIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- Lemma 31.9.1: for a morphism of schemes `f : T ⟶ S` and a finite type quasi-coherent
`\mathcal O_S`-module `\mathcal F`, the inverse-image ideal sheaf
`f^{-1}\operatorname{Fit}_i(\mathcal F) \cdot \mathcal O_T` is exactly the `i`th Fitting ideal
sheaf of the pullback module `f^*\mathcal F`. This is the scheme-level ideal-sheaf bridge for the
ring-level base-change owner `fittingIdeal_baseChange`. -/
@[stacks 0C3D]
theorem fittingIdealSheaf_pullback
    (f : T ⟶ S) (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (i : ℕ) :
    (fittingIdealSheaf ℱ i).comap f =
      fittingIdealSheaf ((Modules.pullback f).obj ℱ) i := by
  sorry

/-- Affine-open companion to Lemma 31.9.1: on every affine open of `T`, the pulled-back
`i`th Fitting ideal sheaf and the `i`th Fitting ideal sheaf of `f^*\mathcal F` have the same
ideal. Together with `fittingIdealSheaf_ideal`, this recovers the affine-open
`Fit[Γ(T, U)]_(i)` formula for `f^*\mathcal F`. -/
@[simp] theorem fittingIdealSheaf_pullback_ideal
    (f : T ⟶ S) (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (i : ℕ) (U : T.affineOpens) :
    ((fittingIdealSheaf ℱ i).comap f).ideal U =
      (fittingIdealSheaf ((Modules.pullback f).obj ℱ) i).ideal U := by
  simpa using
    congrArg (fun I ↦ I.ideal U) (fittingIdealSheaf_pullback f ℱ i)

end AlgebraicGeometry.Scheme
