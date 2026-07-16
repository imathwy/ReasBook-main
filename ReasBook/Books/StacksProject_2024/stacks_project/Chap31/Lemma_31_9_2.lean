import StacksProject_2024.stacks_project.Chap10.Lemma_10_40_8
import StacksProject_2024.stacks_project.Chap31.FittingIdealSheaf
import StacksProject_2024.stacks_project.Chap31.Lemma_31_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: Chapter 31 already fixes the source-facing owner `Scheme.fittingIdealSheaf`
-- in Lemma 31.9.1, while Chapter 15 supplies the ring-level finite-generation theorem for Fitting
-- ideals of finitely presented modules.

/- Lemma 31.9.2 (1): for a finitely presented `\mathcal O_S`-module `\mathcal F`, the affine-open
ideals of the canonical ideal sheaf `Fit_r(\mathcal F)` agree with the module-theoretic `r`th
Fitting ideals of the affine section modules. This is the canonical affine-open computation
already provided by `Scheme.fittingIdealSheaf_ideal`. -/
#check fittingIdealSheaf_ideal

/-- Lemma 31.9.2 (2): if `\mathcal F` is a finitely presented `\mathcal O_S`-module, then on every
affine open `U` the ideal defining `Fit_r(\mathcal F)` is finitely generated. Since
`Scheme.fittingIdealSheaf ℱ r : S.IdealSheafData` already packages quasi-coherence, this is the
finite-type part of the source statement. -/
@[stacks 0C3E]
theorem fittingIdealSheaf_ideal_fg
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFinitePresentation] (r : ℕ) (U : S.affineOpens) :
    ((fittingIdealSheaf ℱ r).ideal U).FG := by
  simpa [fittingIdealSheaf_ideal] using
    (fittingIdeal_fg_of_finitePresentation (R := Γ(S, U)) (M := Γ(ℱ, (U : S.Opens))) r)

end AlgebraicGeometry.Scheme
