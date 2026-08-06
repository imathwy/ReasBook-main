import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open scoped Manifold Topology

noncomputable section

-- Chapter 20 already fixes `singularHomologyWithCoefficients` as the coefficient-module homology
-- owner, whose constant-module specialization recovers ordinary integral coefficients. This file
-- keeps only the Problem 20.7.4 source-facing statements, together with the chapter-local
-- orientability owner `ROrientedManifold`.

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
variable [ConnectedSpace M] [CompactSpace M]

/-- Problem 20.7.4 (1): under the standing compact connected boundaryless `n`-manifold
hypotheses, if `M` is nonorientable, then the torsion subgroup of `H_{n-1}(M; ℤ)` is cyclic of
order `2`. This is stated in predecessor degree `m` for an `(m + 1)`-manifold to avoid an
otherwise redundant positivity side condition. -/
theorem torsion_integralHomology_pred_of_nonorientable
    {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
    (h_nonorientable : ¬ Nonempty (ROrientedManifold ℤ I (m + 1) M)) :
    Nonempty
      (ModuleCat.of ℤ
          (Submodule.torsion ℤ
            (singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ ℤ) m)) ≅
        ModuleCat.of ℤ (ZMod 2)) :=
  sorry

/-- Problem 20.7.4 (2): under the standing compact connected boundaryless `n`-manifold
hypotheses, if `M` is nonorientable, then `H_n(M; ℤ_q)` vanishes for every odd integer `q`. -/
theorem isZero_top_zmodHomology_of_nonorientable_of_odd
    {n q : ℕ} [Fact (Module.finrank ℝ E = n)] (hq_odd : Odd q)
    (h_nonorientable : ¬ Nonempty (ROrientedManifold ℤ I n M)) :
    IsZero
      (singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ (ZMod q)) n) := sorry

/-- Problem 20.7.4 (3): under the standing compact connected boundaryless `n`-manifold
hypotheses, if `M` is nonorientable, then `H_n(M; ℤ_q)` is cyclic of order `2` for every even
positive integer `q`. -/
theorem top_zmodHomology_of_nonorientable_of_even
    {n q : ℕ} [Fact (Module.finrank ℝ E = n)] (hq : 0 < q) (hq_even : Even q)
    (h_nonorientable : ¬ Nonempty (ROrientedManifold ℤ I n M)) :
    Nonempty
      (singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ (ZMod q)) n ≅
        ModuleCat.of ℤ (ZMod 2)) := sorry

end
