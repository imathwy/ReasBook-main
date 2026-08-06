import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3

open CategoryTheory
open scoped Manifold Topology

noncomputable section

-- Semantic recall via `lean_leansearch`: no ready-made manifold top-homology detection theorem
-- surfaced from mathlib. This repository already fixes `integralSingularHomology` as the
-- Chapter 13 owner for ordinary integral singular homology, while Chapter 20 provides
-- `ROrientedManifold` and `rSingularHomology` for orientability and constant-ring coefficient
-- singular homology. The remark is therefore stated directly at the homology-group level.

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable [ConnectedSpace M] [CompactSpace M] [IsManifold I ⊤ M]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n)]

/-- Remark 13.5.10 (1): the `RP^n` integral homology calculation previews the later manifold fact
that, for a connected closed `n`-manifold, orientability is detected by its top integral
homology group. -/
theorem orientability_iff_topIntegralHomologyIso_of_connectedClosedManifold :
    Nonempty (ROrientedManifold ℤ I n M) ↔
      Nonempty (integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) := sorry

/-- Remark 13.5.10 (2): the `RP^n` mod-`2` homology calculation previews the later manifold fact
that the top `ZMod 2`-valued homology of a connected closed `n`-manifold is `ZMod 2`. -/
theorem topModTwoHomologyIso_of_connectedClosedManifold :
    Nonempty
      (rSingularHomology (ZMod 2) n (TopCat.of M) ≅ ModuleCat.of (ZMod 2) (ZMod 2)) := sorry

end
