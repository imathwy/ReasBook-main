import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- Corollary 1.87: Restricting the Borel `σ`-algebra of `EReal` along the canonical inclusion
`ℝ → EReal` recovers the Borel `σ`-algebra of `ℝ`. -/
theorem borel_ereal_comap_toEReal :
    MeasurableSpace.comap Real.toEReal (borel EReal) = borel ℝ :=
  EReal.measurableEmbedding_coe.comap_eq
