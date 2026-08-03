import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter05.Definition_5_1_extra_4

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling across the local Chapter 5 PSB files shows that the owner object for the
-- explicit PSB matrix is already `symmetrizedBroydenLimit`. This file is therefore recall-only.

/- Chapter05 Definition 5.1-extra-7: the explicit PSB matrix is the previously introduced owner
`symmetrizedBroydenLimit`. -/
#check symmetrizedBroydenLimit
