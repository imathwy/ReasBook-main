module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/- Theorem 27.3 (1). A subset of `EuclideanSpace ℝ (Fin n)` is compact if and only
if it is closed and bounded in the Euclidean metric. -/
#check fun (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) ↦
  (Metric.isCompact_iff_isClosed_bounded :
    IsCompact A ↔ IsClosed A ∧ Bornology.IsBounded A)

/- Theorem 27.3 (2). A subset of `Fin n → ℝ` is compact if and only if it is closed
and bounded in the square metric. -/
#check fun (n : ℕ) (A : Set (Fin n → ℝ)) ↦
  (Metric.isCompact_iff_isClosed_bounded :
    IsCompact A ↔ IsClosed A ∧ Bornology.IsBounded A)

end
