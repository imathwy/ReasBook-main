module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section

open MeasureTheory

namespace Set

/-- A set in Euclidean space is Jordan-measurable when it is bounded and its frontier
has zero volume. -/
def IsJordanMeasurable {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Bornology.IsBounded A ∧ volume (frontier A) = 0

/-- The boundedness and null-frontier characterization of a Jordan-measurable set. -/
theorem isJordanMeasurable_iff {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) :
    A.IsJordanMeasurable ↔ Bornology.IsBounded A ∧ volume (frontier A) = 0 :=
  Iff.rfl

/-- A Jordan-measurable set is bounded. -/
theorem IsJordanMeasurable.isBounded {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : A.IsJordanMeasurable) : Bornology.IsBounded A :=
  hA.1

/-- The frontier of a Jordan-measurable set has zero volume. -/
theorem IsJordanMeasurable.null_frontier {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : A.IsJordanMeasurable) : volume (frontier A) = 0 :=
  hA.2

/-- A Jordan-measurable set is measurable up to a set of zero volume. -/
theorem IsJordanMeasurable.nullMeasurableSet {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : A.IsJordanMeasurable) :
    NullMeasurableSet A volume :=
  nullMeasurableSet_of_null_frontier hA.null_frontier

end Set
