import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Text 15.0.14 defines a metric on a carrier by the distance clauses
  positivity/separation, symmetry, and the triangle inequality.
- `core/canonical`: the primitive distance owner is `PseudoMetricSpace`; the extra primitive
  separation datum is a witness `dist x y = 0 → x = y`.
- `bridge/view`: the textbook clauses are exposed by `dist_nonneg`, `dist_eq_zero`, `dist_pos`,
  `dist_comm`, and `dist_triangle`, together with the owner bridge
  `MetricSpace.toPseudoMetricSpace`.
- Primitive data vs derived API: symmetry and triangle inequality belong to the primitive
  pseudometric layer together with nonnegativity; separation is added by the primitive witness
  `dist x y = 0 → x = y`; strict positivity away from the diagonal is then derived.
- Domain-style sampling used here: `PseudoMetricSpace`, `MetricSpace.toPseudoMetricSpace`,
  `dist_nonneg`, `dist_eq_zero`, `dist_pos`, `dist_comm`, `dist_triangle`, and
  `eq_of_dist_eq_zero`.
- Layer target: `core/canonical`, since the textbook notion is exactly the standard metric-space
  structure.
-/

/- A metric is a separated pseudometric, so the primitive distance-data owner is
`PseudoMetricSpace`. -/
recall PseudoMetricSpace

/- Text 15.0.14: a metric is the canonical mathlib notion `MetricSpace`. -/
recall MetricSpace

/- Every metric carries its underlying pseudometric owner. -/
recall MetricSpace.toPseudoMetricSpace

/- In a metric space, the primitive separation witness is
`dist x y = 0 → x = y`. -/
recall eq_of_dist_eq_zero

/- In a metric space, the distance vanishes exactly on equal points, matching the textbook
separation clause. -/
recall dist_eq_zero

/- In a pseudometric space, distances are nonnegative, matching the textbook positivity base
clause. -/
recall dist_nonneg

/- In a metric space, distinct points have strictly positive distance, matching the textbook
positivity clause. -/
recall dist_pos

/- Symmetry is already available at the pseudometric layer:
`dist x y = dist y x`. -/
recall dist_comm

/- The triangle inequality is likewise pseudometric-level:
`dist x z ≤ dist x y + dist y z`. -/
recall dist_triangle

section

variable {α : Type*}

namespace PseudoMetricSpace

/-- A pseudometric plus the primitive separation witness gives the canonical metric owner. -/
@[reducible] def toMetricSpaceOfEqOfDistEqZero [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) : MetricSpace α :=
  { ‹PseudoMetricSpace α› with
    eq_of_dist_eq_zero := fun {x y} hxy ↦ hsep hxy }

/-- Primitive separation bridge at the pseudometric layer. -/
theorem dist_eq_zero_iff_of_eq_of_dist_eq_zero [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) (x y : α) :
    dist x y = 0 ↔ x = y := by
  letI : MetricSpace α := toMetricSpaceOfEqOfDistEqZero hsep
  exact dist_eq_zero

/-- Separation clauses at the pseudometric layer, derived through the canonical metric owner. -/
theorem dist_separation_clauses [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) (x y : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) := by
  letI : MetricSpace α := toMetricSpaceOfEqOfDistEqZero hsep
  exact ⟨dist_eq_zero_iff_of_eq_of_dist_eq_zero hsep x y, dist_pos⟩

/-- The primitive pseudometric distance clauses: nonnegativity, symmetry, and the triangle
inequality. -/
theorem dist_basic_clauses [PseudoMetricSpace α] (x y z : α) :
    (0 ≤ dist x y) ∧
      dist x y = dist y x ∧
      dist x z ≤ dist x y + dist y z := by
  exact ⟨dist_nonneg, dist_comm x y, dist_triangle x y z⟩

end PseudoMetricSpace

namespace MetricSpace

/-- Separation in the canonical metric owner: vanishing distance is equivalent to equality, and
strict positivity is equivalent to inequality. -/
theorem dist_separation_clauses [MetricSpace α] (x y : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) := by
  exact ⟨dist_eq_zero, dist_pos⟩

/-- Text 15.0.14 in canonical ambient form: a metric distance satisfies separation, strict
positivity away from the diagonal, symmetry, and the triangle inequality. -/
theorem dist_clauses [MetricSpace α] (x y z : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) ∧
      (0 ≤ dist x y) ∧
      dist x y = dist y x ∧
      dist x z ≤ dist x y + dist y z := by
  exact ⟨dist_eq_zero, dist_pos, dist_nonneg, dist_comm x y, dist_triangle x y z⟩

end MetricSpace

namespace PseudoMetricSpace

/-- Text 15.0.14 clause package at the primitive pseudometric layer, with separation supplied as
primitive data. -/
theorem dist_clauses [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) (x y z : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) ∧
      (0 ≤ dist x y) ∧
      dist x y = dist y x ∧
      dist x z ≤ dist x y + dist y z := by
  letI : MetricSpace α := toMetricSpaceOfEqOfDistEqZero hsep
  simpa using (MetricSpace.dist_clauses (α := α) x y z)

end PseudoMetricSpace

end
