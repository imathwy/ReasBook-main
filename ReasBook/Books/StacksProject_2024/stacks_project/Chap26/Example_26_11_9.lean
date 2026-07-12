import Mathlib
import StacksProject_2024.Chap05.Definition_5_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped TopologicalSpace

namespace AlgebraicGeometry

-- Semantic recall: the canonical owner for "closed points" is `closedPoints`, with the
-- source-facing notation `(X)₀`; on a scheme this is the closed-point locus of its underlying
-- topological space.

local notation "Xempty" => Spec (CommRingCat.of (ULift PUnit))

/-- Companion witness for Example 26.11.9: the empty affine scheme carried by the one-point ring
`ULift PUnit` has no closed points. -/
theorem empty_affine_scheme_closedPoints_eq_empty :
    (Xempty)₀ = ∅ := by
  have _ : IsEmpty (PrimeSpectrum (ULift PUnit)) :=
    (PrimeSpectrum.isEmpty_iff_subsingleton).2 inferInstance
  ext x
  change PrimeSpectrum (ULift PUnit) at x
  exact isEmptyElim x

/-- Example 26.11.9: there exists a scheme without closed points. -/
@[stacks 01IY]
theorem exists_scheme_without_closed_points :
    ∃ X : Scheme.{0}, (X)₀ = ∅ := by
  exact ⟨Xempty, empty_affine_scheme_closedPoints_eq_empty⟩

/-- Companion pointwise form of Example 26.11.9: some scheme has no closed points at all. -/
theorem exists_scheme_forall_not_mem_closedPoints :
    ∃ X : Scheme.{0}, ∀ x : X, x ∉ (X)₀ := by
  simpa [Set.eq_empty_iff_forall_notMem] using exists_scheme_without_closed_points

end AlgebraicGeometry
