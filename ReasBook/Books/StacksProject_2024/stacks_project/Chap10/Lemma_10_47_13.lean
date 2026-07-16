import Mathlib
import StacksProject_2024.stacks_project.Chap09.Lemma_9_26_11
import StacksProject_2024.stacks_project.Chap10.Lemma_10_47_12

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

-- Proof sketch: apply Lemma `10.47.12` with base field `separableClosure k K`; the required
-- triviality of the relative separable closure is exactly `separableClosure.separableClosure_eq_bot`.
/-- Lemma 10.47.13: if `k' = separableClosure k K` is the subextension of elements separably
algebraic over `k`, then `K` is geometrically irreducible over `k'`. -/
@[instance]
theorem isGeometricallyIrreducibleOver_separableClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap (separableClosure k K) K))) := by
  simpa [isGeometricallyIrreducibleOver_iff_separableClosure_eq_bot] using
    separableClosure.separableClosure_eq_bot k K

-- Proof sketch: Lemma `9.26.11` makes the relative algebraic closure `algebraicClosure k K`
-- finite-dimensional over `k`; the relative separable closure is an intermediate field of that
-- algebraic closure, so it is finite-dimensional as well.
/-- If `K / k` is a finitely generated field extension, then the relative separable closure of `k`
in `K` has finite degree over `k`. -/
theorem finiteDimensional_separableClosure_of_essFiniteType [Algebra.EssFiniteType k K] :
    FiniteDimensional k (separableClosure k K) := by
  letI : FiniteDimensional k (algebraicClosure k K) :=
    finiteDimensional_algebraicClosure k K
  letI : Algebra (separableClosure k K) (algebraicClosure k K) :=
    (IntermediateField.inclusion (le_algebraicClosure k K (separableClosure k K))).toAlgebra
  exact FiniteDimensional.left k (separableClosure k K) (algebraicClosure k K)

end

end Algebra
