import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Set

universe u

variable {E : Type u} [MeasurableSpace E] [StandardBorelSpace E]
variable (μ : Measure E) [NoAtoms μ] {A : Set E} (n : ℕ+)

/-- Exercise 8.3.1: In a standard Borel space with an atom-free measure, every measurable set
admits an equal-measure partition into `n` measurable pieces. A canonical library-facing
bridge/view is a measurable map `f : E → Fin n`; the pieces are its fibers measured with respect
to the restricted measure `μ.restrict A`. -/
-- Proof sketch: Embed the standard Borel space measurably into `ℝ`, transfer the restricted
-- measure on `A` to the image, cut the image into `n` measurable pieces of equal mass by
-- successive one-dimensional measure cuts, and pull the pieces back to `E`.
theorem exists_measurable_fiber_partition_eq_of_noAtoms
    (hA : MeasurableSet A) :
    ∃ f : E → Fin n, Measurable f ∧ ∀ i, μ.restrict A (f ⁻¹' {i}) = μ A / n := sorry

/-- Exercise 8.3.1 in the source-text family-of-sets form: the equal-measure partition pieces may
be empty, so the public textbook-facing statement is an indexed family of measurable sets rather
than a `Finpartition`. -/
theorem exists_pairwiseDisjoint_iUnion_eq_measure_eq_of_noAtoms
    (hA : MeasurableSet A) :
    ∃ s : Fin n → Set E,
      (Pairwise fun i j ↦ Disjoint (s i) (s j)) ∧
      (∀ i, MeasurableSet (s i)) ∧
      (⋃ i, s i) = A ∧
      ∀ i, μ (s i) = μ A / n := by
  obtain ⟨f, hf, hμ⟩ := exists_measurable_fiber_partition_eq_of_noAtoms μ n hA
  refine ⟨fun i ↦ A ∩ f ⁻¹' {i}, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj ↦ ?_
    have hix : f x = i := by simpa using hxi.2
    have hjx : f x = j := by simpa using hxj.2
    exact hij (hix.symm.trans hjx)
  · intro i
    exact hA.inter (hf (measurableSet_singleton i))
  · ext x
    simp
  · intro i
    simpa [Measure.restrict_apply' hA, Set.inter_comm] using hμ i
