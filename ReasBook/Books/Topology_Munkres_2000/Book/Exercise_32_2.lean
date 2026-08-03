module

public import Mathlib.Topology.Separation.Regular

public section

universe u v

private theorem isEmbedding_update {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [DecidableEq ι] (x : (i : ι) → X i) (i : ι) :
    Topology.IsEmbedding (Function.update x i) := by
  exact Topology.IsEmbedding.of_leftInverse (fun y ↦ Function.update_self i y x)
    (continuous_apply i) (continuous_const.update i continuous_id)

/-- Exercise 32.2 (1): If a product of nonempty spaces is Hausdorff, then each factor is
Hausdorff. -/
theorem t2Space_of_pi {ι : Type u} {X : ι → Type v} [(i : ι) → TopologicalSpace (X i)]
    (hX : ∀ i, Nonempty (X i)) [T2Space ((i : ι) → X i)] (i : ι) : T2Space (X i) := by
  classical
  exact (isEmbedding_update (fun j ↦ (hX j).some) i).t2Space

/-- Exercise 32.2 (2): If a product of nonempty spaces is regular, then each factor is regular.
Here `T3Space` expresses the book's convention that a regular space is also `T₁`. -/
theorem t3Space_of_pi {ι : Type u} {X : ι → Type v} [(i : ι) → TopologicalSpace (X i)]
    (hX : ∀ i, Nonempty (X i)) [T3Space ((i : ι) → X i)] (i : ι) : T3Space (X i) := by
  classical
  exact (isEmbedding_update (fun j ↦ (hX j).some) i).t3Space

/-- Exercise 32.2 (3): If a product of nonempty spaces is normal, then each factor is normal.
Here `T4Space` expresses the book's convention that a normal space is also `T₁`. -/
theorem t4Space_of_pi {ι : Type u} {X : ι → Type v} [(i : ι) → TopologicalSpace (X i)]
    (hX : ∀ i, Nonempty (X i)) [T4Space ((i : ι) → X i)] (i : ι) : T4Space (X i) := by
  classical
  let x := fun j ↦ (hX j).some
  have hleft : Function.LeftInverse (fun p : (j : ι) → X j ↦ p i) (Function.update x i) :=
    fun y ↦ Function.update_self i y x
  exact (hleft.isClosedEmbedding (continuous_apply i)
    (continuous_const.update i continuous_id)).t4Space
