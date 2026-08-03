module

import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Int

public section

/- Exercise 2.99.2 (1): The additive group `ℤ` with its usual topology is a
topological group in the sense of Definition 2.99.1. -/
#check (inferInstance : IsTopologicalAddGroup ℤ)
#check (inferInstance : T1Space ℤ)

/- Exercise 2.99.2 (2): The additive group `ℝ` with its usual topology is a
topological group in the sense of Definition 2.99.1. -/
#check (inferInstance : IsTopologicalAddGroup ℝ)
#check (inferInstance : T1Space ℝ)

/- Exercise 2.99.2 (3): The units `NNRealˣ`, canonically representing the
strictly positive real numbers under multiplication, form a topological group. -/
#check (inferInstance : IsTopologicalGroup NNRealˣ)
#check (inferInstance : T1Space NNRealˣ)

/- Exercise 2.99.2 (4): The circle `Circle` of complex numbers of norm one is a
topological group under multiplication. -/
#check (inferInstance : IsTopologicalGroup Circle)
#check (inferInstance : T1Space Circle)

/- Exercise 2.99.2 (5): For every `n : ℕ`, the real general linear group
`GL (Fin n) ℝ` is a topological group under matrix multiplication. -/
#check fun (n : ℕ) ↦ (inferInstance : IsTopologicalGroup (GL (Fin n) ℝ))
#check fun (n : ℕ) ↦ (inferInstance : T1Space (GL (Fin n) ℝ))

open Matrix Topology

namespace Matrix.GeneralLinearGroup

/-- The coercion from the real general linear group to real matrices realizes
its topology as the topology inherited from the ambient matrix space. -/
theorem isEmbedding_val_real (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  refine Units.isEmbedding_val_mk' ?_ (fun A ↦ (coe_inv A).symm)
  intro A hA
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_matrix_inv
  simpa using NormedRing.inverse_continuousAt (det hA.unit)

end Matrix.GeneralLinearGroup
