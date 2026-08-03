module

public import Topology_Munkres_2000.Book.Exercise_67_4.Torsion
public import Mathlib.Algebra.Module.Rat
public import Mathlib.GroupTheory.Torsion

public section

/- Exercise 67.4 (1). The elements of finite additive order form the bundled
torsion subgroup, with membership characterized by `IsOfFinAddOrder`. -/
#check AddCommGroup.torsion
#check AddCommGroup.mem_torsion

/- Exercise 67.4 (2). A free abelian group is torsion-free. -/
#check Module.Free.instIsAddTorsionFree

/- Exercise 67.4 (3). The additive group of rational numbers is torsion-free. -/
#check (inferInstance : IsAddTorsionFree ℚ)

namespace Rat

/-- Helper for Exercise 67.4: an integral basis vector is not twice another vector. -/
private lemma basisVectorNeTwoNsmul {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis ι ℤ M) (i : ι) (x : M) : b i ≠ 2 • x := by
  classical
  intro h
  -- The `i`th coordinate turns the alleged doubling into the impossible equation `1 = 2z`.
  have hcoord := congrArg (fun y ↦ b.coord i y) h
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    map_nsmul, Int.nsmul_eq_mul] at hcoord
  omega

/-- Exercise 67.4 (4). The additive group of rational numbers is not free abelian. -/
theorem notFreeAbelian : ¬ Module.Free ℤ ℚ := by
  intro hfree
  letI : Module.Free ℤ ℚ := hfree
  let b := Module.Free.chooseBasis ℤ ℚ
  -- Nontriviality of `ℚ` ensures that the chosen basis has a vector to test.
  obtain ⟨i⟩ := b.index_nonempty
  -- Rational divisibility writes this basis vector as twice its half.
  have hhalf : 2 • (b i / 2) = b i := by
    simp only [nsmul_eq_mul]
    ring
  exact basisVectorNeTwoNsmul b i (b i / 2) hhalf.symm

end Rat
