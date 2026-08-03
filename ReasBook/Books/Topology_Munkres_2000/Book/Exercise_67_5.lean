module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Group.Int.Even
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public section

/- The free abelian group `Fin n → ℤ` has rank `n`. -/
#check Module.finrank_pi

/-- Helper for Exercise 67.5: the integer submodule of even elements is the range of doubling. -/
lemma AddSubgroup.even_toIntSubmodule_eq_range {M : Type*} [AddCommGroup M] :
    (AddSubgroup.even M).toIntSubmodule =
      LinearMap.range (LinearMap.lsmul ℤ M 2) := by
  -- Membership on both sides says that the element is twice some element of `M`.
  apply SetLike.ext'
  rw [AddSubgroup.coe_toIntSubmodule]
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := AddSubgroup.mem_even.mp hx
    have hdouble : LinearMap.lsmul ℤ M 2 y = x := by
      rw [LinearMap.lsmul_apply, two_smul, ← hy]
    exact ⟨y, hdouble⟩
  · intro hx
    obtain ⟨y, hy⟩ := hx
    have heven : x = y + y := by
      rw [← hy, LinearMap.lsmul_apply, two_smul]
    exact AddSubgroup.mem_even.mpr ⟨y, heven⟩

/-- The even subgroup of `Fin n → ℤ` has the same rank as the ambient free abelian group. -/
theorem evenSubgroupRank (n : ℕ) :
    Module.finrank ℤ (AddSubgroup.even (Fin n → ℤ)) = n := by
  -- Replace the subgroup by the range of the injective doubling endomorphism.
  have htwo : (2 : ℤ) ≠ 0 := two_ne_zero
  have hinjective : Function.Injective (LinearMap.lsmul ℤ (Fin n → ℤ) 2) :=
    LinearMap.lsmul_injective htwo
  have hrange :
      Module.finrank ℤ (LinearMap.range (LinearMap.lsmul ℤ (Fin n → ℤ) 2)) =
        Module.finrank ℤ (Fin n → ℤ) :=
    LinearMap.finrank_range_of_inj hinjective
  rw [← AddSubgroup.even_toIntSubmodule_eq_range] at hrange
  -- The ambient function module has one basis vector for each element of `Fin n`.
  have hambient : Module.finrank ℤ (Fin n → ℤ) = n := by
    simp only [Module.finrank_pi, Fintype.card_fin]
  exact hrange.trans hambient

/-- For positive `n`, the even subgroup of `Fin n → ℤ` is proper. -/
theorem evenSubgroup_ne_top {n : ℕ} (hn : 0 < n) :
    AddSubgroup.even (Fin n → ℤ) ≠ ⊤ := by
  -- If every vector were even, then in particular the constant-one vector would be even.
  intro heq
  have hone_mem : (fun _ : Fin n ↦ (1 : ℤ)) ∈ AddSubgroup.even (Fin n → ℤ) := by
    rw [heq]
    exact AddSubgroup.mem_top _
  obtain ⟨half, hhalf⟩ := (AddSubgroup.mem_even.mp hone_mem)
  -- Evaluating an alleged half at the first coordinate would make the integer `1` even.
  have hcoordinate : (1 : ℤ) = half ⟨0, hn⟩ + half ⟨0, hn⟩ := congrFun hhalf ⟨0, hn⟩
  exact Int.not_even_one ⟨half ⟨0, hn⟩, hcoordinate⟩

/-- Exercise 67.5. For positive `n`, the free abelian group `Fin n → ℤ` and its even subgroup
give a group and a proper subgroup having the same rank `n`. -/
theorem evenSubgroup_isProperOfSameRank {n : ℕ} (hn : 0 < n) :
    Module.finrank ℤ (Fin n → ℤ) = n ∧
      Module.finrank ℤ (AddSubgroup.even (Fin n → ℤ)) = n ∧
        AddSubgroup.even (Fin n → ℤ) ≠ ⊤ := by
  -- Combine the standard rank computation with the two properties of the even subgroup.
  constructor
  · simp only [Module.finrank_pi, Fintype.card_fin]
  · exact ⟨evenSubgroupRank n, evenSubgroup_ne_top hn⟩
