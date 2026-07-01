/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part2

open scoped Pointwise

section Chap03
section Section11

/-- The book's `euclideanRelativeInterior` is contained in mathlib's `intrinsicInterior`
in Euclidean space. -/
lemma euclideanRelativeInterior_subset_intrinsicInterior (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    euclideanRelativeInterior n C ⊆ intrinsicInterior Real C := by
  classical
  intro x hx
  rcases hx with ⟨hx_aff, ε, hε, hxsub⟩
  let A : AffineSubspace Real (EuclideanSpace Real (Fin n)) := affineSpan Real C
  let sA : Set A := ((↑) : A → EuclideanSpace Real (Fin n)) ⁻¹' C
  refine (mem_intrinsicInterior).2 ?_
  refine ⟨(⟨x, hx_aff⟩ : A), ?_, rfl⟩
  have hball : Metric.ball (⟨x, hx_aff⟩ : A) ε ⊆ sA := by
    intro y hy
    have hyBall : dist (y : EuclideanSpace Real (Fin n)) x < ε := by
      simpa using hy
    have hyClosed : (y : EuclideanSpace Real (Fin n)) ∈ Metric.closedBall x ε :=
      (Metric.mem_closedBall).2 (le_of_lt hyBall)
    have hclosed :
        (fun z : EuclideanSpace Real (Fin n) => x + z) '' (ε • euclideanUnitBall n) =
          Metric.closedBall x ε := by
      simpa using (translate_smul_unitBall_eq_closedBall n x ε hε)
    have hyLeft :
        (y : EuclideanSpace Real (Fin n)) ∈
          (fun z : EuclideanSpace Real (Fin n) => x + z) '' (ε • euclideanUnitBall n) := by
      simpa [hclosed] using hyClosed
    have hyC : (y : EuclideanSpace Real (Fin n)) ∈ C := hxsub ⟨hyLeft, y.property⟩
    simpa [sA] using hyC
  have hsA_nhds : sA ∈ nhds (⟨x, hx_aff⟩ : A) :=
    Metric.mem_nhds_iff.2 ⟨ε, hε, hball⟩
  exact (mem_interior_iff_mem_nhds).2 hsA_nhds

end Section11
end Chap03
