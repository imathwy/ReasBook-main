/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part3

noncomputable section
open scoped Topology

section Chap02
section Section07

/-- The vertical section of the embedded epigraph corresponds to the usual inequality. -/
lemma riEpigraph_section_mem_iff {n : Nat} {f : (Fin n → Real) → EReal}
    (x : Fin n → Real) (μ : Real) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let y : EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
    let z : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ)
    let Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
      fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C}
    z ∈ Cy y ↔ f x ≤ (μ : EReal) := by
  classical
  dsimp
  set C :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  set y : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x with hy
  set z : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) with hz
  set Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
    fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C} with hCy
  change z ∈ Cy y ↔ f x ≤ (μ : EReal)
  constructor
  · intro hzmem
    have hzmem' : appendAffineEquiv n 1 (y, z) ∈ C := hzmem
    have hzmem'' := hzmem'
    rw [hC] at hzmem''
    rcases hzmem'' with ⟨q, hq, hqeq⟩
    have hq' : q = (y, z) := (appendAffineEquiv n 1).injective hqeq
    subst hq'
    rcases hq with ⟨p, hp, hp_eq⟩
    have hp1 : p.1 = x := by
      have hp1' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1 = y := by
        simpa using congrArg Prod.fst hp_eq
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.injective
      simpa [hy] using hp1'
    have hp2 : p.2 = μ := by
      have hp2' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => p.2) = z := by
        simpa using congrArg Prod.snd hp_eq
      have hp2'' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => p.2) =
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) := by
        simpa [hz] using hp2'
      have hp2''' :
          (fun _ : Fin 1 => p.2) = (fun _ : Fin 1 => μ) := by
        exact (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.injective hp2''
      have := congrArg (fun g : Fin 1 → Real => g 0) hp2'''
      simpa using this
    have hle : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := f)).1 hp
    simpa [hp1, hp2] using hle
  · intro hle
    have hxmem : (x, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) f :=
      (mem_epigraph_univ_iff (f := f)).2 hle
    have hzmem' :
        (y, z) ∈
          (fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
      refine ⟨(x, μ), hxmem, ?_⟩
      simp [hy, hz]
    have hzmem : appendAffineEquiv n 1 (y, z) ∈ C := by
      refine ⟨(y, z), hzmem', rfl⟩
    exact hzmem

end Section07
end Chap02
