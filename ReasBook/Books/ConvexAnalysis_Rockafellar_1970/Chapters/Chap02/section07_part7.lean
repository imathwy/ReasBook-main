/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part6

noncomputable section
open scoped Topology

section Chap02
section Section07

theorem convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (ClosedConvexFunction (convexFunctionClosure f) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (convexFunctionClosure f)) ∧
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        convexFunctionClosure f x = f x := by
  classical
  have hbot : ∀ x, f x ≠ (⊥ : EReal) := by
    intro x
    exact hf.2.2 x (by simp)
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have h_epi :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).1
  have hconv_closure : ConvexFunction (convexFunctionClosure f) := by
    unfold ConvexFunction ConvexFunctionOn
    have hconv_epi :
        Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
      simpa [ConvexFunction] using hf.1
    have hconv_cl :
        Convex ℝ (closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)) :=
      hconv_epi.closure
    simpa [h_epi] using hconv_cl
  have hclosed_epi :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f)) := by
    simp [h_epi]
  have hclosed_sub :
      ∀ α : Real,
        IsClosed {x : Fin n → Real | convexFunctionClosure f x ≤ (α : EReal)} :=
    closed_sublevel_of_closed_epigraph (f := convexFunctionClosure f) hclosed_epi
  have hlsc : LowerSemicontinuous (convexFunctionClosure f) :=
    (lowerSemicontinuous_iff_closed_sublevel (f := convexFunctionClosure f)).2 hclosed_sub
  have hclosed : ClosedConvexFunction (convexFunctionClosure f) :=
    ⟨hconv_closure, hlsc⟩
  have hagree :
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        convexFunctionClosure f x = f x :=
    convexFunctionClosure_eq_on_ri (f := f) hf
  have hne_epi :
      Set.Nonempty
        (epigraph (S := (Set.univ : Set (Fin n → Real)))
          (convexFunctionClosure f)) := by
    have hne :
        Set.Nonempty (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := hf.2.1
    have hne_cl :
        (closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)).Nonempty :=
      (closure_nonempty_iff).2 hne
    simpa [h_epi] using hne_cl
  have hfinite :
      ∃ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        convexFunctionClosure f x ≠ (⊤ : EReal) ∧
          convexFunctionClosure f x ≠ (⊥ : EReal) := by
    rcases hf.2.1 with ⟨⟨x0, μ0⟩, hx0⟩
    have hle0 : f x0 ≤ (μ0 : EReal) :=
      (mem_epigraph_univ_iff (f := f)).1 hx0
    have hlt0 : f x0 < ((μ0 + 1) : EReal) := by
      have hμ0_lt : (μ0 : EReal) < ((μ0 + 1) : EReal) := by
        exact (EReal.coe_lt_coe_iff).2 (by linarith)
      exact lt_of_le_of_lt hle0 hμ0_lt
    have hα : ∃ x, f x < ((μ0 + 1) : EReal) := ⟨x0, hlt0⟩
    rcases
        exists_lt_on_ri_effectiveDomain_of_convexFunction (n := n) (f := f) hconv
          (α := μ0 + 1) hα with
      ⟨x1, hx1_ri, hlt1⟩
    have hx1_eq : convexFunctionClosure f x1 = f x1 := hagree x1 hx1_ri
    have htop : f x1 < (⊤ : EReal) :=
      lt_trans hlt1 (EReal.coe_lt_top (μ0 + 1))
    have hnottop : convexFunctionClosure f x1 ≠ (⊤ : EReal) := by
      have hnottop' : f x1 ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 htop
      simpa [hx1_eq] using hnottop'
    have hnotbot : convexFunctionClosure f x1 ≠ (⊥ : EReal) := by
      have hnotbot' : f x1 ≠ (⊥ : EReal) := hbot x1
      simpa [hx1_eq] using hnotbot'
    exact ⟨x1, hx1_ri, hnottop, hnotbot⟩
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (convexFunctionClosure f) := by
    refine ⟨?_, hne_epi, ?_⟩
    · simpa [ConvexFunction] using hconv_closure
    · intro x _
      by_contra hxbot
      have himproper :
          ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
            (convexFunctionClosure f) := by
        refine ⟨?_, ?_⟩
        · simpa [ConvexFunction] using hconv_closure
        · intro hproper'
          have hnotbot := hproper'.2.2 x (by simp)
          exact hnotbot hxbot
      have hno_finite :=
        lowerSemicontinuous_improperConvexFunction_no_finite_values
          (f := convexFunctionClosure f) himproper hlsc
      rcases hfinite with ⟨x1, -, hnottop, hnotbot⟩
      rcases hno_finite x1 with htop' | hbot'
      · exact hnottop htop'
      · exact hnotbot hbot'
  exact ⟨⟨hclosed, hproper⟩, hagree⟩

end Section07
end Chap02
