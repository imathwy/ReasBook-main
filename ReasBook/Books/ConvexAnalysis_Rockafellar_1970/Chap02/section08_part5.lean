/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section08_part4

noncomputable section
open scoped RealInnerProductSpace
open scoped Pointwise Topology
open Metric

section Chap02
section Section08

/-- Theorem 8.5. Let `f` be a proper convex function. The recession function `f0^+` of `f`
is a positively homogeneous proper convex function. For every vector `y`, one has
`(f0^+)(y) = sup { f(x + y) - f(x) | x ∈ dom f }`. If `f` is closed, `f0^+` is closed too,
and for any `x ∈ dom f`, `(f0^+)(y) = sup_{λ > 0} (f(x + λ y) - f(x)) / λ =
lim_{λ → ∞} (f(x + λ y) - f(x)) / λ`. -/
theorem recessionFunction_properties {n : Nat}
    {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real}
    {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hC : C = Set.univ)
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    PositivelyHomogeneous f0_plus ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus ∧
      (∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) ∧
      (ClosedConvexFunction (fun x => (f x : EReal)) →
        ClosedConvexFunction f0_plus ∧
          ∀ x ∈ C, ∀ y : Fin n → Real,
            f0_plus y =
              sSup { r : EReal |
                ∃ t : Real, 0 < t ∧ r = (((f (x + t • y) - f x) / t : Real) : EReal) } ∧
            Filter.Tendsto
              (fun t : Real => (((f (x + t • y) - f x) / t : Real) : EReal))
              Filter.atTop (𝓝 (f0_plus y))) := by
  classical
  have hpos : PositivelyHomogeneous f0_plus := by
    have hcone :
        ∀ t : Real, 0 < t →
          Set.image (fun p : (Fin n → Real) × Real => t • p) (epigraph (Set.univ) f0_plus) ⊆
            epigraph (Set.univ) f0_plus := by
      intro t ht p hp
      rcases hp with ⟨⟨y, μ⟩, hmem, rfl⟩
      have hle : f0_plus y ≤ (μ : EReal) := (mem_epigraph_univ_iff).1 hmem
      have hstep :
          ∀ x ∈ C, ((f (x + y) - f x : Real) : EReal) ≤ (μ : EReal) :=
        (recessionFunction_le_iff (C := C) (f := f) (f0_plus := f0_plus) hf0_plus y μ).1 hle
      have hstep' : ∀ x, ((f (x + y) - f x : Real) : EReal) ≤ (μ : EReal) := by
        intro x
        have hx := hstep x (by simp [hC])
        simpa using hx
      have hbound :
          ∀ x, ((f (x + t • y) - f x : Real) : EReal) ≤ ((t * μ : Real) : EReal) := by
        intro x
        exact recessionFunction_ray_bound (hC := hC) (hf := hf) (y := y) (v := μ) hstep' t ht x
      have hboundC :
          ∀ x ∈ C, ((f (x + t • y) - f x : Real) : EReal) ≤ ((t * μ : Real) : EReal) := by
        intro x hx
        simpa using hbound x
      have hle' : f0_plus (t • y) ≤ ((t * μ : Real) : EReal) :=
        (recessionFunction_le_iff (C := C) (f := f) (f0_plus := f0_plus) hf0_plus (t • y)
            (t * μ)).2 hboundC
      exact (mem_epigraph_univ_iff).2 hle'
    exact posHom_of_epigraph_cone (f := f0_plus) hcone
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus := by
    -- Proper convexity should follow from convexity of `f` and the recession formula.
    have hnotbot :
        ∀ y : Fin n → Real, f0_plus y ≠ (⊥ : EReal) :=
      recessionFunction_ne_bot (C := C) (f := f) (f0_plus := f0_plus) hf hf0_plus
    have hne_epi :
        Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f0_plus) :=
      recessionFunction_epigraph_nonempty (C := C) (f := f) (f0_plus := f0_plus) hf hf0_plus
    have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus := by
      exact
        recessionFunction_convex_univ (C := C) (f := f) (f0_plus := f0_plus) hC hf hf0_plus hpos
    refine ⟨hconv, hne_epi, ?_⟩
    intro x hx
    exact hnotbot x
  refine ⟨hpos, hproper, ?_, ?_⟩
  · exact hf0_plus
  · -- Closedness and the ray formula require additional properties of the difference quotients.
    intro hclosed
    have hclosed_f0 :
        ClosedConvexFunction f0_plus := by
      have hls_f0 :
          LowerSemicontinuous f0_plus :=
        recessionFunction_lsc_of_closed (C := C) (f := f) (f0_plus := f0_plus) hC hf0_plus
          hclosed
      exact (properConvexFunction_closed_iff_lowerSemicontinuous (f := f0_plus) hproper).2 hls_f0
    refine ⟨hclosed_f0, ?_⟩
    intro x hx y
    refine ⟨?_, ?_⟩
    · simpa using
        (ray_sSup_eq_of_closed (C := C) (f := f) (f0_plus := f0_plus)
          hC hf hf0_plus hpos hclosed x y)
    · simpa using
        (ray_limit_monotone (C := C) (f := f) (f0_plus := f0_plus)
          hC hf hf0_plus hpos hclosed x y)

end Section08
end Chap02
