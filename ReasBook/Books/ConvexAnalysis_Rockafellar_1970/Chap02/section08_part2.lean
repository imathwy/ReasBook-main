/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section08_part1

noncomputable section
open scoped RealInnerProductSpace
open scoped Pointwise Topology
open Metric

section Chap02
section Section08

/-- Theorem 8.2. Let `C` be a non-empty closed convex set in `ℝ^n`. Then `0^+ C` is closed,
and it consists of all possible limits of sequences of the form `λ_1 x_1, λ_2 x_2, ...`, where
`x_i ∈ C` and `λ_i` decreases to `0`. In fact, for the convex cone `K` in `ℝ^(n+1)` generated
by `{(1, x) | x ∈ C}` one has `cl K = K ∪ {(0, x) | x ∈ 0^+ C}`. -/
theorem recessionCone_closed_and_limits_and_closure_cone {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex Real C) :
    IsClosed (Set.recessionCone C) ∧
      Set.recessionCone C =
        {y : EuclideanSpace Real (Fin n) |
          ∃ (x : ℕ → EuclideanSpace Real (Fin n)) (r : ℕ → ℝ),
            (∀ n, x n ∈ C) ∧ Antitone r ∧ Filter.Tendsto r Filter.atTop (𝓝 (0 : ℝ)) ∧
              Filter.Tendsto (fun n => r n • x n) Filter.atTop (𝓝 y)} ∧
      (let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
          EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n));
        let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0;
        let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
          fun v =>
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
              (fun i => coords v (Fin.natAdd 1 i));
        let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C};
        let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
          (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))));
        closure K = K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C}) := by
  have hclosed : IsClosed (Set.recessionCone C) :=
    recessionCone_isClosed_of_closed (C := C) hCclosed
  refine ⟨hclosed, ?_, ?_⟩
  · classical
    ext y
    constructor
    · intro hy
      exact recessionCone_subset_seq_limits (C := C) hCne hy
    · intro hy
      exact
        seq_limits_subset_recessionCone (C := C) hCne hCclosed hCconv hy
  · classical
    simpa using
      (closure_cone_eq_union_recession (n := n) (C := C) hCne hCclosed hCconv)

/-- Sequence data associated with a half-line inside `C`. -/
lemma halfline_seq_data {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {x0 y : EuclideanSpace Real (Fin n)}
    (hx0 : ∀ t : Real, 0 ≤ t → x0 + t • y ∈ C) :
    ∃ (x : ℕ → EuclideanSpace Real (Fin n)) (r : ℕ → ℝ),
      (∀ n, x n ∈ C) ∧ Antitone r ∧ Filter.Tendsto r Filter.atTop (𝓝 (0 : ℝ)) ∧
        Filter.Tendsto (fun n => r n • x n) Filter.atTop (𝓝 y) := by
  refine ⟨(fun n => x0 + ((n : ℝ) + 1) • y), (fun n => 1 / ((n : ℝ) + 1)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have hnonneg : 0 ≤ (n : ℝ) + 1 := by linarith
    exact hx0 ((n : ℝ) + 1) hnonneg
  · intro m n hmn
    dsimp
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have hle' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    exact one_div_le_one_div_of_le hpos hle
  · simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))
  · have hcont_smul : Continuous fun t : ℝ => t • x0 := by
      continuity
    have hsmul :
        Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • x0) Filter.atTop (𝓝 (0 : _)) :=
      (by
        simpa using
          (hcont_smul.continuousAt.tendsto.comp
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))))
    have hcont_add : Continuous fun z : EuclideanSpace Real (Fin n) => z + y := by
      continuity
    have hlim :
        Filter.Tendsto
            (fun n : ℕ => (1 / ((n : ℝ) + 1)) • x0 + y) Filter.atTop (𝓝 y) := by
      simpa using (hcont_add.continuousAt.tendsto.comp hsmul)
    have hform :
        (fun n : ℕ => (1 / ((n : ℝ) + 1)) • (x0 + ((n : ℝ) + 1) • y)) =
          fun n : ℕ => (1 / ((n : ℝ) + 1)) • x0 + y := by
      funext n
      have hne : (n : ℝ) + 1 ≠ 0 := by linarith
      calc
        (1 / ((n : ℝ) + 1)) • (x0 + ((n : ℝ) + 1) • y)
            = (1 / ((n : ℝ) + 1)) • x0 +
                (1 / ((n : ℝ) + 1)) • (((n : ℝ) + 1) • y) := by
                  simp [smul_add]
        _ = (1 / ((n : ℝ) + 1)) • x0 + y := by
              simp [smul_smul, hne]
    refine hlim.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro n
    exact (congrArg (fun f => f n) hform).symm

/-- A half-line contained in `C` yields a recession direction. -/
lemma halfline_mem_recessionCone {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex Real C)
    {x0 y : EuclideanSpace Real (Fin n)}
    (hx0 : ∀ t : Real, 0 ≤ t → x0 + t • y ∈ C) :
    y ∈ Set.recessionCone C := by
  have hseq := halfline_seq_data (C := C) (x0 := x0) (y := y) hx0
  exact seq_limits_subset_recessionCone (C := C) hCne hCclosed hCconv hseq

/-- Rays from points in the relative interior stay in the relative interior. -/
lemma ri_ray_mem {n : Nat} {C : Set (EuclideanSpace Real (Fin n))} (hCconv : Convex Real C)
    {y : EuclideanSpace Real (Fin n)} (hy : y ∈ Set.recessionCone C)
    {x : EuclideanSpace Real (Fin n)} (hx : x ∈ euclideanRelativeInterior n C) :
    ∀ t : Real, 0 ≤ t → x + t • y ∈ euclideanRelativeInterior n C := by
  intro t ht
  have hxC : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx
  have htp1 : 0 ≤ t + 1 := by linarith
  have hx1C : x + (t + 1) • y ∈ C := hy hxC htp1
  have hx1cl : x + (t + 1) • y ∈ closure C :=
    (euclideanRelativeInterior_subset_closure n C).2 hx1C
  let α : ℝ := t / (t + 1)
  have hα0 : 0 ≤ α := by
    have hden : 0 ≤ t + 1 := by linarith
    dsimp [α]
    exact div_nonneg ht hden
  have hα1 : α < 1 := by
    have hden : 0 < t + 1 := by linarith
    have h : t < t + 1 := by linarith
    have h' : t / (t + 1) < 1 := (div_lt_one hden).2 h
    simpa [α] using h'
  have hcomb :
      (1 - α) • x + α • (x + (t + 1) • y) = x + t • y := by
    have hden : (t + 1) ≠ 0 := by linarith
    have hmul : α * (t + 1) = t := by
      dsimp [α]
      field_simp [hden]
    have hxadd : (1 - α) • x + α • x = x := by
      calc
        (1 - α) • x + α • x = ((1 - α) + α) • x := by
          simpa using (add_smul (1 - α) α x).symm
        _ = x := by simp
    calc
      (1 - α) • x + α • (x + (t + 1) • y)
          = (1 - α) • x + (α • x + α • ((t + 1) • y)) := by
              simp [smul_add]
      _ = ((1 - α) • x + α • x) + α • ((t + 1) • y) := by
              simp [add_assoc]
      _ = x + α • ((t + 1) • y) := by
              simpa [add_assoc] using congrArg (fun z => z + α • ((t + 1) • y)) hxadd
      _ = x + (α * (t + 1)) • y := by
              simp [smul_smul]
      _ = x + t • y := by
              simp [hmul]
  have hri :
      (1 - α) • x + α • (x + (t + 1) • y) ∈ euclideanRelativeInterior n C :=
    euclideanRelativeInterior_convex_combination_mem n C hCconv x (x + (t + 1) • y) hx
      hx1cl α hα0 hα1
  exact hcomb ▸ hri

/-- A ray property in `ri C` yields membership in `0^+ (ri C)`. -/
lemma recessionCone_ri_of_ri_ray {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {y : EuclideanSpace Real (Fin n)}
    (hri : ∀ x ∈ euclideanRelativeInterior n C, ∀ t : Real, 0 ≤ t →
      x + t • y ∈ euclideanRelativeInterior n C) :
    y ∈ Set.recessionCone (euclideanRelativeInterior n C) := by
  intro x hx t ht
  exact hri x hx t ht

/-- Theorem 8.3. Let `C` be a non-empty closed convex set, and let `y ≠ 0`. If there exists
`x` such that the half-line `{x + λ y | λ ≥ 0}` is contained in `C`, then the same holds for
every `x ∈ C`, i.e. `y ∈ 0^+ C`. Moreover, for each `x ∈ ri C`, the half-line
`{x + λ y | λ ≥ 0}` is contained in `ri C`, so `y ∈ 0^+ (ri C)`. -/
theorem recessionCone_of_exists_halfline {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex Real C)
    {y : EuclideanSpace Real (Fin n)} (_hy : y ≠ 0)
    (hex : ∃ x, ∀ t : Real, 0 ≤ t → x + t • y ∈ C) :
    y ∈ Set.recessionCone C ∧
      (∀ x ∈ euclideanRelativeInterior n C, ∀ t : Real, 0 ≤ t →
        x + t • y ∈ euclideanRelativeInterior n C) ∧
      y ∈ Set.recessionCone (euclideanRelativeInterior n C) := by
  rcases hex with ⟨x0, hx0⟩
  have hy_mem : y ∈ Set.recessionCone C :=
    halfline_mem_recessionCone (C := C) hCne hCclosed hCconv (x0 := x0) (y := y) hx0
  have hri :
      ∀ x ∈ euclideanRelativeInterior n C, ∀ t : Real, 0 ≤ t →
        x + t • y ∈ euclideanRelativeInterior n C := by
    intro x hx t ht
    exact ri_ray_mem (C := C) (n := n) hCconv hy_mem (x := x) hx t ht
  refine ⟨hy_mem, hri, ?_⟩
  exact recessionCone_ri_of_ri_ray (n := n) (C := C) (y := y) hri

/-- Characterization of recession directions of `closure C` via rays from a point in `ri C`. -/
lemma recessionCone_closure_iff_ray_in_C {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCconv : Convex Real C)
    {x : EuclideanSpace Real (Fin n)} (hx : x ∈ euclideanRelativeInterior n C) :
    ∀ y : EuclideanSpace Real (Fin n),
      (y ∈ Set.recessionCone (closure C) ↔
        ∀ t : Real, 0 < t → x + t • y ∈ C) := by
  intro y
  by_cases hy : y = 0
  · subst hy
    constructor
    · intro _ t ht
      have hxC : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx
      simpa using hxC
    · intro _ x' hx' t ht
      simpa using hx'
  · have hclconv : Convex Real (closure C) := convex_closure_of_convex n C hCconv
    have hclne : (closure C).Nonempty := by
      rcases hCne with ⟨x0, hx0⟩
      exact ⟨x0, subset_closure hx0⟩
    constructor
    · intro hy_cl t ht
      have hex :
          ∃ x0 : EuclideanSpace Real (Fin n),
            ∀ t : Real, 0 ≤ t → x0 + t • y ∈ closure C := by
        rcases hCne with ⟨x0, hx0⟩
        refine ⟨x0, ?_⟩
        intro t ht'
        have hx0cl : x0 ∈ closure C := subset_closure hx0
        exact hy_cl hx0cl ht'
      have htheorem :
          y ∈ Set.recessionCone (closure C) ∧
            (∀ x ∈ euclideanRelativeInterior n (closure C), ∀ t : Real, 0 ≤ t →
              x + t • y ∈ euclideanRelativeInterior n (closure C)) ∧
            y ∈ Set.recessionCone (euclideanRelativeInterior n (closure C)) :=
        recessionCone_of_exists_halfline (n := n) (C := closure C)
          hclne isClosed_closure hclconv hy hex
      have hri :
          ∀ x ∈ euclideanRelativeInterior n (closure C), ∀ t : Real, 0 ≤ t →
            x + t • y ∈ euclideanRelativeInterior n (closure C) := htheorem.2.1
      have hri_eq :
          euclideanRelativeInterior n (closure C) = euclideanRelativeInterior n C :=
        (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hCconv).2
      have hx_cl : x ∈ euclideanRelativeInterior n (closure C) := by
        simpa [hri_eq] using hx
      have hx_t_ri :
          x + t • y ∈ euclideanRelativeInterior n (closure C) := hri x hx_cl t (le_of_lt ht)
      have hx_t_ri' :
          x + t • y ∈ euclideanRelativeInterior n C := by
        simpa [hri_eq] using hx_t_ri
      exact (euclideanRelativeInterior_subset_closure n C).1 hx_t_ri'
    · intro hline
      have hxC : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx
      have hx_cl : x ∈ closure C := (euclideanRelativeInterior_subset_closure n C).2 hxC
      have hline' :
          ∀ t : Real, 0 ≤ t → x + t • y ∈ closure C := by
        intro t ht
        by_cases ht0 : t = 0
        · subst ht0
          simpa using hx_cl
        · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
          have hx_tC : x + t • y ∈ C := hline t htpos
          exact (euclideanRelativeInterior_subset_closure n C).2 hx_tC
      have hex :
          ∃ x0 : EuclideanSpace Real (Fin n),
            ∀ t : Real, 0 ≤ t → x0 + t • y ∈ closure C := ⟨x, hline'⟩
      have htheorem :
          y ∈ Set.recessionCone (closure C) ∧
            (∀ x ∈ euclideanRelativeInterior n (closure C), ∀ t : Real, 0 ≤ t →
              x + t • y ∈ euclideanRelativeInterior n (closure C)) ∧
            y ∈ Set.recessionCone (euclideanRelativeInterior n (closure C)) :=
        recessionCone_of_exists_halfline (n := n) (C := closure C)
          hclne isClosed_closure hclconv hy hex
      exact htheorem.1

/-- Corollary 8.3.1. For any non-empty convex set `C`, one has
`0^+ (ri C) = 0^+ (cl C)`. In fact, given any `x ∈ ri C`, one has
`y ∈ 0^+ (cl C)` if and only if `x + λ • y ∈ C` for every `λ > 0`. -/
theorem recessionCone_ri_eq_cl_and_characterization {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCconv : Convex Real C) :
    Set.recessionCone (euclideanRelativeInterior n C) =
      Set.recessionCone (closure C) ∧
      (∀ x ∈ euclideanRelativeInterior n C, ∀ y : EuclideanSpace Real (Fin n),
        (y ∈ Set.recessionCone (closure C) ↔
          ∀ t : Real, 0 < t → x + t • y ∈ C)) := by
  have hclconv : Convex Real (closure C) := convex_closure_of_convex n C hCconv
  have hri_eq :
      euclideanRelativeInterior n (closure C) = euclideanRelativeInterior n C :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hCconv).2
  have hri_nonempty :
      (euclideanRelativeInterior n C).Nonempty :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C hCconv).2.2.2.2 hCne
  have hclne : (closure C).Nonempty := by
    rcases hCne with ⟨x0, hx0⟩
    exact ⟨x0, subset_closure hx0⟩
  have hsubset1 :
      Set.recessionCone (euclideanRelativeInterior n C) ⊆
        Set.recessionCone (closure C) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      intro x hx t ht
      simpa using hx
    · rcases hri_nonempty with ⟨x0, hx0⟩
      have hex :
          ∃ x : EuclideanSpace Real (Fin n),
            ∀ t : Real, 0 ≤ t → x + t • y ∈ closure C := by
        refine ⟨x0, ?_⟩
        intro t ht
        have hx0_ri : x0 + t • y ∈ euclideanRelativeInterior n C := hy hx0 ht
        have hx0_C : x0 + t • y ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx0_ri
        exact (euclideanRelativeInterior_subset_closure n C).2 hx0_C
      have htheorem :
          y ∈ Set.recessionCone (closure C) ∧
            (∀ x ∈ euclideanRelativeInterior n (closure C), ∀ t : Real, 0 ≤ t →
              x + t • y ∈ euclideanRelativeInterior n (closure C)) ∧
            y ∈ Set.recessionCone (euclideanRelativeInterior n (closure C)) :=
        recessionCone_of_exists_halfline (n := n) (C := closure C)
          hclne isClosed_closure hclconv hy0 hex
      exact htheorem.1
  have hsubset2 :
      Set.recessionCone (closure C) ⊆
        Set.recessionCone (euclideanRelativeInterior n C) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      intro x hx t ht
      simpa using hx
    · have hex :
          ∃ x0 : EuclideanSpace Real (Fin n),
            ∀ t : Real, 0 ≤ t → x0 + t • y ∈ closure C := by
        rcases hCne with ⟨x0, hx0⟩
        refine ⟨x0, ?_⟩
        intro t ht
        have hx0cl : x0 ∈ closure C := subset_closure hx0
        exact hy hx0cl ht
      have htheorem :
          y ∈ Set.recessionCone (closure C) ∧
            (∀ x ∈ euclideanRelativeInterior n (closure C), ∀ t : Real, 0 ≤ t →
              x + t • y ∈ euclideanRelativeInterior n (closure C)) ∧
            y ∈ Set.recessionCone (euclideanRelativeInterior n (closure C)) :=
        recessionCone_of_exists_halfline (n := n) (C := closure C)
          hclne isClosed_closure hclconv hy0 hex
      have hy_ri : y ∈ Set.recessionCone (euclideanRelativeInterior n (closure C)) :=
        htheorem.2.2
      simpa [hri_eq] using hy_ri
  refine ⟨?_, ?_⟩
  · exact le_antisymm hsubset1 hsubset2
  · intro x hx y
    exact recessionCone_closure_iff_ray_in_C (n := n) (C := C) hCne hCconv hx y

/-- Elements of the recession cone scale back into `C` from the origin. -/
lemma recessionCone_subset_inv_smul_set {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hC0 : (0 : EuclideanSpace Real (Fin n)) ∈ C) :
    ∀ y, y ∈ Set.recessionCone C → ∀ ε : ℝ, 0 < ε → (ε⁻¹) • y ∈ C := by
  intro y hy ε hε
  have hεnonneg : 0 ≤ (ε⁻¹) := inv_nonneg.mpr (le_of_lt hε)
  have hmem := hy (x := 0) hC0 (t := ε⁻¹) hεnonneg
  simpa using hmem

/-- If all inverse scalings of `y` lie in `C`, then `y` is a recession direction. -/
lemma inv_smul_set_subset_recessionCone {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hC0 : (0 : EuclideanSpace Real (Fin n)) ∈ C) :
    ∀ y, (∀ ε : ℝ, 0 < ε → (ε⁻¹) • y ∈ C) → y ∈ Set.recessionCone C := by
  intro y hy
  have hCne : C.Nonempty := ⟨0, hC0⟩
  have hx0 : ∀ t : Real, 0 ≤ t → (0 : EuclideanSpace Real (Fin n)) + t • y ∈ C := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      simpa using hC0
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hmem : t • y ∈ C := by
        have hmem' := hy (t⁻¹) (inv_pos.mpr htpos)
        simpa using hmem'
      simpa using hmem
  exact halfline_mem_recessionCone (C := C) hCne hCclosed hCconv (x0 := 0) (y := y) hx0

/-- The inverse-scaling characterization equals the intersection of all positive scalings. -/
lemma inv_smul_set_eq_iInter_smul {n : Nat} {C : Set (EuclideanSpace Real (Fin n))} :
    { y : EuclideanSpace Real (Fin n) | ∀ ε : ℝ, 0 < ε → (ε⁻¹) • y ∈ C } =
      ⋂ (ε : ℝ) (_ : 0 < ε), (ε • C) := by
  ext y
  constructor
  · intro hy
    have hy' : ∀ ε : ℝ, 0 < ε → y ∈ ε • C := by
      intro ε hε
      have hεne : ε ≠ 0 := ne_of_gt hε
      exact (Set.mem_smul_set_iff_inv_smul_mem₀ hεne C y).2 (hy ε hε)
    simpa using hy'
  · intro hy
    have hy' : ∀ ε : ℝ, 0 < ε → y ∈ ε • C := by
      simpa using hy
    intro ε hε
    have hεne : ε ≠ 0 := ne_of_gt hε
    exact (Set.mem_smul_set_iff_inv_smul_mem₀ hεne C y).1 (hy' ε hε)

/-- Corollary 8.3.2. If `C` is a closed convex set containing the origin, then
`0^+ C = { y | ε⁻¹ • y ∈ C, ∀ ε > 0 } = ⋂ (ε > 0), ε • C`. -/
theorem recessionCone_eq_inv_smul_set_and_iInter {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hC0 : (0 : EuclideanSpace Real (Fin n)) ∈ C) :
    Set.recessionCone C =
      { y : EuclideanSpace Real (Fin n) | ∀ ε : ℝ, 0 < ε → (ε⁻¹) • y ∈ C } ∧
      { y : EuclideanSpace Real (Fin n) | ∀ ε : ℝ, 0 < ε → (ε⁻¹) • y ∈ C } =
        ⋂ (ε : ℝ) (_ : 0 < ε), (ε • C) := by
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · intro hy
      exact recessionCone_subset_inv_smul_set (C := C) hC0 y hy
    · intro hy
      exact inv_smul_set_subset_recessionCone (C := C) hCclosed hCconv hC0 y hy
  · exact inv_smul_set_eq_iInter_smul (C := C)

/-- A recession direction for the intersection yields half-lines in each set. -/
lemma recessionCone_iInter_halfline {n : Nat} {ι : Type*}
    {C : ι → Set (EuclideanSpace Real (Fin n))}
    {x0 y : EuclideanSpace Real (Fin n)}
    (hy : y ∈ Set.recessionCone (⋂ i, C i)) (hx0 : x0 ∈ ⋂ i, C i) :
    ∀ i, ∀ t : Real, 0 ≤ t → x0 + t • y ∈ C i := by
  intro i t ht
  have hmem : x0 + t • y ∈ ⋂ i, C i := hy (x := x0) (t := t) hx0 ht
  have hmem' : ∀ i, x0 + t • y ∈ C i := by
    simpa using hmem
  exact hmem' i

/-- The recession cone of an intersection is contained in the intersection of recession cones. -/
lemma recessionCone_iInter_subset {n : Nat} {ι : Type*}
    (C : ι → Set (EuclideanSpace Real (Fin n)))
    (hCclosed : ∀ i, IsClosed (C i)) (hCconv : ∀ i, Convex Real (C i))
    (hCne : (⋂ i, C i).Nonempty) :
    Set.recessionCone (⋂ i, C i) ⊆ ⋂ i, Set.recessionCone (C i) := by
  intro y hy
  rcases hCne with ⟨x0, hx0⟩
  have hx0' : ∀ i, x0 ∈ C i := by
    simpa using hx0
  have hhalf :
      ∀ i, ∀ t : Real, 0 ≤ t → x0 + t • y ∈ C i :=
    recessionCone_iInter_halfline (C := C) (x0 := x0) (y := y) hy hx0
  have hyi : ∀ i, y ∈ Set.recessionCone (C i) := by
    intro i
    have hCne_i : (C i).Nonempty := ⟨x0, hx0' i⟩
    have hx0line : ∀ t : Real, 0 ≤ t → x0 + t • y ∈ C i := hhalf i
    exact
      halfline_mem_recessionCone (C := C i) hCne_i (hCclosed i) (hCconv i)
        (x0 := x0) (y := y) hx0line
  simpa using hyi

/-- Recession directions common to all sets are recession directions of the intersection. -/
lemma iInter_recessionCone_subset {n : Nat} {ι : Type*}
    (C : ι → Set (EuclideanSpace Real (Fin n))) :
    (⋂ i, Set.recessionCone (C i)) ⊆ Set.recessionCone (⋂ i, C i) := by
  intro y hy x hx t ht
  have hy' : ∀ i, y ∈ Set.recessionCone (C i) := by
    simpa using hy
  have hx' : ∀ i, x ∈ C i := by
    simpa using hx
  have hmem : ∀ i, x + t • y ∈ C i := by
    intro i
    exact hy' i (x := x) (t := t) (hx' i) ht
  simpa using hmem

/-- Corollary 8.3.3. If `{C_i | i ∈ I}` is an arbitrary collection of closed convex sets in
`ℝ^n` whose intersection is not empty, then `0^+ (⋂ i, C_i) = ⋂ i, 0^+ C_i`. -/
theorem recessionCone_iInter_eq_iInter {n : Nat} {ι : Type*}
    (C : ι → Set (EuclideanSpace Real (Fin n)))
    (hCclosed : ∀ i, IsClosed (C i)) (hCconv : ∀ i, Convex Real (C i))
    (hCne : (⋂ i, C i).Nonempty) :
    Set.recessionCone (⋂ i, C i) = ⋂ i, Set.recessionCone (C i) := by
  ext y
  constructor
  · intro hy
    exact (recessionCone_iInter_subset (C := C) hCclosed hCconv hCne) hy
  · intro hy
    exact (iInter_recessionCone_subset (C := C)) hy

/-- Nonempty preimage implies nonempty target set. -/
lemma preimage_nonempty_implies_C_nonempty {n m : Nat}
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    {C : Set (EuclideanSpace Real (Fin m))} :
    (A ⁻¹' C).Nonempty → C.Nonempty := by
  intro h
  rcases h with ⟨x0, hx0⟩
  exact ⟨A x0, hx0⟩

/-- Recession cone of the preimage lies in the preimage of the recession cone. -/
lemma recessionCone_preimage_linearMap_subset {n m : Nat}
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    {C : Set (EuclideanSpace Real (Fin m))} (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hCne : (A ⁻¹' C).Nonempty) :
    Set.recessionCone (A ⁻¹' C) ⊆ A ⁻¹' (Set.recessionCone C) := by
  intro y hy
  rcases hCne with ⟨x0, hx0⟩
  have hCne' : C.Nonempty := preimage_nonempty_implies_C_nonempty (A := A) ⟨x0, hx0⟩
  have hx0line : ∀ t : Real, 0 ≤ t → A x0 + t • A y ∈ C := by
    intro t ht
    have hpre : x0 + t • y ∈ A ⁻¹' C := hy (x := x0) hx0 ht
    simpa [Set.preimage, A.map_add, A.map_smul] using hpre
  have hy' : A y ∈ Set.recessionCone C :=
    halfline_mem_recessionCone (C := C) hCne' hCclosed hCconv
      (x0 := A x0) (y := A y) hx0line
  simpa [Set.preimage] using hy'

/-- Preimage of the recession cone lies in the recession cone of the preimage. -/
lemma preimage_recessionCone_subset_recessionCone_preimage {n m : Nat}
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    {C : Set (EuclideanSpace Real (Fin m))} :
    A ⁻¹' (Set.recessionCone C) ⊆ Set.recessionCone (A ⁻¹' C) := by
  intro y hy x hx t ht
  have hy' : A y ∈ Set.recessionCone C := by
    simpa [Set.preimage] using hy
  have hx' : A x ∈ C := by
    simpa [Set.preimage] using hx
  have hmem : A x + t • A y ∈ C := hy' hx' ht
  have hpre : A (x + t • y) ∈ C := by
    simpa [A.map_add, A.map_smul] using hmem
  simpa [Set.preimage] using hpre

/-- Corollary 8.3.4. Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`, and let `C` be a
closed convex set in `ℝ^m` such that `A ⁻¹' C` is nonempty. Then
`0^+ (A ⁻¹' C) = A ⁻¹' (0^+ C)`. -/
theorem recessionCone_preimage_linearMap {n m : Nat}
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    {C : Set (EuclideanSpace Real (Fin m))} (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hCne : (A ⁻¹' C).Nonempty) :
    Set.recessionCone (A ⁻¹' C) = A ⁻¹' (Set.recessionCone C) := by
  ext y
  constructor
  · intro hy
    exact
      (recessionCone_preimage_linearMap_subset (A := A) hCclosed hCconv hCne) hy
  · intro hy
    exact (preimage_recessionCone_subset_recessionCone_preimage (A := A)) hy

/-- Bounded sets have only the zero recession direction. -/
lemma recessionCone_subset_singleton_of_bounded {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty)
    (hCbdd : Bornology.IsBounded C) :
    Set.recessionCone C ⊆ {0} := by
  intro y hy
  by_contra hy0
  rcases hCne with ⟨x0, hx0⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  rcases hCbdd.subset_closedBall (0 : EuclideanSpace Real (Fin n)) with ⟨R, hR⟩
  have hx0R : ‖x0‖ ≤ R := by
    have hx0mem : x0 ∈ closedBall (0 : EuclideanSpace Real (Fin n)) R := hR hx0
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx0mem
  have hRnonneg : 0 ≤ R := le_trans (norm_nonneg _) hx0R
  set t : ℝ := (R + ‖x0‖ + 1) / ‖y‖
  have ht_nonneg : 0 ≤ t := by
    have hnum : 0 ≤ R + ‖x0‖ + 1 := by
      linarith [hRnonneg, norm_nonneg x0]
    exact div_nonneg hnum (le_of_lt hypos)
  have hx_t : x0 + t • y ∈ C := hy hx0 ht_nonneg
  have hx_t_R : ‖x0 + t • y‖ ≤ R := by
    have hx_t_mem : x0 + t • y ∈ closedBall (0 : EuclideanSpace Real (Fin n)) R := hR hx_t
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx_t_mem
  have htriangle : ‖t • y‖ ≤ ‖x0 + t • y‖ + ‖x0‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (norm_sub_le (x0 + t • y) x0)
  have hnorm_bound : ‖t • y‖ ≤ R + ‖x0‖ := by
    linarith [htriangle, hx_t_R]
  have hnorm_t : ‖t • y‖ = t * ‖y‖ := by
    calc
      ‖t • y‖ = ‖t‖ * ‖y‖ := norm_smul _ _
      _ = t * ‖y‖ := by
            simp [Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
  have hbound : t * ‖y‖ ≤ R + ‖x0‖ := by
    simpa [hnorm_t] using hnorm_bound
  have ht_eq : t * ‖y‖ = R + ‖x0‖ + 1 := by
    have hyne : ‖y‖ ≠ 0 := ne_of_gt hypos
    calc
      t * ‖y‖ = ((R + ‖x0‖ + 1) / ‖y‖) * ‖y‖ := by simp [t]
      _ = R + ‖x0‖ + 1 := by
            field_simp [hyne]
  have : (R + ‖x0‖ + 1 : ℝ) ≤ R + ‖x0‖ := by
    simpa [ht_eq] using hbound
  linarith

/-- An unbounded set admits a sequence with strictly increasing norms. -/
lemma exists_strictMono_norm_seq_of_unbounded {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCunbdd : ¬ Bornology.IsBounded C) :
    ∃ x : ℕ → EuclideanSpace Real (Fin n),
      (∀ n, x n ∈ C) ∧ StrictMono (fun n => ‖x n‖) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ ‖x n‖) := by
  classical
  have hforall : ∀ R : ℝ, ∃ x ∈ C, R < ‖x‖ := by
    by_contra h
    push_neg at h
    rcases h with ⟨R, hR⟩
    have hsubset : C ⊆ closedBall (0 : EuclideanSpace Real (Fin n)) R := by
      intro x hx
      have hxR : ‖x‖ ≤ R := hR x hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
    have hbounded : Bornology.IsBounded C :=
      (isBounded_closedBall.subset hsubset)
    exact hCunbdd hbounded
  obtain ⟨x0, hx0C, hx0_gt⟩ := hforall 1
  let x : ℕ → EuclideanSpace Real (Fin n) :=
    Nat.rec x0 (fun n xn => Classical.choose (hforall (‖xn‖ + 1)))
  have hx_mem : ∀ n, x n ∈ C := by
    intro n
    induction n with
    | zero =>
        simpa [x] using hx0C
    | succ n ih =>
        have hspec := Classical.choose_spec (hforall (‖x n‖ + 1))
        simpa [x] using hspec.1
  have hx_succ : ∀ n, ‖x n‖ + 1 < ‖x (n + 1)‖ := by
    intro n
    have hspec := Classical.choose_spec (hforall (‖x n‖ + 1))
    simpa [x] using hspec.2
  have hx_strict : StrictMono (fun n => ‖x n‖) := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    have h := hx_succ n
    linarith
  have hx_ge : ∀ n : ℕ, (n : ℝ) + 1 ≤ ‖x n‖ := by
    intro n
    induction n with
    | zero =>
        have : (1 : ℝ) ≤ ‖x0‖ := le_of_lt hx0_gt
        simpa [x] using this
    | succ n ih =>
        have hsucc : ‖x n‖ + 1 < ‖x (n + 1)‖ := hx_succ n
        have hsucc_le : ‖x n‖ + 1 ≤ ‖x (n + 1)‖ := le_of_lt hsucc
        have :
            (n : ℝ) + 1 + 1 ≤ ‖x (n + 1)‖ := by
          linarith [ih, hsucc_le]
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using this
  exact ⟨x, hx_mem, hx_strict, hx_ge⟩

/-- An unbounded closed convex set has a nonzero recession direction. -/
lemma exists_nonzero_mem_recessionCone_of_unbounded {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex Real C) (hCunbdd : ¬ Bornology.IsBounded C) :
    ∃ y, y ≠ 0 ∧ y ∈ Set.recessionCone C := by
  classical
  obtain ⟨x, hxC, hx_strict, hx_ge⟩ :=
    exists_strictMono_norm_seq_of_unbounded (C := C) hCunbdd
  let r : ℕ → ℝ := fun n => 1 / ‖x n‖
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n
    have hpos : 0 < ‖x n‖ := by
      have hge : (1 : ℝ) ≤ ‖x n‖ := by
        have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
        exact le_trans this (hx_ge n)
      linarith
    have hnonneg : 0 ≤ ‖x n‖⁻¹ := inv_nonneg.mpr (le_of_lt hpos)
    convert hnonneg using 1
    simp [r, one_div]
  have hr_le : ∀ n, r n ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : 0 < (n : ℝ) + 1 := by linarith
    have hle : (n : ℝ) + 1 ≤ ‖x n‖ := hx_ge n
    have h := one_div_le_one_div_of_le hpos hle
    simpa [r] using h
  have hr_antitone : Antitone r := by
    intro m n hmn
    have hpos : 0 < ‖x m‖ := by
      have hge : (1 : ℝ) ≤ ‖x m‖ := by
        have : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
        exact le_trans this (hx_ge m)
      linarith
    have hle : ‖x m‖ ≤ ‖x n‖ := (StrictMono.monotone hx_strict) hmn
    have h := one_div_le_one_div_of_le hpos hle
    simpa [r] using h
  have hr_tendsto : Filter.Tendsto r Filter.atTop (𝓝 (0 : ℝ)) := by
    have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds
    have hupper :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hle1 : (fun n : ℕ => (0 : ℝ)) ≤ r := by
      intro n
      exact hr_nonneg n
    have hle2 : r ≤ fun n : ℕ => 1 / ((n : ℝ) + 1) := by
      intro n
      exact hr_le n
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hzero hupper hle1 hle2
  let u : ℕ → EuclideanSpace Real (Fin n) := fun n => r n • x n
  have hu_mem : ∀ k, u k ∈ sphere (0 : EuclideanSpace Real (Fin n)) (1 : ℝ) := by
    intro k
    have hnorm_ne : ‖x k‖ ≠ 0 := by
      have hge : (1 : ℝ) ≤ ‖x k‖ := by
        have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
        exact le_trans this (hx_ge k)
      have hpos : 0 < ‖x k‖ := by linarith
      exact ne_of_gt hpos
    have hnorm : ‖u k‖ = 1 := by
      have hnonneg : 0 ≤ r k := hr_nonneg k
      calc
        ‖u k‖ = ‖r k‖ * ‖x k‖ := norm_smul _ _
        _ = r k * ‖x k‖ := by
              simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        _ = (1 / ‖x k‖) * ‖x k‖ := by simp [r]
        _ = 1 := by field_simp [hnorm_ne]
    simp [hnorm]
  have hsphere : IsCompact (sphere (0 : EuclideanSpace Real (Fin n)) (1 : ℝ)) :=
    isCompact_sphere (0 : EuclideanSpace Real (Fin n)) (1 : ℝ)
  obtain ⟨y, hy_mem, φ, hφmono, hφtendsto⟩ := hsphere.tendsto_subseq hu_mem
  have hy_norm : ‖y‖ = 1 := by
    have hy_mem' := hy_mem
    simp at hy_mem'
    exact hy_mem'
  have hy0 : y ≠ 0 := by
    have : ‖y‖ ≠ 0 := by
      simp [hy_norm]
    exact (norm_ne_zero_iff).1 this
  have hy_recession : y ∈ Set.recessionCone C := by
    have hseq :
        ∃ (x' : ℕ → EuclideanSpace Real (Fin n)) (r' : ℕ → ℝ),
          (∀ n, x' n ∈ C) ∧ Antitone r' ∧
            Filter.Tendsto r' Filter.atTop (𝓝 (0 : ℝ)) ∧
              Filter.Tendsto (fun n => r' n • x' n) Filter.atTop (𝓝 y) := by
      refine ⟨fun n => x (φ n), fun n => r (φ n), ?_, ?_, ?_, ?_⟩
      · intro n
        exact hxC (φ n)
      · exact hr_antitone.comp_monotone hφmono.monotone
      · exact hr_tendsto.comp hφmono.tendsto_atTop
      · simpa [u, Function.comp] using hφtendsto
    exact seq_limits_subset_recessionCone (C := C) hCne hCclosed hCconv hseq
  exact ⟨y, hy0, hy_recession⟩

/-- Theorem 8.4. A non-empty closed convex set `C` in `ℝ^n` is bounded if and only if its
recession cone `0^+ C` consists of the zero vector alone. -/
theorem bounded_iff_recessionCone_eq_singleton_zero {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex Real C) :
    Bornology.IsBounded C ↔ Set.recessionCone C = {0} := by
  constructor
  · intro hCbdd
    have hsubset :
        Set.recessionCone C ⊆ {0} :=
      recessionCone_subset_singleton_of_bounded (C := C) hCne hCbdd
    have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
      intro x hx t ht
      simpa using hx
    ext y
    constructor
    · intro hy
      exact hsubset hy
    · intro hy
      have : y = 0 := by simpa using hy
      subst this
      exact hzero
  · intro hrc
    by_contra hCbdd
    obtain ⟨y, hy0, hy_mem⟩ :=
      exists_nonzero_mem_recessionCone_of_unbounded (C := C) hCne hCclosed hCconv hCbdd
    have : y ∈ ({0} : Set (EuclideanSpace Real (Fin n))) := by
      simpa [hrc] using hy_mem
    have : y = 0 := by simpa using this
    exact hy0 this

/-- Recession cone of a nonempty intersection of two closed convex sets. -/
lemma recessionCone_inter_eq {n : Nat}
    {A B : Set (EuclideanSpace Real (Fin n))}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hAconv : Convex Real A) (hBconv : Convex Real B)
    (hABne : (A ∩ B).Nonempty) :
    Set.recessionCone (A ∩ B) = Set.recessionCone A ∩ Set.recessionCone B := by
  let C : Bool → Set (EuclideanSpace Real (Fin n)) := fun b => if b then A else B
  have hCclosed : ∀ b, IsClosed (C b) := by
    intro b
    cases b <;> simp [C, hAclosed, hBclosed]
  have hCconv : ∀ b, Convex Real (C b) := by
    intro b
    cases b <;> simp [C, hAconv, hBconv]
  have hCne : (⋂ b, C b).Nonempty := by
    rcases hABne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hx' : ∀ b, x ∈ C b := by
      intro b
      cases b with
      | false =>
          simpa [C] using hx.2
      | true =>
          simpa [C] using hx.1
    simpa using hx'
  have hInter : (⋂ b, C b) = A ∩ B := by
    ext x
    constructor
    · intro hx
      have hx' : ∀ b, x ∈ C b := by simpa using hx
      have hxA : x ∈ C true := hx' true
      have hxB : x ∈ C false := hx' false
      have hxA' : x ∈ A := by simpa [C] using hxA
      have hxB' : x ∈ B := by simpa [C] using hxB
      exact ⟨hxA', hxB'⟩
    · intro hx
      have hx' : ∀ b, x ∈ C b := by
        intro b
        rcases hx with ⟨hxA, hxB⟩
        cases b with
        | false =>
            simpa [C] using hxB
        | true =>
            simpa [C] using hxA
      simpa using hx'
  have hInterRec :
      (⋂ b, Set.recessionCone (C b)) =
        Set.recessionCone A ∩ Set.recessionCone B := by
    ext x
    constructor
    · intro hx
      have hx' : ∀ b, x ∈ Set.recessionCone (C b) := by simpa using hx
      have hxA : x ∈ Set.recessionCone (C true) := hx' true
      have hxB : x ∈ Set.recessionCone (C false) := hx' false
      have hxA' : x ∈ Set.recessionCone A := by simpa [C] using hxA
      have hxB' : x ∈ Set.recessionCone B := by simpa [C] using hxB
      exact ⟨hxA', hxB'⟩
    · intro hx
      have hx' : ∀ b, x ∈ Set.recessionCone (C b) := by
        intro b
        rcases hx with ⟨hxA, hxB⟩
        cases b with
        | false =>
            simpa [C] using hxB
        | true =>
            simpa [C] using hxA
      simpa using hx'
  calc
    Set.recessionCone (A ∩ B) = Set.recessionCone (⋂ b, C b) := by
      simp [hInter]
    _ = ⋂ b, Set.recessionCone (C b) := by
      exact recessionCone_iInter_eq_iInter (C := C) hCclosed hCconv hCne
    _ = Set.recessionCone A ∩ Set.recessionCone B := by
      simp [hInterRec]

/-- Parallel nonempty affine subspaces have the same recession cone. -/
lemma recessionCone_affine_parallel_eq {n : Nat}
    {M M' : AffineSubspace Real (EuclideanSpace Real (Fin n))}
    (hM : (M : Set (EuclideanSpace Real (Fin n))).Nonempty)
    (hM' : (M' : Set (EuclideanSpace Real (Fin n))).Nonempty)
    (hparallel : M'.direction = M.direction) :
    Set.recessionCone (M' : Set (EuclideanSpace Real (Fin n))) =
      Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) := by
  calc
    Set.recessionCone (M' : Set (EuclideanSpace Real (Fin n))) =
        (M'.direction : Set (EuclideanSpace Real (Fin n))) := by
          simpa using
            (recessionCone_affineSubspace_eq_direction (M := M') hM'
              (L := M'.direction) rfl)
    _ = (M.direction : Set (EuclideanSpace Real (Fin n))) := by
          simp [hparallel]
    _ = Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) := by
          symm
          simpa using
            (recessionCone_affineSubspace_eq_direction (M := M) hM
              (L := M.direction) rfl)

/-- An empty intersection is bounded. -/
lemma bounded_empty_intersection {n : Nat} {A B : Set (EuclideanSpace Real (Fin n))}
    (h : ¬ (A ∩ B).Nonempty) : Bornology.IsBounded (A ∩ B) := by
  have hEmpty : (A ∩ B) = ∅ := (Set.not_nonempty_iff_eq_empty).1 h
  simp [hEmpty]

/-- Boundedness transfer via recession cones for parallel affine subspaces. -/
lemma boundedness_via_recessionCone_inter {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCclosed : IsClosed C) (hCconv : Convex Real C)
    {M M' : AffineSubspace Real (EuclideanSpace Real (Fin n))}
    (hMCne : ((M : Set (EuclideanSpace Real (Fin n))) ∩ C).Nonempty)
    (hMCbdd : Bornology.IsBounded ((M : Set (EuclideanSpace Real (Fin n))) ∩ C))
    (hM'Cne : ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C).Nonempty)
    (hparallel : M'.direction = M.direction) :
    Set.recessionCone ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) = {0} := by
  have hMne : (M : Set (EuclideanSpace Real (Fin n))).Nonempty := by
    rcases hMCne with ⟨x, hx⟩
    exact ⟨x, hx.1⟩
  have hM'ne : (M' : Set (EuclideanSpace Real (Fin n))).Nonempty := by
    rcases hM'Cne with ⟨x, hx⟩
    exact ⟨x, hx.1⟩
  have hMclosed : IsClosed (M : Set (EuclideanSpace Real (Fin n))) := by
    simpa using (AffineSubspace.closed_of_finiteDimensional (s := M))
  have hM'closed : IsClosed (M' : Set (EuclideanSpace Real (Fin n))) := by
    simpa using (AffineSubspace.closed_of_finiteDimensional (s := M'))
  have hMconv : Convex Real (M : Set (EuclideanSpace Real (Fin n))) := M.convex
  have hM'conv : Convex Real (M' : Set (EuclideanSpace Real (Fin n))) := M'.convex
  have hMCclosed : IsClosed ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) :=
    hMclosed.inter hCclosed
  have hMCconv : Convex Real ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) :=
    hMconv.inter hCconv
  have hMCrec :
      Set.recessionCone ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) = {0} :=
    (bounded_iff_recessionCone_eq_singleton_zero
        (C := (M : Set (EuclideanSpace Real (Fin n))) ∩ C) hMCne hMCclosed hMCconv).1 hMCbdd
  have hM'Crec :
      Set.recessionCone ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) =
        Set.recessionCone ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) := by
    have hInterM' :
        Set.recessionCone ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) =
          Set.recessionCone (M' : Set (EuclideanSpace Real (Fin n))) ∩
            Set.recessionCone C :=
      recessionCone_inter_eq (A := (M' : Set (EuclideanSpace Real (Fin n)))) (B := C)
        hM'closed hCclosed hM'conv hCconv hM'Cne
    have hInterM :
        Set.recessionCone ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) =
          Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) ∩
            Set.recessionCone C :=
      recessionCone_inter_eq (A := (M : Set (EuclideanSpace Real (Fin n)))) (B := C)
        hMclosed hCclosed hMconv hCconv hMCne
    calc
      Set.recessionCone ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) =
          Set.recessionCone (M' : Set (EuclideanSpace Real (Fin n))) ∩
            Set.recessionCone C := hInterM'
      _ = Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) ∩
            Set.recessionCone C := by
            have hparallel' :
                Set.recessionCone (M' : Set (EuclideanSpace Real (Fin n))) =
                  Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) :=
              recessionCone_affine_parallel_eq (M := M) (M' := M') hMne hM'ne hparallel
            simp [hparallel']
      _ = Set.recessionCone ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) := by
            symm
            exact hInterM
  simpa [hMCrec] using hM'Crec

/-- Corollary 8.4.1. Let `C` be a closed convex set, and let `M` be an affine set such that
`M ∩ C` is non-empty and bounded. Then `M' ∩ C` is bounded for every affine set `M'` parallel
to `M`. -/
theorem bounded_inter_of_parallel_affine {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n)))
    (hMCne : ((M : Set (EuclideanSpace Real (Fin n))) ∩ C).Nonempty)
    (hMCbdd : Bornology.IsBounded ((M : Set (EuclideanSpace Real (Fin n))) ∩ C)) :
    ∀ (M' : AffineSubspace Real (EuclideanSpace Real (Fin n))),
      M'.direction = M.direction →
      Bornology.IsBounded ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) := by
  intro M' hparallel
  by_cases hM'Cne : ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C).Nonempty
  · have hM'Crec :
        Set.recessionCone ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) = {0} :=
      boundedness_via_recessionCone_inter (C := C) hCclosed hCconv
        (M := M) (M' := M') hMCne hMCbdd hM'Cne hparallel
    have hM'closed : IsClosed (M' : Set (EuclideanSpace Real (Fin n))) := by
      simpa using (AffineSubspace.closed_of_finiteDimensional (s := M'))
    have hM'conv : Convex Real (M' : Set (EuclideanSpace Real (Fin n))) := M'.convex
    have hM'Cclosed : IsClosed ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) :=
      hM'closed.inter hCclosed
    have hM'Cconv : Convex Real ((M' : Set (EuclideanSpace Real (Fin n))) ∩ C) :=
      hM'conv.inter hCconv
    exact
      (bounded_iff_recessionCone_eq_singleton_zero
          (C := (M' : Set (EuclideanSpace Real (Fin n))) ∩ C) hM'Cne hM'Cclosed
          hM'Cconv).2 hM'Crec
  · exact bounded_empty_intersection (A := (M' : Set (EuclideanSpace Real (Fin n)))) (B := C)
      hM'Cne

end Section08
end Chap02
