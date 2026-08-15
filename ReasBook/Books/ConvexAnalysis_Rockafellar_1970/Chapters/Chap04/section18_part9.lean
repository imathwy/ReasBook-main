/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section18_part8

open scoped Pointwise

section Chap04
section Section18

noncomputable section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

set_option maxHeartbeats 600000

/-- Corollary 18.5.1. Let `C` be a closed bounded convex set. Then `C` is the convex hull of its
extreme points. -/
theorem closed_bounded_convex_eq_convexHull_extremePoints_part9 {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C)
    (hCconv : Convex ℝ C) :
    C = convexHull ℝ (C.extremePoints ℝ) := by
  classical
  by_cases hCne : C.Nonempty
  ·
    have hrec :
        Set.recessionCone C = ({0} : Set (Fin n → ℝ)) :=
      recessionCone_eq_singleton_zero_of_closed_bounded_convex_fin (n := n) (C := C) hCne hCclosed
        hCconv hCbounded
    have hNoLines :
        ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C :=
      noLines_of_recessionCone_eq_singleton_zero (n := n) (C := C) hrec
    have hS1 :
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} = (∅ : Set (Fin n → ℝ)) :=
      extremeDirections_eq_empty_of_recessionCone_eq_singleton_zero (n := n) (C := C) hCclosed hrec
    have hEq :=
      closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections (n := n) (C := C) hCclosed
        hCconv hNoLines
    calc
      C =
          mixedConvexHull (n := n) (C.extremePoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := hEq
      _ = mixedConvexHull (n := n) (C.extremePoints ℝ) (∅ : Set (Fin n → ℝ)) := by
            simp [hS1]
      _ = convexHull ℝ (C.extremePoints ℝ) := by
            simpa using
              (mixedConvexHull_empty_directions_eq_convexHull (n := n) (C.extremePoints ℝ))
  ·
    have hCempty : C = (∅ : Set (Fin n → ℝ)) :=
      Set.not_nonempty_iff_eq_empty.1 hCne
    simp [hCempty]

/-- Extreme points are monotone with respect to set inclusion. -/
lemma theorem18_6_isExtremePoint_mono {n : ℕ} {C D : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hDC : D ⊆ C) (hxD : x ∈ D) (hxext : IsExtremePoint (𝕜 := ℝ) C x) :
    IsExtremePoint (𝕜 := ℝ) D x := by
  refine ⟨hxD, ?_⟩
  intro y z hy hz hseg
  exact hxext.2 (hDC hy) (hDC hz) hseg

/-- `conv (closure (exposedPoints))` is closed and contained in the set. -/
lemma theorem18_6_isClosed_conv_closure_exposedPoints {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    IsClosed (conv (closure (C.exposedPoints ℝ))) ∧
      conv (closure (C.exposedPoints ℝ)) ⊆ C := by
  have hSsub : C.exposedPoints ℝ ⊆ C := exposedPoints_subset (A := C) (𝕜 := ℝ)
  have hSclosed_sub : closure (C.exposedPoints ℝ) ⊆ C :=
    (IsClosed.closure_subset_iff (t := C) hCclosed).2 hSsub
  have hSbdd : Bornology.IsBounded (C.exposedPoints ℝ) := hCbounded.subset hSsub
  have hSbdd' : Bornology.IsBounded (closure (C.exposedPoints ℝ)) := hSbdd.closure
  have hclosed : IsClosed (conv (closure (C.exposedPoints ℝ))) :=
    (isClosed_and_isBounded_conv_of_isClosed_and_isBounded (n := n)
      (S := closure (C.exposedPoints ℝ)) isClosed_closure hSbdd').1
  have hsub : conv (closure (C.exposedPoints ℝ)) ⊆ C := by
    simpa [conv] using (convexHull_min hSclosed_sub hCconv)
  exact ⟨hclosed, hsub⟩

/-- An extreme point outside the closure of exposed points is not in `conv (closure ...)`. -/
lemma theorem18_6_not_mem_C0_of_extreme_not_mem_closure_exposedPoints {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    {x : Fin n → ℝ} (hxext : IsExtremePoint (𝕜 := ℝ) C x)
    (hxnot : x ∉ closure (C.exposedPoints ℝ)) :
    x ∉ conv (closure (C.exposedPoints ℝ)) := by
  intro hxC0
  have hC0sub : conv (closure (C.exposedPoints ℝ)) ⊆ C :=
    (theorem18_6_isClosed_conv_closure_exposedPoints (n := n) (C := C) hCclosed hCbounded
      hCconv).2
  have hxextC0 : IsExtremePoint (𝕜 := ℝ) (conv (closure (C.exposedPoints ℝ))) x :=
    theorem18_6_isExtremePoint_mono (C := C) (D := conv (closure (C.exposedPoints ℝ)))
      hC0sub hxC0 hxext
  have hxext' :
      IsExtremePoint (𝕜 := ℝ)
        (mixedConvexHull (n := n) (closure (C.exposedPoints ℝ)) (∅ : Set (Fin n → ℝ))) x := by
    simpa [conv, mixedConvexHull_empty_directions_eq_convexHull] using hxextC0
  have hxmem :
      x ∈ closure (C.exposedPoints ℝ) :=
    mem_points_of_isExtremePoint_mixedConvexHull (n := n) (S₀ := closure (C.exposedPoints ℝ))
      (S₁ := (∅ : Set (Fin n → ℝ))) (x := x) hxext'
  exact hxnot hxmem

/-- Given a compact convex set `C`, a closed convex subset `D`, and a point `x ∈ C \ D`, there is
a nonempty exposed face of `C` disjoint from `D`. -/
lemma theorem18_6_exists_exposedFace_disjoint_closedConvex {n : ℕ}
    {C D : Set (Fin n → ℝ)} (hCcompact : IsCompact C) (hDclosed : IsClosed D)
    (hDconv : Convex ℝ D) {x : Fin n → ℝ} (hxC : x ∈ C) (hxnotD : x ∉ D) :
    ∃ (l : (Fin n → ℝ) →L[ℝ] ℝ),
      (l.toExposed C).Nonempty ∧ IsExposed ℝ C (l.toExposed C) ∧ (l.toExposed C) ⊆ C \ D := by
  obtain ⟨l, r, hlD, hrx⟩ :=
    geometric_hahn_banach_closed_point (s := D) hDconv hDclosed hxnotD
  obtain ⟨z, hzC, hzmax⟩ := hCcompact.exists_isMaxOn ⟨x, hxC⟩ l.continuous.continuousOn
  have hzExp : z ∈ l.toExposed C := by
    refine ⟨hzC, ?_⟩
    exact (isMaxOn_iff.1 hzmax)
  refine ⟨l, ⟨z, hzExp⟩, ?_, ?_⟩
  · simpa using (ContinuousLinearMap.toExposed.isExposed (l := l) (A := C))
  · intro y hy
    have hyC : y ∈ C := hy.1
    have hxy : l x ≤ l y := hy.2 x hxC
    have hrlty : r < l y := lt_of_lt_of_le hrx hxy
    refine ⟨hyC, ?_⟩
    intro hyD
    have hlt : l y < r := hlD y hyD
    exact (lt_irrefl _ (lt_trans hlt hrlty))

/-- An extreme point outside the closure of exposed points yields a disjoint exposed face. -/
lemma theorem18_6_exists_exposedFace_disjoint_C0 {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    {x : Fin n → ℝ} (hxext : IsExtremePoint (𝕜 := ℝ) C x)
    (hxnot : x ∉ closure (C.exposedPoints ℝ)) :
    ∃ (l : (Fin n → ℝ) →L[ℝ] ℝ),
      (l.toExposed C).Nonempty ∧ IsExposed ℝ C (l.toExposed C) ∧
        (l.toExposed C) ⊆ C \ conv (closure (C.exposedPoints ℝ)) := by
  classical
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  have hC0closed : IsClosed (conv (closure (C.exposedPoints ℝ))) :=
    (theorem18_6_isClosed_conv_closure_exposedPoints (n := n) (C := C) hCclosed hCbounded
      hCconv).1
  have hxnotC0 :
      x ∉ conv (closure (C.exposedPoints ℝ)) :=
    theorem18_6_not_mem_C0_of_extreme_not_mem_closure_exposedPoints (n := n) (C := C) hCclosed
      hCbounded hCconv (x := x) hxext hxnot
  have hC0conv : Convex ℝ (conv (closure (C.exposedPoints ℝ))) := by
    simpa [conv] using
      (convex_convexHull (𝕜 := ℝ) (s := closure (C.exposedPoints ℝ)))
  exact
    theorem18_6_exists_exposedFace_disjoint_closedConvex (n := n) (C := C)
      (D := conv (closure (C.exposedPoints ℝ))) hCcompact hC0closed hC0conv (x := x) hxext.1
      hxnotC0

/-- A nonempty exposed subset is of the form `l.toExposed C`. -/
lemma theorem18_6_exposed_eq_toExposed {n : ℕ} {C : Set (Fin n → ℝ)} {F : Set (Fin n → ℝ)}
    (hFexposed : IsExposed ℝ C F) (hFne : F.Nonempty) :
    ∃ l : (Fin n → ℝ) →L[ℝ] ℝ, F = l.toExposed C := by
  rcases hFexposed hFne with ⟨l, rfl⟩
  exact ⟨l, rfl⟩

/-- An exposed singleton yields an exposed point. -/
lemma theorem18_6_exposedPoint_of_exposed_singleton {n : ℕ} {C : Set (Fin n → ℝ)}
    {p : Fin n → ℝ} (hFexposed : IsExposed ℝ C ({p} : Set (Fin n → ℝ))) :
    p ∈ C.exposedPoints ℝ := by
  exact (mem_exposedPoints_iff_exposed_singleton (A := C) (x := p)).2 hFexposed

/-- The vector span of a maximizer set lies in the kernel of the functional. -/
lemma theorem18_6_vectorSpan_toExposed_le_ker {n : ℕ} {A : Set (Fin n → ℝ)}
    (g : (Fin n → ℝ) →L[ℝ] ℝ) :
    vectorSpan ℝ (g.toExposed A) ≤ LinearMap.ker g.toLinearMap := by
  classical
  refine Submodule.span_le.2 ?_
  intro v hv
  rcases hv with ⟨x, hx, y, hy, rfl⟩
  have hxy : g x = g y := by
    apply le_antisymm
    · exact hy.2 x hx.1
    · exact hx.2 y hy.1
  change g (x -ᵥ y) = 0
  have hsub : g (x - y) = 0 := by
    simp [g.map_sub, hxy]
  simpa [vsub_eq_sub] using hsub

/-- If `vectorSpan` has dimension zero, the set is a singleton. -/
lemma theorem18_6_singleton_of_finrank_vectorSpan_eq_zero {n : ℕ} {F : Set (Fin n → ℝ)}
    (hFne : F.Nonempty) (hfin : _root_.Module.finrank ℝ (vectorSpan ℝ F) = 0) :
    ∃ p, F = {p} := by
  classical
  have hbot : vectorSpan ℝ F = ⊥ := (Submodule.finrank_eq_zero.mp hfin)
  have hsub : F.Subsingleton := (vectorSpan_eq_bot_iff_subsingleton (k := ℝ) (s := F)).1 hbot
  rcases hFne with ⟨p, hp⟩
  refine ⟨p, Set.eq_singleton_iff_unique_mem.2 ?_⟩
  refine ⟨hp, ?_⟩
  intro q hq
  exact hsub hq hp

/-- Relative to a fixed maximizer `z`, membership in `l.toExposed C` is equivalent to equality of
functional values. -/
lemma theorem18_6_mem_toExposed_iff_eq_of_mem {n : ℕ} {C : Set (Fin n → ℝ)}
    {l : (Fin n → ℝ) →L[ℝ] ℝ} {z x : Fin n → ℝ} (hz : z ∈ l.toExposed C) (hxC : x ∈ C) :
    x ∈ l.toExposed C ↔ l x = l z := by
  constructor
  · intro hx
    exact le_antisymm (hz.2 x hx.1) (hx.2 z hz.1)
  · intro hEq
    refine ⟨hxC, ?_⟩
    intro y hyC
    have hyz : l y ≤ l z := hz.2 y hyC
    simpa [hEq] using hyz

/-- Relative to a fixed maximizer `z`, non-membership in `l.toExposed C` is equivalent to strict
functional decrease. -/
lemma theorem18_6_not_mem_toExposed_iff_lt_of_mem {n : ℕ} {C : Set (Fin n → ℝ)}
    {l : (Fin n → ℝ) →L[ℝ] ℝ} {z x : Fin n → ℝ} (hz : z ∈ l.toExposed C) (hxC : x ∈ C) :
    x ∉ l.toExposed C ↔ l x < l z := by
  constructor
  · intro hxnot
    have hxle : l x ≤ l z := hz.2 x hxC
    have hne : l x ≠ l z := by
      intro hEq
      exact hxnot ((theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z)
        (x := x) hz hxC).2 hEq)
    exact lt_of_le_of_ne hxle hne
  · intro hlt hx
    have hEq :
        l x = l z :=
      (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z)
        (x := x) hz hxC).1 hx
    have : l z < l z := by linarith [hlt, hEq]
    exact (lt_irrefl _ this)

/-- Any nonempty `toExposed` set is a level set in `C` at its maximizing value. -/
lemma theorem18_6_toExposed_eq_levelset_of_mem {n : ℕ} {C : Set (Fin n → ℝ)}
    {l : (Fin n → ℝ) →L[ℝ] ℝ} {z : Fin n → ℝ} (hz : z ∈ l.toExposed C) :
    l.toExposed C = {x ∈ C | l x = l z} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z)
      (x := x) hz hx.1).1 hx⟩
  · intro hx
    exact (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z)
      (x := x) hz hx.1).2 hx.2

/-- Uniform-gap perturbation: if `l` has a positive gap away from `l.toExposed C` and `g` is
bounded on `C`, then for small positive `ε`, every maximizer of `l + ε g` lies in `l.toExposed C`.
-/
lemma theorem18_6_toExposed_subset_of_small_perturbation_of_uniform_gap {n : ℕ}
    {C : Set (Fin n → ℝ)} {l g : (Fin n → ℝ) →L[ℝ] ℝ} {z : Fin n → ℝ}
    (hz : z ∈ l.toExposed C) (hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, |g x| ≤ B)
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C \ l.toExposed C, l y ≤ l z - δ) :
    ∃ ε : ℝ, 0 < ε ∧ (l + ε • g).toExposed C ⊆ l.toExposed C := by
  rcases hB with ⟨B, hBnonneg, hBbound⟩
  rcases hgap with ⟨δ, hδpos, hgap'⟩
  let ε : ℝ := δ / (4 * (B + 1))
  have hεpos : 0 < ε := by
    have hdenpos : 0 < 4 * (B + 1) := by nlinarith [hBnonneg]
    exact div_pos hδpos hdenpos
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hεB_le : ε * B ≤ δ / 4 := by
    have hB_le : B ≤ B + 1 := by linarith
    have h1 : ε * B ≤ ε * (B + 1) := mul_le_mul_of_nonneg_left hB_le hεnonneg
    have hB1ne : (B + 1) ≠ 0 := by linarith [hBnonneg]
    have hεB1 : ε * (B + 1) = δ / 4 := by
      dsimp [ε]
      field_simp [hB1ne]
    simpa [hεB1] using h1
  refine ⟨ε, hεpos, ?_⟩
  intro x hx
  by_contra hxnot
  have hxC : x ∈ C := hx.1
  have hxCF : x ∈ C \ l.toExposed C := ⟨hxC, hxnot⟩
  have hxl : l x ≤ l z - δ := hgap' x hxCF
  have hxgbound : |g x| ≤ B := hBbound x hxC
  have hxg_le : g x ≤ B := (abs_le.mp hxgbound).2
  have hxval : (l + ε • g) x ≤ l z - δ + ε * B := by
    have hmul : ε * g x ≤ ε * B := mul_le_mul_of_nonneg_left hxg_le hεnonneg
    have hsum : l x + ε * g x ≤ (l z - δ) + ε * B := add_le_add hxl hmul
    simpa using hsum
  have hzgbound : |g z| ≤ B := hBbound z hz.1
  have hzg_ge : -B ≤ g z := (abs_le.mp hzgbound).1
  have hmulz : -(ε * B) ≤ ε * g z := by
    have hmul := mul_le_mul_of_nonneg_left hzg_ge hεnonneg
    simpa [mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hzval : l z - ε * B ≤ (l + ε • g) z := by
    have hsum : l z - ε * B ≤ l z + ε * g z := by
      have hsum' := add_le_add_left hmulz (l z)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
    simpa using hsum
  have hxmax : (l + ε • g) z ≤ (l + ε • g) x := hx.2 z hz.1
  have hδhalf : δ / 2 ≤ δ - 2 * (ε * B) := by
    linarith [hεB_le]
  have hstrict_aux : l z - δ + ε * B < l z - ε * B := by
    have : 0 < δ - 2 * (ε * B) := by
      have hδhalf' : 0 < δ / 2 := by nlinarith [hδpos]
      exact lt_of_lt_of_le hδhalf' hδhalf
    linarith
  have hchain : l z - ε * B ≤ l z - δ + ε * B := by
    exact le_trans hzval (le_trans hxmax hxval)
  exact (not_le_of_gt hstrict_aux) hchain

/-- On any closed subset of `C` disjoint from `l.toExposed C`, the exposing functional is
uniformly below its maximal value by a positive gap. -/
lemma theorem18_6_exists_uniform_gap_on_closed_disjoint_subset {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCcompact : IsCompact C) {l : (Fin n → ℝ) →L[ℝ] ℝ}
    {z : Fin n → ℝ} (hz : z ∈ l.toExposed C) {K : Set (Fin n → ℝ)} (hKclosed : IsClosed K)
    (hKsub : K ⊆ C) (hKdisj : Disjoint K (l.toExposed C)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ K, l y ≤ l z - δ := by
  by_cases hKne : K.Nonempty
  · have hKcompact : IsCompact K := hCcompact.of_isClosed_subset hKclosed hKsub
    let f : (Fin n → ℝ) → ℝ := fun y => l z - l y
    obtain ⟨y0, hy0K, hy0min⟩ :=
      hKcompact.exists_isMinOn hKne ((continuous_const.sub l.continuous).continuousOn)
    have hKdisj' : ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → x ∈ l.toExposed C → False :=
      Set.disjoint_left.1 hKdisj
    have hy0notF : y0 ∉ l.toExposed C := fun hy0F => hKdisj' hy0K hy0F
    have hy0lt : l y0 < l z :=
      (theorem18_6_not_mem_toExposed_iff_lt_of_mem (n := n) (C := C) (l := l) (z := z) (x := y0)
        hz (hKsub hy0K)).1 hy0notF
    let δ : ℝ := l z - l y0
    have hδpos : 0 < δ := by
      dsimp [δ]
      linarith [hy0lt]
    refine ⟨δ, hδpos, ?_⟩
    intro y hyK
    have hymin : f y0 ≤ f y := (isMinOn_iff.mp hy0min) y hyK
    have hyy0 : l y ≤ l y0 := by
      dsimp [f] at hymin
      linarith
    calc
      l y ≤ l y0 := hyy0
      _ = l z - δ := by simp [δ]
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    refine ⟨1, by norm_num, ?_⟩
    intro y hyK
    exfalso
    simp [hKempty] at hyK

/-- Compact lexicographic perturbation (singleton target): if `z` is the unique `g`-maximizer on
`l.toExposed C` and `l` has a uniform positive gap away from `l.toExposed C`, then for a small
positive perturbation `l + ε g`, the exposed set on `C` is exactly `{z}`. -/
lemma theorem18_6_compact_lexicographic_perturbation_singleton {n : ℕ}
    {C : Set (Fin n → ℝ)} {l g : (Fin n → ℝ) →L[ℝ] ℝ} {z : Fin n → ℝ}
    (hz : z ∈ l.toExposed C) (huniq : g.toExposed (l.toExposed C) = ({z} : Set (Fin n → ℝ)))
    (hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, |g x| ≤ B)
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C \ l.toExposed C, l y ≤ l z - δ) :
    ∃ ε : ℝ, 0 < ε ∧ (l + ε • g).toExposed C = ({z} : Set (Fin n → ℝ)) := by
  rcases hB with ⟨B, hBnonneg, hBbound⟩
  rcases hgap with ⟨δ, hδpos, hgap'⟩
  let ε : ℝ := δ / (4 * (B + 1))
  have hεpos : 0 < ε := by
    have hdenpos : 0 < 4 * (B + 1) := by nlinarith [hBnonneg]
    exact div_pos hδpos hdenpos
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hεB_le : ε * B ≤ δ / 4 := by
    have hB_le : B ≤ B + 1 := by linarith
    have h1 : ε * B ≤ ε * (B + 1) := mul_le_mul_of_nonneg_left hB_le hεnonneg
    have hB1ne : (B + 1) ≠ 0 := by linarith [hBnonneg]
    have hεB1 : ε * (B + 1) = δ / 4 := by
      dsimp [ε]
      field_simp [hB1ne]
    simpa [hεB1] using h1
  have hzG : z ∈ g.toExposed (l.toExposed C) := by
    simp [huniq]
  have hzPert : z ∈ (l + ε • g).toExposed C := by
    refine ⟨hz.1, ?_⟩
    intro y hyC
    by_cases hyF : y ∈ l.toExposed C
    · have hlyz :
        l y = l z :=
        (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z) (x := y) hz
          hyC).1 hyF
      have hyg : g y ≤ g z := hzG.2 y hyF
      have hmul : ε * g y ≤ ε * g z := mul_le_mul_of_nonneg_left hyg hεnonneg
      have hsum : l y + ε * g y ≤ l z + ε * g z := add_le_add (le_of_eq hlyz) hmul
      simpa using hsum
    · have hyCF : y ∈ C \ l.toExposed C := ⟨hyC, hyF⟩
      have hyl : l y ≤ l z - δ := hgap' y hyCF
      have hygbound : |g y| ≤ B := hBbound y hyC
      have hyg_le : g y ≤ B := (abs_le.mp hygbound).2
      have hyval : (l + ε • g) y ≤ l z - δ + ε * B := by
        have hmul : ε * g y ≤ ε * B := mul_le_mul_of_nonneg_left hyg_le hεnonneg
        have hsum : l y + ε * g y ≤ (l z - δ) + ε * B := add_le_add hyl hmul
        simpa using hsum
      have hzgbound : |g z| ≤ B := hBbound z hz.1
      have hzg_ge : -B ≤ g z := (abs_le.mp hzgbound).1
      have hmulz : -(ε * B) ≤ ε * g z := by
        have hmul := mul_le_mul_of_nonneg_left hzg_ge hεnonneg
        simpa [mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hzval : l z - ε * B ≤ (l + ε • g) z := by
        have hsum : l z - ε * B ≤ l z + ε * g z := by
          have hsum' := add_le_add_left hmulz (l z)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
        simpa using hsum
      have hδhalf : δ / 2 ≤ δ - 2 * (ε * B) := by
        linarith [hεB_le]
      have hstrict_aux : l z - δ + ε * B < l z - ε * B := by
        have : 0 < δ - 2 * (ε * B) := by
          have hδhalf' : 0 < δ / 2 := by nlinarith [hδpos]
          exact lt_of_lt_of_le hδhalf' hδhalf
        linarith
      have hylt : (l + ε • g) y < (l + ε • g) z := by
        exact lt_of_le_of_lt hyval (lt_of_lt_of_le hstrict_aux hzval)
      exact le_of_lt hylt
  have hsubset_singleton : (l + ε • g).toExposed C ⊆ ({z} : Set (Fin n → ℝ)) := by
    intro x hx
    have hxC : x ∈ C := hx.1
    by_cases hxF : x ∈ l.toExposed C
    · have hxle : (l + ε • g) x ≤ (l + ε • g) z := hzPert.2 x hxC
      have hxge : (l + ε • g) z ≤ (l + ε • g) x := hx.2 z hz.1
      have hlxz :
          l x = l z :=
        (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z) (x := x) hz
          hxC).1 hxF
      have hzgx_mul : ε * g z ≤ ε * g x := by
        have hxge' : l z + ε * g z ≤ l z + ε * g x := by
          simpa [hlxz] using hxge
        linarith
      have hzgx : g z ≤ g x := by
        nlinarith [hzgx_mul, hεpos]
      have hxgz : g x ≤ g z := hzG.2 x hxF
      have hxG : x ∈ g.toExposed (l.toExposed C) := by
        refine ⟨hxF, ?_⟩
        intro w hwF
        have hwgz : g w ≤ g z := hzG.2 w hwF
        have hEqG : g x = g z := le_antisymm hxgz hzgx
        simpa [hEqG] using hwgz
      simpa [huniq] using hxG
    · exfalso
      have hxCF : x ∈ C \ l.toExposed C := ⟨hxC, hxF⟩
      have hxl : l x ≤ l z - δ := hgap' x hxCF
      have hxgbound : |g x| ≤ B := hBbound x hxC
      have hxg_le : g x ≤ B := (abs_le.mp hxgbound).2
      have hxval : (l + ε • g) x ≤ l z - δ + ε * B := by
        have hmul : ε * g x ≤ ε * B := mul_le_mul_of_nonneg_left hxg_le hεnonneg
        have hsum : l x + ε * g x ≤ (l z - δ) + ε * B := add_le_add hxl hmul
        simpa using hsum
      have hzgbound : |g z| ≤ B := hBbound z hz.1
      have hzg_ge : -B ≤ g z := (abs_le.mp hzgbound).1
      have hmulz : -(ε * B) ≤ ε * g z := by
        have hmul := mul_le_mul_of_nonneg_left hzg_ge hεnonneg
        simpa [mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hzval : l z - ε * B ≤ (l + ε • g) z := by
        have hsum : l z - ε * B ≤ l z + ε * g z := by
          have hsum' := add_le_add_left hmulz (l z)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
        simpa using hsum
      have hδhalf : δ / 2 ≤ δ - 2 * (ε * B) := by
        linarith [hεB_le]
      have hstrict_aux : l z - δ + ε * B < l z - ε * B := by
        have : 0 < δ - 2 * (ε * B) := by
          have hδhalf' : 0 < δ / 2 := by nlinarith [hδpos]
          exact lt_of_lt_of_le hδhalf' hδhalf
        linarith
      have hchain : l z - ε * B ≤ l z - δ + ε * B := by
        exact le_trans hzval (le_trans (hx.2 z hz.1) hxval)
      exact (not_le_of_gt hstrict_aux) hchain
  refine ⟨ε, hεpos, Set.Subset.antisymm hsubset_singleton ?_⟩
  intro x hx
  rcases Set.mem_singleton_iff.1 hx with rfl
  exact hzPert

/-- Quantitative lexicographic perturbation:
with a uniform gap away from `l.toExposed C` and a bound on `g` over `C`, a small perturbation
realizes exactly `g.toExposed (l.toExposed C)`. -/
lemma theorem18_6_compact_lexicographic_perturbation_toExposed_eq {n : ℕ}
    {C : Set (Fin n → ℝ)} {l g : (Fin n → ℝ) →L[ℝ] ℝ} {z : Fin n → ℝ}
    (hz : z ∈ l.toExposed C) (hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, |g x| ≤ B)
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C \ l.toExposed C, l y ≤ l z - δ) :
    ∃ ε : ℝ, 0 < ε ∧ (l + ε • g).toExposed C = g.toExposed (l.toExposed C) := by
  rcases hB with ⟨B, hBnonneg, hBbound⟩
  rcases hgap with ⟨δ, hδpos, hgap'⟩
  let ε : ℝ := δ / (4 * (B + 1))
  have hεpos : 0 < ε := by
    have hdenpos : 0 < 4 * (B + 1) := by nlinarith [hBnonneg]
    exact div_pos hδpos hdenpos
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hεB_le : ε * B ≤ δ / 4 := by
    have hB_le : B ≤ B + 1 := by linarith
    have h1 : ε * B ≤ ε * (B + 1) := mul_le_mul_of_nonneg_left hB_le hεnonneg
    have hB1ne : (B + 1) ≠ 0 := by linarith [hBnonneg]
    have hεB1 : ε * (B + 1) = δ / 4 := by
      dsimp [ε]
      field_simp [hB1ne]
    simpa [hεB1] using h1
  have hsubsetF : (l + ε • g).toExposed C ⊆ l.toExposed C := by
    intro x hx
    by_contra hxF
    have hxC : x ∈ C := hx.1
    have hxCF : x ∈ C \ l.toExposed C := ⟨hxC, hxF⟩
    have hxl : l x ≤ l z - δ := hgap' x hxCF
    have hxgbound : |g x| ≤ B := hBbound x hxC
    have hxg_le : g x ≤ B := (abs_le.mp hxgbound).2
    have hxval : (l + ε • g) x ≤ l z - δ + ε * B := by
      have hmul : ε * g x ≤ ε * B := mul_le_mul_of_nonneg_left hxg_le hεnonneg
      have hsum : l x + ε * g x ≤ (l z - δ) + ε * B := add_le_add hxl hmul
      simpa using hsum
    have hzgbound : |g z| ≤ B := hBbound z hz.1
    have hzg_ge : -B ≤ g z := (abs_le.mp hzgbound).1
    have hmulz : -(ε * B) ≤ ε * g z := by
      have hmul := mul_le_mul_of_nonneg_left hzg_ge hεnonneg
      simpa [mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hzval : l z - ε * B ≤ (l + ε • g) z := by
      have hsum : l z - ε * B ≤ l z + ε * g z := by
        have hsum' := add_le_add_left hmulz (l z)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
      simpa using hsum
    have hxmax : (l + ε • g) z ≤ (l + ε • g) x := hx.2 z hz.1
    have hδhalf : δ / 2 ≤ δ - 2 * (ε * B) := by
      linarith [hεB_le]
    have hstrict_aux : l z - δ + ε * B < l z - ε * B := by
      have : 0 < δ - 2 * (ε * B) := by
        have hδhalf' : 0 < δ / 2 := by nlinarith [hδpos]
        exact lt_of_lt_of_le hδhalf' hδhalf
      linarith
    have hchain : l z - ε * B ≤ l z - δ + ε * B := by
      exact le_trans hzval (le_trans hxmax hxval)
    exact (not_le_of_gt hstrict_aux) hchain
  refine ⟨ε, hεpos, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hxF : x ∈ l.toExposed C := hsubsetF hx
    refine ⟨hxF, ?_⟩
    intro y hyF
    have hyC : y ∈ C := hyF.1
    have hxy : (l + ε • g) y ≤ (l + ε • g) x := hx.2 y hyC
    have hlyz : l y = l z :=
      (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z) (x := y) hz
        hyC).1 hyF
    have hlxz : l x = l z :=
      (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z) (x := x) hz
        hxF.1).1 hxF
    have hlyx : l y = l x := by linarith
    have hxy' : l y + ε * g y ≤ l y + ε * g x := by
      simpa [hlyx] using hxy
    have hmul : ε * g y ≤ ε * g x := (add_le_add_iff_left (l y)).1 hxy'
    have hgyx : g y ≤ g x := by
      nlinarith [hmul, hεpos]
    exact hgyx
  · intro x hxG
    have hxF : x ∈ l.toExposed C := hxG.1
    have hxC : x ∈ C := hxF.1
    refine ⟨hxC, ?_⟩
    intro y hyC
    by_cases hyF : y ∈ l.toExposed C
    · have hgy : g y ≤ g x := hxG.2 y hyF
      have hmul : ε * g y ≤ ε * g x := mul_le_mul_of_nonneg_left hgy hεnonneg
      have hxy' : l y + ε * g y ≤ l y + ε * g x := by
        simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hmul (l y))
      have hlyz : l y = l z :=
        (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z) (x := y) hz
          hyC).1 hyF
      have hlxz : l x = l z :=
        (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z) (x := x) hz
          hxC).1 hxF
      have hlyx : l y = l x := by linarith
      have hxy : l y + ε * g y ≤ l x + ε * g x := by
        simpa [hlyx] using hxy'
      simpa using hxy
    · have hyCF : y ∈ C \ l.toExposed C := ⟨hyC, hyF⟩
      have hyl : l y ≤ l z - δ := hgap' y hyCF
      have hygbound : |g y| ≤ B := hBbound y hyC
      have hyg_le : g y ≤ B := (abs_le.mp hygbound).2
      have hyval : (l + ε • g) y ≤ l z - δ + ε * B := by
        have hmul : ε * g y ≤ ε * B := mul_le_mul_of_nonneg_left hyg_le hεnonneg
        have hsum : l y + ε * g y ≤ (l z - δ) + ε * B := add_le_add hyl hmul
        simpa using hsum
      have hxgbound : |g x| ≤ B := hBbound x hxC
      have hxg_ge : -B ≤ g x := (abs_le.mp hxgbound).1
      have hmulx : -(ε * B) ≤ ε * g x := by
        have hmul := mul_le_mul_of_nonneg_left hxg_ge hεnonneg
        simpa [mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hlxz : l x = l z :=
        (theorem18_6_mem_toExposed_iff_eq_of_mem (n := n) (C := C) (l := l) (z := z) (x := x) hz
          hxC).1 hxF
      have hxval : l z - ε * B ≤ (l + ε • g) x := by
        have hsum : l z - ε * B ≤ l z + ε * g x := by
          have hsum' := add_le_add_left hmulx (l z)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
        simpa [hlxz] using hsum
      have hδhalf : δ / 2 ≤ δ - 2 * (ε * B) := by
        linarith [hεB_le]
      have hstrict_aux : l z - δ + ε * B < l z - ε * B := by
        have : 0 < δ - 2 * (ε * B) := by
          have hδhalf' : 0 < δ / 2 := by nlinarith [hδpos]
          exact lt_of_lt_of_le hδhalf' hδhalf
        linarith
      have hgapx : l z - δ + ε * B < (l + ε • g) x := lt_of_lt_of_le hstrict_aux hxval
      have hylt : (l + ε • g) y < (l + ε • g) x := lt_of_le_of_lt hyval hgapx
      exact le_of_lt hylt

/-- A nonempty exposed face of a compact set contains an extreme point of the ambient set. -/
lemma theorem18_6_exposedFace_contains_extremePoint_fin {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) {F : Set (Fin n → ℝ)}
    (hFexposed : IsExposed ℝ C F) (hFne : F.Nonempty) :
    ∃ p ∈ F, p ∈ C.extremePoints ℝ := by
  have hFcompact : IsCompact F := hFexposed.isCompact hCcompact
  rcases hFcompact.extremePoints_nonempty hFne with ⟨p, hpFext⟩
  refine ⟨p, hpFext.1, ?_⟩
  exact hFexposed.isExtreme.extremePoints_subset_extremePoints hpFext

/-- Bridge-to-ambient step: once the compact lexicographic singleton data is available on an
exposed face `l.toExposed C`, the selected point is an exposed point of `C`. -/
lemma theorem18_6_exposedPoint_of_compact_lexicographic_bridge {n : ℕ}
    {C : Set (Fin n → ℝ)} {l g : (Fin n → ℝ) →L[ℝ] ℝ} {z : Fin n → ℝ}
    (hz : z ∈ l.toExposed C) (huniq : g.toExposed (l.toExposed C) = ({z} : Set (Fin n → ℝ)))
    (hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, |g x| ≤ B)
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C \ l.toExposed C, l y ≤ l z - δ) :
    z ∈ C.exposedPoints ℝ := by
  rcases
      theorem18_6_compact_lexicographic_perturbation_singleton
        (C := C) (l := l) (g := g) (z := z) hz huniq hB hgap with
    ⟨ε, _hεpos, hEq⟩
  have hExpPert : IsExposed ℝ C ((l + ε • g).toExposed C) := by
    simpa using (ContinuousLinearMap.toExposed.isExposed (l := l + ε • g) (A := C))
  have hExpSingleton : IsExposed ℝ C ({z} : Set (Fin n → ℝ)) := by
    simpa [hEq] using hExpPert
  exact
    theorem18_6_exposedPoint_of_exposed_singleton (n := n) (C := C) (p := z)
      hExpSingleton

/-- Perturbation-limit bridge:
if exposed points `p k` are selected from perturbed maximizer sets `(l + εₖ g).toExposed C`,
converge to `z`, and the perturbation terms vanish in the limit, then `z` lies in the exposed face
`l.toExposed C` and in `closure (C.exposedPoints ℝ)`. -/
lemma theorem18_6_bridge_of_perturbation_limit {n : ℕ}
    {C : Set (Fin n → ℝ)} {l g : (Fin n → ℝ) →L[ℝ] ℝ}
    {ε : ℕ → ℝ} {p : ℕ → (Fin n → ℝ)} {z : Fin n → ℝ}
    (hzC : z ∈ C) (hpExp : ∀ k, p k ∈ C.exposedPoints ℝ)
    (hpPert : ∀ k, p k ∈ (l + ε k • g).toExposed C)
    (hpTend : Filter.Tendsto p Filter.atTop (nhds z))
    (hεgP : Filter.Tendsto (fun k => ε k * g (p k)) Filter.atTop (nhds 0))
    (hεgConst : ∀ y ∈ C, Filter.Tendsto (fun k => ε k * g y) Filter.atTop (nhds 0)) :
    ∃ q ∈ l.toExposed C, q ∈ closure (C.exposedPoints ℝ) := by
  have hzFace : z ∈ l.toExposed C := by
    refine ⟨hzC, ?_⟩
    intro y hyC
    have hLeft :
        Filter.Tendsto (fun k => l y + ε k * g y) Filter.atTop (nhds (l y + 0)) :=
      tendsto_const_nhds.add (hεgConst y hyC)
    have hRight :
        Filter.Tendsto (fun k => l (p k) + ε k * g (p k)) Filter.atTop (nhds (l z + 0)) := by
      have hlpk : Filter.Tendsto (fun k => l (p k)) Filter.atTop (nhds (l z)) :=
        (l.continuous.continuousAt.tendsto).comp hpTend
      exact hlpk.add hεgP
    have hEventually :
        ∀ᶠ k in Filter.atTop, l y + ε k * g y ≤ l (p k) + ε k * g (p k) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      have hk := (hpPert k).2 y hyC
      simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hk
    have hle :
        l y + 0 ≤ l z + 0 :=
      tendsto_le_of_eventuallyLE hLeft hRight hEventually
    simpa using hle
  have hzcl : z ∈ closure (C.exposedPoints ℝ) :=
    mem_closure_of_tendsto hpTend (Filter.Eventually.of_forall hpExp)
  exact ⟨z, hzFace, hzcl⟩

/-- Compact extraction for perturbed exposed selectors. -/
lemma theorem18_6_compact_extract_subseq_exposed_perturbed {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCcompact : IsCompact C)
    {l g : (Fin n → ℝ) →L[ℝ] ℝ} {ε : ℕ → ℝ} {p : ℕ → (Fin n → ℝ)}
    (hpExp : ∀ k, p k ∈ C.exposedPoints ℝ)
    (hpPert : ∀ k, p k ∈ (l + ε k • g).toExposed C) :
    ∃ z : Fin n → ℝ, z ∈ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun k => p (φ k)) Filter.atTop (nhds z) ∧
        (∀ k, p (φ k) ∈ C.exposedPoints ℝ) ∧
        (∀ k, p (φ k) ∈ (l + ε (φ k) • g).toExposed C) := by
  have hpC : ∀ k, p k ∈ C := fun k => (hpPert k).1
  rcases hCcompact.tendsto_subseq (x := p) hpC with ⟨z, hzC, φ, hφmono, hφtend⟩
  refine ⟨z, hzC, φ, hφmono, hφtend, ?_, ?_⟩
  · intro k
    exact hpExp (φ k)
  · intro k
    simpa using hpPert (φ k)

/-- Vanishing perturbation terms from a vanishing scale and bounded functional values on `C`. -/
lemma theorem18_6_perturbation_terms_tendsto_zero {n : ℕ} {C : Set (Fin n → ℝ)}
    {g : (Fin n → ℝ) →L[ℝ] ℝ} {ε : ℕ → ℝ} {p : ℕ → (Fin n → ℝ)}
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, |g x| ≤ B) (hpC : ∀ k, p k ∈ C) :
    Filter.Tendsto (fun k => ε k * g (p k)) Filter.atTop (nhds 0) ∧
      (∀ y ∈ C, Filter.Tendsto (fun k => ε k * g y) Filter.atTop (nhds 0)) := by
  rcases hB with ⟨B, _hBnonneg, hBbound⟩
  have hfgBound : ∀ᶠ k in Filter.atTop, |g (p k)| ≤ B := by
    refine Filter.Eventually.of_forall ?_
    intro k
    exact hBbound (p k) (hpC k)
  have hmul0 :
      Filter.Tendsto (fun k => g (p k) * ε k) Filter.atTop (nhds 0) :=
    bdd_le_mul_tendsto_zero' B hfgBound hε
  have hmain :
      Filter.Tendsto (fun k => ε k * g (p k)) Filter.atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul0
  refine ⟨hmain, ?_⟩
  intro y hyC
  have hmul :
      Filter.Tendsto (fun k => g y * ε k) Filter.atTop (nhds 0) :=
    by simpa [mul_zero] using (hε.const_mul (g y))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- A continuous linear functional is uniformly bounded in absolute value on a compact set. -/
lemma theorem18_6_exists_abs_bound_on_compact {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) (g : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, |g x| ≤ B := by
  by_cases hCne : C.Nonempty
  · rcases
      hCcompact.exists_isMaxOn hCne ((g.continuous.abs).continuousOn) with
        ⟨x0, hx0C, hx0Max⟩
    refine ⟨|g x0|, abs_nonneg _, ?_⟩
    intro x hxC
    exact (isMaxOn_iff.mp hx0Max) x hxC
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    refine ⟨0, le_rfl, ?_⟩
    intro x hxC
    exfalso
    simp [hCempty] at hxC

/-- Choice form: nonempty intersections of exposed points with perturbed exposed faces give a
selector sequence. -/
lemma theorem18_6_choose_selector_of_nonempty_intersections {n : ℕ} {C : Set (Fin n → ℝ)}
    {l g : (Fin n → ℝ) →L[ℝ] ℝ}
    (hNonempty :
      ∀ k : ℕ,
        (C.exposedPoints ℝ ∩ (l + (1 / ((k : ℝ) + 1)) • g).toExposed C).Nonempty) :
    ∃ p : ℕ → (Fin n → ℝ),
      (∀ k : ℕ, p k ∈ C.exposedPoints ℝ) ∧
        (∀ k : ℕ, p k ∈ (l + (1 / ((k : ℝ) + 1)) • g).toExposed C) := by
  classical
  choose p hp using hNonempty
  refine ⟨p, ?_, ?_⟩
  · intro k
    exact (hp k).1
  · intro k
    exact (hp k).2


/-- A Euclidean-farthest point from `y` in `C` is an exposed point of `C`. -/
lemma theorem18_6_mem_exposedPoints_of_isMaxOn_dotProduct_sub_self {n : ℕ}
    {C : Set (Fin n → ℝ)} {y p : Fin n → ℝ} (hpC : p ∈ C)
    (hpmax : IsMaxOn (fun z : Fin n → ℝ => dotProduct (z - y) (z - y)) C p) :
    p ∈ C.exposedPoints ℝ := by
  let m : (Fin n → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.flip (dotProductBilin (R := ℝ) (S := ℝ) (m := Fin n) (A := ℝ))) (p - y))
  have hm : ∀ z : Fin n → ℝ, m z = dotProduct z (p - y) := by
    intro z
    simp [m, LinearMap.flip_apply, dotProductBilin]
  refine ⟨hpC, m, ?_⟩
  intro q hqC
  have hqmax : dotProduct (q - y) (q - y) ≤ dotProduct (p - y) (p - y) :=
    (isMaxOn_iff.mp hpmax) q hqC
  have hcross_le : dotProduct (q - y) (p - y) ≤ dotProduct (p - y) (p - y) := by
    have hnonneg : 0 ≤ dotProduct ((q - y) - (p - y)) ((q - y) - (p - y)) := by
      simpa using (dotProduct_self_star_nonneg (v := (q - y) - (p - y)))
    have hsq :
        dotProduct ((q - y) - (p - y)) ((q - y) - (p - y)) =
          dotProduct (q - y) (q - y) - 2 * dotProduct (q - y) (p - y) +
            dotProduct (p - y) (p - y) := by
      simp [dotProduct_comm, two_mul, sub_eq_add_neg, add_left_comm, add_comm]
      ring
    nlinarith [hnonneg, hsq, hqmax]
  have hqsub :
      dotProduct (q - y) (p - y) = dotProduct q (p - y) - dotProduct y (p - y) := by
    simpa using (sub_dotProduct q y (p - y))
  have hpsub :
      dotProduct (p - y) (p - y) = dotProduct p (p - y) - dotProduct y (p - y) := by
    simpa using (sub_dotProduct p y (p - y))
  have hdot_le : dotProduct q (p - y) ≤ dotProduct p (p - y) := by
    linarith [hcross_le, hqsub, hpsub]
  have hmq : m q ≤ m p := by
    simpa [hm] using hdot_le
  refine ⟨hmq, ?_⟩
  intro hmpq
  have hmEq : m q = m p := le_antisymm hmq hmpq
  have hdot_eq : dotProduct q (p - y) = dotProduct p (p - y) := by
    simpa [hm] using hmEq
  have hcross_eq : dotProduct (q - y) (p - y) = dotProduct (p - y) (p - y) := by
    linarith [hdot_eq, hqsub, hpsub]
  have hnonneg : 0 ≤ dotProduct ((q - y) - (p - y)) ((q - y) - (p - y)) := by
    simpa using (dotProduct_self_star_nonneg (v := (q - y) - (p - y)))
  have hsq :
      dotProduct ((q - y) - (p - y)) ((q - y) - (p - y)) =
        dotProduct (q - y) (q - y) - 2 * dotProduct (q - y) (p - y) +
          dotProduct (p - y) (p - y) := by
    simp [dotProduct_comm, two_mul, sub_eq_add_neg, add_left_comm, add_comm]
    ring
  have hsq_le_zero : dotProduct ((q - y) - (p - y)) ((q - y) - (p - y)) ≤ 0 := by
    nlinarith [hsq, hqmax, hcross_eq]
  have hsq_zero : dotProduct ((q - y) - (p - y)) ((q - y) - (p - y)) = 0 :=
    le_antisymm hsq_le_zero hnonneg
  have hqp_zero : dotProduct (q - p) (q - p) = 0 := by
    have hrewrite : q - p = (q - y) - (p - y) := by
      abel_nf
    calc
      dotProduct (q - p) (q - p)
          = dotProduct ((q - y) - (p - y)) ((q - y) - (p - y)) := by
              rw [hrewrite]
      _ = 0 := hsq_zero
  have hqp : q - p = 0 := dotProduct_self_eq_zero.mp hqp_zero
  exact sub_eq_zero.mp hqp

/-- Theorem 18.6. Every extreme point lies in the closure of the exposed points (bounded case). -/
theorem theorem18_6_extremePoints_subset_closure_exposedPoints {n : ℕ} (C : Set (Fin n → ℝ))
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) := by
  classical
  intro x hxext
  have hxext' : IsExtremePoint (𝕜 := ℝ) C x :=
    (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := x)).2 hxext
  have hxC : x ∈ C := hxext'.1
  by_contra hxnot
  let C0 : Set (Fin n → ℝ) := conv (closure (C.exposedPoints ℝ))
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  have hC0closed : IsClosed C0 :=
    (theorem18_6_isClosed_conv_closure_exposedPoints (n := n) (C := C) hCclosed hCbounded
      hCconv).1
  have hC0conv : Convex ℝ C0 := by
    simpa [C0, conv] using
      (convex_convexHull (𝕜 := ℝ) (s := closure (C.exposedPoints ℝ)))
  have hxnotC0 : x ∉ C0 := by
    simpa [C0] using
      theorem18_6_not_mem_C0_of_extreme_not_mem_closure_exposedPoints (n := n) (C := C) hCclosed
        hCbounded hCconv (x := x) hxext' hxnot
  obtain ⟨l, r, hlC0, hrx⟩ := geometric_hahn_banach_closed_point (s := C0) hC0conv hC0closed hxnotC0
  let b : Fin n → ℝ := fun i => l (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
  have hl_apply : ∀ z : Fin n → ℝ, l z = dotProduct z b := by
    simpa [b] using (strongDual_apply_eq_dotProduct (n := n) l)
  let qfun : (Fin n → ℝ) → ℝ := fun z => dotProduct (z - x) (z - x)
  have hqcont : ContinuousOn qfun C := by
    have hcont : Continuous qfun := by
      simpa [qfun] using
        ((continuous_id.sub continuous_const) : Continuous fun z : Fin n → ℝ => z - x).dotProduct
          ((continuous_id.sub continuous_const) : Continuous fun z : Fin n → ℝ => z - x)
    exact hcont.continuousOn
  obtain ⟨x0, hx0C, hx0max⟩ := hCcompact.exists_isMaxOn ⟨x, hxC⟩ hqcont
  let B : ℝ := qfun x0
  have hBbound : ∀ z ∈ C, qfun z ≤ B := by
    intro z hzC
    exact (isMaxOn_iff.mp hx0max) z hzC
  have hBnonneg : 0 ≤ B := by
    have hxB : qfun x ≤ B := hBbound x hxC
    simpa [B, qfun] using hxB
  let lam : ℝ := (B + 1) / (2 * (l x - r))
  have hlampos : 0 < lam := by
    have hnumpos : 0 < B + 1 := by nlinarith [hBnonneg]
    have hdenpos : 0 < 2 * (l x - r) := by nlinarith [hrx]
    exact div_pos hnumpos hdenpos
  let y : Fin n → ℝ := x - lam • b
  have hdist_lt :
      ∀ z ∈ C, l z ≤ r → dotProduct (z - y) (z - y) < dotProduct (x - y) (x - y) := by
    intro z hzC hzr
    have hBz : dotProduct (z - x) (z - x) ≤ B := by
      simpa [qfun] using (hBbound z hzC)
    have hxy : x - y = lam • b := by
      simp [y, sub_eq_add_neg, add_comm]
    have hzy : z - y = (z - x) + (x - y) := by
      abel
    have hzx_dot : dotProduct (z - x) b = l z - l x := by
      rw [sub_dotProduct]
      simp [hl_apply z, hl_apply x]
    have hformula :
        dotProduct (z - y) (z - y) =
          dotProduct (z - x) (z - x) + 2 * lam * (l z - l x) + dotProduct (x - y) (x - y) := by
      rw [hzy]
      rw [dotProduct_add, add_dotProduct]
      rw [dotProduct_comm (x - y) (z - x)]
      rw [hxy]
      rw [dotProduct_smul, smul_dotProduct]
      rw [add_dotProduct]
      rw [dotProduct_smul, smul_dotProduct]
      rw [hzx_dot]
      simp [smul_eq_mul, mul_assoc]
      ring
    have hsub_le : l z - l x ≤ r - l x := by linarith
    have hmul_le : 2 * lam * (l z - l x) ≤ 2 * lam * (r - l x) := by
      have hlamnonneg : 0 ≤ lam := le_of_lt hlampos
      nlinarith [hsub_le, hlamnonneg]
    have hsum_eq : B + 2 * lam * (r - l x) = -1 := by
      have hlamdef : lam = (B + 1) / (2 * (l x - r)) := rfl
      have hne : l x - r ≠ 0 := by linarith [hrx]
      have hratio : (r - l x) / (l x - r) = -1 := by
        field_simp [hne]
        ring
      calc
        B + 2 * lam * (r - l x)
            = B + 2 * ((B + 1) / (2 * (l x - r))) * (r - l x) := by rw [hlamdef]
        _ = B + ((B + 1) / (l x - r)) * (r - l x) := by
              congr 1
              field_simp
        _ = B + (B + 1) * ((r - l x) / (l x - r)) := by
              field_simp [hne]
        _ = B + (B + 1) * (-1) := by rw [hratio]
        _ = -1 := by ring
    have hsum_neg : B + 2 * lam * (r - l x) < 0 := by
      nlinarith [hsum_eq]
    have hmain_lt : dotProduct (z - x) (z - x) + 2 * lam * (l z - l x) < 0 := by
      have hmain_le :
          dotProduct (z - x) (z - x) + 2 * lam * (l z - l x) ≤ B + 2 * lam * (r - l x) :=
        add_le_add hBz hmul_le
      exact lt_of_le_of_lt hmain_le hsum_neg
    linarith [hformula, hmain_lt]
  have hcontFar : ContinuousOn (fun z : Fin n → ℝ => dotProduct (z - y) (z - y)) C := by
    have hcont : Continuous (fun z : Fin n → ℝ => dotProduct (z - y) (z - y)) := by
      simpa using
        ((continuous_id.sub continuous_const) : Continuous fun z : Fin n → ℝ => z - y).dotProduct
          ((continuous_id.sub continuous_const) : Continuous fun z : Fin n → ℝ => z - y)
    exact hcont.continuousOn
  obtain ⟨p, hpC, hpmax⟩ := hCcompact.exists_isMaxOn ⟨x, hxC⟩ hcontFar
  have hpOutside : r < l p := by
    by_contra hpNot
    have hple : l p ≤ r := le_of_not_gt hpNot
    have hpLt : dotProduct (p - y) (p - y) < dotProduct (x - y) (x - y) := hdist_lt p hpC hple
    have hxLe : dotProduct (x - y) (x - y) ≤ dotProduct (p - y) (p - y) :=
      (isMaxOn_iff.mp hpmax) x hxC
    exact (not_le_of_gt hpLt) hxLe
  have hpExp : p ∈ C.exposedPoints ℝ :=
    theorem18_6_mem_exposedPoints_of_isMaxOn_dotProduct_sub_self (C := C) (y := y) (p := p) hpC
      hpmax
  have hpC0 : p ∈ C0 := by
    have hpcl : p ∈ closure (C.exposedPoints ℝ) := subset_closure hpExp
    simpa [C0, conv] using
      (subset_convexHull (𝕜 := ℝ) (s := closure (C.exposedPoints ℝ)) hpcl)
  have hpLtR : l p < r := hlC0 p hpC0
  exact (not_lt_of_ge (le_of_lt hpOutside)) hpLtR

/-- Theorem 18.6 in the no-lines form used later in Theorem 25.6: a closed convex set containing
no lines still has every extreme point in the closure of its exposed points. The bounded theorem
above is the compact special case; the unbounded proof is deferred to the Chapter 18 no-lines
development. -/
lemma theorem18_6_mem_exposedPoints_of_mem_exposedPoints_inter_closedBall {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCconv : Convex ℝ C) {R : ℝ} {x : Fin n → ℝ}
    (hxnorm : ‖x‖ < R) (hxExp : x ∈ (C ∩ Metric.closedBall (0 : Fin n → ℝ) R).exposedPoints ℝ) :
    x ∈ C.exposedPoints ℝ := by
  classical
  rcases (exposed_point_def.mp hxExp) with ⟨hxD, l, hl⟩
  refine (exposed_point_def.mpr ?_)
  refine ⟨hxD.1, l, ?_⟩
  intro y hyC
  by_cases hyBall : y ∈ Metric.closedBall (0 : Fin n → ℝ) R
  · exact hl y ⟨hyC, hyBall⟩
  · have hxBall : x ∈ Metric.closedBall (0 : Fin n → ℝ) R := hxD.2
    have hyne : y ≠ x := by
      intro hxy
      exact hyBall (hxy.symm ▸ hxBall)
    have hyEq_of_hxyle : l x ≤ l y → y = x := by
      intro hxy
      let δ : ℝ := R - ‖x‖
      have hδpos : 0 < δ := by
        dsimp [δ]
        linarith
      let t : ℝ := min (1 / 2) (δ / (‖y - x‖ + 1))
      have htpos : 0 < t := by
        dsimp [t]
        refine lt_min ?_ ?_
        · norm_num
        · exact div_pos hδpos (by positivity)
      have ht_nonneg : 0 ≤ t := le_of_lt htpos
      have htle : t ≤ δ / (‖y - x‖ + 1) := by
        dsimp [t]
        exact min_le_right _ _
      have htle_one : t ≤ 1 := by
        have hhalf : t ≤ (1 / 2 : ℝ) := by
          dsimp [t]
          exact min_le_left _ _
        linarith
      let w : Fin n → ℝ := (1 - t) • x + t • y
      have hwC : w ∈ C := by
        refine hCconv hxD.1 hyC ?_ ht_nonneg ?_
        · linarith
        · ring
      have htmul_add_le : t * (‖y - x‖ + 1) ≤ δ := by
        have hdenpos : 0 < ‖y - x‖ + 1 := by positivity
        exact (le_div_iff₀ hdenpos).mp htle
      have htmul_lt : t * ‖y - x‖ < δ := by
        have hEq : t * ‖y - x‖ = t * (‖y - x‖ + 1) - t := by ring
        rw [hEq]
        linarith
      have hw_eq : w = x + t • (y - x) := by
        ext i
        simp [w]
        ring
      have hnorm_tsub_lt : ‖t • (y - x)‖ < δ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
        exact htmul_lt
      have hwBall : w ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hnorm_w_le : ‖w‖ ≤ ‖x‖ + ‖t • (y - x)‖ := by
          rw [hw_eq]
          exact norm_add_le _ _
        have hnorm_w_lt : ‖w‖ < R := by
          dsimp [δ] at htmul_lt hδpos
          linarith
        simpa using le_of_lt hnorm_w_lt
      have hwge : l x ≤ l w := by
        have hwformula : l w = (1 - t) * l x + t * l y := by
          simp [w, map_add]
        have hrewrite : (1 - t) * l x + t * l y = l x + t * (l y - l x) := by ring
        rw [hwformula, hrewrite]
        have hnonneg : 0 ≤ t * (l y - l x) := by
          exact mul_nonneg ht_nonneg (sub_nonneg.mpr hxy)
        linarith
      have hwuniq : w = x := (hl w ⟨hwC, hwBall⟩).2 hwge
      have hsmul : t • (y - x) = 0 := by
        have hEq : x + t • (y - x) = x := by simpa [hw_eq] using hwuniq
        have hsub := congrArg (fun z : Fin n → ℝ => z - x) hEq
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
      have hyx : y = x := by
        rcases smul_eq_zero.mp hsmul with ht0 | hyx
        · exact False.elim (ne_of_gt htpos ht0)
        · exact sub_eq_zero.mp hyx
      exact hyx
    have hyle : l y ≤ l x := by
      by_contra hnot
      have hyx : y = x := hyEq_of_hxyle (le_of_lt (lt_of_not_ge hnot))
      exact hyBall (hyx.symm ▸ hxBall)
    exact ⟨hyle, hyEq_of_hxyle⟩

theorem theorem18_6_extremePoints_subset_closure_exposedPoints_of_noLines
    {n : ℕ} (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) := by
  classical
  let _ := hCclosed
  let _ := hCconv
  let _ := hNoLines
  intro x hxext
  have hxext' : IsExtremePoint (𝕜 := ℝ) C x :=
    (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := x)).2 hxext
  let R : ℝ := ‖x‖ + 1
  let D : Set (Fin n → ℝ) := C ∩ Metric.closedBall (0 : Fin n → ℝ) R
  have hDclosed : IsClosed D := by
    dsimp [D]
    exact hCclosed.inter Metric.isClosed_closedBall
  have hDbounded : Bornology.IsBounded D := by
    dsimp [D]
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := R)).subset ?_
    intro y hy
    exact hy.2
  have hDconv : Convex ℝ D := by
    dsimp [D]
    exact hCconv.inter (convex_closedBall (0 : Fin n → ℝ) R)
  have hxD : x ∈ D := by
    refine ⟨hxext'.1, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [R]
    have hnorm : ‖x - (0 : Fin n → ℝ)‖ = ‖x‖ := by simp
    rw [hnorm]
    exact le_add_of_nonneg_right (show (0 : ℝ) ≤ (1 : ℝ) from zero_le_one)
  have hxextD : IsExtremePoint (𝕜 := ℝ) D x :=
    theorem18_6_isExtremePoint_mono (C := C) (D := D) (by
      intro y hy
      exact hy.1) hxD hxext'
  have hxclD : x ∈ closure (D.exposedPoints ℝ) := by
    exact
      theorem18_6_extremePoints_subset_closure_exposedPoints (n := n) (C := D) hDclosed hDbounded
        hDconv ((isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := D) (x := x)).1 hxextD)
  rw [Metric.mem_closure_iff] at hxclD ⊢
  intro ε hε
  obtain ⟨y, hyExpD, hxy⟩ := hxclD (min ε 1) (by positivity)
  have hdist_lt_one : dist x y < 1 := lt_of_lt_of_le hxy (min_le_right _ _)
  have hy_norm_lt : ‖y‖ < R := by
    have hnorm_sub_lt : ‖y - x‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hdist_lt_one
    have hy_eq : x + (y - x) = y := by
      ext i
      simp
    have hy_norm_le : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc
        ‖y‖ = ‖x + (y - x)‖ := by simp [hy_eq]
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    dsimp [R]
    linarith
  refine ⟨y, ?_, ?_⟩
  · exact
      theorem18_6_mem_exposedPoints_of_mem_exposedPoints_inter_closedBall (n := n) (C := C) hCconv
        (R := R) hy_norm_lt hyExpD
  · exact lt_of_lt_of_le hxy (min_le_left _ _)

/-- The RHS mixed convex hull is contained in the closed convex set. -/
lemma theorem18_7_rhs_subset_C {n : ℕ} {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) ⊆ C := by
  classical
  have hsubset0 :
      mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} ⊆ C := by
    refine
      mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
        (S₀ := C.exposedPoints ℝ)
        (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) (Ccand := C) hCconv
        ?_ ?_
    · exact exposedPoints_subset (A := C) (𝕜 := ℝ)
    · intro d hd x hxC t ht
      have hdrec :
          d ∈ Set.recessionCone C :=
        mem_recessionCone_of_isExtremeDirection_fin (hCclosed := hCclosed) (by simpa using hd)
      exact hdrec hxC ht
  exact (IsClosed.closure_subset_iff (t := C) hCclosed).2 hsubset0

/-- The mixed convex hull recedes in all directions in its direction set. -/
lemma theorem18_7_mixedConvexHull_recedes {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (hd : d ∈ S₁) {x : Fin n → ℝ} (hx : x ∈ mixedConvexHull (n := n) S₀ S₁) {t : ℝ}
    (ht : 0 ≤ t) :
    x + t • d ∈ mixedConvexHull (n := n) S₀ S₁ := by
  classical
  refine (Set.mem_sInter).2 ?_
  intro C hC
  have hxC : x ∈ C := (Set.mem_sInter.mp hx) C hC
  rcases hC with ⟨_hCconv, _hCsub, hCrec⟩
  exact hCrec hd hxC t ht

/-- The closure mixed convex hull is closed and convex. -/
lemma theorem18_7_K_isClosed_isConvex {n : ℕ} {C : Set (Fin n → ℝ)} :
    IsClosed
        (closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})) ∧
      Convex ℝ
        (closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})) := by
  classical
  refine ⟨isClosed_closure, ?_⟩
  exact
    (Convex.closure
      (convex_mixedConvexHull (n := n) (C.exposedPoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}))

/-- The closure mixed convex hull recedes along extreme directions. -/
lemma theorem18_7_K_recedes_extremeDirections {n : ℕ} {C : Set (Fin n → ℝ)}
    {d : Fin n → ℝ} (hd : d ∈ {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})
    {x : Fin n → ℝ}
    (hx :
      x ∈
        closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}))
    {t : ℝ} (ht : 0 ≤ t) :
    x + t • d ∈
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  let A :=
    mixedConvexHull (n := n) (C.exposedPoints ℝ)
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}
  have hcont : Continuous fun y : Fin n → ℝ => y + t • d := by
    simpa using (continuous_id.add continuous_const)
  have himage : (fun y : Fin n → ℝ => y + t • d) '' A ⊆ A := by
    intro y hy
    rcases hy with ⟨y, hyA, rfl⟩
    exact theorem18_7_mixedConvexHull_recedes (n := n) (S₀ := C.exposedPoints ℝ)
      (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) hd hyA ht
  have hximage : x + t • d ∈ closure ((fun y : Fin n → ℝ => y + t • d) '' A) := by
    have hsubset := image_closure_subset_closure_image (s := A) hcont
    exact hsubset ⟨x, hx, rfl⟩
  have hcl : closure ((fun y : Fin n → ℝ => y + t • d) '' A) ⊆ closure A := by
    exact closure_mono himage
  simpa [A] using hcl hximage

/-- Exposed points are contained in the mixed convex hull, hence their closure lies in `K`. -/
lemma theorem18_7_closure_exposedPoints_subset_K {n : ℕ} {C : Set (Fin n → ℝ)} :
    closure (C.exposedPoints ℝ) ⊆
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  refine closure_mono ?_
  intro x hx
  refine (Set.mem_sInter).2 ?_
  intro D hD
  rcases hD with ⟨_hDconv, hS0, _hDrec⟩
  exact hS0 hx

/-- Extreme points lie in the closure mixed convex hull (bounded Straszewicz step). -/
lemma theorem18_7_extremePoints_subset_K {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    C.extremePoints ℝ ⊆
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  have hcl :
      closure (C.exposedPoints ℝ) ⊆
        closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) :=
    theorem18_7_closure_exposedPoints_subset_K (n := n) (C := C)
  have hstrasz :
      C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) :=
    theorem18_6_extremePoints_subset_closure_exposedPoints (n := n) (C := C) hCclosed hCbounded
      hCconv
  exact Set.Subset.trans hstrasz hcl

/-- Use Theorem 18.5 to show `C ⊆ K` once extreme points lie in `K`. -/
lemma theorem18_7_C_subset_K_via_theorem18_5 {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    C ⊆
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  let K :=
    closure
      (mixedConvexHull (n := n) (C.exposedPoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})
  have hKconv : Convex ℝ K := by
    simpa using (theorem18_7_K_isClosed_isConvex (n := n) (C := C)).2
  have hKrec :
      ∀ d ∈ {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d},
        ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ K := by
    intro d hd x hx t ht
    simpa [K] using
      (theorem18_7_K_recedes_extremeDirections (n := n) (C := C) (d := d) hd (x := x) hx
        (t := t) ht)
  have hExt : C.extremePoints ℝ ⊆ K := by
    simpa [K] using
      (theorem18_7_extremePoints_subset_K (n := n) (C := C) hCclosed hCbounded hCconv)
  have hsubset :
      mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} ⊆ K := by
    refine
      mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
        (S₀ := C.extremePoints ℝ)
        (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) (Ccand := K) hKconv
        ?_ ?_
    · exact hExt
    · intro d hd x hxK t ht
      exact hKrec d hd x hxK t ht
  have hCeq :
      C =
        mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} :=
    closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections (n := n) (C := C) hCclosed
      hCconv hNoLines
  intro x hxC
  have hx' :
      x ∈
        mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
    rw [hCeq] at hxC
    exact hxC
  simpa [K] using hsubset hx'

/-- Theorem 18.7. A closed bounded convex set with no lines is the closure of the mixed convex
hull of its exposed points and extreme directions. -/
theorem theorem18_7_closedConvex_eq_closure_mixedConvexHull_exposedPoints_extremeDirections
    {n : ℕ} (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C)
    (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    C =
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  have hsubset :
      closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) ⊆ C :=
    theorem18_7_rhs_subset_C (n := n) (C := C) hCclosed hCconv
  refine le_antisymm ?_ hsubset
  exact
    theorem18_7_C_subset_K_via_theorem18_5 (n := n) (C := C) hCclosed hCbounded hCconv hNoLines

/-- A bounded cone contains only the origin. -/
lemma cor18_7_1_bounded_cone_subset_singleton_zero {n : ℕ} {K : Set (Fin n → ℝ)}
    (hKcone : IsConeSet n K) (hKbounded : Bornology.IsBounded K) :
    K ⊆ ({0} : Set (Fin n → ℝ)) := by
  intro x hx
  by_contra hxne
  rcases (Metric.isBounded_iff_subset_closedBall (c := (0 : Fin n → ℝ))).1 hKbounded with
    ⟨r, hr⟩
  have hxball : x ∈ Metric.closedBall (0 : Fin n → ℝ) r := hr hx
  have hr_nonneg : 0 ≤ r := by
    have hdist : dist x (0 : Fin n → ℝ) ≤ r := (Metric.mem_closedBall).1 hxball
    exact le_trans dist_nonneg hdist
  have hnorm_pos : 0 < ‖x‖ := (norm_pos_iff).2 hxne
  have hnorm_ne : ‖x‖ ≠ 0 := ne_of_gt hnorm_pos
  let t : ℝ := r / ‖x‖ + 1
  have hdiv_nonneg : 0 ≤ r / ‖x‖ := div_nonneg hr_nonneg (le_of_lt hnorm_pos)
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have htx : t • x ∈ K := hKcone x hx t ht_pos
  have htxball : t • x ∈ Metric.closedBall (0 : Fin n → ℝ) r := hr htx
  have hnorm_le : ‖t • x‖ ≤ r := by
    have hdist : dist (t • x) (0 : Fin n → ℝ) ≤ r := (Metric.mem_closedBall).1 htxball
    simpa [dist_eq_norm] using hdist
  have hnorm_eq : ‖t • x‖ = t * ‖x‖ := by
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg ht_nonneg] using (norm_smul t x)
  have ht_mul : t * ‖x‖ = r + ‖x‖ := by
    dsimp [t]
    field_simp [hnorm_ne]
  have hnorm_gt : r < ‖t • x‖ := by
    have : r < r + ‖x‖ := by linarith [hnorm_pos]
    simpa [hnorm_eq, ht_mul] using this
  exact (not_lt_of_ge hnorm_le hnorm_gt)

/-- A bounded cone containing the origin is `{0}`. -/
lemma cor18_7_1_bounded_cone_eq_singleton_zero {n : ℕ} {K : Set (Fin n → ℝ)}
    (hKcone : IsConeSet n K) (hKbounded : Bornology.IsBounded K)
    (hK0 : (0 : Fin n → ℝ) ∈ K) :
    K = ({0} : Set (Fin n → ℝ)) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact cor18_7_1_bounded_cone_subset_singleton_zero (n := n) (K := K) hKcone hKbounded
  · intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simpa using hK0

/-- Corollary 18.7.1 (bounded cone version). -/
theorem corollary18_7_1_closedConvexCone_eq_closure_cone {n : ℕ} (K T : Set (Fin n → ℝ))
    (hKcone : IsConeSet n K) (hKbounded : Bornology.IsBounded K)
    (hK0 : (0 : Fin n → ℝ) ∈ K) (hTsub : T ⊆ K) :
    K = closure (cone n T) := by
  classical
  have hK : K = ({0} : Set (Fin n → ℝ)) :=
    cor18_7_1_bounded_cone_eq_singleton_zero (n := n) (K := K) hKcone hKbounded hK0
  have hT0 : T ⊆ ({0} : Set (Fin n → ℝ)) := fun x hx => by
    have hx' : x ∈ K := hTsub hx
    simpa [hK] using hx'
  have hcone : cone n T = ({0} : Set (Fin n → ℝ)) :=
    cone_eq_singleton_zero_of_subset (n := n) (S := T) hT0
  simp [hK, hcone]

/-- The continuous linear functional `x ↦ dotProduct x xStar`. -/
noncomputable def dotProductCLM {n : ℕ} (xStar : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.flip (dotProductBilin (R := ℝ) (S := ℝ) (m := Fin n) (A := ℝ))) xStar)

@[simp] lemma dotProductCLM_apply {n : ℕ} (xStar y : Fin n → ℝ) :
    dotProductCLM (n := n) xStar y = dotProduct y xStar := by
  simp [dotProductCLM, LinearMap.flip_apply, dotProductBilin]

/-- A compact set gives a bounded-above dot-product image. -/
lemma theorem18_8_bddAbove_image_dotProduct_of_isCompact {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) :
    ∀ xStar : Fin n → ℝ,
      BddAbove (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) := by
  intro xStar
  have hcont :
      ContinuousOn (fun y : Fin n → ℝ => dotProduct y xStar) C := by
    simpa [dotProductCLM_apply] using
      (dotProductCLM (n := n) xStar).continuous.continuousOn
  simpa using (IsCompact.bddAbove_image (α := ℝ) (β := Fin n → ℝ) (f := fun y =>
    dotProduct y xStar) hCcompact hcont)

/-- For each `xStar`, there is an extreme-point maximizer of `y ↦ dotProduct y xStar`. -/
lemma theorem18_8_exists_exposedPoint_maximizer_dotProduct {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCne : C.Nonempty) :
    ∀ xStar : Fin n → ℝ,
      ∃ p, p ∈ (dotProductCLM (n := n) xStar).toExposed C ∧ p ∈ C.extremePoints ℝ := by
  intro xStar
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  have hcont :
      ContinuousOn (fun y : Fin n → ℝ => dotProductCLM (n := n) xStar y) C :=
    (dotProductCLM (n := n) xStar).continuous.continuousOn
  rcases hCcompact.exists_isMaxOn hCne hcont with ⟨p, hpC, hpmax⟩
  have hpmax' : ∀ y ∈ C, dotProductCLM (n := n) xStar y ≤ dotProductCLM (n := n) xStar p :=
    (isMaxOn_iff).1 hpmax
  have hpF : p ∈ (dotProductCLM (n := n) xStar).toExposed C := by
    refine ⟨hpC, ?_⟩
    intro y hyC
    exact hpmax' y hyC
  have hFne : ((dotProductCLM (n := n) xStar).toExposed C).Nonempty := ⟨p, hpF⟩
  have hFexp : IsExposed ℝ C ((dotProductCLM (n := n) xStar).toExposed C) := by
    simpa using
      (ContinuousLinearMap.toExposed.isExposed (l := dotProductCLM (n := n) xStar) (A := C))
  rcases
      theorem18_6_exposedFace_contains_extremePoint_fin (n := n) (C := C) hCcompact
        (F := (dotProductCLM (n := n) xStar).toExposed C) hFexp hFne with
    ⟨q, hqF, hqExt⟩
  exact ⟨q, hqF, hqExt⟩

/-- A maximizer in an exposed face realizes the support function value. -/
lemma theorem18_8_deltaStar_eq_dotProduct_of_mem_toExposed {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCbd :
      ∀ xStar : Fin n → ℝ,
        BddAbove (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C))
    {xStar : Fin n → ℝ} {p : Fin n → ℝ}
    (hp : p ∈ (dotProductCLM (n := n) xStar).toExposed C) :
    deltaStar C xStar = dotProduct p xStar := by
  classical
  have hpC : p ∈ C := hp.1
  have hmax : ∀ y ∈ C, dotProduct y xStar ≤ dotProduct p xStar := by
    intro y hyC
    simpa [dotProductCLM_apply] using (hp.2 y hyC)
  have hmem :
      dotProduct p xStar ∈ Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C :=
    ⟨p, hpC, rfl⟩
  have hle : dotProduct p xStar ≤
      sSup (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) :=
    le_csSup (hCbd xStar) hmem
  have hne :
      (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C).Nonempty :=
    ⟨dotProduct p xStar, hmem⟩
  have hge :
      sSup (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) ≤ dotProduct p xStar := by
    refine csSup_le hne ?_
    intro r hr
    rcases hr with ⟨y, hyC, rfl⟩
    exact hmax y hyC
  have hsSup :
      sSup (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) = dotProduct p xStar :=
    le_antisymm hge hle
  simp [deltaStar_eq_sSup_image_dotProduct_right, hsSup]

/-- Theorem 18.8 (extreme-point form). A closed bounded convex set is the intersection of its
tangent half-spaces at extreme points. -/
theorem theorem18_8_closedBoundedConvex_eq_sInter_tangentHalfspaces_exposedPoints {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C)
    (hCconv : Convex ℝ C) (hCne : C.Nonempty) :
    C =
      ⋂₀ {H : Set (Fin n → ℝ) |
        ∃ xStar p,
          p ∈ (dotProductCLM (n := n) xStar).toExposed C ∧ p ∈ C.extremePoints ℝ ∧
            H = {x : Fin n → ℝ | dotProduct x xStar ≤ dotProduct p xStar} } := by
  classical
  let H : Set (Set (Fin n → ℝ)) :=
    {H : Set (Fin n → ℝ) |
      ∃ xStar p,
        p ∈ (dotProductCLM (n := n) xStar).toExposed C ∧ p ∈ C.extremePoints ℝ ∧
          H = {x : Fin n → ℝ | dotProduct x xStar ≤ dotProduct p xStar} }
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  have hCbd :
      ∀ xStar : Fin n → ℝ,
        BddAbove (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) :=
    theorem18_8_bddAbove_image_dotProduct_of_isCompact (n := n) (C := C) hCcompact
  have hsubset : C ⊆ ⋂₀ H := by
    intro x hxC
    refine (Set.mem_sInter).2 ?_
    intro S hS
    rcases hS with ⟨xStar, p, hpF, _hpExt, rfl⟩
    have hxle : dotProduct x xStar ≤ dotProduct p xStar := by
      simpa [dotProductCLM_apply] using (hpF.2 x hxC)
    exact hxle
  have hsupset : ⋂₀ H ⊆ C := by
    intro x hx
    have hxle : ∀ xStar : Fin n → ℝ, dotProduct x xStar ≤ deltaStar C xStar := by
      intro xStar
      obtain ⟨p, hpF, hpExt⟩ :=
        theorem18_8_exists_exposedPoint_maximizer_dotProduct (n := n) (C := C) hCclosed
          hCbounded hCne xStar
      have hxmem :
          x ∈ {x : Fin n → ℝ | dotProduct x xStar ≤ dotProduct p xStar} :=
        (Set.mem_sInter.mp hx) _ ⟨xStar, p, hpF, hpExt, rfl⟩
      have hdelta :
          deltaStar C xStar = dotProduct p xStar :=
        theorem18_8_deltaStar_eq_dotProduct_of_mem_toExposed (n := n) (C := C) hCbd hpF
      simpa [hdelta] using hxmem
    have hxset :
        x ∈ {x : Fin n → ℝ | ∀ xStar : Fin n → ℝ, dotProduct x xStar ≤ deltaStar C xStar} :=
      hxle
    have hEq :=
      setOf_forall_dotProduct_le_deltaStar_eq_of_isClosed (C := C) hCconv hCclosed hCne hCbd
    simpa [hEq] using hxset
  refine le_antisymm ?_ ?_
  · simpa [H] using hsubset
  · simpa [H] using hsupset

end
end Section18
end Chap04
