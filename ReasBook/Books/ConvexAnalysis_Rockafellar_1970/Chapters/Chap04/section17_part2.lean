/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part1

open scoped BigOperators Pointwise

section Chap04
section Section17

/-- A nonnegative linear combination of ray elements comes from a nonnegative combination in `T`. -/
lemma exists_nonnegLinearCombination_of_sum_smul_mem_ray_ne_zero_terms {n ℓ : Nat}
    {T : Set (Fin n → Real)} (d : Fin ℓ → Fin n → Real) (b : Fin ℓ → Real)
    (hd : ∀ j, d j ∈ ray n T) (hb : ∀ j, 0 ≤ b j) :
    ∃ r, r ≤ ℓ ∧ ∃ (y : Fin r → Fin n → Real) (c : Fin r → Real),
      (∀ i, y i ∈ T) ∧ (∀ i, 0 ≤ c i) ∧ (∑ j, b j • d j) = ∑ i, c i • y i := by
  classical
  let I : Type := {j : Fin ℓ // d j ≠ 0}
  have hdecomp :
      ∀ j : I, ∃ s ∈ T, ∃ t : Real, 0 ≤ t ∧ d j.1 = t • s := by
    intro j
    have hdj : d j.1 ∈ ray n T := hd j.1
    rcases ray_mem_decompose (n := n) (S := T) (v := d j.1) hdj with h0 | hdecomp
    · exfalso
      exact j.2 (by simpa using h0)
    · exact hdecomp
  choose s hs t ht hd_eq using hdecomp
  have hsum_subtype :
      (∑ j, b j • d j) = ∑ j : I, b j.1 • d j.1 := by
    have hsum_filter :
        (∑ j, b j • d j) =
          ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), b j • d j := by
      have hsum_if :
          (∑ j, b j • d j) = ∑ j, (if d j ≠ 0 then b j • d j else 0) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        by_cases h : d j = 0
        · simp [h]
        · simp [h]
      have hsum_filter' :
          ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), b j • d j =
            ∑ j, (if d j ≠ 0 then b j • d j else 0) := by
        simpa using
          (Finset.sum_filter (s := (Finset.univ : Finset (Fin ℓ)))
            (f := fun j => b j • d j) (p := fun j => d j ≠ 0))
      calc
        (∑ j, b j • d j) =
            ∑ j, (if d j ≠ 0 then b j • d j else 0) := hsum_if
        _ = ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), b j • d j := by
            symm
            exact hsum_filter'
    have hsum_subtype' :
        ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), b j • d j =
          ∑ j : I, b j.1 • d j.1 := by
      refine (Finset.sum_subtype (s := Finset.univ.filter (fun j => d j ≠ 0))
        (p := fun j => d j ≠ 0) (f := fun j => b j • d j) ?_)
      intro j
      simp
    calc
      (∑ j, b j • d j) =
          ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), b j • d j := hsum_filter
      _ = ∑ j : I, b j.1 • d j.1 := hsum_subtype'
  have hsum_subtype' :
      (∑ j, b j • d j) = ∑ j : I, (b j.1 * t j) • s j := by
    calc
      (∑ j, b j • d j) = ∑ j : I, b j.1 • d j.1 := hsum_subtype
      _ = ∑ j : I, b j.1 • (t j • s j) := by
          simp [hd_eq]
      _ = ∑ j : I, (b j.1 * t j) • s j := by
          simp [smul_smul]
  let r := Fintype.card I
  have hr : r ≤ ℓ := by
    dsimp [r]
    have hr' : Fintype.card I ≤ Fintype.card (Fin ℓ) := by
      dsimp [I]
      exact Fintype.card_subtype_le (p := fun j : Fin ℓ => d j ≠ 0)
    rw [Fintype.card_fin] at hr'
    exact hr'
  let e : I ≃ Fin r := Fintype.equivFin I
  let y : Fin r → Fin n → Real := fun i => s (e.symm i)
  let c : Fin r → Real := fun i => b (e.symm i).1 * t (e.symm i)
  have hy : ∀ i, y i ∈ T := by
    intro i
    simpa [y] using hs (e.symm i)
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    have hb' : 0 ≤ b (e.symm i).1 := hb (e.symm i).1
    have ht' : 0 ≤ t (e.symm i) := ht (e.symm i)
    exact mul_nonneg hb' ht'
  have hsum' : (∑ j, b j • d j) = ∑ i, c i • y i := by
    have hsum_equiv :
        ∑ i, c i • y i = ∑ j : I, (b j.1 * t j) • s j := by
      simpa [y, c] using
        (Equiv.sum_comp (e.symm) (fun j : I => (b j.1 * t j) • s j))
    calc
      (∑ j, b j • d j) = ∑ j : I, (b j.1 * t j) • s j := hsum_subtype'
      _ = ∑ i, c i • y i := by
          symm
          exact hsum_equiv
  exact ⟨r, hr, y, c, hy, hc, hsum'⟩

/-- Pad a nonnegative linear combination to a fixed length using zero coefficients. -/
lemma pad_nonnegLinearCombination_to_fixed_length {n r m : Nat} {T : Set (Fin n → Real)}
    (hT : T.Nonempty) {x : Fin n → Real} (y : Fin r → Fin n → Real) (c : Fin r → Real)
    (hy : ∀ i, y i ∈ T) (hc : ∀ i, 0 ≤ c i) (hx : x = ∑ i, c i • y i) (hr : r ≤ m - 1) :
    ∃ (y' : Fin (m - 1) → Fin n → Real) (c' : Fin (m - 1) → Real),
      (∀ j, y' j ∈ T) ∧ (∀ j, 0 ≤ c' j) ∧ x = ∑ j, c' j • y' j := by
  classical
  rcases hT with ⟨y0, hy0⟩
  let y' : Fin (m - 1) → Fin n → Real :=
    fun j => if h : (j.1 < r) then y ⟨j.1, h⟩ else y0
  let c' : Fin (m - 1) → Real :=
    fun j => if h : (j.1 < r) then c ⟨j.1, h⟩ else 0
  have hy' : ∀ j, y' j ∈ T := by
    intro j
    by_cases h : (j.1 < r)
    · simp [y', h, hy]
    · simp [y', h, hy0]
  have hc' : ∀ j, 0 ≤ c' j := by
    intro j
    by_cases h : (j.1 < r)
    · simp [c', h, hc]
    · simp [c', h]
  have hsum_filter :
      ∑ j, c' j • y' j =
        ∑ j ∈ Finset.univ.filter (fun j => j.1 < r), c' j • y' j := by
    have hsum_if :
        (∑ j, c' j • y' j) = ∑ j, (if j.1 < r then c' j • y' j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      by_cases h : (j.1 < r)
      · simp [h]
      · simp [h, c', y']
    have hsum_filter' :
        ∑ j ∈ Finset.univ.filter (fun j => j.1 < r), c' j • y' j =
          ∑ j, (if j.1 < r then c' j • y' j else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin (m - 1))))
          (f := fun j => c' j • y' j) (p := fun j => j.1 < r))
    calc
      (∑ j, c' j • y' j) =
          ∑ j, (if j.1 < r then c' j • y' j else 0) := hsum_if
      _ = ∑ j ∈ Finset.univ.filter (fun j => j.1 < r), c' j • y' j := by
          symm
          exact hsum_filter'
  let I : Type := {j : Fin (m - 1) // j.1 < r}
  have hsum_subtype :
      ∑ j ∈ Finset.univ.filter (fun j => j.1 < r), c' j • y' j =
        ∑ j : I, c' j.1 • y' j.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun j => j.1 < r))
      (p := fun j => j.1 < r) (f := fun j => c' j • y' j) ?_)
    intro j
    simp
  let e : I ≃ Fin r := by
    classical
    refine
      { toFun := fun j => ⟨j.1.1, j.2⟩
        invFun := fun i => ⟨Fin.castLE hr i, by simp⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro j
      apply Subtype.ext
      ext
      simp
    · intro i
      ext
      simp
  have hsum_I :
      ∑ j : I, c' j.1 • y' j.1 = ∑ i, c i • y i := by
    have hsum_I' :
        ∑ j : I, c' j.1 • y' j.1 = ∑ j : I, c (e j) • y (e j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [c', y', e, j.2]
    have hsum_equiv :
        ∑ j : I, c (e j) • y (e j) = ∑ i, c i • y i := by
      have h := (Equiv.sum_comp (e.symm) (fun j : I => c (e j) • y (e j)))
      simpa using h.symm
    exact hsum_I'.trans hsum_equiv
  have hsum_eq :
      ∑ j, c' j • y' j = ∑ i, c i • y i := by
    calc
      ∑ j, c' j • y' j =
          ∑ j ∈ Finset.univ.filter (fun j => j.1 < r), c' j • y' j := hsum_filter
      _ = ∑ j : I, c' j.1 • y' j.1 := hsum_subtype
      _ = ∑ i, c i • y i := hsum_I
  refine ⟨y', c', hy', hc', ?_⟩
  exact hx.trans hsum_eq.symm

/-- Proposition 17.0.11 (Cone as a mixed convex hull), LaTeX label `prop:cone-as-mixed`.

Let `T ⊆ ℝⁿ`. The convex cone generated by `T` can be viewed as the mixed convex hull with
point-set `{0}` and direction-set `T`.

Moreover, a mixed convex combination of `m` elements of this mixed set is necessarily a
combination of `0` and `m-1` directions; hence it can be written as a nonnegative linear
combination of `m-1` vectors in `T`. -/
theorem convexConeGenerated_eq_mixedConvexHull_singleton_zero {n : Nat}
    (T : Set (Fin n → Real)) :
    convexConeGenerated n T = mixedConvexHull ({0} : Set (Fin n → Real)) T := by
  calc
    convexConeGenerated n T = cone n T := (cone_eq_convexConeGenerated n T).symm
    _ = mixedConvexHull ({0} : Set (Fin n → Real)) T :=
      (mixedConvexHull_singleton_zero_eq_cone (n := n) T).symm

/-- Proposition 17.0.11 (Cone as a mixed convex hull), LaTeX label `prop:cone-as-mixed`, part 2:
when the point-set is `{0}`, a mixed convex combination reduces to a nonnegative linear
combination of vectors from `T`. -/
theorem isMixedConvexCombination_singleton_zero_imp_exists_nonnegLinearCombination
    {n m : Nat} (T : Set (Fin n → Real)) (x : Fin n → Real) (hT : T.Nonempty) :
    IsMixedConvexCombination n m ({0} : Set (Fin n → Real)) T x →
      ∃ (y : Fin (m - 1) → Fin n → Real) (c : Fin (m - 1) → Real),
        (∀ j, y j ∈ T) ∧ (∀ j, 0 ≤ c j) ∧ x = ∑ j, c j • y j := by
  intro hx
  rcases hx with ⟨k, hk_pos, _hk_le, p, d, a, b, hpS₀, hdS₁, ha, hb, _ha_sum, hx_eq⟩
  have hp0 : ∀ i, p i = 0 := by
    intro i
    simpa using hpS₀ i
  have hpsum0 : (∑ i, a i • p i) = 0 := by
    simp [hp0]
  have hx_dir : x = ∑ j, b j • d j := by
    simpa [hpsum0] using hx_eq
  obtain ⟨r, hr_le, y, c, hy, hc, hsum⟩ :=
    exists_nonnegLinearCombination_of_sum_smul_mem_ray_ne_zero_terms
      (n := n) (ℓ := m - k) (T := T) d b hdS₁ hb
  have hx' : x = ∑ i, c i • y i := by
    calc
      x = ∑ j, b j • d j := hx_dir
      _ = ∑ i, c i • y i := hsum
  have hmk : m - k ≤ m - 1 := Nat.sub_le_sub_left hk_pos m
  have hr : r ≤ m - 1 := le_trans hr_le hmk
  obtain ⟨y', c', hy', hc', hx_final⟩ :=
    pad_nonnegLinearCombination_to_fixed_length (n := n) (r := r) (m := m) (T := T)
      hT y c hy hc hx' hr
  exact ⟨y', c', hy', hc', hx_final⟩

/-- Definition 17.0.12 (Affine hull of a mixed set), LaTeX label `def:affine-hull`. Let
`S = S₀ ∪ S₁` be a mixed set consisting of points `S₀ ⊆ ℝⁿ` and directions `S₁ ⊆ ℝⁿ`. Define
`aff S := aff (conv S)`; in other words, the affine hull of a mixed set is the affine hull of
its (mixed) convex hull, i.e. the smallest affine set containing all points of `S` and
receding in all directions of `S`.

If `S` contains directions only (i.e. `S₀ = ∅`), then `conv S = aff S = ∅`. -/
def mixedAffineHull {n : Nat} (S₀ S₁ : Set (Fin n → Real)) : Set (Fin n → Real) :=
  (affineSpan Real (mixedConvexHull S₀ S₁) : Set (Fin n → Real))

/-- Definition 17.0.12 (Affine hull of a mixed set), direction-only case: if there are no
points, then the mixed convex hull is empty. -/
theorem mixedConvexHull_empty_points {n : Nat} (S₁ : Set (Fin n → Real)) :
    mixedConvexHull (n := n) (∅ : Set (Fin n → Real)) S₁ = (∅ : Set (Fin n → Real)) := by
  calc
    mixedConvexHull (n := n) (∅ : Set (Fin n → Real)) S₁ =
        conv ((∅ : Set (Fin n → Real)) + ray n S₁) :=
      (mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n)
        (S₀ := (∅ : Set (Fin n → Real))) (S₁ := S₁)).1
    _ = (∅ : Set (Fin n → Real)) := by
      simp [conv]

/-- The affine span of the empty set is empty. -/
lemma affineSpan_empty_set {n : Nat} :
    (affineSpan Real (∅ : Set (Fin n → Real)) : Set (Fin n → Real)) = ∅ := by
  have hspan : affineSpan Real (∅ : Set (Fin n → Real)) = ⊥ := by
    simp
  simp [hspan]

/-- Definition 17.0.12 (Affine hull of a mixed set), direction-only case: if there are no
points, then the mixed affine hull is empty. -/
theorem mixedAffineHull_empty_points {n : Nat} (S₁ : Set (Fin n → Real)) :
    mixedAffineHull (n := n) (∅ : Set (Fin n → Real)) S₁ = (∅ : Set (Fin n → Real)) := by
  calc
    mixedAffineHull (n := n) (∅ : Set (Fin n → Real)) S₁ =
        (affineSpan Real (mixedConvexHull (∅ : Set (Fin n → Real)) S₁) :
          Set (Fin n → Real)) := by
      rfl
    _ = (affineSpan Real (∅ : Set (Fin n → Real)) : Set (Fin n → Real)) := by
      simp [mixedConvexHull_empty_points]
    _ = (∅ : Set (Fin n → Real)) := affineSpan_empty_set

/-- Definition 17.0.13 (Affine independence for mixed sets), LaTeX label `def:aff-indep`.

Let `S` contain `m` total elements (points and directions). We say that `S` is *affinely
independent* if `dim(aff S) = m - 1`, where `aff S` is the affine hull of the mixed set
(Definition 17.0.12).

For nonempty `S`, this means `S` contains at least one point and the lifted vectors
`(1, x₁), …, (1, xₖ), (0, xₖ₊₁), …, (0, xₘ)` are linearly independent in `ℝ^{n+1}`, where
`x₁, …, xₖ` are the points in `S` and `xₖ₊₁, …, xₘ` represent the distinct directions in `S`. -/
def IsMixedAffinelyIndependent {n : Nat} (S₀ S₁ : Finset (Fin n → Real)) : Prop :=
  let m := S₀.card + S₁.card
  Module.finrank Real (affineSpan Real (mixedConvexHull (S₀ : Set (Fin n → Real))
    (S₁ : Set (Fin n → Real)))).direction = m - 1


end Section17
end Chap04
