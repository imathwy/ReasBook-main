/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part3

open scoped Pointwise

section Chap04
section Section18

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- Extract a strict mixed convex combination from membership in a mixed convex hull. -/
lemma exists_strict_mixedConvexCombination_of_mem_mixedConvexHull {n : ℕ}
    {S₀ S₁ : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ mixedConvexHull (n := n) S₀ S₁) :
    ∃ k m : ℕ, ∃ p : Fin k → Fin n → ℝ, ∃ d : Fin m → Fin n → ℝ,
      ∃ a : Fin k → ℝ, ∃ b : Fin m → ℝ,
        (∀ i, p i ∈ S₀) ∧ (∀ j, d j ∈ S₁) ∧
        (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
        (∑ i, a i = 1) ∧ x = (∑ i, a i • p i) + (∑ j, b j • d j) := by
  classical
  rcases
      (mem_mixedConvexHull_iff_exists_mixedConvexCombination (n := n) (S₀ := S₀) (S₁ := S₁)
          (x := x)).1 hx with
    ⟨m, hmix⟩
  rcases hmix with ⟨k, _hkpos, _hkle, p, d, a, b, hp, hd, ha, hb, hasum, hxeq⟩
  -- Drop zero coefficients in the point part.
  let I : Type := {i : Fin k // a i ≠ 0}
  let k' : ℕ := Fintype.card I
  let e : I ≃ Fin k' := Fintype.equivFin I
  let p' : Fin k' → Fin n → ℝ := fun i => p (e.symm i).1
  let a' : Fin k' → ℝ := fun i => a (e.symm i).1
  have hp' : ∀ i, p' i ∈ S₀ := by
    intro i
    simpa [p'] using hp (e.symm i).1
  have ha'pos : ∀ i, 0 < a' i := by
    intro i
    have hne : a (e.symm i).1 ≠ 0 := (e.symm i).property
    have hnonneg : 0 ≤ a (e.symm i).1 := ha (e.symm i).1
    have hne' : (0 : ℝ) ≠ a (e.symm i).1 := by
      simpa [eq_comm] using hne
    exact lt_of_le_of_ne hnonneg hne'
  have hsum_points_filter :
      (∑ i, a i • p i) =
        ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i • p i := by
    have hsum_if :
        (∑ i, a i • p i) = ∑ i, (if a i ≠ 0 then a i • p i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : a i = 0 <;> simp [h]
    have hsum_filter' :
        ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i • p i =
          ∑ i, (if a i ≠ 0 then a i • p i else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin k)))
          (f := fun i => a i • p i) (p := fun i => a i ≠ 0))
    calc
      (∑ i, a i • p i) = ∑ i, (if a i ≠ 0 then a i • p i else 0) := hsum_if
      _ =
          ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i • p i := by
            symm
            exact hsum_filter'
  have hsum_points_subtype :
      ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i • p i =
        ∑ i : I, a i.1 • p i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => a i ≠ 0))
      (p := fun i => a i ≠ 0) (f := fun i => a i • p i) ?_)
    intro i
    simp
  have hsum_points_equiv :
      ∑ i, a' i • p' i = ∑ i : I, a i.1 • p i.1 := by
    simpa [a', p'] using
      (Equiv.sum_comp (e.symm) (fun i : I => a i.1 • p i.1))
  have hsum_points :
      ∑ i, a' i • p' i = ∑ i, a i • p i := by
    calc
      ∑ i, a' i • p' i = ∑ i : I, a i.1 • p i.1 := hsum_points_equiv
      _ = ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i • p i := by
          symm
          exact hsum_points_subtype
      _ = ∑ i, a i • p i := by
          symm
          exact hsum_points_filter
  have hsum_a_filter :
      (∑ i, a i) = ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i := by
    have hsum_if : (∑ i, a i) = ∑ i, (if a i ≠ 0 then a i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : a i = 0 <;> simp [h]
    have hsum_filter' :
        ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i =
          ∑ i, (if a i ≠ 0 then a i else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin k)))
          (f := fun i => a i) (p := fun i => a i ≠ 0))
    calc
      (∑ i, a i) = ∑ i, (if a i ≠ 0 then a i else 0) := hsum_if
      _ = ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i := by
          symm
          exact hsum_filter'
  have hsum_a_subtype :
      ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i = ∑ i : I, a i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => a i ≠ 0))
      (p := fun i => a i ≠ 0) (f := fun i => a i) ?_)
    intro i
    simp
  have hsum_a_equiv : ∑ i, a' i = ∑ i : I, a i.1 := by
    simpa [a'] using (Equiv.sum_comp (e.symm) (fun i : I => a i.1))
  have hsum_a : ∑ i, a' i = 1 := by
    calc
      ∑ i, a' i = ∑ i : I, a i.1 := hsum_a_equiv
      _ = ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i := by
          symm
          exact hsum_a_subtype
      _ = ∑ i, a i := by
          symm
          exact hsum_a_filter
      _ = 1 := hasum
  -- Convert ray directions into genuine directions in `S₁`.
  let J : Type := {j : Fin (m - k) // b j ≠ 0 ∧ d j ≠ 0}
  have hdir :
      ∀ j : J, ∃ s ∈ S₁, ∃ t : ℝ, 0 < t ∧ d j.1 = t • s := by
    intro j
    have hdj : d j.1 ∈ ray n S₁ := hd j.1
    have hdj_ne : d j.1 ≠ 0 := j.2.2
    have hdj' : d j.1 ∈ rayNonneg n S₁ := by
      rcases (Set.mem_insert_iff).1 hdj with hzero | hray
      · exact (hdj_ne hzero).elim
      · exact hray
    rcases hdj' with ⟨s, hs, t, ht, hdt⟩
    have htpos : 0 < t := by
      have hne : t ≠ 0 := by
        intro ht0
        apply hdj_ne
        calc
          d j.1 = t • s := hdt
          _ = 0 := by simp [ht0]
      exact lt_of_le_of_ne ht (by symm; exact hne)
    exact ⟨s, hs, t, htpos, hdt⟩
  classical
  choose s hs t htpos hdt using hdir
  let m' : ℕ := Fintype.card J
  let e2 : J ≃ Fin m' := Fintype.equivFin J
  let d' : Fin m' → Fin n → ℝ := fun j => s (e2.symm j)
  let b' : Fin m' → ℝ := fun j => b (e2.symm j).1 * t (e2.symm j)
  have hd' : ∀ j, d' j ∈ S₁ := by
    intro j
    simpa [d'] using hs (e2.symm j)
  have hb'pos : ∀ j, 0 < b' j := by
    intro j
    have hbne : b (e2.symm j).1 ≠ 0 := (e2.symm j).property.1
    have hbnonneg : 0 ≤ b (e2.symm j).1 := hb (e2.symm j).1
    have hbpos : 0 < b (e2.symm j).1 := by
      have hbne' : (0 : ℝ) ≠ b (e2.symm j).1 := by
        simpa [eq_comm] using hbne
      exact lt_of_le_of_ne hbnonneg hbne'
    exact mul_pos hbpos (htpos (e2.symm j))
  have hsum_dir_filter :
      (∑ j, b j • d j) =
        ∑ j ∈ Finset.univ.filter (fun j => b j ≠ 0 ∧ d j ≠ 0), b j • d j := by
    have hsum_if :
        (∑ j, b j • d j) =
          ∑ j, (if b j ≠ 0 ∧ d j ≠ 0 then b j • d j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      by_cases hb0 : b j = 0
      · simp [hb0]
      by_cases hd0 : d j = 0
      · simp [hb0, hd0]
      · simp [hb0, hd0]
    have hsum_filter' :
        ∑ j ∈ Finset.univ.filter (fun j => b j ≠ 0 ∧ d j ≠ 0), b j • d j =
          ∑ j, (if b j ≠ 0 ∧ d j ≠ 0 then b j • d j else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin (m - k))))
          (f := fun j => b j • d j) (p := fun j => b j ≠ 0 ∧ d j ≠ 0))
    calc
      (∑ j, b j • d j) =
          ∑ j, (if b j ≠ 0 ∧ d j ≠ 0 then b j • d j else 0) := hsum_if
      _ =
          ∑ j ∈ Finset.univ.filter (fun j => b j ≠ 0 ∧ d j ≠ 0), b j • d j := by
            symm
            exact hsum_filter'
  have hsum_dir_subtype :
      ∑ j ∈ Finset.univ.filter (fun j => b j ≠ 0 ∧ d j ≠ 0), b j • d j =
        ∑ j : J, b j.1 • d j.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun j => b j ≠ 0 ∧ d j ≠ 0))
      (p := fun j => b j ≠ 0 ∧ d j ≠ 0) (f := fun j => b j • d j) ?_)
    intro j
    simp
  have hsum_dir_rewrite :
      ∑ j : J, b j.1 • d j.1 = ∑ j : J, (b j.1 * t j) • s j := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    have hdt' : d j.1 = t j • s j := hdt j
    simp [hdt', smul_smul]
  have hsum_dir_equiv :
      ∑ j, b' j • d' j = ∑ j : J, (b j.1 * t j) • s j := by
    simpa [b', d'] using
      (Equiv.sum_comp (e2.symm) (fun j : J => (b j.1 * t j) • s j))
  have hsum_dir :
      ∑ j, b' j • d' j = ∑ j, b j • d j := by
    calc
      ∑ j, b' j • d' j = ∑ j : J, (b j.1 * t j) • s j := hsum_dir_equiv
      _ = ∑ j : J, b j.1 • d j.1 := by
          symm
          exact hsum_dir_rewrite
      _ = ∑ j ∈ Finset.univ.filter (fun j => b j ≠ 0 ∧ d j ≠ 0), b j • d j := by
          symm
          exact hsum_dir_subtype
      _ = ∑ j, b j • d j := by
          symm
          exact hsum_dir_filter
  have hxeq' :
      x = (∑ i, a' i • p' i) + (∑ j, b' j • d' j) := by
    calc
      x = (∑ i, a i • p i) + (∑ j, b j • d j) := hxeq
      _ = (∑ i, a' i • p' i) + (∑ j, b' j • d' j) := by
          simp [hsum_points.symm, hsum_dir.symm]
  refine ⟨k', m', p', d', a', b', ?_, ?_, ?_, ?_, ?_, hxeq'⟩
  · exact hp'
  · exact hd'
  · exact ha'pos
  · exact hb'pos
  · exact hsum_a

/-- A mixed convex combination over fixed finite families lies in their mixed convex hull. -/
lemma mem_mixedConvexHull_range_of_exists_coeffs {n k m : ℕ}
    (p : Fin k → Fin n → ℝ) (d : Fin m → Fin n → ℝ) {y : Fin n → ℝ}
    (a : Fin k → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (hsum : ∑ i, a i = 1)
    (hy : y = (∑ i, a i • p i) + (∑ j, b j • d j)) :
    y ∈ mixedConvexHull (n := n) (Set.range p) (Set.range d) := by
  classical
  have hkpos : 0 < k := by
    by_contra hkpos
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hkpos)
    subst hk0
    have hzero : (0 : ℝ) = 1 := by
      simp at hsum
    exact (zero_ne_one (α := ℝ)) hzero
  have hk : 1 ≤ k := Nat.succ_le_iff.2 hkpos
  have hk_le : k ≤ k + m := Nat.le_add_right k m
  have hkm : k + m - k = m := Nat.add_sub_cancel_left k m
  refine
    mem_mixedConvexHull_of_IsMixedConvexCombination (n := n) (m := k + m)
      (S₀ := Set.range p) (S₁ := Set.range d) ?_
  let d' : Fin (k + m - k) → Fin n → ℝ := fun j => d (Fin.cast hkm j)
  let b' : Fin (k + m - k) → ℝ := fun j => b (Fin.cast hkm j)
  refine ⟨k, hk, hk_le, p, d', a, b', ?_, ?_, ha, ?_, hsum, ?_⟩
  · intro i
    exact ⟨i, rfl⟩
  · intro j
    have : d (Fin.cast hkm j) ∈ ray n (Set.range d) := by
      refine (Set.mem_insert_iff).2 (Or.inr ?_)
      refine ⟨d (Fin.cast hkm j), ⟨Fin.cast hkm j, rfl⟩, (1 : ℝ), by norm_num, by simp⟩
    simpa [d'] using this
  ·
    intro j
    simpa [b'] using hb (Fin.cast hkm j)
  ·
    have hsum_bd : (∑ j, b' j • d' j) = ∑ j, b j • d j := by
      simpa [b', d'] using (Equiv.sum_comp (finCongr hkm) (fun j => b j • d j))
    calc
      y = (∑ i, a i • p i) + (∑ j, b j • d j) := hy
      _ = (∑ i, a i • p i) + (∑ j, b' j • d' j) := by simp [hsum_bd]

/-- Relative interior in `Fin n → ℝ`, transported via `EuclideanSpace.equiv`. -/
def euclideanRelativeInterior_fin (n : ℕ) (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  e '' euclideanRelativeInterior n (e.symm '' C)

lemma mem_euclideanRelativeInterior_fin_iff {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ euclideanRelativeInterior_fin n C ↔
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x ∈
        euclideanRelativeInterior n
          ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' C) := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  change x ∈ e '' euclideanRelativeInterior n (e.symm '' C) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨e.symm x, hx, ?_⟩
    simp

lemma euclideanRelativeInterior_fin_singleton (n : ℕ) (x : Fin n → ℝ) :
    euclideanRelativeInterior_fin n ({x} : Set (Fin n → ℝ)) = {x} := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  have hri :
      euclideanRelativeInterior n ({e.symm x} : Set (EuclideanSpace ℝ (Fin n))) = {e.symm x} := by
    simpa [euclideanRelativelyOpen] using (euclideanRelativelyOpen_singleton n (e.symm x))
  ext y
  constructor
  · intro hy
    have hy' :
        e.symm y ∈ euclideanRelativeInterior n (e.symm '' ({x} : Set (Fin n → ℝ))) :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := ({x} : Set (Fin n → ℝ)))
        (x := y)).1 hy
    have hyEq : y = x := by
      simp [Set.image_singleton, hri, Set.mem_singleton_iff] at hy'
      exact hy'
    simp [hyEq]
  · intro hy
    have hy' := hy
    simp [Set.mem_singleton_iff] at hy'
    subst hy'
    refine (mem_euclideanRelativeInterior_fin_iff (n := n) (C := ({y} : Set (Fin n → ℝ)))
      (x := y)).2 ?_
    have hyri : e.symm y ∈ euclideanRelativeInterior n ({e.symm y} : Set (EuclideanSpace ℝ (Fin n))) := by
      simp [hri]
    simpa [Set.image_singleton] using hyri

/-- A strict convex combination of finitely many points lies in the relative interior. -/
lemma mem_euclideanRelativeInterior_convexHull_of_strict_combination {n k : ℕ}
    (p : Fin k → Fin n → ℝ) (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) :
    (∑ i, a i • p i) ∈ euclideanRelativeInterior_fin n (convexHull ℝ (Set.range p)) := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let pE : Fin k → EuclideanSpace ℝ (Fin n) := fun i => e.symm (p i)
  have hsumE :
      e.symm (∑ i, a i • p i) = ∑ i, a i • pE i := by
    classical
    calc
      e.symm (∑ i, a i • p i) = ∑ i, e.symm (a i • p i) := by
        change
          e.symm.toLinearMap (∑ i ∈ (Finset.univ : Finset (Fin k)), a i • p i) =
            ∑ i ∈ (Finset.univ : Finset (Fin k)), e.symm.toLinearMap (a i • p i)
        exact
          map_sum (g := e.symm.toLinearMap) (f := fun i => a i • p i)
            (s := (Finset.univ : Finset (Fin k)))
      _ = ∑ i, a i • pE i := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        have hterm : e.symm (a i • p i) = a i • e.symm (p i) := by
          exact e.symm.map_smul (a i) (p i)
        dsimp [pE]
        exact hterm
  have himage :
      e.symm '' convexHull ℝ (Set.range p) = convexHull ℝ (Set.range pE) := by
    have himage' :
        e.symm '' Set.range p = Set.range pE := by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨p i, ⟨i, rfl⟩, rfl⟩
    simpa [himage'] using
      (LinearMap.image_convexHull (f := e.symm.toLinearMap) (s := Set.range p))
  have hxE :
      (∑ i, a i • pE i) ∈ euclideanRelativeInterior n (convexHull ℝ (Set.range pE)) := by
    let C : Fin k → Set (EuclideanSpace ℝ (Fin n)) := fun i => ({pE i} : Set _)
    have hCne : ∀ i, (C i).Nonempty := by
      intro i
      exact ⟨pE i, by simp [C]⟩
    have hCconv : ∀ i, Convex ℝ (C i) := by
      intro i
      change Convex ℝ ({pE i} : Set (EuclideanSpace ℝ (Fin n)))
      exact convex_singleton (pE i)
    have hri :
        euclideanRelativeInterior n (convexHull ℝ (⋃ i, C i)) =
          {x | ∃ (w : Fin k → ℝ) (x_i : Fin k → EuclideanSpace ℝ (Fin n)),
              (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
                (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
                x = ∑ i, w i • x_i i} := by
      simpa using
        (euclideanRelativeInterior_convexHull_iUnion_eq (n := n) (m := k) (C := C) hCne hCconv)
    have hUnion : (⋃ i, C i) = Set.range pE := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        simpa [C, Set.mem_singleton_iff, eq_comm] using hi
      · rintro ⟨i, rfl⟩
        exact Set.mem_iUnion.2 ⟨i, by simp [C]⟩
    have hx :
        (∑ i, a i • pE i) ∈
          {x | ∃ (w : Fin k → ℝ) (x_i : Fin k → EuclideanSpace ℝ (Fin n)),
              (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
                (∀ i, x_i i ∈ euclideanRelativeInterior n (C i)) ∧
                x = ∑ i, w i • x_i i} := by
      refine ⟨a, pE, ha, hsum, ?_, by simp⟩
      intro i
      have hri_singleton :
          euclideanRelativeInterior n (C i) = (C i) := by
        simpa [euclideanRelativelyOpen] using (euclideanRelativelyOpen_singleton n (pE i))
      simp [C, hri_singleton]
    have hx' :
        (∑ i, a i • pE i) ∈ euclideanRelativeInterior n (convexHull ℝ (⋃ i, C i)) := by
      simpa [hri] using hx
    simpa [hUnion] using hx'
  have hxE' :
      e.symm (∑ i, a i • p i) ∈
        euclideanRelativeInterior n (e.symm '' convexHull ℝ (Set.range p)) := by
    simpa [himage, hsumE] using hxE
  exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := convexHull ℝ (Set.range p))
    (x := ∑ i, a i • p i)).2 hxE'

/-- Image of a Minkowski sum under the EuclideanSpace equivalence. -/
lemma euclideanEquiv_symm_image_add {n : ℕ} (C1 C2 : Set (Fin n → ℝ)) :
    ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' (C1 + C2) :
      Set (EuclideanSpace ℝ (Fin n))) =
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' C1 +
        (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' C2 := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    refine ⟨e.symm a, ⟨a, ha, rfl⟩, e.symm b, ⟨b, hb, rfl⟩, ?_⟩
    exact (e.symm.map_add a b).symm
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨a + b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    exact e.symm.map_add a b

/-- Convex cone hull commutes with the EuclideanSpace equivalence. -/
lemma convexConeHull_image_equiv_fin {n : ℕ} (S : Set (Fin n → ℝ)) :
    (ConvexCone.hull ℝ ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' S) :
      Set (EuclideanSpace ℝ (Fin n))) =
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
        (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  simpa using
    (convexCone_hull_image_linearEquiv (e := e.symm.toLinearEquiv) (D := S)).symm

/-- Relative interior of a convex cone in `Fin n → ℝ`. -/
lemma euclideanRelativeInterior_fin_convexConeGenerated_eq_smul {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCconv : Convex ℝ C) (hCne : C.Nonempty) :
    euclideanRelativeInterior_fin n (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) =
      {v | ∃ r : ℝ, 0 < r ∧ ∃ x : Fin n → ℝ,
          x ∈ euclideanRelativeInterior_fin n C ∧ v = r • x} := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  ext v
  constructor
  · intro hv
    have hvE :
        e.symm v ∈ euclideanRelativeInterior n (e.symm '' (ConvexCone.hull ℝ C : Set (Fin n → ℝ))) :=
      (mem_euclideanRelativeInterior_fin_iff (n := n)
        (C := (ConvexCone.hull ℝ C : Set (Fin n → ℝ))) (x := v)).1 hv
    have hvE' :
        e.symm v ∈ euclideanRelativeInterior n (ConvexCone.hull ℝ (e.symm '' C) :
          Set (EuclideanSpace ℝ (Fin n))) := by
      have hcone_eq := (convexConeHull_image_equiv_fin (n := n) (S := C)).symm
      have hvE' := hvE
      rw [hcone_eq] at hvE'
      exact hvE'
    have hCconv' : Convex ℝ (e.symm '' C) :=
      Convex.affine_image (f := e.symm.toAffineMap) hCconv
    have hCne' : (e.symm '' C).Nonempty := by
      rcases hCne with ⟨x, hx⟩
      exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
    have hvE'' :
        e.symm v ∈ {v | ∃ r : ℝ, 0 < r ∧ ∃ x ∈ euclideanRelativeInterior n (e.symm '' C),
          v = r • x} := by
      have hriEq :
          euclideanRelativeInterior n (ConvexCone.hull ℝ (e.symm '' C) :
            Set (EuclideanSpace ℝ (Fin n))) =
            {v | ∃ r : ℝ, 0 < r ∧ ∃ x ∈ euclideanRelativeInterior n (e.symm '' C),
              v = r • x} :=
        euclideanRelativeInterior_convexConeGenerated_eq_smul (n := n) (C := e.symm '' C)
          hCconv' hCne'
      have hvE'' := hvE'
      rw [hriEq] at hvE''
      exact hvE''
    rcases hvE'' with ⟨r, hr, x, hxri, hxEq⟩
    have hxri' : e x ∈ euclideanRelativeInterior_fin n C := ⟨x, hxri, rfl⟩
    have hvEq : v = r • e x := by
      have hEq : e (e.symm v) = e (r • x) := by
        simp [hxEq]
      have hEq' := hEq
      simp [e.map_smul] at hEq'
      exact hEq'
    exact ⟨r, hr, e x, hxri', by simp [hvEq]⟩
  · rintro ⟨r, hr, x, hxri, rfl⟩
    have hxriE :
        e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hxri
    have hCconv' : Convex ℝ (e.symm '' C) :=
      Convex.affine_image (f := e.symm.toAffineMap) hCconv
    have hCne' : (e.symm '' C).Nonempty := by
      rcases hCne with ⟨x', hx'⟩
      exact ⟨e.symm x', ⟨x', hx', rfl⟩⟩
    have hxE :
        r • e.symm x ∈
          euclideanRelativeInterior n (ConvexCone.hull ℝ (e.symm '' C) :
            Set (EuclideanSpace ℝ (Fin n))) := by
      have hxE' :
          r • e.symm x ∈ {v | ∃ r : ℝ, 0 < r ∧ ∃ x ∈ euclideanRelativeInterior n (e.symm '' C),
            v = r • x} := by
        exact ⟨r, hr, e.symm x, hxriE, rfl⟩
      have hriEq :
          euclideanRelativeInterior n (ConvexCone.hull ℝ (e.symm '' C) :
            Set (EuclideanSpace ℝ (Fin n))) =
            {v | ∃ r : ℝ, 0 < r ∧ ∃ x ∈ euclideanRelativeInterior n (e.symm '' C),
              v = r • x} :=
        euclideanRelativeInterior_convexConeGenerated_eq_smul (n := n) (C := e.symm '' C)
          hCconv' hCne'
      have hxE'' := hxE'
      rw [← hriEq] at hxE''
      exact hxE''
    have hxE' :
        r • e.symm x ∈ euclideanRelativeInterior n (e.symm '' (ConvexCone.hull ℝ C :
          Set (Fin n → ℝ))) := by
      have hxE' := hxE
      rw [convexConeHull_image_equiv_fin (n := n) (S := C)] at hxE'
      exact hxE'
    exact
      (mem_euclideanRelativeInterior_fin_iff (n := n)
        (C := (ConvexCone.hull ℝ C : Set (Fin n → ℝ))) (x := r • x)).2 hxE'

/-- Relative interior of a Minkowski sum in `Fin n → ℝ`. -/
lemma euclideanRelativeInterior_fin_add_eq_and_closure_add_superset {n : ℕ}
    {C1 C2 : Set (Fin n → ℝ)} (hC1 : Convex ℝ C1) (hC2 : Convex ℝ C2) :
    euclideanRelativeInterior_fin n (C1 + C2) =
      euclideanRelativeInterior_fin n C1 + euclideanRelativeInterior_fin n C2 := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  ext x
  constructor
  · intro hx
    have hxE :
        e.symm x ∈ euclideanRelativeInterior n (e.symm '' (C1 + C2)) :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C1 + C2) (x := x)).1 hx
    have hxE' :
        e.symm x ∈ euclideanRelativeInterior n (e.symm '' C1 + e.symm '' C2) := by
      have hxE' := hxE
      rw [euclideanEquiv_symm_image_add (n := n) (C1 := C1) (C2 := C2)] at hxE'
      exact hxE'
    have hC1' : Convex ℝ (e.symm '' C1) :=
      Convex.affine_image (f := e.symm.toAffineMap) hC1
    have hC2' : Convex ℝ (e.symm '' C2) :=
      Convex.affine_image (f := e.symm.toAffineMap) hC2
    have hri_add :
        euclideanRelativeInterior n (e.symm '' C1 + e.symm '' C2) =
          euclideanRelativeInterior n (e.symm '' C1) + euclideanRelativeInterior n (e.symm '' C2) :=
      (euclideanRelativeInterior_add_eq_and_closure_add_superset (n := n)
        (C1 := e.symm '' C1) (C2 := e.symm '' C2) hC1' hC2').1
    have hxE'' :
        e.symm x ∈ euclideanRelativeInterior n (e.symm '' C1) +
          euclideanRelativeInterior n (e.symm '' C2) := by
      have hxE'' := hxE'
      simp [hri_add] at hxE''
      exact hxE''
    rcases hxE'' with ⟨u, hu, v, hv, hsum⟩
    have hu' : e u ∈ euclideanRelativeInterior_fin n C1 := ⟨u, hu, rfl⟩
    have hv' : e v ∈ euclideanRelativeInterior_fin n C2 := ⟨v, hv, rfl⟩
    have hxsum : x = e u + e v := by
      have hEq : e (e.symm x) = e (u + v) := by
        simp [hsum]
      have hEq' := hEq
      simp [e.map_add] at hEq'
      exact hEq'
    refine ⟨e u, hu', e v, hv', ?_⟩
    simp [hxsum]
  · rintro ⟨x1, hx1, x2, hx2, rfl⟩
    have hx1' :
        e.symm x1 ∈ euclideanRelativeInterior n (e.symm '' C1) :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C1) (x := x1)).1 hx1
    have hx2' :
        e.symm x2 ∈ euclideanRelativeInterior n (e.symm '' C2) :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C2) (x := x2)).1 hx2
    have hC1' : Convex ℝ (e.symm '' C1) :=
      Convex.affine_image (f := e.symm.toAffineMap) hC1
    have hC2' : Convex ℝ (e.symm '' C2) :=
      Convex.affine_image (f := e.symm.toAffineMap) hC2
    have hri_add :
        euclideanRelativeInterior n (e.symm '' C1 + e.symm '' C2) =
          euclideanRelativeInterior n (e.symm '' C1) + euclideanRelativeInterior n (e.symm '' C2) :=
      (euclideanRelativeInterior_add_eq_and_closure_add_superset (n := n)
        (C1 := e.symm '' C1) (C2 := e.symm '' C2) hC1' hC2').1
    have hxE :
        e.symm (x1 + x2) ∈ euclideanRelativeInterior n (e.symm '' C1 + e.symm '' C2) := by
      have hxE' :
          e.symm x1 + e.symm x2 ∈
            euclideanRelativeInterior n (e.symm '' C1) +
              euclideanRelativeInterior n (e.symm '' C2) :=
        Set.add_mem_add hx1' hx2'
      have hxE'' :
          e.symm x1 + e.symm x2 ∈ euclideanRelativeInterior n (e.symm '' C1 + e.symm '' C2) := by
        have hxE'' := hxE'
        rw [← hri_add] at hxE''
        exact hxE''
      have hxE''' :
          e.symm (x1 + x2) ∈ euclideanRelativeInterior n (e.symm '' C1 + e.symm '' C2) := by
        convert hxE'' using 1
      exact hxE'''
    have hxE' :
        e.symm (x1 + x2) ∈ euclideanRelativeInterior n (e.symm '' (C1 + C2)) := by
      rw [euclideanEquiv_symm_image_add (n := n) (C1 := C1) (C2 := C2)]
      exact hxE
    exact
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C1 + C2) (x := x1 + x2)).2 hxE'

/-- The convex cone hull of a convex hull equals the convex cone hull of the set. -/
lemma convexConeHull_convexHull_eq {n : ℕ} (S : Set (Fin n → ℝ)) :
    (ConvexCone.hull ℝ (convexHull ℝ S) : Set (Fin n → ℝ)) =
      (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  ·
    have hsubset : convexHull ℝ S ⊆ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
      have hconv : Convex ℝ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
        simpa using (ConvexCone.convex (C := ConvexCone.hull ℝ S))
      have hS : S ⊆ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
        intro x hx
        exact (ConvexCone.subset_hull (R := ℝ) (s := S) hx)
      exact convexHull_min hS hconv
    have hcone :
        ConvexCone.hull ℝ (convexHull ℝ S) ≤ ConvexCone.hull ℝ S :=
      ConvexCone.hull_min (R := ℝ) (s := convexHull ℝ S) (C := ConvexCone.hull ℝ S) hsubset
    simpa [SetLike.coe_subset_coe] using hcone
  ·
    have hsubset : S ⊆ (ConvexCone.hull ℝ (convexHull ℝ S) : Set (Fin n → ℝ)) := by
      intro x hx
      have hx' : x ∈ convexHull ℝ S := (subset_convexHull (𝕜 := ℝ) (s := S)) hx
      exact (ConvexCone.subset_hull (R := ℝ) (s := convexHull ℝ S) hx')
    have hcone :
        ConvexCone.hull ℝ S ≤ ConvexCone.hull ℝ (convexHull ℝ S) :=
      ConvexCone.hull_min (R := ℝ) (s := S) (C := ConvexCone.hull ℝ (convexHull ℝ S)) hsubset
    simpa [SetLike.coe_subset_coe] using hcone

/-- A strictly positive linear combination of directions lies in the relative interior of the cone. -/
lemma mem_euclideanRelativeInterior_cone_of_strict_positive_combination {n m : ℕ}
    (d : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (hb : ∀ j, 0 < b j) :
    (∑ j, b j • d j) ∈ euclideanRelativeInterior_fin n (cone n (Set.range d)) := by
  classical
  by_cases hm : m = 0
  · subst hm
    have hrange : (Set.range d) = (∅ : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨j, _⟩
        exact (Fin.elim0 j)
      · intro hx
        exact (Set.notMem_empty x hx).elim
    have hcone : cone n (Set.range d) = ({0} : Set (Fin n → ℝ)) := by
      calc
        cone n (Set.range d) = convexConeGenerated n (Set.range d) := by
          simpa using (cone_eq_convexConeGenerated (n := n) (S₁ := Set.range d))
        _ = ({0} : Set (Fin n → ℝ)) := by
          simp [hrange, convexConeGenerated_empty]
    have hcone0 : cone n (∅ : Set (Fin n → ℝ)) = ({0} : Set (Fin n → ℝ)) := by
      simpa [hrange] using hcone
    simp [hcone0, euclideanRelativeInterior_fin_singleton]
  ·
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let j0 : Fin m := ⟨0, hmpos⟩
    have hdenpos : 0 < ∑ j, b j := by
      have hnonneg : ∀ j, 0 ≤ b j := fun j => le_of_lt (hb j)
      have hsum_ge :
          b j0 ≤ ∑ j, b j := by
        exact
          Finset.single_le_sum (f := fun j => b j) (s := (Finset.univ : Finset (Fin m)))
            (fun j _ => hnonneg j) (by simp [j0])
      exact lt_of_lt_of_le (hb j0) hsum_ge
    set den : ℝ := ∑ j, b j
    have hdenne : den ≠ 0 := ne_of_gt hdenpos
    let w : Fin m → ℝ := fun j => b j / den
    have hwpos : ∀ j, 0 < w j := by
      intro j
      exact div_pos (hb j) hdenpos
    have hsumw : ∑ j, w j = 1 := by
      calc
        ∑ j, w j = ∑ j, b j / den := by rfl
        _ = ∑ j, b j * (1 / den) := by
            simp [div_eq_mul_inv]
        _ = (∑ j, b j) * (1 / den) := by
            symm
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Fin m)))
                (f := fun j => b j) (a := (1 / den)))
        _ = den * (1 / den) := by
            simp [den]
        _ = 1 := by
            field_simp [hdenne]
    let x0 : Fin n → ℝ := ∑ j, w j • d j
    have hx0ri :
        x0 ∈ euclideanRelativeInterior_fin n (convexHull ℝ (Set.range d)) := by
      simpa [x0] using
        (mem_euclideanRelativeInterior_convexHull_of_strict_combination (n := n) (k := m)
          (p := d) (a := w) hwpos hsumw)
    have hCconv : Convex ℝ (convexHull ℝ (Set.range d)) := by
      exact (convex_convexHull (𝕜 := ℝ) (s := Set.range d))
    have hCne : (convexHull ℝ (Set.range d)).Nonempty := by
      refine ⟨d j0, ?_⟩
      exact (subset_convexHull (𝕜 := ℝ) (s := Set.range d)) ⟨j0, rfl⟩
    have hri_eq :
        euclideanRelativeInterior_fin n
            (ConvexCone.hull ℝ (convexHull ℝ (Set.range d)) : Set (Fin n → ℝ)) =
          {v | ∃ r : ℝ, 0 < r ∧ ∃ x : Fin n → ℝ,
              x ∈ euclideanRelativeInterior_fin n (convexHull ℝ (Set.range d)) ∧ v = r • x} := by
      exact
        (euclideanRelativeInterior_fin_convexConeGenerated_eq_smul (n := n)
          (C := convexHull ℝ (Set.range d)) hCconv hCne)
    have hsmul : den • x0 = ∑ j, b j • d j := by
      calc
        den • x0 = ∑ j, den • (w j • d j) := by
          simp [x0, Finset.smul_sum]
        _ = ∑ j, (den * w j) • d j := by
          simp [smul_smul]
        _ = ∑ j, b j • d j := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          have hmul : den * (b j / den) = b j := by
            field_simp [hdenne]
          simp [w, hmul]
    have hmem :
        (∑ j, b j • d j) ∈
          {v | ∃ r : ℝ, 0 < r ∧ ∃ x : Fin n → ℝ,
              x ∈ euclideanRelativeInterior_fin n (convexHull ℝ (Set.range d)) ∧ v = r • x} := by
      refine ⟨den, hdenpos, x0, hx0ri, ?_⟩
      exact hsmul.symm
    let K : Set (Fin n → ℝ) := (ConvexCone.hull ℝ (Set.range d) : Set (Fin n → ℝ))
    have hhull :
        (ConvexCone.hull ℝ (convexHull ℝ (Set.range d)) : Set (Fin n → ℝ)) = K := by
      simpa [K] using (convexConeHull_convexHull_eq (n := n) (S := Set.range d))
    have hmem' :
        (∑ j, b j • d j) ∈ euclideanRelativeInterior_fin n K := by
      have hmem' :
          (∑ j, b j • d j) ∈
            euclideanRelativeInterior_fin n
              (ConvexCone.hull ℝ (convexHull ℝ (Set.range d)) : Set (Fin n → ℝ)) := by
        simpa [hri_eq] using hmem
      simpa [hhull] using hmem'
    have hri_cone_eq : euclideanRelativeInterior_fin n (cone n (Set.range d)) =
        euclideanRelativeInterior_fin n K := by
      classical
      let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
      have hconv_cone : Convex ℝ (cone n (Set.range d)) := by
        simpa [cone, conv] using
          (convex_convexHull (𝕜 := ℝ) (s := ray n (Set.range d)))
      have hconvK : Convex ℝ K := by
        simpa [K] using (ConvexCone.convex (C := ConvexCone.hull ℝ (Set.range d)))
      have hKne : K.Nonempty := by
        refine ⟨d j0, ?_⟩
        exact (ConvexCone.subset_hull (R := ℝ) (s := Set.range d) ⟨j0, rfl⟩)
      have h0cl : (0 : Fin n → ℝ) ∈ closure K := by
        rcases hKne with ⟨x, hxK⟩
        by_cases hx0 : x = 0
        · subst hx0
          exact subset_closure hxK
        ·
          refine Metric.mem_closure_iff.2 ?_
          intro ε hε
          have hnormpos : 0 < ‖x‖ := by
            simpa using (norm_pos_iff.mpr hx0)
          have hnormne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hnormpos
          let t : ℝ := ε / (2 * ‖x‖)
          have htpos : 0 < t := by
            have hdenpos : 0 < (2 * ‖x‖) := by nlinarith [hnormpos]
            exact div_pos hε hdenpos
          have htmem : t • x ∈ K := by
            simpa [K] using
              (ConvexCone.smul_mem (C := ConvexCone.hull ℝ (Set.range d)) htpos hxK)
          refine ⟨t • x, htmem, ?_⟩
          have hnorm : ‖t • x‖ = ε / 2 := by
            calc
              ‖t • x‖ = ‖t‖ * ‖x‖ := by simpa using (norm_smul t x)
              _ = t * ‖x‖ := by
                have htabs : ‖t‖ = t := by
                  simp [Real.norm_eq_abs, abs_of_pos htpos]
                simp [htabs]
              _ = ε / 2 := by
                have hcalc : t * ‖x‖ * 2 = ε := by
                  dsimp [t]
                  field_simp [hnormne, mul_comm, mul_left_comm, mul_assoc]
                linarith
          have hhalf : ε / 2 < ε := by linarith [hε]
          simpa [dist_eq_norm, hnorm] using hhalf
      have hcone_set :
          cone n (Set.range d) = Set.insert (0 : Fin n → ℝ) K := by
        have hcone_eq' := cone_eq_convexConeGenerated (n := n) (S₁ := Set.range d)
        simpa [K, convexConeGenerated] using hcone_eq'
      have hKsub : K ⊆ cone n (Set.range d) := by
        simpa [K] using
          (cone_eq_convexConeGenerated_aux_hull_subset_cone (n := n) (S₁ := Set.range d))
      have hcone_sub : cone n (Set.range d) ⊆ closure K := by
        intro x hx
        have hx' : x ∈ Set.insert (0 : Fin n → ℝ) K := by
          simpa [hcone_set] using hx
        rcases hx' with rfl | hxK
        · exact h0cl
        · exact subset_closure hxK
      have hclosure_eq : closure (cone n (Set.range d)) = closure K := by
        refine Set.Subset.antisymm ?_ ?_
        ·
          have hcl := closure_mono hcone_sub
          simpa [closure_closure] using hcl
        · exact closure_mono hKsub
      have hconv_cone_E : Convex ℝ (e.symm '' cone n (Set.range d)) :=
        Convex.affine_image (f := e.symm.toAffineMap) hconv_cone
      have hconvK_E : Convex ℝ (e.symm '' K) :=
        Convex.affine_image (f := e.symm.toAffineMap) hconvK
      have hclosure_eq_E :
          closure (e.symm '' cone n (Set.range d)) = closure (e.symm '' K) := by
        calc
          closure (e.symm '' cone n (Set.range d)) =
              e.symm '' closure (cone n (Set.range d)) := by
                symm
                simpa using
                  (Homeomorph.image_closure (h := e.symm.toHomeomorph)
                    (s := cone n (Set.range d)))
          _ = e.symm '' closure K := by
                simp [hclosure_eq]
          _ = closure (e.symm '' K) := by
                simpa using (Homeomorph.image_closure (h := e.symm.toHomeomorph) (s := K))
      have hri_cone_E :
          euclideanRelativeInterior n (e.symm '' cone n (Set.range d)) =
            euclideanRelativeInterior n (closure (e.symm '' cone n (Set.range d))) := by
        symm
        exact
          (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n
              (e.symm '' cone n (Set.range d)) hconv_cone_E).2
      have hri_K_E :
          euclideanRelativeInterior n (e.symm '' K) =
            euclideanRelativeInterior n (closure (e.symm '' K)) := by
        symm
        exact
          (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n
              (e.symm '' K) hconvK_E).2
      ext v
      constructor
      · intro hv
        have hvE :
            e.symm v ∈ euclideanRelativeInterior n (e.symm '' cone n (Set.range d)) :=
          (mem_euclideanRelativeInterior_fin_iff (n := n)
            (C := cone n (Set.range d)) (x := v)).1 hv
        have hvE' :
            e.symm v ∈ euclideanRelativeInterior n (e.symm '' K) := by
          have hvE'' : e.symm v ∈ euclideanRelativeInterior n (closure (e.symm '' K)) := by
            have hvE'' :
                e.symm v ∈ euclideanRelativeInterior n (closure (e.symm '' cone n (Set.range d))) := by
              simpa [hri_cone_E] using hvE
            simpa [hclosure_eq_E] using hvE''
          simpa [hri_K_E] using hvE''
        exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := K) (x := v)).2 hvE'
      · intro hv
        have hvE :
            e.symm v ∈ euclideanRelativeInterior n (e.symm '' K) :=
          (mem_euclideanRelativeInterior_fin_iff (n := n) (C := K) (x := v)).1 hv
        have hvE' :
            e.symm v ∈ euclideanRelativeInterior n (e.symm '' cone n (Set.range d)) := by
          have hvE'' : e.symm v ∈ euclideanRelativeInterior n (closure (e.symm '' K)) := by
            simpa [hri_K_E] using hvE
          have hvE''' :
              e.symm v ∈ euclideanRelativeInterior n (closure (e.symm '' cone n (Set.range d))) := by
            simpa [hclosure_eq_E] using hvE''
          simpa [hri_cone_E] using hvE'''
        exact
          (mem_euclideanRelativeInterior_fin_iff (n := n)
            (C := cone n (Set.range d)) (x := v)).2 hvE'
    simpa [hri_cone_eq] using hmem'

end Section18
end Chap04
