/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part9

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise
open scoped InnerProductSpace

/-- Remove both closures under the `ri` hypothesis and record attainment. -/
lemma section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain_proof_step
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :
    (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) ∧
      ∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
  classical
  have hsum :
      (fun x => ∑ i, convexFunctionClosure (f i) x) =
        convexFunctionClosure (fun x => ∑ i, f i x) :=
    section16_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_of_nonempty_iInter_ri_effectiveDomain
      (f := f) hf hri
  have hEq0 :
      fenchelConjugate n (convexFunctionClosure (fun x => ∑ i, f i x)) =
        convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := by
    simpa [hsum] using
      (section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily
        (f := f) hf)
  have hEq1 :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := by
    calc
      fenchelConjugate n (fun x => ∑ i, f i x) =
          fenchelConjugate n (convexFunctionClosure (fun x => ∑ i, f i x)) := by
            symm
            simpa using
              (section16_fenchelConjugate_convexFunctionClosure_eq
                (n := n) (g := fun x => ∑ i, f i x))
      _ = convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := hEq0
  have hclosed_att :
      (convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) =
          infimalConvolutionFamily fun i => fenchelConjugate n (f i)) ∧
        ∀ xStar : Fin n → ℝ,
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
            ∃ xStarFamily : Fin m → Fin n → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                  infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar :=
    section16_infimalConvolutionFamily_fenchelConjugate_closed_and_attained_of_nonempty_iInter_ri
      (f := f) hf hri
  have hEq2 :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) := by
    simpa [hclosed_att.1] using hEq1
  exact ⟨hEq2, hclosed_att.2⟩

/-- Theorem 16.4.3 (sum vs infimal convolution without closures). -/
theorem section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :
    (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) ∧
      ∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
  simpa using
    (section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain_proof_step
      (f := f) hf hri)

/-- If `a + t * b ≤ 0` for all positive `t`, then `a ≤ 0`. -/
lemma section16_le_zero_of_forall_pos_add_mul_le {a b : ℝ}
    (h : ∀ t : ℝ, 0 < t → a + t * b ≤ 0) : a ≤ 0 := by
  by_contra ha
  have ha' : 0 < a := lt_of_not_ge ha
  obtain ⟨t, ht_pos, hlt⟩ := exists_pos_mul_lt ha' (|b|)
  have hlt' : |t * b| < a := by
    have habs : |t * b| = |b| * t := by
      calc
        |t * b| = |b * t| := by simp [mul_comm]
        _ = |b| * |t| := by simp
        _ = |b| * t := by simp [abs_of_nonneg (le_of_lt ht_pos)]
    simpa [habs] using hlt
  have hneg : -a < t * b := (abs_lt.mp hlt').1
  have hpos : 0 < a + t * b := by linarith
  exact (not_lt_of_ge (h t ht_pos)) hpos

/-- The intersection of the polars is contained in the polar of the sum. -/
lemma section16_iInter_polar_subset_polar_sum {n m : Nat}
    (K : Fin m → ConvexCone ℝ (Fin n → ℝ)) :
    (⋂ i : Fin m,
        {xStar : Fin n → ℝ | ∀ x ∈ (K i : Set (Fin n → ℝ)), (dotProduct x xStar : ℝ) ≤ 0}) ⊆
      {xStar : Fin n → ℝ |
        ∀ x ∈ (∑ i, (K i : Set (Fin n → ℝ))),
          (dotProduct x xStar : ℝ) ≤ 0} := by
  classical
  intro xStar hxStar
  refine Set.mem_setOf.2 ?_
  intro x hxsum
  rcases (Set.mem_fintype_sum (f := fun i => (K i : Set (Fin n → ℝ))) (a := x)).1 hxsum with
    ⟨g, hg, rfl⟩
  have hdot : dotProduct (∑ i, g i) xStar = ∑ i, dotProduct (g i) xStar := by
    simpa using (sum_dotProduct (s := Finset.univ) (u := g) (v := xStar))
  have hneg : ∀ i, dotProduct (g i) xStar ≤ 0 := by
    intro i
    exact (Set.mem_setOf.mp ((Set.mem_iInter.mp hxStar) i)) (g i) (hg i)
  have hsum : (∑ i, dotProduct (g i) xStar) ≤ (0 : ℝ) := by
    classical
    have hsum' : (∑ i, dotProduct (g i) xStar) ≤ ∑ i : Fin m, (0 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hneg i
    simpa using hsum'
  simpa [hdot] using hsum

/-- The polar of the sum is contained in the intersection of the polars. -/
lemma section16_polar_sum_subset_iInter_polar {n m : Nat}
    (K : Fin m → ConvexCone ℝ (Fin n → ℝ))
    (hKne : ∀ i, (K i : Set (Fin n → ℝ)).Nonempty) :
    {xStar : Fin n → ℝ |
        ∀ x ∈ (∑ i, (K i : Set (Fin n → ℝ))),
          (dotProduct x xStar : ℝ) ≤ 0} ⊆
      ⋂ i : Fin m,
        {xStar : Fin n → ℝ | ∀ x ∈ (K i : Set (Fin n → ℝ)), (dotProduct x xStar : ℝ) ≤ 0} := by
  classical
  intro xStar hxStar
  refine Set.mem_iInter.2 ?_
  intro i
  refine Set.mem_setOf.2 ?_
  intro x hx
  classical
  choose y hy using hKne
  let b : ℝ := ∑ j ∈ (Finset.univ.erase i), dotProduct (y j) xStar
  have hmain : ∀ t : ℝ, 0 < t → dotProduct x xStar + t * b ≤ 0 := by
    intro t ht
    let g : Fin m → Fin n → ℝ := fun j => if j = i then x else t • y j
    have hg : ∀ j, g j ∈ (K j : Set (Fin n → ℝ)) := by
      intro j
      by_cases hji : j = i
      · subst hji
        simpa [g] using hx
      · have : t • y j ∈ (K j : Set (Fin n → ℝ)) := (K j).smul_mem ht (hy j)
        simpa [g, hji] using this
    have hsum_mem : (∑ j, g j) ∈ ∑ j, (K j : Set (Fin n → ℝ)) := by
      refine (Set.mem_fintype_sum (f := fun j => (K j : Set (Fin n → ℝ))) (a := ∑ j, g j)).2 ?_
      refine ⟨g, ?_, rfl⟩
      intro j
      exact hg j
    have hle := hxStar (∑ j, g j) hsum_mem
    have hdot : dotProduct (∑ j, g j) xStar = ∑ j, dotProduct (g j) xStar := by
      simpa using (sum_dotProduct (s := Finset.univ) (u := g) (v := xStar))
    have hsum_erase :
        ∑ j ∈ Finset.univ.erase i, dotProduct (g j) xStar = t * b := by
      have hsum_erase' :
          ∑ j ∈ Finset.univ.erase i, dotProduct (g j) xStar =
            ∑ j ∈ Finset.univ.erase i, t * dotProduct (y j) xStar := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [g, hji, smul_dotProduct, smul_eq_mul]
      have hsum_erase'' :
          ∑ j ∈ Finset.univ.erase i, t * dotProduct (y j) xStar =
            t * ∑ j ∈ Finset.univ.erase i, dotProduct (y j) xStar := by
        symm
        simpa using
          (Finset.mul_sum (s := Finset.univ.erase i)
            (f := fun j => dotProduct (y j) xStar) (a := t))
      have hsum_erase''' :
          ∑ j ∈ Finset.univ.erase i, dotProduct (g j) xStar =
            t * ∑ j ∈ Finset.univ.erase i, dotProduct (y j) xStar := by
        exact hsum_erase'.trans hsum_erase''
      simpa [b] using hsum_erase'''
    have hsum :
        ∑ j, dotProduct (g j) xStar = dotProduct x xStar + t * b := by
      have hsplit :
          ∑ j, dotProduct (g j) xStar =
            dotProduct (g i) xStar + ∑ j ∈ Finset.univ.erase i, dotProduct (g j) xStar := by
        exact
          (Finset.add_sum_erase (s := Finset.univ)
            (f := fun j => dotProduct (g j) xStar) (Finset.mem_univ i)).symm
      calc
        ∑ j, dotProduct (g j) xStar
            = dotProduct (g i) xStar + ∑ j ∈ Finset.univ.erase i, dotProduct (g j) xStar := hsplit
        _ = dotProduct x xStar + ∑ j ∈ Finset.univ.erase i, dotProduct (g j) xStar := by
            simp [g]
        _ = dotProduct x xStar + t * b := by
            simp [hsum_erase]
    have hle' : ∑ j, dotProduct (g j) xStar ≤ 0 := by
      simpa [hdot] using hle
    have hle'' : dotProduct x xStar + t * b ≤ 0 := by
      simpa [hsum] using hle'
    exact hle''
  exact section16_le_zero_of_forall_pos_add_mul_le (a := dotProduct x xStar) (b := b) hmain

/-- Corollary 16.4.2.1: Let `K₁, …, Kₘ` be non-empty convex cones in `ℝⁿ`. Then the polar cone of
their Minkowski sum is the intersection of their polar cones:

`(K₁ + ⋯ + Kₘ)^∘ = K₁^∘ ∩ ⋯ ∩ Kₘ^∘`. -/
theorem section16_polar_sum_convexCones {n m : Nat} (K : Fin m → ConvexCone ℝ (Fin n → ℝ))
    (hKne : ∀ i, (K i : Set (Fin n → ℝ)).Nonempty) :
    {xStar : Fin n → ℝ |
        ∀ x ∈ (∑ i, (K i : Set (Fin n → ℝ))),
          (dotProduct x xStar : ℝ) ≤ 0} =
      ⋂ i : Fin m,
        {xStar : Fin n → ℝ | ∀ x ∈ (K i : Set (Fin n → ℝ)), (dotProduct x xStar : ℝ) ≤ 0} := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · exact section16_polar_sum_subset_iInter_polar (K := K) hKne
  · exact section16_iInter_polar_subset_polar_sum (K := K)

/-- Negating a set flips the inner dual cone. -/
lemma section16_innerDual_neg_eq_neg_innerDual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (s : Set H) :
    (ProperCone.innerDual (E := H) (-s) : Set H) =
      -(ProperCone.innerDual (E := H) s : Set H) := by
  classical
  ext y
  constructor
  · intro hy
    change -y ∈ (ProperCone.innerDual (E := H) s : Set H)
    refine (ProperCone.mem_innerDual (E := H) (s := s) (y := -y)).2 ?_
    intro x hx
    have hx' : (-x) ∈ (-s : Set H) := by
      simpa using hx
    have hinner :
        0 ≤ ⟪-x, y⟫_ℝ :=
      (ProperCone.mem_innerDual (E := H) (s := -s) (y := y)).1 hy hx'
    simpa [inner_neg_left, inner_neg_right] using hinner
  · intro hy
    have hy' : -y ∈ (ProperCone.innerDual (E := H) s : Set H) := by
      simpa using hy
    refine (ProperCone.mem_innerDual (E := H) (s := -s) (y := y)).2 ?_
    intro x hx
    have hx' : (-x) ∈ s := by
      simpa using hx
    have hinner :
        0 ≤ ⟪-x, -y⟫_ℝ :=
      (ProperCone.mem_innerDual (E := H) (s := s) (y := -y)).1 hy' hx'
    simpa [inner_neg_left, inner_neg_right] using hinner

/-- The inner-product polar set is the negation of the inner dual cone. -/
lemma section16_inner_polar_eq_neg_innerDual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (s : Set H) :
    {y : H | ∀ x ∈ s, ⟪x, y⟫_ℝ ≤ 0} =
      -(ProperCone.innerDual (E := H) s : Set H) := by
  classical
  ext y
  constructor
  · intro hy
    change -y ∈ (ProperCone.innerDual (E := H) s : Set H)
    refine (ProperCone.mem_innerDual (E := H) (s := s) (y := -y)).2 ?_
    intro x hx
    have hxy : ⟪x, y⟫_ℝ ≤ 0 := hy x hx
    have : 0 ≤ -⟪x, y⟫_ℝ := (neg_nonneg).2 hxy
    simpa [inner_neg_right] using this
  · intro hy
    have hy' : -y ∈ (ProperCone.innerDual (E := H) s : Set H) := by
      simpa using hy
    intro x hx
    have hxy : 0 ≤ ⟪x, -y⟫_ℝ :=
      (ProperCone.mem_innerDual (E := H) (s := s) (y := -y)).1 hy' hx
    have : 0 ≤ -⟪x, y⟫_ℝ := by
      simpa [inner_neg_right] using hxy
    exact (neg_nonneg).1 this

/-- The double inner-product polar of a convex cone is its closure. -/
lemma section16_inner_polar_polar_eq_closure_convexCone {n : Nat}
    (K : ConvexCone ℝ (EuclideanSpace ℝ (Fin n)))
    (hKne : (K : Set (EuclideanSpace ℝ (Fin n))).Nonempty) :
    {xStar : EuclideanSpace ℝ (Fin n) |
        ∀ x ∈
          {z : EuclideanSpace ℝ (Fin n) |
            ∀ x ∈ (K : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0},
          ⟪x, xStar⟫_ℝ ≤ 0} =
      closure (K : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  have h0 :
      (0 : EuclideanSpace ℝ (Fin n)) ∈ closure (K : Set (EuclideanSpace ℝ (Fin n))) := by
    refine
      zero_mem_closure_of_pos_smul_closed
        (K := (K : Set (EuclideanSpace ℝ (Fin n)))) hKne ?_
    intro x hx t ht
    exact (K.smul_mem ht hx)
  have hsubset :
      Set.insert (0 : EuclideanSpace ℝ (Fin n))
          (K : Set (EuclideanSpace ℝ (Fin n))) ⊆
        (K.closure : Set (EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · simpa [ConvexCone.coe_closure] using h0
    · simpa [ConvexCone.coe_closure] using subset_closure hx
  have hHull_subset :
      ((ConvexCone.hull ℝ
            (Set.insert (0 : EuclideanSpace ℝ (Fin n))
              (K : Set (EuclideanSpace ℝ (Fin n)))) :
          ConvexCone ℝ (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) ⊆
        closure (K : Set (EuclideanSpace ℝ (Fin n))) := by
    have hle :
        (ConvexCone.hull ℝ
            (Set.insert (0 : EuclideanSpace ℝ (Fin n))
              (K : Set (EuclideanSpace ℝ (Fin n)))) :
            ConvexCone ℝ (EuclideanSpace ℝ (Fin n))) ≤
          K.closure :=
      (ConvexCone.hull_le_iff (C := K.closure)
        (s := Set.insert (0 : EuclideanSpace ℝ (Fin n))
          (K : Set (EuclideanSpace ℝ (Fin n))))).2 hsubset
    intro x hx
    have hx' : x ∈ (K.closure : ConvexCone ℝ (EuclideanSpace ℝ (Fin n))) := hle hx
    simpa [ConvexCone.coe_closure] using hx'
  have hK_subset :
      (K : Set (EuclideanSpace ℝ (Fin n))) ⊆
        (ConvexCone.hull ℝ
            (Set.insert (0 : EuclideanSpace ℝ (Fin n))
              (K : Set (EuclideanSpace ℝ (Fin n)))) :
            ConvexCone ℝ (EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    refine
      ConvexCone.subset_hull (R := ℝ)
        (s :=
          Set.insert (0 : EuclideanSpace ℝ (Fin n))
            (K : Set (EuclideanSpace ℝ (Fin n)))) ?_
    exact Set.mem_insert_of_mem (0 : EuclideanSpace ℝ (Fin n)) hx
  have hclosure_eq :
      closure
          ((ConvexCone.hull ℝ
                (Set.insert (0 : EuclideanSpace ℝ (Fin n))
                  (K : Set (EuclideanSpace ℝ (Fin n)))) :
              ConvexCone ℝ (EuclideanSpace ℝ (Fin n))) :
            Set (EuclideanSpace ℝ (Fin n))) =
        closure (K : Set (EuclideanSpace ℝ (Fin n))) := by
    refine Set.Subset.antisymm ?_ ?_
    ·
      have h := closure_mono hHull_subset
      simpa [closure_closure] using h
    · exact closure_mono hK_subset
  have hpolar :
      {z : EuclideanSpace ℝ (Fin n) |
          ∀ x ∈ (K : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0} =
        -(ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
            (K : Set (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) := by
    simpa using
      (section16_inner_polar_eq_neg_innerDual
        (H := EuclideanSpace ℝ (Fin n)) (s := (K : Set (EuclideanSpace ℝ (Fin n)))))
  calc
    {xStar : EuclideanSpace ℝ (Fin n) |
        ∀ x ∈
          {z : EuclideanSpace ℝ (Fin n) |
            ∀ x ∈ (K : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0},
          ⟪x, xStar⟫_ℝ ≤ 0}
        =
      {xStar : EuclideanSpace ℝ (Fin n) |
        ∀ x ∈
          (-(ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
              (K : Set (EuclideanSpace ℝ (Fin n))) :
            Set (EuclideanSpace ℝ (Fin n)))),
          ⟪x, xStar⟫_ℝ ≤ 0} := by
        simp
    _ =
        -(ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
            (-(ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
                (K : Set (EuclideanSpace ℝ (Fin n))) :
              Set (EuclideanSpace ℝ (Fin n))) :
              Set (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) := by
        simpa using
          (section16_inner_polar_eq_neg_innerDual
            (H := EuclideanSpace ℝ (Fin n))
            (s :=
              -(ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
                  (K : Set (EuclideanSpace ℝ (Fin n))) :
                Set (EuclideanSpace ℝ (Fin n)))))
    _ =
        (ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
            (ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
                (K : Set (EuclideanSpace ℝ (Fin n))) :
              Set (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) := by
        simp
          [section16_innerDual_neg_eq_neg_innerDual
            (H := EuclideanSpace ℝ (Fin n))
            (s :=
              (ProperCone.innerDual (E := EuclideanSpace ℝ (Fin n))
                  (K : Set (EuclideanSpace ℝ (Fin n))) :
                Set (EuclideanSpace ℝ (Fin n))))]
    _ = closure (K : Set (EuclideanSpace ℝ (Fin n))) := by
        exact
          (section14_innerDualCone_innerDualCone_eq_closure_coneHull
              (H := EuclideanSpace ℝ (Fin n))
              (s := (K : Set (EuclideanSpace ℝ (Fin n))))).trans hclosure_eq

/-- The dot-product double polar of a convex cone is its closure. -/
lemma section16_polar_polar_eq_closure_convexCone {n : Nat}
    (K : ConvexCone ℝ (Fin n → ℝ)) (hKne : (K : Set (Fin n → ℝ)).Nonempty) :
    {xStar : Fin n → ℝ |
        ∀ x ∈ {z : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x z ≤ 0},
          dotProduct x xStar ≤ 0} =
      closure (K : Set (Fin n → ℝ)) := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  let K' : ConvexCone ℝ (EuclideanSpace ℝ (Fin n)) := K.comap e.toLinearMap
  have hKne' : (K' : Set (EuclideanSpace ℝ (Fin n))).Nonempty := by
    rcases hKne with ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    simpa [K', ConvexCone.coe_comap] using hy
  have hiff :
      ∀ xStar : Fin n → ℝ,
        (xStar ∈
            {xStar : Fin n → ℝ |
              ∀ x ∈
                {z : Fin n → ℝ |
                  ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x z ≤ 0},
                dotProduct x xStar ≤ 0}) ↔
          (e.symm xStar ∈
            {y : EuclideanSpace ℝ (Fin n) |
              ∀ x ∈
                {z : EuclideanSpace ℝ (Fin n) |
                  ∀ x ∈ (K' : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0},
                ⟪x, y⟫_ℝ ≤ 0}) := by
    intro xStar
    constructor
    · intro hx
      have hx' := Set.mem_setOf.mp hx
      refine Set.mem_setOf.2 ?_
      intro x hxmem
      have hxmem' := Set.mem_setOf.mp hxmem
      have hpolar : e x ∈
          {z : Fin n → ℝ |
            ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x z ≤ 0} := by
        refine Set.mem_setOf.2 ?_
        intro y hy
        have hy' : e.symm y ∈ (K' : Set (EuclideanSpace ℝ (Fin n))) := by
          simpa [K', ConvexCone.coe_comap] using hy
        have hinner : ⟪e.symm y, x⟫_ℝ ≤ 0 := hxmem' (e.symm y) hy'
        have hdot :
            dotProduct y (e x) = ⟪e.symm y, x⟫_ℝ := by
          simpa [e.symm_apply_apply] using
            (dotProduct_eq_inner_euclideanSpace (n := n) (x := y) (y := e x))
        simpa [hdot] using hinner
      have hdot : dotProduct (e x) xStar ≤ 0 := hx' (e x) hpolar
      have hinner :
          dotProduct (e x) xStar = ⟪x, e.symm xStar⟫_ℝ := by
        simpa [e.symm_apply_apply] using
          (dotProduct_eq_inner_euclideanSpace (n := n) (x := e x) (y := xStar))
      simpa [hinner] using hdot
    · intro hx
      have hx' := Set.mem_setOf.mp hx
      refine Set.mem_setOf.2 ?_
      intro x hxmem
      have hxmem' := Set.mem_setOf.mp hxmem
      have hpolar : e.symm x ∈
          {z : EuclideanSpace ℝ (Fin n) |
            ∀ x ∈ (K' : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0} := by
        refine Set.mem_setOf.2 ?_
        intro y hy
        have hy' : e y ∈ (K : Set (Fin n → ℝ)) := by
          simpa [K', ConvexCone.coe_comap] using hy
        have hdot : dotProduct (e y) x ≤ 0 := hxmem' (e y) hy'
        have hinner :
            dotProduct (e y) x = ⟪y, e.symm x⟫_ℝ := by
          simpa [e.symm_apply_apply] using
            (dotProduct_eq_inner_euclideanSpace (n := n) (x := e y) (y := x))
        simpa [hinner] using hdot
      have hinner : ⟪e.symm x, e.symm xStar⟫_ℝ ≤ 0 := hx' (e.symm x) hpolar
      have hdot :
          dotProduct x xStar = ⟪e.symm x, e.symm xStar⟫_ℝ := by
        simpa using
          (dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := xStar))
      simpa [hdot] using hinner
  have hinner :
      {y : EuclideanSpace ℝ (Fin n) |
          ∀ x ∈
            {z : EuclideanSpace ℝ (Fin n) |
              ∀ x ∈ (K' : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0},
            ⟪x, y⟫_ℝ ≤ 0} =
        closure (K' : Set (EuclideanSpace ℝ (Fin n))) :=
    section16_inner_polar_polar_eq_closure_convexCone (K := K') hKne'
  have himage :
      e '' (K' : Set (EuclideanSpace ℝ (Fin n))) = (K : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [K', ConvexCone.coe_comap] using hx
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      simpa [K', ConvexCone.coe_comap] using hy
  have hclosure :
      e '' closure (K' : Set (EuclideanSpace ℝ (Fin n))) =
        closure (K : Set (Fin n → ℝ)) := by
    simpa [himage] using
      (Homeomorph.image_closure (h := e.toHomeomorph)
        (s := (K' : Set (EuclideanSpace ℝ (Fin n)))))
  ext xStar
  constructor
  · intro hx
    have hx' :
        e.symm xStar ∈
          {y : EuclideanSpace ℝ (Fin n) |
            ∀ x ∈
              {z : EuclideanSpace ℝ (Fin n) |
                ∀ x ∈ (K' : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0},
              ⟪x, y⟫_ℝ ≤ 0} := (hiff xStar).1 hx
    have hx'' : e.symm xStar ∈ closure (K' : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [← hinner]
      exact hx'
    have hx''' : xStar ∈ e '' closure (K' : Set (EuclideanSpace ℝ (Fin n))) :=
      ⟨e.symm xStar, hx'', by simp⟩
    simpa [hclosure] using hx'''
  · intro hx
    have hx' :
        xStar ∈ e '' closure (K' : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [hclosure] using hx
    rcases hx' with ⟨y, hy, rfl⟩
    have hy' :
        y ∈
          {y : EuclideanSpace ℝ (Fin n) |
            ∀ x ∈
              {z : EuclideanSpace ℝ (Fin n) |
                ∀ x ∈ (K' : Set (EuclideanSpace ℝ (Fin n))), ⟪x, z⟫_ℝ ≤ 0},
              ⟪x, y⟫_ℝ ≤ 0} := by
      rw [hinner]
      exact hy
    exact (hiff (e y)).2 hy'

/-- The polar of the sum of polars is the intersection of the closures. -/
lemma section16_polar_sum_polars_eq_iInter_closure {n m : Nat}
    (K : Fin m → ConvexCone ℝ (Fin n → ℝ)) (hKne : ∀ i, (K i : Set (Fin n → ℝ)).Nonempty) :
    {xStar : Fin n → ℝ |
        ∀ x ∈
          (∑ i : Fin m,
            {xStar : Fin n → ℝ |
              ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}),
          dotProduct x xStar ≤ 0} =
      ⋂ i : Fin m, closure (K i : Set (Fin n → ℝ)) := by
  classical
  let Kpol : Fin m → ConvexCone ℝ (Fin n → ℝ) := fun i =>
    { carrier :=
        {xStar : Fin n → ℝ | ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}
      smul_mem' := by
        intro c hc y hy x hx
        have hy' : dotProduct x y ≤ 0 := hy x hx
        have hmul : c * dotProduct x y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hy'
        simpa [dotProduct_smul, smul_eq_mul] using hmul
      add_mem' := by
        intro y hy z hz x hx
        have hy' : dotProduct x y ≤ 0 := hy x hx
        have hz' : dotProduct x z ≤ 0 := hz x hx
        have hsum : dotProduct x y + dotProduct x z ≤ 0 := add_nonpos hy' hz'
        simpa [dotProduct_add] using hsum }
  have hKpolne : ∀ i, (Kpol i : Set (Fin n → ℝ)).Nonempty := by
    intro i
    refine ⟨0, ?_⟩
    intro x hx
    simp
  have hsum :
      {xStar : Fin n → ℝ |
          ∀ x ∈ (∑ i, (Kpol i : Set (Fin n → ℝ))), dotProduct x xStar ≤ 0} =
        ⋂ i : Fin m,
          {xStar : Fin n → ℝ |
            ∀ x ∈ (Kpol i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} := by
    simpa using (section16_polar_sum_convexCones (K := Kpol) hKpolne)
  have hdouble :
      ∀ i,
        {xStar : Fin n → ℝ |
            ∀ x ∈ (Kpol i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} =
          closure (K i : Set (Fin n → ℝ)) := by
    intro i
    simpa [Kpol] using
      (section16_polar_polar_eq_closure_convexCone (K := K i) (hKne := hKne i))
  calc
    {xStar : Fin n → ℝ |
        ∀ x ∈
          (∑ i : Fin m,
            {xStar : Fin n → ℝ |
              ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}),
          dotProduct x xStar ≤ 0}
        =
      {xStar : Fin n → ℝ |
        ∀ x ∈ (∑ i, (Kpol i : Set (Fin n → ℝ))), dotProduct x xStar ≤ 0} := by
        simp [Kpol]
    _ = ⋂ i : Fin m,
          {xStar : Fin n → ℝ |
            ∀ x ∈ (Kpol i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} := hsum
    _ = ⋂ i : Fin m, closure (K i : Set (Fin n → ℝ)) := by
        ext xStar
        constructor
        · intro hx
          refine Set.mem_iInter.2 ?_
          intro i
          have hx' := (Set.mem_iInter.mp hx) i
          rw [← hdouble i]
          exact hx'
        · intro hx
          refine Set.mem_iInter.2 ?_
          intro i
          have hx' := (Set.mem_iInter.mp hx) i
          rw [hdouble i]
          exact hx'

/-- The double polar of the sum of polars is the closure of that sum. -/
lemma section16_polar_polar_sum_polars_eq_closure_sum_polars {n m : Nat}
    (K : Fin m → ConvexCone ℝ (Fin n → ℝ)) :
    {xStar : Fin n → ℝ |
        ∀ x ∈
          {y : Fin n → ℝ |
            ∀ z ∈
              (∑ i : Fin m,
                {xStar : Fin n → ℝ |
                  ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}),
              dotProduct z y ≤ 0},
          dotProduct x xStar ≤ 0} =
      closure
        (∑ i : Fin m,
          {xStar : Fin n → ℝ |
            ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}) := by
  classical
  let Kpol : Fin m → ConvexCone ℝ (Fin n → ℝ) := fun i =>
    { carrier :=
        {xStar : Fin n → ℝ | ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}
      smul_mem' := by
        intro c hc y hy x hx
        have hy' : dotProduct x y ≤ 0 := hy x hx
        have hmul : c * dotProduct x y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hy'
        simpa [dotProduct_smul, smul_eq_mul] using hmul
      add_mem' := by
        intro y hy z hz x hx
        have hy' : dotProduct x y ≤ 0 := hy x hx
        have hz' : dotProduct x z ≤ 0 := hz x hx
        have hsum : dotProduct x y + dotProduct x z ≤ 0 := add_nonpos hy' hz'
        simpa [dotProduct_add] using hsum }
  let Ksum : ConvexCone ℝ (Fin n → ℝ) :=
    { carrier := ∑ i, (Kpol i : Set (Fin n → ℝ))
      smul_mem' := by
        intro c hc x hx
        rcases
            (Set.mem_fintype_sum (f := fun i => (Kpol i : Set (Fin n → ℝ))) (a := x)).1 hx with
          ⟨g, hg, rfl⟩
        refine
          (Set.mem_fintype_sum (f := fun i => (Kpol i : Set (Fin n → ℝ)))
              (a := c • ∑ i, g i)).2 ?_
        refine ⟨fun i => c • g i, ?_, ?_⟩
        · intro i
          exact (Kpol i).smul_mem hc (hg i)
        ·
          simpa using
            (Finset.smul_sum (s := Finset.univ) (f := g) (r := c)).symm
      add_mem' := by
        intro x hx y hy
        rcases
            (Set.mem_fintype_sum (f := fun i => (Kpol i : Set (Fin n → ℝ))) (a := x)).1 hx with
          ⟨g, hg, rfl⟩
        rcases
            (Set.mem_fintype_sum (f := fun i => (Kpol i : Set (Fin n → ℝ))) (a := y)).1 hy with
          ⟨h, hh, rfl⟩
        refine
          (Set.mem_fintype_sum (f := fun i => (Kpol i : Set (Fin n → ℝ)))
              (a := ∑ i, g i + ∑ i, h i)).2 ?_
        refine ⟨fun i => g i + h i, ?_, ?_⟩
        · intro i
          exact (Kpol i).add_mem (hg i) (hh i)
        ·
          simpa using
            (Finset.sum_add_distrib (s := Finset.univ) (f := g) (g := h)) }
  have hKsumne : (Ksum : Set (Fin n → ℝ)).Nonempty := by
    refine ⟨0, ?_⟩
    refine
      (Set.mem_fintype_sum (f := fun i => (Kpol i : Set (Fin n → ℝ)))
        (a := (0 : Fin n → ℝ))).2 ?_
    refine ⟨fun _ => 0, ?_, by simp⟩
    intro i
    intro x hx
    simp
  have hdouble :
      {xStar : Fin n → ℝ |
          ∀ x ∈
            {y : Fin n → ℝ | ∀ z ∈ (Ksum : Set (Fin n → ℝ)), dotProduct z y ≤ 0},
            dotProduct x xStar ≤ 0} =
        closure (Ksum : Set (Fin n → ℝ)) := by
    simpa using
      (section16_polar_polar_eq_closure_convexCone (K := Ksum) hKsumne)
  simpa [Ksum, Kpol] using hdouble

/-- Corollary 16.4.2.2. Let `K₁, …, Kₘ` be non-empty convex cones in `ℝⁿ`. Then
`(cl K₁ ∩ ⋯ ∩ cl Kₘ)^∘ = cl (K₁^∘ + ⋯ + Kₘ^∘)`.

In this development, `cl` is `closure`, `∩` is `⋂`, and `K^∘` is represented as the set
`{xStar | ∀ x ∈ K, ⟪x, xStar⟫ ≤ 0}`. -/
theorem section16_polar_iInter_closure_eq_closure_sum_polars {n m : Nat}
    (K : Fin m → ConvexCone ℝ (Fin n → ℝ)) (hKne : ∀ i, (K i : Set (Fin n → ℝ)).Nonempty) :
    {xStar : Fin n → ℝ |
        ∀ x ∈ (⋂ i : Fin m, closure (K i : Set (Fin n → ℝ))),
          (dotProduct x xStar : ℝ) ≤ 0} =
      closure
        (∑ i : Fin m,
          {xStar : Fin n → ℝ | ∀ x ∈ (K i : Set (Fin n → ℝ)), (dotProduct x xStar : ℝ) ≤ 0}) := by
  classical
  have hsum_polars :
      {xStar : Fin n → ℝ |
          ∀ x ∈
            (∑ i : Fin m,
              {xStar : Fin n → ℝ |
                ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}),
            dotProduct x xStar ≤ 0} =
        ⋂ i : Fin m, closure (K i : Set (Fin n → ℝ)) :=
    section16_polar_sum_polars_eq_iInter_closure (K := K) hKne
  have hdouble :
      {xStar : Fin n → ℝ |
          ∀ x ∈
            {y : Fin n → ℝ |
              ∀ z ∈
                (∑ i : Fin m,
                  {xStar : Fin n → ℝ |
                    ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}),
                dotProduct z y ≤ 0},
            dotProduct x xStar ≤ 0} =
        closure
          (∑ i : Fin m,
            {xStar : Fin n → ℝ |
              ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}) :=
    section16_polar_polar_sum_polars_eq_closure_sum_polars (K := K)
  calc
    {xStar : Fin n → ℝ |
        ∀ x ∈ (⋂ i : Fin m, closure (K i : Set (Fin n → ℝ))),
          (dotProduct x xStar : ℝ) ≤ 0} =
      {xStar : Fin n → ℝ |
        ∀ x ∈
          {y : Fin n → ℝ |
            ∀ z ∈
              (∑ i : Fin m,
                {xStar : Fin n → ℝ |
                  ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}),
              dotProduct z y ≤ 0},
          dotProduct x xStar ≤ 0} := by
        simp [hsum_polars.symm]
    _ = closure
          (∑ i : Fin m,
            {xStar : Fin n → ℝ |
              ∀ x ∈ (K i : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0}) := hdouble

/-- The support function of a nonempty convex cone is the indicator of its polar. -/
lemma section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar {n : Nat}
    (K : ConvexCone ℝ (Fin n → ℝ)) (hKne : (K : Set (Fin n → ℝ)).Nonempty) :
    supportFunctionEReal (K : Set (Fin n → ℝ)) =
      indicatorFunction
        {xStar : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} := by
  classical
  funext xStar
  by_cases hpol : ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0
  · have hle : supportFunctionEReal (K : Set (Fin n → ℝ)) xStar ≤ (0 : EReal) := by
      refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hxK, rfl⟩
      have hx : dotProduct x xStar ≤ 0 := hpol x hxK
      exact_mod_cast hx
    obtain ⟨x0, hx0K⟩ := hKne
    have hnear :
        ∀ ε : ℝ,
          0 < ε → (-(ε : ℝ) : EReal) < supportFunctionEReal (K : Set (Fin n → ℝ)) xStar := by
      intro ε hε
      have hc0 : dotProduct x0 xStar ≤ 0 := hpol x0 hx0K
      by_cases hczero : dotProduct x0 xStar = 0
      · have hmem :
            ((0 : ℝ) : EReal) ∈
              {z : EReal |
                ∃ x ∈ (K : Set (Fin n → ℝ)), z = ((dotProduct x xStar : ℝ) : EReal)} := by
          exact ⟨x0, hx0K, by simp [hczero]⟩
        have hle0 : ((0 : ℝ) : EReal) ≤ supportFunctionEReal (K : Set (Fin n → ℝ)) xStar :=
          le_sSup hmem
        have hlt0 : (-(ε : ℝ) : EReal) < (0 : EReal) := by
          exact_mod_cast (by linarith)
        exact lt_of_lt_of_le hlt0 hle0
      · have hcneg : dotProduct x0 xStar < 0 := lt_of_le_of_ne hc0 hczero
        obtain ⟨t, htpos, htlt⟩ := exists_pos_mul_lt hε (-dotProduct x0 xStar)
        have hmem : t • x0 ∈ (K : Set (Fin n → ℝ)) := K.smul_mem htpos hx0K
        have hdot : dotProduct (t • x0) xStar = t * dotProduct x0 xStar := by
          simp [smul_eq_mul]
        have hlt' : (-(ε : ℝ)) < t * dotProduct x0 xStar := by
          have htlt' : -(dotProduct x0 xStar * t) < ε := by
            simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using htlt
          have h := (neg_lt).1 htlt'
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        have hmem' :
            ((dotProduct (t • x0) xStar : ℝ) : EReal) ∈
              {z : EReal |
                ∃ x ∈ (K : Set (Fin n → ℝ)), z = ((dotProduct x xStar : ℝ) : EReal)} := by
          exact ⟨t • x0, hmem, rfl⟩
        have hle' :
            ((dotProduct (t • x0) xStar : ℝ) : EReal) ≤
              supportFunctionEReal (K : Set (Fin n → ℝ)) xStar :=
          le_sSup hmem'
        have hltE : (-(ε : ℝ) : EReal) < ((dotProduct (t • x0) xStar : ℝ) : EReal) := by
          have : -ε < dotProduct (t • x0) xStar := by simpa [hdot] using hlt'
          exact_mod_cast this
        exact lt_of_lt_of_le hltE hle'
    have hge : (0 : EReal) ≤ supportFunctionEReal (K : Set (Fin n → ℝ)) xStar := by
      refine le_of_forall_lt ?_
      intro c hc
      cases c using EReal.rec with
      | bot =>
          have hne : supportFunctionEReal (K : Set (Fin n → ℝ)) xStar ≠ ⊥ := by
            have hx0le :
                ((dotProduct x0 xStar : ℝ) : EReal) ≤
                  supportFunctionEReal (K : Set (Fin n → ℝ)) xStar := by
              refine le_sSup ?_
              exact ⟨x0, hx0K, rfl⟩
            intro hbot
            have : ¬ ((dotProduct x0 xStar : ℝ) : EReal) ≤ (⊥ : EReal) := by simp
            have hx0le' := hx0le
            rw [hbot] at hx0le'
            exact this hx0le'
          exact (bot_lt_iff_ne_bot.mpr hne)
      | top =>
          cases (not_lt_of_ge (show (0 : EReal) ≤ (⊤ : EReal) from le_top) hc)
      | coe r =>
          have hr : r < 0 := by simpa using hc
          have hε : 0 < -r := by linarith
          have hnear' := hnear (-r) hε
          simpa using hnear'
    have hsup : supportFunctionEReal (K : Set (Fin n → ℝ)) xStar = (0 : EReal) :=
      le_antisymm hle hge
    have hInd :
        indicatorFunction
            {xStar : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} xStar = 0 := by
      simpa [indicatorFunction] using hpol
    calc
      supportFunctionEReal (K : Set (Fin n → ℝ)) xStar = 0 := hsup
      _ =
          indicatorFunction
            {xStar : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} xStar := by
          symm
          exact hInd
  · have hpos : ∃ x ∈ (K : Set (Fin n → ℝ)), 0 < dotProduct x xStar := by
      classical
      push_neg at hpol
      exact hpol
    rcases hpos with ⟨x0, hx0K, hx0pos⟩
    have hsup : supportFunctionEReal (K : Set (Fin n → ℝ)) xStar = ⊤ := by
      refine (sSup_eq_top).2 ?_
      intro b hb
      cases b using EReal.rec with
      | bot =>
          refine ⟨((dotProduct x0 xStar : ℝ) : EReal), ?_, ?_⟩
          · exact ⟨x0, hx0K, rfl⟩
          · simp
      | top =>
          cases (lt_irrefl _ hb)
      | coe r =>
          obtain ⟨n, hn⟩ := exists_nat_gt (r / (dotProduct x0 xStar))
          have hlt' : r / (dotProduct x0 xStar) < (n.succ : ℝ) := by
            have hn' : r / (dotProduct x0 xStar) < (n : ℝ) := by
              simpa using hn
            have hnsucc : (n : ℝ) < (n.succ : ℝ) := by
              exact_mod_cast (Nat.lt_succ_self n)
            exact lt_trans hn' hnsucc
          have hcpos : 0 < dotProduct x0 xStar := hx0pos
          have hmul :
              (r / (dotProduct x0 xStar)) * dotProduct x0 xStar <
                (n.succ : ℝ) * dotProduct x0 xStar := by
            exact (mul_lt_mul_of_pos_right hlt' hcpos)
          have hlt : r < (n.succ : ℝ) * dotProduct x0 xStar := by
            have hne : dotProduct x0 xStar ≠ 0 := ne_of_gt hcpos
            simpa [div_eq_mul_inv, hne] using hmul
          have htpos : 0 < (n.succ : ℝ) := by
            exact_mod_cast (Nat.succ_pos n)
          have hxmem : (n.succ : ℝ) • x0 ∈ K := K.smul_mem htpos hx0K
          have hdot :
              dotProduct ((n.succ : ℝ) • x0) xStar = (n.succ : ℝ) * dotProduct x0 xStar := by
            simp [smul_eq_mul]
          refine ⟨((dotProduct ((n.succ : ℝ) • x0) xStar : ℝ) : EReal), ?_, ?_⟩
          · exact ⟨(n.succ : ℝ) • x0, hxmem, rfl⟩
          · have hlt' : r < dotProduct ((n.succ : ℝ) • x0) xStar := by
              simpa [hdot] using hlt
            exact_mod_cast hlt'
    have hInd :
        indicatorFunction
            {xStar : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} xStar = ⊤ := by
      simpa [indicatorFunction] using hpol
    calc
      supportFunctionEReal (K : Set (Fin n → ℝ)) xStar = ⊤ := hsup
      _ =
          indicatorFunction
            {xStar : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} xStar := by
          symm
          exact hInd

/-- Indicator functions determine their sets. -/
lemma section16_set_eq_of_indicatorFunction_eq {n : Nat} {A B : Set (Fin n → ℝ)}
    (h : indicatorFunction A = indicatorFunction B) : A = B := by
  ext x
  have h' : indicatorFunction A x = indicatorFunction B x := congrArg (fun f => f x) h
  have hlt : indicatorFunction A x < (⊤ : EReal) ↔ indicatorFunction B x < (⊤ : EReal) := by
    simp [h']
  simpa [indicatorFunction_lt_top_iff_mem] using hlt

/-- Corollary 16.4.2.3: Let `K₁, …, Kₘ` be non-empty convex cones in `ℝⁿ`. If the cones `ri Kᵢ`,
`i = 1, …, m`, have a point in common, then

`(K₁ ∩ ⋯ ∩ Kₘ)^∘ = (K₁^∘ + ⋯ + Kₘ^∘)`.

In this development, `K^∘` is represented as the set `{xStar | ∀ x ∈ K, ⟪x, xStar⟫ ≤ 0}` and
`ri` is `euclideanRelativeInterior`. -/
theorem section16_polar_iInter_eq_sum_polars_of_nonempty_iInter_ri {n m : Nat}
    (K : Fin m → ConvexCone ℝ (Fin n → ℝ)) (hKne : ∀ i, (K i : Set (Fin n → ℝ)).Nonempty)
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (K i)))) :
    {xStar : Fin n → ℝ |
        ∀ x ∈ (⋂ i : Fin m, (K i : Set (Fin n → ℝ))),
          (dotProduct x xStar : ℝ) ≤ 0} =
      ∑ i : Fin m, {xStar : Fin n → ℝ | ∀ x ∈ (K i : Set (Fin n → ℝ)), (dotProduct x xStar : ℝ) ≤ 0} := by
  classical
  let Kset : Fin m → Set (Fin n → ℝ) := fun i => (K i : Set (Fin n → ℝ))
  let Kpol : Fin m → Set (Fin n → ℝ) :=
    fun i => {xStar : Fin n → ℝ | ∀ x ∈ Kset i, dotProduct x xStar ≤ 0}
  let Kinter : ConvexCone ℝ (Fin n → ℝ) := ⨅ i, K i
  have hKinter : (Kinter : Set (Fin n → ℝ)) = ⋂ i, Kset i := by
    ext x
    simp [Kinter, Kset]
  have hKinter_ne : (Kinter : Set (Fin n → ℝ)).Nonempty := by
    rcases hri with ⟨x, hx⟩
    refine ⟨(x : Fin n → ℝ), ?_⟩
    have hxmem_inter : (x : Fin n → ℝ) ∈ ⋂ i, Kset i := by
      refine Set.mem_iInter.2 ?_
      intro i
      have hxri :
          x ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (K i)) :=
        (Set.mem_iInter.mp hx) i
      have hxmem :
          x ∈ ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (K i)) :=
        (euclideanRelativeInterior_subset_closure n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (K i))).1 hxri
      simpa [Kset] using hxmem
    simpa [hKinter] using hxmem_inter
  have hsupport :
      supportFunctionEReal (⋂ i, Kset i) =
        infimalConvolutionFamily (fun i => supportFunctionEReal (Kset i)) :=
    (section16_supportFunctionEReal_iInter_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_proof_step
        (C := Kset) (hC := fun i => (K i).convex) (hCne := hKne) hri).1
  have hconv :
      (fun i => supportFunctionEReal (Kset i)) = fun i => indicatorFunction (Kpol i) := by
    funext i
    simpa [Kset, Kpol] using
      (section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar (K := K i)
        (hKne := hKne i))
  have hEqInd :
      indicatorFunction {xStar : Fin n → ℝ | ∀ x ∈ ⋂ i, Kset i, dotProduct x xStar ≤ 0} =
        indicatorFunction (∑ i, Kpol i) := by
    calc
      indicatorFunction {xStar : Fin n → ℝ | ∀ x ∈ ⋂ i, Kset i, dotProduct x xStar ≤ 0} =
          supportFunctionEReal (⋂ i, Kset i) := by
            simpa [hKinter] using
              (section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar (K := Kinter)
                (hKne := hKinter_ne)).symm
      _ = infimalConvolutionFamily (fun i => supportFunctionEReal (Kset i)) := hsupport
      _ = infimalConvolutionFamily (fun i => indicatorFunction (Kpol i)) := by
            simp [hconv]
      _ = indicatorFunction (∑ i, Kpol i) := by
            simpa using
              (section16_infimalConvolutionFamily_indicatorFunction_eq_indicatorFunction_sum (C := Kpol))
  have hset :
      {xStar : Fin n → ℝ | ∀ x ∈ ⋂ i, Kset i, dotProduct x xStar ≤ 0} = ∑ i, Kpol i :=
    section16_set_eq_of_indicatorFunction_eq hEqInd
  simpa [Kset, Kpol] using hset

end Section16
end Chap03
