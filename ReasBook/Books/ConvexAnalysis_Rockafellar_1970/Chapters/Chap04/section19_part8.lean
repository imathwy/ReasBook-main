/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part7

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Theorem 19.2: extract a finite Text 19.0.10 representation from
polyhedrality. -/
lemma helperForTheorem_19_2_extractFiniteRepresentation
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ∃ (k m : ℕ) (a : Fin m → Fin n → ℝ) (α : Fin m → ℝ),
      k ≤ m ∧
        ∀ x,
          f x =
            sInf {r : EReal |
              ∃ (lam : Fin m → ℝ),
                (∀ j, (∑ i, lam i * a i j) = x j) ∧
                (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                  (fun i => lam i)) = 1 ∧
                (∀ i, 0 ≤ lam i) ∧
                r = ((∑ i, lam i * α i : ℝ) : EReal)} := by
  have hfgen : IsFinitelyGeneratedConvexFunction n f :=
    helperForCorollary_19_1_2_polyhedral_imp_finitelyGenerated (n := n) (f := f) hfpoly
  exact
    helperForCorollary_19_1_2_unpack_finitelyGeneratedData
      (n := n) (f := f) hfgen

/-- Helper for Theorem 19.2: in a Text 19.0.10 representation, `k = 0` forces `f = ⊤`. -/
lemma helperForTheorem_19_2_kZero_forces_constTop
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hk0 : k = 0)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    ∀ x, f x = ⊤ := by
  intro x
  let Sx : Set EReal :=
    {r : EReal |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        r = ((∑ i, lam i * α i : ℝ) : EReal)}
  have hSx_empty : Sx = (∅ : Set EReal) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨lam, _hlin, hnorm, _hnonneg, _hobj⟩
      have hsum_zero :
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 0 := by
        simp [hk0]
      have hzero_one : (0 : ℝ) = 1 := by
        calc
          (0 : ℝ) = (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) := hsum_zero.symm
          _ = 1 := hnorm
      norm_num at hzero_one
    · intro hr
      exact False.elim (Set.notMem_empty r hr)
  calc
    f x = sInf Sx := by simpa [Sx] using (hrepr x)
    _ = sInf (∅ : Set EReal) := by simp [hSx_empty]
    _ = ⊤ := by simp

/-- Helper for Theorem 19.2: the degenerate `k = 0` branch gives
`fenchelConjugate n f = constNegInf n`. -/
lemma helperForTheorem_19_2_kZero_forces_constTop_and_conjugate_constNegInf
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hk0 : k = 0)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    fenchelConjugate n f = constNegInf n := by
  have htop : ∀ x, f x = ⊤ :=
    helperForTheorem_19_2_kZero_forces_constTop
      (k := k) (m := m) (f := f) (a := a) (α := α) hk0 hrepr
  have hf_eq_constTop : f = (fun _ : Fin n → ℝ => (⊤ : EReal)) := by
    funext x
    exact htop x
  calc
    fenchelConjugate n f =
        fenchelConjugate n (fun _ : Fin n → ℝ => (⊤ : EReal)) := by
          simp [hf_eq_constTop]
    _ = constNegInf n := fenchelConjugate_constPosInf n

/-- Helper for Theorem 19.2: the constant `-∞` function is polyhedral convex. -/
lemma helperForTheorem_19_2_constNegInf_isPolyhedralConvexFunction
    (n : ℕ) :
    IsPolyhedralConvexFunction n (constNegInf n) := by
  refine ⟨?_, ?_⟩
  · have hEpiUniv : epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n) = Set.univ := by
      ext p
      constructor
      · intro hp
        trivial
      · intro hp
        refine ⟨?_, ?_⟩
        · trivial
        · simp [constNegInf]
    simpa [ConvexFunctionOn, hEpiUniv] using
      (convex_univ : Convex ℝ (Set.univ : Set ((Fin n → ℝ) × ℝ)))
  · classical
    let ι : Type := PEmpty
    let b : ι → Fin (n + 1) → ℝ := fun i => nomatch i
    let β : ι → ℝ := fun i => nomatch i
    have hPolyUniv : IsPolyhedralConvexSet (n + 1) (Set.univ : Set (Fin (n + 1) → ℝ)) := by
      refine ⟨ι, inferInstance, b, β, ?_⟩
      ext x
      simp [closedHalfSpaceLE, b, β]
    have hEpiUniv : epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n) = Set.univ := by
      ext p
      constructor
      · intro hp
        trivial
      · intro hp
        refine ⟨?_, ?_⟩
        · trivial
        · simp [constNegInf]
    have hImageUnivCoord :
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n)) =
          (Set.univ : Set (Fin (n + 1) → ℝ)) := by
      rw [hEpiUniv, Set.image_univ]
      exact Set.range_eq_univ.mpr (prodLinearEquiv_append_coord (n := n)).surjective
    have hpolyCoord :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n)) := by
      simpa [hImageUnivCoord] using hPolyUniv
    simpa [prodLinearEquiv_append_coord] using hpolyCoord

/-- Helper for Theorem 19.2: positivity of `k` and `k ≤ m` provides a point-index
below `k`. -/
lemma helperForTheorem_19_2_existsPointIndex_of_posK
    {k m : ℕ}
    (hkpos : 0 < k)
    (hk : k ≤ m) :
    ∃ i0 : Fin m, (i0 : ℕ) < k := by
  refine ⟨⟨0, ?_⟩, hkpos⟩
  exact lt_of_lt_of_le hkpos hk

/-- Helper for Theorem 19.2: any feasible coefficient vector gives an upper bound on
the represented function value. -/
lemma helperForTheorem_19_2_value_le_of_feasibleCoefficients
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {x : Fin n → ℝ} {lam : Fin m → ℝ}
    (hlin : ∀ j, (∑ i, lam i * a i j) = x j)
    (hnorm :
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1)
    (hnonneg : ∀ i, 0 ≤ lam i) :
    f x ≤ ((∑ i, lam i * α i : ℝ) : EReal) := by
  have hmem :
      ((∑ i, lam i * α i : ℝ) : EReal) ∈
        {r : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r = ((∑ i, lam i * α i : ℝ) : EReal)} := by
    exact ⟨lam, hlin, hnorm, hnonneg, rfl⟩
  calc
    f x =
        sInf {r : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r = ((∑ i, lam i * α i : ℝ) : EReal)} := by
          simpa using (hrepr x)
    _ ≤ ((∑ i, lam i * α i : ℝ) : EReal) := sInf_le hmem

/-- Helper for Theorem 19.2: each point-generator value is bounded above by its
coefficient value. -/
lemma helperForTheorem_19_2_generatorValue_le_alpha
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    (i : Fin m)
    (hi : (i : ℕ) < k) :
    f (a i) ≤ (α i : EReal) := by
  classical
  let lam : Fin m → ℝ := fun j => if j = i then 1 else 0
  have hlin : ∀ j, (∑ t, lam t * a t j) = a i j := by
    intro j
    simp [lam]
  have hnorm :
      (Finset.sum (Finset.univ.filter (fun j : Fin m => (j : ℕ) < k))
        (fun j => lam j)) = 1 := by
    have hi_mem : i ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k) := by
      simp [hi]
    simp [lam, hi_mem]
  have hnonneg : ∀ j, 0 ≤ lam j := by
    intro j
    by_cases hji : j = i
    · simp [lam, hji]
    · simp [lam, hji]
  simpa [lam] using
    (helperForTheorem_19_2_value_le_of_feasibleCoefficients
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr
      (x := a i) (lam := lam) hlin hnorm hnonneg)

/-- Helper for Theorem 19.2: a finite upper bound on the conjugate yields the
point-generator inequalities. -/
lemma helperForTheorem_19_2_pointBounds_of_conjugateLe
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ}
    (hconj : fenchelConjugate n f xStar ≤ (μ : EReal)) :
    ∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ := by
  intro i hi
  have hvalue : f (a i) ≤ (α i : EReal) :=
    helperForTheorem_19_2_generatorValue_le_alpha
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr i hi
  have hAffineAll :
      ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f x :=
    (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := μ)).1 hconj
  have hAtA : ((a i ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f (a i) := hAffineAll (a i)
  have hAtA' : ((a i ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ (α i : EReal) := le_trans hAtA hvalue
  have hreal : dotProduct (a i) xStar - μ ≤ α i := by
    exact_mod_cast hAtA'
  linarith

/-- Helper for Theorem 19.2: finite conjugate sublevel bounds imply the two finite
generator inequality families (point and direction). -/
lemma helperForTheorem_19_2_finiteBounds_of_conjugateLe
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ}
    (hconj : fenchelConjugate n f xStar ≤ (μ : EReal)) :
    (∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ) ∧
      (∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0) := by
  have hpoint : ∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ :=
    helperForTheorem_19_2_pointBounds_of_conjugateLe
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr hconj
  have hdir : ∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0 := by
    have hi0 : ∃ i0 : Fin m, (i0 : ℕ) < k :=
      helperForTheorem_19_2_existsPointIndex_of_posK (k := k) (m := m) hkpos hk
    rcases hi0 with ⟨i0, hi0⟩
    intro i hi
    have hbase : dotProduct (a i0) xStar - α i0 ≤ μ := hpoint i0 hi0
    by_contra hnot
    have hslope_pos : 0 < dotProduct (a i) xStar - α i := lt_of_not_ge hnot
    have hoffset_nonpos : dotProduct (a i0) xStar - α i0 - μ ≤ 0 := by
      linarith
    obtain ⟨t, ht_nonneg, ht_pos⟩ :=
      helperForTheorem_19_1_exists_t_pos_of_neg_offset_pos_slope
        (a := dotProduct (a i0) xStar - α i0 - μ)
        (b := dotProduct (a i) xStar - α i)
        hoffset_nonpos hslope_pos
    have hineq : i ≠ i0 := by
      intro hEq
      have hk_le_i0 : k ≤ (i0 : ℕ) := by simpa [hEq] using hi
      exact (Nat.not_lt_of_ge hk_le_i0) hi0
    let x_t : Fin n → ℝ := a i0 + t • a i
    let lam_t : Fin m → ℝ :=
      fun j => if j = i0 then 1 else if j = i then t else 0
    have hlin_t : ∀ j, (∑ l, lam_t l * a l j) = x_t j := by
      intro j
      have hne : i0 ≠ i := by
        intro hEq
        exact hineq hEq.symm
      have hlam_split : ∀ x : Fin m,
          (if x = i0 then (1 : ℝ) else if x = i then t else 0) =
            (if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0) := by
        intro x
        by_cases hx0 : x = i0
        · subst hx0
          simp [hne]
        · by_cases hxi : x = i
          · subst hxi
            simp [hineq]
          · simp [hx0, hxi]
      calc
        (∑ l, lam_t l * a l j)
            = ∑ x, (((if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0)) * a x j) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp [lam_t, hlam_split x]
        _ = ∑ x, ((if x = i0 then (1 : ℝ) else 0) * a x j + (if x = i then t else 0) * a x j) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
        _ = (∑ x, (if x = i0 then (1 : ℝ) else 0) * a x j) +
              (∑ x, (if x = i then t else 0) * a x j) := by
              simp [Finset.sum_add_distrib]
        _ = a i0 j + t * a i j := by
              simp
        _ = x_t j := by
              simp [x_t]
    have hnorm_t :
        (Finset.sum (Finset.univ.filter (fun j : Fin m => (j : ℕ) < k))
          (fun j => lam_t j)) = 1 := by
      let F : Finset (Fin m) :=
        Finset.univ.filter (fun j : Fin m => (j : ℕ) < k)
      have hsum_eq :
          Finset.sum F (fun j => lam_t j) =
            Finset.sum F (fun j => if j = i0 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hjlt : (j : ℕ) < k := (Finset.mem_filter.mp hj).2
        have hj_ne_i : j ≠ i := by
          have hj_lt_i : (j : ℕ) < (i : ℕ) := lt_of_lt_of_le hjlt hi
          exact fun hji => hj_lt_i.ne (by simp [hji])
        simp [lam_t, hj_ne_i]
      have hi0_mem : i0 ∈ F := by
        simp [F, hi0]
      have hsum_delta : Finset.sum F (fun j => if j = i0 then (1 : ℝ) else 0) = 1 := by
        simp [hi0_mem]
      exact hsum_eq.trans hsum_delta
    have hnonneg_t : ∀ j, 0 ≤ lam_t j := by
      intro j
      by_cases hj0 : j = i0
      · simp [lam_t, hj0]
      · by_cases hji : j = i
        · subst hji
          simp [lam_t, hineq, ht_nonneg]
        · simp [lam_t, hj0, hji]
    have hvalue_t : f x_t ≤ ((∑ j, lam_t j * α j : ℝ) : EReal) :=
      helperForTheorem_19_2_value_le_of_feasibleCoefficients
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr
        (x := x_t) (lam := lam_t) hlin_t hnorm_t hnonneg_t
    have hAffineAll :
        ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f x :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := μ)).1 hconj
    have hAtXT : ((x_t ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f x_t := hAffineAll x_t
    have hAtXT' :
        ((x_t ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ ((∑ j, lam_t j * α j : ℝ) : EReal) :=
      le_trans hAtXT hvalue_t
    have hreal : x_t ⬝ᵥ xStar - μ ≤ (∑ j, lam_t j * α j : ℝ) := by
      exact_mod_cast hAtXT'
    have hdot_xt : x_t ⬝ᵥ xStar = dotProduct (a i0) xStar + t * dotProduct (a i) xStar := by
      calc
        x_t ⬝ᵥ xStar = dotProduct (a i0 + t • a i) xStar := by rfl
        _ = dotProduct (a i0) xStar + dotProduct (t • a i) xStar := by
              rw [add_dotProduct]
        _ = dotProduct (a i0) xStar + t * dotProduct (a i) xStar := by
              simp [smul_dotProduct]
    have halpha_lam : (∑ j, lam_t j * α j : ℝ) = α i0 + t * α i := by
      have hne : i0 ≠ i := by
        intro hEq
        exact hineq hEq.symm
      have hlam_split : ∀ x : Fin m,
          (if x = i0 then (1 : ℝ) else if x = i then t else 0) =
            (if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0) := by
        intro x
        by_cases hx0 : x = i0
        · subst hx0
          simp [hne]
        · by_cases hxi : x = i
          · subst hxi
            simp [hineq]
          · simp [hx0, hxi]
      calc
        (∑ j, lam_t j * α j : ℝ)
            = ∑ x, (((if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0)) * α x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp [lam_t, hlam_split x]
        _ = ∑ x, ((if x = i0 then (1 : ℝ) else 0) * α x + (if x = i then t else 0) * α x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
        _ = (∑ x, (if x = i0 then (1 : ℝ) else 0) * α x) +
              (∑ x, (if x = i then t else 0) * α x) := by
              simp [Finset.sum_add_distrib]
        _ = α i0 + t * α i := by
              simp
    have hlinineq :
        dotProduct (a i0) xStar - α i0 - μ + t * (dotProduct (a i) xStar - α i) ≤ 0 := by
      have hreal' :
          dotProduct (a i0) xStar + t * dotProduct (a i) xStar - μ ≤ α i0 + t * α i := by
        simpa [hdot_xt, halpha_lam, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hreal
      linarith
    exact (not_le_of_gt ht_pos) hlinineq
  exact ⟨hpoint, hdir⟩

/-- Helper for Theorem 19.2: finite point and direction generator bounds imply the
corresponding finite upper bound for the conjugate. -/
lemma helperForTheorem_19_2_conjugateLe_of_finiteBounds
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ}
    (hpoint : ∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ)
    (hdir : ∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0) :
    fenchelConjugate n f xStar ≤ (μ : EReal) := by
  have _ : 0 < k := hkpos
  have _ : k ≤ m := hk
  refine
    (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := μ)).2 ?_
  intro x
  rw [hrepr x]
  refine le_sInf ?_
  intro r hr
  rcases hr with ⟨lam, hlin, hnorm, hnonneg, rfl⟩
  let F : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)
  have hlin_vec : x = ∑ i, lam i • a i := by
    funext j
    simpa [smul_eq_mul] using (hlin j).symm
  have hdot :
      dotProduct x xStar = ∑ i, lam i * dotProduct (a i) xStar := by
    calc
      dotProduct x xStar = dotProduct xStar x := by simp [dotProduct_comm]
      _ = dotProduct xStar (∑ i, lam i • a i) := by simp [hlin_vec]
      _ = ∑ i, dotProduct xStar (lam i • a i) := by
            simpa using
              (dotProduct_sum (u := xStar) (s := (Finset.univ : Finset (Fin m)))
                (v := fun i => lam i • a i))
      _ = ∑ i, lam i * dotProduct xStar (a i) := by
            simp [dotProduct_smul, smul_eq_mul]
      _ = ∑ i, lam i * dotProduct (a i) xStar := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [dotProduct_comm]
  have hsum_point :
      Finset.sum F (fun i => lam i * (dotProduct (a i) xStar - α i)) ≤
        Finset.sum F (fun i => lam i * μ) := by
    refine Finset.sum_le_sum ?_
    intro i hiF
    exact mul_le_mul_of_nonneg_left
      (hpoint i (Finset.mem_filter.mp hiF).2) (hnonneg i)
  have hsum_dir :
      Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
          (fun i => lam i * (dotProduct (a i) xStar - α i)) ≤ 0 := by
    have hle_each :
        ∀ i ∈ Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k),
          lam i * (dotProduct (a i) xStar - α i) ≤ 0 := by
      intro i hiF
      exact mul_nonpos_of_nonneg_of_nonpos
        (hnonneg i) (hdir i (Nat.not_lt.mp (Finset.mem_filter.mp hiF).2))
    have :
        Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
            (fun i => lam i * (dotProduct (a i) xStar - α i)) ≤
          Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
            (fun _ : Fin m => 0) := by
      refine Finset.sum_le_sum ?_
      intro i hiF
      exact hle_each i hiF
    simpa using this
  have hsum_split :
      (∑ i, lam i * (dotProduct (a i) xStar - α i)) =
        Finset.sum F (fun i => lam i * (dotProduct (a i) xStar - α i)) +
          Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
            (fun i => lam i * (dotProduct (a i) xStar - α i)) := by
    simpa [F] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun i : Fin m => lam i * (dotProduct (a i) xStar - α i))
        (p := fun i : Fin m => (i : ℕ) < k)).symm
  have hsum_point_mu :
      Finset.sum F (fun i => lam i * μ) = (Finset.sum F (fun i => lam i)) * μ := by
    simpa using (Finset.sum_mul (s := F) (f := fun i : Fin m => lam i) (a := μ)).symm
  have hsum_bound :
      ∑ i, lam i * (dotProduct (a i) xStar - α i) ≤ μ := by
    calc
      ∑ i, lam i * (dotProduct (a i) xStar - α i)
          = Finset.sum F (fun i => lam i * (dotProduct (a i) xStar - α i)) +
              Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
                (fun i => lam i * (dotProduct (a i) xStar - α i)) := hsum_split
      _ ≤ Finset.sum F (fun i => lam i * μ) + 0 := add_le_add hsum_point hsum_dir
      _ = Finset.sum F (fun i => lam i * μ) := by ring
      _ = (Finset.sum F (fun i => lam i)) * μ := hsum_point_mu
      _ = μ := by simp [F, hnorm]
  have hsum_rewrite :
      (∑ i, lam i * (dotProduct (a i) xStar - α i)) =
        (∑ i, lam i * dotProduct (a i) xStar) - (∑ i, lam i * α i) := by
    simp [mul_sub, Finset.sum_sub_distrib]
  have hreal : dotProduct x xStar - μ ≤ (∑ i, lam i * α i : ℝ) := by
    have haux :
        (∑ i, lam i * dotProduct (a i) xStar) - (∑ i, lam i * α i) ≤ μ := by
      simpa [hsum_rewrite] using hsum_bound
    have haux' : dotProduct x xStar - (∑ i, lam i * α i) ≤ μ := by
      simpa [hdot] using haux
    linarith
  exact_mod_cast hreal

/-- Helper for Theorem 19.2: conjugate sublevel membership is equivalent to the two
finite generator-bound families. -/
lemma helperForTheorem_19_2_conjugate_le_iff_finiteGeneratorBounds
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ} :
    fenchelConjugate n f xStar ≤ (μ : EReal) ↔
      (∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ) ∧
        (∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0) := by
  constructor
  · intro hconj
    exact
      helperForTheorem_19_2_finiteBounds_of_conjugateLe
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr hconj
  · intro hbounds
    exact
      helperForTheorem_19_2_conjugateLe_of_finiteBounds
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr hbounds.1 hbounds.2

/-- Helper for Theorem 19.2: transformed-epigraph membership is equivalent to the
finite generator-bound families at the pulled-back pair coordinates. -/
lemma helperForTheorem_19_2_memTransformedEpigraphCoord_iff_bounds
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    (y : Fin (n + 1) → ℝ) :
    y ∈ ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ↔
      (∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2) ∧
        (∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0) := by
  let q : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm y
  constructor
  · intro hy
    rcases hy with ⟨p, hp, hpy⟩
    have hq_eq_p : q = p := by
      dsimp [q]
      calc
        (prodLinearEquiv_append_coord (n := n)).symm y
            = (prodLinearEquiv_append_coord (n := n)).symm
                ((prodLinearEquiv_append_coord (n := n)) p) := by
                  simp [hpy]
        _ = p := by simp
    have hq_epi : q ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      simpa [hq_eq_p] using hp
    have hq_conj : fenchelConjugate n f q.1 ≤ (q.2 : EReal) :=
      (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hq_epi
    have hq_bounds :
        (∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) q.1 - α i ≤ q.2) ∧
          (∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) q.1 - α i ≤ 0) := by
      exact
        (helperForTheorem_19_2_conjugate_le_iff_finiteGeneratorBounds
          (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
          hkpos hk hrepr).1 hq_conj
    simpa [q] using hq_bounds
  · intro hyBounds
    have hq_conj : fenchelConjugate n f q.1 ≤ (q.2 : EReal) := by
      exact
        (helperForTheorem_19_2_conjugate_le_iff_finiteGeneratorBounds
          (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
          hkpos hk hrepr).2 (by simpa [q] using hyBounds)
    have hq_epi : q ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      exact (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2 hq_conj
    refine ⟨q, hq_epi, ?_⟩
    simp [q]

/-- Helper for Theorem 19.2: packed-coordinate dot products with `(a i, -1)` decode
to the affine expression `dotProduct (a i) x - μ`. -/
lemma helperForTheorem_19_2_prodLinearEquivAppendCoord_castSucc
    {n : ℕ} (x0 : Fin n → ℝ) (μ0 : ℝ) (j0 : Fin n) :
    x0 j0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.castSucc j0) := by
  change x0 j0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.castSucc j0)
  change x0 j0 =
    ((appendAffineEquiv n 1).linear
      (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0)
  have happ := congrArg
    (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.castSucc j0))
    (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
  have hlin :
      (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
        (appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
    simpa using congrArg
      (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have happ' :
      ((appendAffineEquiv n 1).linear
        (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0) =
        Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) := by
    simpa [hlin] using happ
  have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) = x0 j0 := by
    exact Fin.append_left (u := x0) (v := Function.const (Fin 1) μ0) j0
  exact (happ'.trans happend).symm

/-- Helper for Theorem 19.2: the last packed coordinate is the appended scalar. -/
lemma helperForTheorem_19_2_prodLinearEquivAppendCoord_last
    {n : ℕ} (x0 : Fin n → ℝ) (μ0 : ℝ) :
    μ0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.last n) := by
  change μ0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.last n)
  change μ0 =
    ((appendAffineEquiv n 1).linear
      (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n)
  have happ := congrArg
    (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.last n))
    (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
  have hlin :
      (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
        (appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
    simpa using congrArg
      (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have happ' :
      ((appendAffineEquiv n 1).linear
        (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n) =
        Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) := by
    simpa [hlin] using happ
  have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) = μ0 := by
    change Fin.append x0 (Function.const (Fin 1) μ0) (Fin.natAdd n (0 : Fin 1)) = μ0
    exact Fin.append_right (u := x0) (v := Function.const (Fin 1) μ0) (0 : Fin 1)
  exact (happ'.trans happend).symm

/-- Helper for Theorem 19.2: dot product in packed coordinates splits into the base
dot product plus the product of appended scalar coordinates. -/
lemma helperForTheorem_19_2_dotProduct_prodLinearEquivAppendCoord
    {n : ℕ} (p q : (Fin n → ℝ) × ℝ) :
    dotProduct
      (prodLinearEquiv_append_coord (n := n) p)
      (prodLinearEquiv_append_coord (n := n) q) =
      dotProduct p.1 q.1 + p.2 * q.2 := by
  rcases p with ⟨x, μ⟩
  rcases q with ⟨y, ν⟩
  have hx_cast :
      ∀ j : Fin n,
        (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.castSucc j) = x j := by
    intro j
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_castSucc
        (n := n) (x0 := x) (μ0 := μ) (j0 := j)).symm
  have hy_cast :
      ∀ j : Fin n,
        (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.castSucc j) = y j := by
    intro j
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_castSucc
        (n := n) (x0 := y) (μ0 := ν) (j0 := j)).symm
  have hx_last :
      (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.last n) = μ := by
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_last
        (n := n) (x0 := x) (μ0 := μ)).symm
  have hy_last :
      (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.last n) = ν := by
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_last
        (n := n) (x0 := y) (μ0 := ν)).symm
  calc
    dotProduct
      (prodLinearEquiv_append_coord (n := n) (x, μ))
      (prodLinearEquiv_append_coord (n := n) (y, ν))
        =
          (∑ j : Fin n,
            (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.castSucc j) *
              (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.castSucc j)) +
            (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.last n) *
              (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.last n) := by
          simp [dotProduct, Fin.sum_univ_castSucc]
    _ = (∑ j : Fin n, x j * y j) + μ * ν := by
          simp [hx_cast, hy_cast, hx_last, hy_last]
    _ = dotProduct x y + μ * ν := by
          simp [dotProduct]

/-- Helper for Theorem 19.2: packed-coordinate dot products with `(a i, -1)` decode
to the affine expression `dotProduct (a i) x - μ`. -/
lemma helperForTheorem_19_2_dotPacked_point
    {n m : ℕ} {a : Fin m → Fin n → ℝ} (i : Fin m)
    (y : Fin (n + 1) → ℝ) :
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) =
      dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
        ((prodLinearEquiv_append_coord (n := n)).symm y).2 := by
  let q : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm y
  have hy : prodLinearEquiv_append_coord (n := n) q = y := by
    simp [q]
  calc
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ)))
        = dotProduct (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) y := by
            simp [dotProduct_comm]
    _ = dotProduct
          (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ)))
          (prodLinearEquiv_append_coord (n := n) q) := by
            simp [hy]
    _ = dotProduct (a i) q.1 + (-1 : ℝ) * q.2 := by
          simpa using
            helperForTheorem_19_2_dotProduct_prodLinearEquivAppendCoord
              (n := n) (p := (a i, (-1 : ℝ))) (q := q)
    _ = dotProduct (a i) q.1 - q.2 := by
          ring
    _ = dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
          ((prodLinearEquiv_append_coord (n := n)).symm y).2 := by
            simp [q]

/-- Helper for Theorem 19.2: packed-coordinate dot products with `(a i, 0)` decode
to `dotProduct (a i) x`. -/
lemma helperForTheorem_19_2_dotPacked_direction
    {n m : ℕ} {a : Fin m → Fin n → ℝ} (i : Fin m)
    (y : Fin (n + 1) → ℝ) :
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) =
      dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 := by
  let q : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm y
  have hy : prodLinearEquiv_append_coord (n := n) q = y := by
    simp [q]
  calc
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ)))
        = dotProduct (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) y := by
            simp [dotProduct_comm]
    _ = dotProduct
          (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ)))
          (prodLinearEquiv_append_coord (n := n) q) := by
            simp [hy]
    _ = dotProduct (a i) q.1 + (0 : ℝ) * q.2 := by
          simpa using
            helperForTheorem_19_2_dotProduct_prodLinearEquivAppendCoord
              (n := n) (p := (a i, (0 : ℝ))) (q := q)
    _ = dotProduct (a i) q.1 := by
          ring
    _ = dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 := by
          simp [q]

/-- Helper for Theorem 19.2: the point-generator bound family in transformed
coordinates is a polyhedral convex set. -/
lemma helperForTheorem_19_2_pointBoundsCoord_polyhedral
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} :
    IsPolyhedralConvexSet (n + 1)
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2} := by
  let aEq : Fin 0 → Fin (n + 1) → ℝ := Fin.elim0
  let αEq : Fin 0 → ℝ := Fin.elim0
  let bIneq : Fin m → Fin (n + 1) → ℝ :=
    fun i =>
      if (i : ℕ) < k then
        prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))
      else 0
  let βIneq : Fin m → ℝ := fun i => if (i : ℕ) < k then α i else 0
  have hpoly_system :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    simpa [βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        (n + 1) 0 m aEq αEq bIneq βIneq)
  have hset :
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2} =
      {y : Fin (n + 1) → ℝ |
        (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
        (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, ?_⟩
      · intro t
        exact Fin.elim0 t
      · intro i
        by_cases hi : (i : ℕ) < k
        · have hbound :
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2 := hy i hi
          have hdecoded :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) =
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
                  ((prodLinearEquiv_append_coord (n := n)).symm y).2 :=
            helperForTheorem_19_2_dotPacked_point (n := n) (m := m) (a := a) i y
          have hbound' :
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
                  ((prodLinearEquiv_append_coord (n := n)).symm y).2 ≤ α i := by
            linarith
          have hdot :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) ≤ α i := by
            simpa [hdecoded] using hbound'
          simpa [bIneq, βIneq, hi] using hdot
        · simp [bIneq, βIneq, hi]
    · intro hy i hi
      have hineq : dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) ≤ α i := by
        have hyi := hy.2 i
        simpa [bIneq, βIneq, hi] using hyi
      have hdecoded :
          dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) =
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
              ((prodLinearEquiv_append_coord (n := n)).symm y).2 :=
        helperForTheorem_19_2_dotPacked_point (n := n) (m := m) (a := a) i y
      have hineq' :
          dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
            ((prodLinearEquiv_append_coord (n := n)).symm y).2 ≤ α i := by
        simpa [hdecoded] using hineq
      linarith
  have hpoly_target :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} := by
    have hpoly_system' :
        IsPolyhedralConvexSet (n + 1)
          {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      simpa [aEq, αEq] using hpoly_system
    have hset' :
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} =
        {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      calc
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2}
            =
          {y : Fin (n + 1) → ℝ |
            (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
            (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := hset
        _ = {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
            ext y
            simp [aEq, αEq]
    exact hset'.symm ▸ hpoly_system'
  exact hpoly_target

/-- Helper for Theorem 19.2: the direction-generator bound family in transformed
coordinates is a polyhedral convex set. -/
lemma helperForTheorem_19_2_directionBoundsCoord_polyhedral
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} :
    IsPolyhedralConvexSet (n + 1)
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} := by
  let aEq : Fin 0 → Fin (n + 1) → ℝ := Fin.elim0
  let αEq : Fin 0 → ℝ := Fin.elim0
  let bIneq : Fin m → Fin (n + 1) → ℝ :=
    fun i =>
      if k ≤ (i : ℕ) then
        prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))
      else 0
  let βIneq : Fin m → ℝ := fun i => if k ≤ (i : ℕ) then α i else 0
  have hpoly_system :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    simpa [βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        (n + 1) 0 m aEq αEq bIneq βIneq)
  have hset :
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} =
      {y : Fin (n + 1) → ℝ |
        (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
        (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, ?_⟩
      · intro t
        exact Fin.elim0 t
      · intro i
        by_cases hi : k ≤ (i : ℕ)
        · have hbound :
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0 := hy i hi
          have hdecoded :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) =
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 :=
            helperForTheorem_19_2_dotPacked_direction (n := n) (m := m) (a := a) i y
          have hbound' :
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 ≤ α i := by
            linarith
          have hdot :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) ≤ α i := by
            simpa [hdecoded] using hbound'
          simpa [bIneq, βIneq, hi] using hdot
        · simp [bIneq, βIneq, hi]
    · intro hy i hi
      have hineq : dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) ≤ α i := by
        have hyi := hy.2 i
        simpa [bIneq, βIneq, hi] using hyi
      have hdecoded :
          dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) =
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 :=
        helperForTheorem_19_2_dotPacked_direction (n := n) (m := m) (a := a) i y
      have hineq' :
          dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 ≤ α i := by
        simpa [hdecoded] using hineq
      linarith
  have hpoly_target :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} := by
    have hpoly_system' :
        IsPolyhedralConvexSet (n + 1)
          {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      simpa [aEq, αEq] using hpoly_system
    have hset' :
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} =
        {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      calc
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}
            =
          {y : Fin (n + 1) → ℝ |
            (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
            (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := hset
        _ = {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
            ext y
            simp [aEq, αEq]
    exact hset'.symm ▸ hpoly_system'
  exact hpoly_target

/-- Helper for Theorem 19.2: the transformed epigraph of the conjugate equals the
intersection of the point- and direction-bound coordinate sets. -/
lemma helperForTheorem_19_2_transformedEpigraphCoord_eq_pointDirInter
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) =
      ({y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2} ∩
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}) := by
  ext y
  constructor
  · intro hy
    have hyBounds :=
      (helperForTheorem_19_2_memTransformedEpigraphCoord_iff_bounds
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr y).1 hy
    exact ⟨hyBounds.1, hyBounds.2⟩
  · intro hy
    exact
      (helperForTheorem_19_2_memTransformedEpigraphCoord_iff_bounds
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr y).2 ⟨hy.1, hy.2⟩

/-- Helper for Theorem 19.2: in the nondegenerate branch, the transformed epigraph of
the conjugate is polyhedral. -/
lemma helperForTheorem_19_2_polyhedralTransformedEpigraph_of_conjugate
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    IsPolyhedralConvexSet (n + 1)
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
  have hpoint :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} :=
    helperForTheorem_19_2_pointBoundsCoord_polyhedral
      (n := n) (k := k) (m := m) (a := a) (α := α)
  have hdir :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} :=
    helperForTheorem_19_2_directionBoundsCoord_polyhedral
      (n := n) (k := k) (m := m) (a := a) (α := α)
  have hinter :
      IsPolyhedralConvexSet (n + 1)
        ({y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} ∩
          {y : Fin (n + 1) → ℝ |
            ∀ i : Fin m,
              k ≤ (i : ℕ) →
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}) := by
    exact helperForTheorem_19_1_polyhedral_inter hpoint hdir
  have hEq :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) =
        ({y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} ∩
          {y : Fin (n + 1) → ℝ |
            ∀ i : Fin m,
              k ≤ (i : ℕ) →
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}) :=
    helperForTheorem_19_2_transformedEpigraphCoord_eq_pointDirInter
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
      hkpos hk hrepr
  simpa [hEq] using hinter

/-- Helper for Theorem 19.2: the nondegenerate representation branch (`0 < k`)
already yields polyhedrality of the Fenchel conjugate. -/
lemma helperForTheorem_19_2_nondegenerate_branch_polyhedralConjugate
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    IsPolyhedralConvexFunction n (fenchelConjugate n f) := by
  refine ⟨?_, ?_⟩
  · have hconv : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    simpa [ConvexFunction] using hconv
  · have hpoly_coord :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) :=
      helperForTheorem_19_2_polyhedralTransformedEpigraph_of_conjugate
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr
    simpa [prodLinearEquiv_append_coord] using hpoly_coord

/-- Theorem 19.2: The conjugate of a polyhedral convex function is polyhedral. -/
theorem polyhedralConvexFunction_fenchelConjugate (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f →
      IsPolyhedralConvexFunction n (fenchelConjugate n f) := by
  intro hfpoly
  rcases
    helperForTheorem_19_2_extractFiniteRepresentation
      (n := n) (f := f) hfpoly with
    ⟨k, m, a, α, hk, hrepr⟩
  by_cases hk0 : k = 0
  · have hconj : fenchelConjugate n f = constNegInf n :=
      helperForTheorem_19_2_kZero_forces_constTop_and_conjugate_constNegInf
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hk0 hrepr
    simpa [hconj] using
      helperForTheorem_19_2_constNegInf_isPolyhedralConvexFunction (n := n)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    exact
      helperForTheorem_19_2_nondegenerate_branch_polyhedralConjugate
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr


end Section19
end Chap19
