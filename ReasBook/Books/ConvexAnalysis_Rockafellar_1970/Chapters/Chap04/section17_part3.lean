/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part2

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section17

/-- Definition 17.0.14 ($m$-dimensional (skew) orthant), LaTeX label `def:orthant`. A generalized
`m`-dimensional simplex with one ordinary vertex and `m - 1` vertices at infinity is called an
`m`-dimensional (skew) orthant. The `m`-dimensional orthants in `ℝⁿ` are exactly the images of
the nonnegative orthant `ℝ^m_{≥ 0}` under one-to-one affine transformations from `ℝ^m` into
`ℝⁿ`. -/
abbrev nonnegOrthant (m : Nat) : Set (Fin m → Real) :=
  Set.Ici (0 : Fin m → Real)

/-- A set `O ⊆ ℝⁿ` is an `m`-dimensional (skew) orthant if it is the image of the nonnegative
orthant `ℝ^m_{≥ 0}` under an injective affine map `ℝ^m → ℝⁿ`. -/
def IsSkewOrthant (n m : Nat) (O : Set (Fin n → Real)) : Prop :=
  ∃ f : (Fin m → Real) →ᵃ[Real] (Fin n → Real), Function.Injective f ∧ O = f '' nonnegOrthant m

/-- The nonnegative orthant is closed. -/
lemma isClosed_nonnegOrthant (m : Nat) : IsClosed (nonnegOrthant m) := by
  simpa [nonnegOrthant] using (isClosed_Ici : IsClosed (Set.Ici (0 : Fin m → Real)))

/-- An injective affine map between finite-dimensional real vector spaces is a closed embedding. -/
lemma isClosedEmbedding_of_injective_affineMap {n m : Nat}
    (f : (Fin m → Real) →ᵃ[Real] (Fin n → Real)) (hf : Function.Injective f) :
    IsClosedEmbedding (fun x => f x) := by
  have hlin : Function.Injective f.linear := (f.linear_injective_iff).2 hf
  have hker : LinearMap.ker f.linear = ⊥ := (LinearMap.ker_eq_bot).2 hlin
  have hlinClosed : IsClosedEmbedding f.linear :=
    LinearMap.isClosedEmbedding_of_injective (f := f.linear) hker
  have htrans : IsClosedEmbedding (fun y : Fin n → Real => y + f 0) :=
    (Homeomorph.addRight (f 0)).isClosedEmbedding
  have hcomp : IsClosedEmbedding (fun x : Fin m → Real => f.linear x + f 0) :=
    htrans.comp hlinClosed
  have hfun : (fun x : Fin m → Real => f x) = fun x => f.linear x + f 0 := by
    simpa using (AffineMap.decomp f)
  rw [hfun]
  exact hcomp

/-- Propositon 17.0.15 (Closedness), LaTeX label `prop:closedness`. Every `m`-dimensional (skew)
orthant in `ℝⁿ` is closed. -/
theorem isClosed_of_isSkewOrthant {n m : Nat} {O : Set (Fin n → Real)} :
    IsSkewOrthant n m O → IsClosed O := by
  rintro ⟨f, hf, rfl⟩
  have hf' : IsClosedEmbedding (fun x => f x) := isClosedEmbedding_of_injective_affineMap f hf
  exact (hf'.isClosed_iff_image_isClosed).1 (isClosed_nonnegOrthant m)

/-- A generalized `m`-dimensional simplex in `ℝⁿ`, modeled via the identification
`x ↦ (1, x) ∈ H = {(1, x) | x ∈ ℝⁿ}` as a slice of an `(m+1)`-dimensional skew orthant in
`ℝ^{n+1}`. -/
def IsGeneralizedSimplex (n m : Nat) (S : Set (Fin n → Real)) : Prop :=
  ∃ O : Set (Fin (n + 1) → Real),
    IsSkewOrthant (n + 1) (m + 1) O ∧
      S = (fun x : Fin n → Real => Fin.cases (1 : Real) x) ⁻¹' (O ∩ liftingHyperplane n)

/-- The lift map `x ↦ (1, x)` is continuous. -/
lemma continuous_lift1 (n : Nat) :
    Continuous (fun x : Fin n → Real =>
      (Fin.cases (1 : Real) x : Fin (n + 1) → Real)) := by
  refine continuous_pi ?_
  intro i
  cases i using Fin.cases with
  | zero =>
      simpa using (continuous_const : Continuous fun _ : Fin n → Real => (1 : Real))
  | succ i =>
      simpa using (continuous_apply i)

/-- The lifting hyperplane is given by the equation `y 0 = 1`. -/
lemma liftingHyperplane_eq (n : Nat) :
    liftingHyperplane n = {y : Fin (n + 1) → Real | y 0 = 1} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hy
    refine ⟨fun i => y (Fin.succ i), ?_⟩
    ext i
    cases i using Fin.cases with
    | zero =>
        have hy0 : y 0 = 1 := by simpa using hy
        simpa using hy0.symm
    | succ i =>
        simp

/-- The lifting hyperplane is closed. -/
lemma isClosed_liftingHyperplane (n : Nat) : IsClosed (liftingHyperplane n) := by
  have hclosed :
      IsClosed {y : Fin (n + 1) → Real | y 0 = 1} := by
    simpa using
      (isClosed_singleton.preimage (continuous_apply (0 : Fin (n + 1))))
  simpa [liftingHyperplane_eq] using hclosed

/-- Propositon 17.0.15 (Closedness), generalized simplex version: every generalized
`m`-dimensional simplex in `ℝⁿ` is closed. -/
theorem isClosed_of_isGeneralizedSimplex {n m : Nat} {S : Set (Fin n → Real)} :
    IsGeneralizedSimplex n m S → IsClosed S := by
  rintro ⟨O, hO, rfl⟩
  have hOclosed : IsClosed O := isClosed_of_isSkewOrthant hO
  have hHclosed : IsClosed (liftingHyperplane n) := isClosed_liftingHyperplane n
  have hclosed : IsClosed (O ∩ liftingHyperplane n) := hOclosed.inter hHclosed
  exact hclosed.preimage (continuous_lift1 n)

/-- Propositon 17.0.16 (Closedness via orthant slicing), LaTeX label `prop:gen-simplex-closed`.

Every generalized `m`-dimensional simplex in `ℝⁿ` is closed. More precisely, such a set can be
identified with the intersection of an `(m+1)`-dimensional orthant in `ℝ^{n+1}` and the
hyperplane `H = {(1, x) | x ∈ ℝⁿ}`.

In this file, a “generalized simplex” is represented by `IsGeneralizedSimplex n m S`, which
models the “orthant slicing” description. -/
theorem isClosed_of_isGeneralizedSimplex_via_orthant_slicing {n m : Nat} {S : Set (Fin n → Real)} :
    IsGeneralizedSimplex n m S → IsClosed S := by
  simpa using (isClosed_of_isGeneralizedSimplex (n := n) (m := m) (S := S))

/-- Split a lifting-set sum into a mixed convex combination, preserving the length. -/
lemma split_liftingSet_sum_to_IsMixedConvexCombination_fixed_length {n m : Nat}
    {S₀ S₁' : Set (Fin n → Real)} {x : Fin n → Real}
    (s : Fin m → Fin (n + 1) → Real) (c : Fin m → Real)
    (hs : ∀ i, s i ∈ liftingSet (n := n) S₀ S₁') (hc : ∀ i, 0 ≤ c i)
    (hsum : (Fin.cases (1 : Real) x) = ∑ i, c i • s i) :
    IsMixedConvexCombination n m S₀ S₁' x := by
  classical
  let lift1 : (Fin n → Real) → Fin (n + 1) → Real :=
    fun y => Fin.cases (motive := fun _ : Fin (n + 1) => Real) (1 : Real) y
  let lift0 : (Fin n → Real) → Fin (n + 1) → Real :=
    fun y => Fin.cases (motive := fun _ : Fin (n + 1) => Real) (0 : Real) y
  let isPoint : Fin m → Prop := fun i =>
    ∃ p ∈ S₀, s i = lift1 p
  have hcases :
      ∀ i, isPoint i ∨ ∃ d ∈ S₁', s i = lift0 d := by
    intro i
    simpa [isPoint, lift1, lift0] using
      (liftingSet_mem_cases (n := n) (S₀ := S₀) (S₁' := S₁') (v := s i) (hs i))
  have hdir_of_not_point :
      ∀ i, ¬ isPoint i → ∃ d ∈ S₁', s i = lift0 d := by
    intro i hnot
    have hcases_i := hcases i
    cases hcases_i with
    | inl hpoint => exact (False.elim (hnot hpoint))
    | inr hdir => exact hdir
  let I : Type := {i : Fin m // isPoint i}
  let J : Type := {i : Fin m // ¬ isPoint i}
  have hpoint : ∀ i : I, ∃ p ∈ S₀, s i.1 = lift1 p := by
    intro i
    exact i.2
  choose p hpS₀ hs_p using hpoint
  have hdir : ∀ j : J, ∃ d ∈ S₁', s j.1 = lift0 d := by
    intro j
    exact hdir_of_not_point j.1 j.2
  choose d hdS₁ hs_d using hdir
  have hsum_point_fun :
      ∑ i ∈ Finset.univ.filter isPoint, c i • s i =
        ∑ i : I, c i.1 • s i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter isPoint)
      (p := isPoint) (f := fun i => c i • s i) ?_)
    intro i
    simp
  have hsum_dir_fun :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ isPoint i), c i • s i =
        ∑ j : J, c j.1 • s j.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => ¬ isPoint i))
      (p := fun i => ¬ isPoint i) (f := fun i => c i • s i) ?_)
    intro i
    simp
  have hsum_split :
      ∑ i, c i • s i =
        (∑ i : I, c i.1 • lift1 (p i)) +
        (∑ j : J, c j.1 • lift0 (d j)) := by
    have hsplit' : ∑ i, c i • s i =
        (∑ i ∈ Finset.univ.filter isPoint, c i • s i) +
        (∑ i ∈ Finset.univ.filter (fun i => ¬ isPoint i), c i • s i) := by
      simpa using
        (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
          (p := isPoint) (f := fun i => c i • s i)).symm
    calc
      ∑ i, c i • s i =
          (∑ i ∈ Finset.univ.filter isPoint, c i • s i) +
          (∑ i ∈ Finset.univ.filter (fun i => ¬ isPoint i), c i • s i) := hsplit'
      _ = (∑ i : I, c i.1 • s i.1) + (∑ j : J, c j.1 • s j.1) := by
          simp [hsum_point_fun, hsum_dir_fun]
      _ = (∑ i : I, c i.1 • lift1 (p i)) +
          (∑ j : J, c j.1 • lift0 (d j)) := by
          have hsumI :
              ∑ i : I, c i.1 • s i.1 =
                ∑ i : I, c i.1 • lift1 (p i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hs_p i]
          have hsumJ :
              ∑ j : J, c j.1 • s j.1 =
                ∑ j : J, c j.1 • lift0 (d j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hs_d j]
          simp [hsumI, hsumJ]
  have hsum_point : ∑ i : I, c i.1 = (1 : Real) := by
    have h0 := congrArg (fun f => f 0) hsum
    have h0' : (1 : Real) = (∑ i, c i • s i) 0 := by
      simpa using h0
    have h0_split := congrArg (fun f => f 0) hsum_split
    have hsum_point' : (1 : Real) = ∑ i : I, c i.1 := by
      calc
        (1 : Real) = (∑ i, c i • s i) 0 := h0'
        _ =
            (∑ i : I, c i.1 • lift1 (p i)) 0 +
            (∑ j : J, c j.1 • lift0 (d j)) 0 := by
              simpa using h0_split
        _ = ∑ i : I, c i.1 := by
            simp [lift1, lift0]
    simpa using hsum_point'.symm
  have hx_eq_subtype :
      x = (∑ i : I, c i.1 • p i) + (∑ j : J, c j.1 • d j) := by
    ext j
    have hsum' :
        (Fin.cases (1 : Real) x) =
          (∑ i : I, c i.1 • lift1 (p i)) + (∑ j : J, c j.1 • lift0 (d j)) := by
      simpa [hsum_split] using hsum
    have hsum_succ := congrArg (fun f => f (Fin.succ j)) hsum'
    simpa [lift1, lift0] using hsum_succ
  let k := Fintype.card I
  let l := Fintype.card J
  let eI : I ≃ Fin k := Fintype.equivFin I
  let eJ : J ≃ Fin l := Fintype.equivFin J
  let p' : Fin k → Fin n → Real := fun i => p (eI.symm i)
  let d' : Fin l → Fin n → Real := fun j => d (eJ.symm j)
  let a : Fin k → Real := fun i => c (eI.symm i).1
  let b : Fin l → Real := fun j => c (eJ.symm j).1
  have hp' : ∀ i, p' i ∈ S₀ := by
    intro i
    simpa [p'] using hpS₀ (eI.symm i)
  have hd' : ∀ j, d' j ∈ ray n S₁' := by
    intro j
    have hd' : d (eJ.symm j) ∈ S₁' := hdS₁ (eJ.symm j)
    simpa [d'] using mem_ray_of_mem (n := n) (S := S₁') (x := d (eJ.symm j)) hd'
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    simpa [a] using hc (eI.symm i).1
  have hb : ∀ j, 0 ≤ b j := by
    intro j
    simpa [b] using hc (eJ.symm j).1
  have hsum_a : ∑ i, a i = (1 : Real) := by
    have hsum_a' : ∑ i, a i = ∑ i : I, c i.1 := by
      simpa [a] using (Equiv.sum_comp (eI.symm) (fun i : I => c i.1))
    simpa [hsum_a'] using hsum_point
  have hx_eq :
      x = (∑ i, a i • p' i) + (∑ j, b j • d' j) := by
    have hsum_p :
        ∑ i : I, c i.1 • p i = ∑ i, a i • p' i := by
      symm
      simpa [a, p'] using
        (Equiv.sum_comp (eI.symm) (fun i : I => c i.1 • p i))
    have hsum_d :
        ∑ j : J, c j.1 • d j = ∑ j, b j • d' j := by
      symm
      simpa [b, d'] using
        (Equiv.sum_comp (eJ.symm) (fun j : J => c j.1 • d j))
    calc
      x = (∑ i : I, c i.1 • p i) + (∑ j : J, c j.1 • d j) := hx_eq_subtype
      _ = (∑ i, a i • p' i) + (∑ j, b j • d' j) := by
          simp [hsum_p, hsum_d]
  have ha_weights : IsConvexWeights k a := ⟨ha, hsum_a⟩
  have hk_pos : 1 ≤ k := one_le_of_IsConvexWeights (m := k) (w := a) ha_weights
  have hcomb : IsMixedConvexCombination n (k + l) S₀ S₁' x := by
    refine ⟨k, hk_pos, ?_, ?_⟩
    · exact Nat.le_add_right k l
    ·
      have hm : k + l - k = l := by simp
      have hFin : Fin (k + l - k) = Fin l := by
        simp [hm]
      let e : Fin (k + l - k) ≃ Fin l := Equiv.cast hFin
      let d'' : Fin (k + l - k) → Fin n → Real := fun j => d' (e j)
      let b'' : Fin (k + l - k) → Real := fun j => b (e j)
      have hd'' : ∀ j, d'' j ∈ ray n S₁' := by
        intro j
        simpa [d'', e] using hd' (e j)
      have hb'' : ∀ j, 0 ≤ b'' j := by
        intro j
        simpa [b'', e] using hb (e j)
      have hsum_b : ∑ j, b j • d' j = ∑ j, b'' j • d'' j := by
        symm
        simpa [b'', d''] using (Equiv.sum_comp e (fun j : Fin l => b j • d' j))
      have hx_eq' :
          x = (∑ i, a i • p' i) + (∑ j, b'' j • d'' j) := by
        simpa [hsum_b] using hx_eq
      refine ⟨p', d'', a, b'', ?_⟩
      exact ⟨hp', hd'', ha, hb'', hsum_a, hx_eq'⟩
  have hcard_or :
      Fintype.card {i : Fin m // isPoint i ∨ ¬ isPoint i} =
        Fintype.card I + Fintype.card J := by
    simpa [I, J] using
      (Fintype.card_subtype_or_disjoint (p := isPoint) (q := fun i => ¬ isPoint i)
        (Set.disjoint_left.2 (by
          intro i hi hni
          exact hni hi)))
  have hcard_all : Fintype.card {i : Fin m // isPoint i ∨ ¬ isPoint i} = m := by
    let e : {i : Fin m // isPoint i ∨ ¬ isPoint i} ≃ Fin m :=
      { toFun := fun i => i.1
        , invFun := fun i => ⟨i, by classical exact em (isPoint i)⟩
        , left_inv := by
            intro i
            cases i with
            | mk i hi =>
                apply Subtype.ext
                rfl
        , right_inv := by
            intro i
            rfl }
    simpa using (Fintype.card_congr e)
  have hkl : k + l = m := by
    have hcard_or' :
        Fintype.card {i : Fin m // isPoint i ∨ ¬ isPoint i} = k + l := by
      simpa [k, l] using hcard_or
    calc
      k + l = Fintype.card {i : Fin m // isPoint i ∨ ¬ isPoint i} := by
        symm
        exact hcard_or'
      _ = m := hcard_all
  simpa [hkl] using hcomb

/-- Drop zero coefficients from a nonnegative sum and reindex to obtain positive coefficients. -/
lemma trim_nonneg_sum_smul_drop_zero_coeffs {n m : Nat}
    {S : Set (Fin (n + 1) → Real)} {y : Fin (n + 1) → Real}
    (s : Fin m → Fin (n + 1) → Real) (c : Fin m → Real)
    (hs : ∀ i, s i ∈ S) (hc : ∀ i, 0 ≤ c i)
    (hsum : y = ∑ i, c i • s i) :
    ∃ (m' : Nat) (s' : Fin m' → Fin (n + 1) → Real) (c' : Fin m' → Real),
      (∀ i, s' i ∈ S) ∧ (∀ i, 0 < c' i) ∧ y = ∑ i, c' i • s' i := by
  classical
  let I : Type := {i : Fin m // c i ≠ 0}
  let m' := Fintype.card I
  let e : I ≃ Fin m' := Fintype.equivFin I
  let s' : Fin m' → Fin (n + 1) → Real := fun j => s (e.symm j)
  let c' : Fin m' → Real := fun j => c (e.symm j)
  have hs' : ∀ j, s' j ∈ S := by
    intro j
    simpa [s'] using hs (e.symm j)
  have hc' : ∀ j, 0 < c' j := by
    intro j
    have hne : c (e.symm j) ≠ 0 := (e.symm j).property
    have hnonneg : 0 ≤ c (e.symm j) := hc (e.symm j)
    have hne' : (0 : Real) ≠ c (e.symm j) := by
      simpa [eq_comm] using hne
    exact lt_of_le_of_ne hnonneg hne'
  have hsum_filter :
      (∑ i, c i • s i) =
        ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), c i • s i := by
    have hsum_if :
        (∑ i, c i • s i) = ∑ i, (if c i ≠ 0 then c i • s i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : c i = 0 <;> simp [h]
    have hsum_filter' :
        ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), c i • s i =
          ∑ i, (if c i ≠ 0 then c i • s i else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => c i • s i) (p := fun i => c i ≠ 0))
    calc
      (∑ i, c i • s i) = ∑ i, (if c i ≠ 0 then c i • s i else 0) := hsum_if
      _ = ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), c i • s i := by
          symm
          exact hsum_filter'
  have hsum_subtype :
      ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), c i • s i =
        ∑ i : I, c i.1 • s i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => c i ≠ 0))
      (p := fun i => c i ≠ 0) (f := fun i => c i • s i) ?_)
    intro i
    simp
  have hsum_I : y = ∑ i : I, c i.1 • s i.1 := by
    calc
      y = ∑ i, c i • s i := hsum
      _ = ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), c i • s i := hsum_filter
      _ = ∑ i : I, c i.1 • s i.1 := hsum_subtype
  have hsum_equiv :
      ∑ j, c' j • s' j = ∑ i : I, c i.1 • s i.1 := by
    simpa [s', c'] using
      (Equiv.sum_comp (e.symm) (fun i : I => c i.1 • s i.1))
  refine ⟨m', s', c', hs', hc', ?_⟩
  calc
    y = ∑ i : I, c i.1 • s i.1 := hsum_I
    _ = ∑ j, c' j • s' j := by
        symm
        exact hsum_equiv

/-- A linear dependence yields a relation with a positive coefficient. -/
lemma exists_linear_relation_sum_smul_eq_zero_exists_pos {m : Nat}
    {V : Type*} [AddCommGroup V] [Module Real V]
    (s : Fin m → V) (hlin : ¬ LinearIndependent Real s) :
    ∃ μ : Fin m → Real, (∑ i, μ i • s i = 0) ∧ (∃ i, 0 < μ i) := by
  classical
  obtain ⟨g, hsum, hne⟩ := (Fintype.not_linearIndependent_iff).1 hlin
  by_cases hpos : ∃ i, 0 < g i
  · exact ⟨g, hsum, hpos⟩
  · have hle : ∀ i, g i ≤ 0 := by
      intro i
      by_contra hgt
      exact hpos ⟨i, lt_of_not_ge hgt⟩
    rcases hne with ⟨i0, hi0⟩
    have hlt : g i0 < 0 := lt_of_le_of_ne (hle i0) (by simpa using hi0)
    refine ⟨fun i => -g i, ?_, ?_⟩
    · calc
        ∑ i, (-g i) • s i = -∑ i, g i • s i := by
          simp [neg_smul, Finset.sum_neg_distrib]
        _ = 0 := by
          simp [hsum]
    · refine ⟨i0, ?_⟩
      simpa using (neg_pos.mpr hlt)

/-- Remove a zero coefficient from a nonnegative sum and shorten the index set. -/
lemma drop_zero_coeff_sum_smul_to_shorter {n m : Nat}
    {T : Set (Fin (n + 1) → Real)} {y : Fin (n + 1) → Real}
    (s : Fin (m + 1) → Fin (n + 1) → Real) (c : Fin (m + 1) → Real)
    (hs : ∀ i, s i ∈ T) (hc : ∀ i, 0 ≤ c i)
    (hsum : y = ∑ i, c i • s i) (i0 : Fin (m + 1)) (hci0 : c i0 = 0) :
    ∃ (s' : Fin m → Fin (n + 1) → Real) (c' : Fin m → Real),
      (∀ j, s' j ∈ T) ∧ (∀ j, 0 ≤ c' j) ∧ y = ∑ j, c' j • s' j := by
  classical
  let I : Type := {i : Fin (m + 1) // i ≠ i0}
  let e : Fin m ≃ I := finSuccAboveEquiv i0
  let s' : Fin m → Fin (n + 1) → Real := fun j => s (e j).1
  let c' : Fin m → Real := fun j => c (e j).1
  have hs' : ∀ j, s' j ∈ T := by
    intro j
    simpa [s'] using hs (e j).1
  have hc' : ∀ j, 0 ≤ c' j := by
    intro j
    simpa [c'] using hc (e j).1
  have hsum_filter :
      (∑ i, c i • s i) =
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • s i := by
    have hsum_if :
        (∑ i, c i • s i) = ∑ i, (if i ≠ i0 then c i • s i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : i = i0
      · subst h
        simp [hci0]
      · simp [h]
    have hsum_filter' :
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • s i =
          ∑ i, (if i ≠ i0 then c i • s i else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin (m + 1))))
          (f := fun i => c i • s i) (p := fun i => i ≠ i0))
    calc
      (∑ i, c i • s i) = ∑ i, (if i ≠ i0 then c i • s i else 0) := hsum_if
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • s i := by
          symm
          exact hsum_filter'
  have hsum_subtype :
      ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • s i =
        ∑ i : I, c i.1 • s i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => i ≠ i0))
      (p := fun i => i ≠ i0) (f := fun i => c i • s i) ?_)
    intro i
    simp
  have hsum_I : y = ∑ i : I, c i.1 • s i.1 := by
    calc
      y = ∑ i, c i • s i := hsum
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • s i := hsum_filter
      _ = ∑ i : I, c i.1 • s i.1 := hsum_subtype
  have hsum_equiv :
      ∑ j, c' j • s' j = ∑ i : I, c i.1 • s i.1 := by
    simpa [s', c'] using
      (Equiv.sum_comp e (fun i : I => c i.1 • s i.1))
  refine ⟨s', c', hs', hc', ?_⟩
  calc
    y = ∑ i : I, c i.1 • s i.1 := hsum_I
    _ = ∑ j, c' j • s' j := by
        symm
        exact hsum_equiv

/-- Eliminate one generator from a positive conic combination under linear dependence. -/
lemma conic_elim_one_generator_pos_to_shorter {n m : Nat}
    {T : Set (Fin (n + 1) → Real)} {y : Fin (n + 1) → Real}
    (s : Fin (m + 1) → Fin (n + 1) → Real) (c : Fin (m + 1) → Real)
    (hs : ∀ i, s i ∈ T) (hc : ∀ i, 0 < c i)
    (hsum : y = ∑ i, c i • s i) (hlin : ¬ LinearIndependent Real s) :
    ∃ (s' : Fin m → Fin (n + 1) → Real) (c' : Fin m → Real),
      (∀ j, s' j ∈ T) ∧ (∀ j, 0 ≤ c' j) ∧ y = ∑ j, c' j • s' j := by
  classical
  obtain ⟨μ, hμsum, hμpos⟩ :=
    exists_linear_relation_sum_smul_eq_zero_exists_pos (s := s) hlin
  let P : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => 0 < μ i)
  have hPne : P.Nonempty := by
    rcases hμpos with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp [P, hi]
  obtain ⟨i0, hi0P, hmin⟩ := Finset.exists_min_image P (fun i => c i / μ i) hPne
  have hμi0 : 0 < μ i0 := (Finset.mem_filter.mp hi0P).2
  have hμi0_ne : μ i0 ≠ 0 := ne_of_gt hμi0
  let lam : Real := c i0 / μ i0
  let c1 : Fin (m + 1) → Real := fun i => c i - lam * μ i
  have hlamnonneg : 0 ≤ lam := by
    exact div_nonneg (le_of_lt (hc i0)) (le_of_lt hμi0)
  have hci0 : c1 i0 = 0 := by
    have hmul : (c i0 / μ i0) * μ i0 = c i0 := by
      field_simp [hμi0_ne]
    have hmul' : lam * μ i0 = c i0 := by
      simpa [lam] using hmul
    simp [c1, hmul']
  have hc1 : ∀ i, 0 ≤ c1 i := by
    intro i
    by_cases hμpos_i : 0 < μ i
    · have hi : i ∈ P := by
        simp [P, hμpos_i]
      have hmin_i : lam ≤ c i / μ i := hmin i hi
      have hle : lam * μ i ≤ c i := (le_div_iff₀ hμpos_i).1 hmin_i
      exact sub_nonneg_of_le hle
    · have hμle : μ i ≤ 0 := le_of_not_gt hμpos_i
      have hterm : 0 ≤ -lam * μ i := by
        have : 0 ≤ lam * (-μ i) := mul_nonneg hlamnonneg (neg_nonneg.mpr hμle)
        simpa [mul_comm, mul_left_comm, mul_assoc, mul_neg, neg_mul] using this
      have hc_nonneg : 0 ≤ c i := le_of_lt (hc i)
      have : 0 ≤ c i + (-lam * μ i) := add_nonneg hc_nonneg hterm
      simpa [c1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using this
  have hsum_c1 : y = ∑ i, c1 i • s i := by
    have hsum_expand :
        ∑ i, c i • s i = ∑ i, c1 i • s i + lam • ∑ i, μ i • s i := by
      calc
        ∑ i, c i • s i = ∑ i, (c1 i + lam * μ i) • s i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [c1, sub_eq_add_neg, add_comm, add_left_comm]
        _ = ∑ i, c1 i • s i + ∑ i, (lam * μ i) • s i := by
          simp [add_smul, Finset.sum_add_distrib]
        _ = ∑ i, c1 i • s i + lam • ∑ i, μ i • s i := by
          have hmul :
              ∑ i, (lam * μ i) • s i = lam • ∑ i, μ i • s i := by
            calc
              ∑ i, (lam * μ i) • s i = ∑ i, lam • (μ i • s i) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                simp [mul_smul]
              _ = lam • ∑ i, μ i • s i := by
                simp [Finset.smul_sum]
          simp [hmul]
    calc
      y = ∑ i, c i • s i := hsum
      _ = ∑ i, c1 i • s i + lam • ∑ i, μ i • s i := hsum_expand
      _ = ∑ i, c1 i • s i := by
        simp [hμsum]
  have hsum_filter :
      (∑ i, c1 i • s i) =
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c1 i • s i := by
    have hsum_if :
        (∑ i, c1 i • s i) = ∑ i, (if i ≠ i0 then c1 i • s i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : i = i0
      · subst h
        simp [hci0]
      · simp [h]
    have hsum_filter' :
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c1 i • s i =
          ∑ i, (if i ≠ i0 then c1 i • s i else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin (m + 1))))
          (f := fun i => c1 i • s i) (p := fun i => i ≠ i0))
    calc
      (∑ i, c1 i • s i) = ∑ i, (if i ≠ i0 then c1 i • s i else 0) := hsum_if
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c1 i • s i := by
          symm
          exact hsum_filter'
  let I : Type := {i : Fin (m + 1) // i ≠ i0}
  have hsum_subtype :
      ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c1 i • s i =
        ∑ i : I, c1 i.1 • s i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => i ≠ i0))
      (p := fun i => i ≠ i0) (f := fun i => c1 i • s i) ?_)
    intro i
    simp
  have hsum_I : y = ∑ i : I, c1 i.1 • s i.1 := by
    calc
      y = ∑ i, c1 i • s i := hsum_c1
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c1 i • s i := hsum_filter
      _ = ∑ i : I, c1 i.1 • s i.1 := hsum_subtype
  let e : Fin m ≃ I := finSuccAboveEquiv i0
  let s' : Fin m → Fin (n + 1) → Real := fun j => s (e j).1
  let c' : Fin m → Real := fun j => c1 (e j).1
  have hs' : ∀ j, s' j ∈ T := by
    intro j
    simpa [s'] using hs (e j).1
  have hc' : ∀ j, 0 ≤ c' j := by
    intro j
    simpa [c'] using hc1 (e j).1
  have hsum_equiv :
      ∑ j, c' j • s' j = ∑ i : I, c1 i.1 • s i.1 := by
    simpa [s', c'] using
      (Equiv.sum_comp e (fun i : I => c1 i.1 • s i.1))
  refine ⟨s', c', hs', hc', ?_⟩
  calc
    y = ∑ i : I, c1 i.1 • s i.1 := hsum_I
    _ = ∑ j, c' j • s' j := by
        symm
        exact hsum_equiv

/-- Reduce a lifting-set representation to at most `n + 1` generators. -/
lemma exists_nonneg_sum_smul_liftingSet_le_add_one {n : Nat}
    {S₀ S₁ : Set (Fin n → Real)} {x : Fin n → Real} :
    (Fin.cases (1 : Real) x) ∈ liftingCone (n := n) S₀ S₁ →
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (s : Fin m → Fin (n + 1) → Real) (c : Fin m → Real),
          (∀ i, s i ∈ liftingSet (n := n) S₀ S₁) ∧ (∀ i, 0 ≤ c i) ∧
            (Fin.cases (1 : Real) x) = ∑ i, c i • s i := by
  intro hxcone
  classical
  rcases
      exists_nonneg_sum_smul_liftingSet_of_lift_mem_liftingCone
        (n := n) (S₀ := S₀) (S₁' := S₁) (x := x) hxcone with
    ⟨m, s, c, hs, hc, hsum⟩
  let P : Nat → Prop := fun k =>
    ∃ (t : Fin k → Fin (n + 1) → Real) (w : Fin k → Real),
      (∀ i, t i ∈ liftingSet (n := n) S₀ S₁) ∧ (∀ i, 0 ≤ w i) ∧
        (Fin.cases (1 : Real) x) = ∑ i, w i • t i
  have hP : ∃ k, P k := ⟨m, s, c, hs, hc, hsum⟩
  let m0 := Nat.find hP
  have hP0 : P m0 := Nat.find_spec hP
  rcases hP0 with ⟨s0, c0, hs0, hc0, hsum0⟩
  have hm0 : m0 ≤ n + 1 := by
    by_contra hgt
    have hgt' : m0 > n + 1 := Nat.lt_of_not_ge hgt
    cases h : m0 with
    | zero =>
        simp [h] at hgt'
    | succ m =>
        let e : Fin (m + 1) ≃ Fin m0 := by
          simpa [h] using (Equiv.cast (congrArg Fin h.symm))
        let s0' : Fin (m + 1) → Fin (n + 1) → Real := fun i => s0 (e i)
        let c0' : Fin (m + 1) → Real := fun i => c0 (e i)
        have hs0' : ∀ i, s0' i ∈ liftingSet (n := n) S₀ S₁ := by
          intro i
          have hi : s0 (e i) ∈ liftingSet (n := n) S₀ S₁ := hs0 (e i)
          simpa [s0'] using hi
        have hc0' : ∀ i, 0 ≤ c0' i := by
          intro i
          have hi : 0 ≤ c0 (e i) := hc0 (e i)
          simpa [c0'] using hi
        have hsum0' :
            (Fin.cases (1 : Real) x) = ∑ i, c0' i • s0' i := by
          have hsum0_eq :
              ∑ i : Fin (m + 1), c0 (e i) • s0 (e i) = ∑ i : Fin m0, c0 i • s0 i := by
            simpa using (Equiv.sum_comp e (fun i : Fin m0 => c0 i • s0 i))
          calc
            (Fin.cases (1 : Real) x) = ∑ i : Fin m0, c0 i • s0 i := hsum0
            _ = ∑ i : Fin (m + 1), c0 (e i) • s0 (e i) := by
              symm
              exact hsum0_eq
            _ = ∑ i, c0' i • s0' i := by
              simp [s0', c0']
        have hc0pos : ∀ i, 0 < c0' i := by
          intro i
          by_contra hpos
          have hci0_le : c0' i ≤ 0 := le_of_not_gt hpos
          have hci0_eq : c0' i = 0 := le_antisymm hci0_le (hc0' i)
          rcases
              drop_zero_coeff_sum_smul_to_shorter
                (n := n) (m := m) (T := liftingSet (n := n) S₀ S₁)
                (y := Fin.cases (1 : Real) x) (s := s0') (c := c0')
                hs0' hc0' hsum0' i hci0_eq with
            ⟨s1, c1, hs1, hc1, hsum1⟩
          have hPm : P m := ⟨s1, c1, hs1, hc1, hsum1⟩
          have hm0_le : m0 ≤ m := Nat.find_min' hP hPm
          have hlt : m < m0 := by
            rw [h]
            exact Nat.lt_succ_self m
          exact (not_lt_of_ge hm0_le) hlt
        have hlin : ¬ LinearIndependent Real s0 := by
          intro hli
          have hcard := LinearIndependent.fintype_card_le_finrank (b := s0) hli
          have hm0_le : m0 ≤ n + 1 := by
            simpa using hcard
          exact (not_lt_of_ge hm0_le) hgt'
        have hlin' : ¬ LinearIndependent Real s0' := by
          intro hli
          have hli' : LinearIndependent Real (fun i => s0' (e.symm i)) :=
            LinearIndependent.comp hli e.symm (by simpa using e.symm.injective)
          have hli'' : LinearIndependent Real s0 := by
            simpa [s0'] using hli'
          exact hlin hli''
        rcases
            conic_elim_one_generator_pos_to_shorter
              (n := n) (m := m) (T := liftingSet (n := n) S₀ S₁)
              (y := Fin.cases (1 : Real) x) (s := s0') (c := c0')
              hs0' hc0pos hsum0' hlin' with
          ⟨s1, c1, hs1, hc1, hsum1⟩
        have hPm : P m := ⟨s1, c1, hs1, hc1, hsum1⟩
        have hm0_le : m0 ≤ m := Nat.find_min' hP hPm
        have hlt : m < m0 := by
          rw [h]
          exact Nat.lt_succ_self m
        exact (not_lt_of_ge hm0_le) hlt
  refine ⟨m0, hm0, s0, c0, hs0, hc0, hsum0⟩

/-- Theorem 17.1 (Caratheodory's Theorem). Let `S` be a set of points and directions in `ℝⁿ`,
modeled as a pair `(S₀, S₁)` with point-set `S₀ ⊆ ℝⁿ` and direction-set `S₁ ⊆ ℝⁿ`, and let
`C := conv S` be the resulting mixed convex hull (here: `C := mixedConvexHull S₀ S₁`).

Then `x ∈ C` if and only if `x` can be expressed as a convex combination of `n + 1` of the
points and directions in `S` (not necessarily distinct); in this file, this is represented as
existence of a mixed convex combination of size `m ≤ n + 1`. -/
theorem mem_mixedConvexHull_iff_exists_mixedConvexCombination_le_finrank_add_one
    {n : Nat} (S₀ S₁ : Set (Fin n → Real)) (x : Fin n → Real) :
    x ∈ mixedConvexHull (n := n) S₀ S₁ ↔
      ∃ m : Nat, m ≤ n + 1 ∧ IsMixedConvexCombination n m S₀ S₁ x := by
  constructor
  · intro hx
    have hx' :
        (Fin.cases (1 : Real) x) ∈
          (liftingCone (n := n) S₀ S₁ ∩ liftingHyperplane n) :=
      (mem_mixedConvexHull_iff_lift_mem_liftingCone_inter_liftingHyperplane
        (n := n) (S₀ := S₀) (S₁' := S₁) (x := x)).1 hx
    have hxcone : (Fin.cases (1 : Real) x) ∈ liftingCone (n := n) S₀ S₁ := hx'.1
    rcases
        exists_nonneg_sum_smul_liftingSet_le_add_one
          (n := n) (S₀ := S₀) (S₁ := S₁) (x := x) hxcone with
      ⟨m, hm, s, c, hs, hc, hsum⟩
    have hcomb :
        IsMixedConvexCombination n m S₀ S₁ x :=
      split_liftingSet_sum_to_IsMixedConvexCombination_fixed_length
        (n := n) (m := m) (S₀ := S₀) (S₁' := S₁) s c hs hc hsum
    exact ⟨m, hm, hcomb⟩
  · rintro ⟨m, _hm, hcomb⟩
    exact mem_mixedConvexHull_of_IsMixedConvexCombination
      (n := n) (m := m) (S₀ := S₀) (S₁ := S₁) hcomb

/-- A convex combination lies in the convex hull of its range. -/
lemma conv_mem_range_of_convexCombination {n k : Nat} {p : Fin k → Fin n → Real}
    {w : Fin k → Real} {x : Fin n → Real} (hw : IsConvexWeights k w)
    (hx : x = convexCombination n k p w) :
    x ∈ conv (Set.range p) := by
  rcases hw with ⟨hw_nonneg, hw_sum⟩
  have hx' : ∑ i, w i • p i = x := by
    simpa [convexCombination] using hx.symm
  have hz : ∀ i, p i ∈ Set.range p := fun i => ⟨i, rfl⟩
  have hx'' :
      x ∈ convexHull ℝ (Set.range p) :=
    mem_convexHull_of_exists_fintype (s := Set.range p) (x := x) (w := w) (z := p)
      hw_nonneg hw_sum hz hx'
  simpa [conv] using hx''

/-- Coalesce a convex combination in a union into one indexed by distinct sets. -/
lemma exists_injective_indexed_convexCombination_of_mem_conv_iUnion
    {n : Nat} {I : Type*} (Cᵢ : I → Set (Fin n → Real)) (hconv : ∀ i, Convex ℝ (Cᵢ i))
    {x : Fin n → Real} (hx : x ∈ conv (⋃ i, Cᵢ i)) :
    ∃ k : Nat, ∃ idx : Fin k → I, ∃ p : Fin k → Fin n → Real, ∃ w : Fin k → Real,
      Function.Injective idx ∧ (∀ j, p j ∈ Cᵢ (idx j)) ∧
        IsConvexWeights k w ∧ x = convexCombination n k p w := by
  classical
  have hx' : x ∈ convexHull ℝ (⋃ i, Cᵢ i) := by
    simpa [conv] using hx
  rcases (mem_convexHull_iff_exists_fintype (R := Real) (s := ⋃ i, Cᵢ i) (x := x)).1 hx' with
    ⟨ι, _inst, w0, z, hw0_nonneg, hw0_sum, hz, hsum⟩
  have hidx0_exists : ∀ i, ∃ j, z i ∈ Cᵢ j := by
    intro i
    rcases (Set.mem_iUnion.mp (hz i)) with ⟨j, hj⟩
    exact ⟨j, hj⟩
  choose idx0 hidx0_mem using hidx0_exists
  let s : Finset I := Finset.image idx0 Finset.univ
  let μ : I → Real := fun b =>
    ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i
  let t : Finset I := s.filter (fun b => μ b ≠ 0)
  let y : I → Fin n → Real := fun b =>
    if h : μ b = 0 then 0
    else (1 / μ b) • ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i
  have hμ_nonneg : ∀ b, 0 ≤ μ b := by
    intro b
    refine Finset.sum_nonneg ?_
    intro i hi
    exact hw0_nonneg i
  have hy_mem : ∀ b ∈ t, y b ∈ Cᵢ b := by
    intro b hb
    have hμ : μ b ≠ 0 := (Finset.mem_filter.1 hb).2
    have hμ_pos : 0 < μ b := lt_of_le_of_ne (hμ_nonneg b) (Ne.symm hμ)
    let fiber : Finset ι := Finset.univ.filter (fun i => idx0 i = b)
    have hweights_nonneg : ∀ i ∈ fiber, 0 ≤ w0 i / μ b := by
      intro i hi
      exact div_nonneg (hw0_nonneg i) (le_of_lt hμ_pos)
    have hweights_sum : ∑ i ∈ fiber, w0 i / μ b = (1 : Real) := by
      have hμ_ne : μ b ≠ 0 := hμ
      calc
        ∑ i ∈ fiber, w0 i / μ b
            = ∑ i ∈ fiber, w0 i * (μ b)⁻¹ := by
                simp [div_eq_mul_inv]
        _ = (∑ i ∈ fiber, w0 i) * (μ b)⁻¹ := by
                simpa using
                  (Finset.sum_mul (s := fiber) (f := w0) (a := (μ b)⁻¹)).symm
        _ = μ b * (μ b)⁻¹ := by
                simp [μ, fiber]
        _ = 1 := by
                simp [hμ_ne]
    have hz_mem' : ∀ i ∈ fiber, z i ∈ Cᵢ b := by
      intro i hi
      have hidx : idx0 i = b := (Finset.mem_filter.1 hi).2
      simpa [hidx] using hidx0_mem i
    have hy' :
        (∑ i ∈ fiber, (w0 i / μ b) • z i) ∈ Cᵢ b :=
      (hconv b).sum_mem hweights_nonneg hweights_sum hz_mem'
    have hy_eq :
        y b = ∑ i ∈ fiber, (w0 i / μ b) • z i := by
      have hμ_ne : μ b ≠ 0 := hμ
      calc
        y b = (1 / μ b) • ∑ i ∈ fiber, w0 i • z i := by
          simp [y, hμ, fiber]
        _ = ∑ i ∈ fiber, (1 / μ b) • (w0 i • z i) := by
          simpa using (Finset.smul_sum (s := fiber) (f := fun i => w0 i • z i) (r := 1 / μ b))
        _ = ∑ i ∈ fiber, (w0 i / μ b) • z i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [div_eq_mul_inv, smul_smul, mul_comm]
    simpa [hy_eq] using hy'
  have hy_mul :
      ∀ b ∈ s, μ b • y b =
        ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i := by
    intro b hb
    by_cases hμ : μ b = 0
    · have hsum_weights : ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i = 0 := by
        simp [μ, hμ]
      have hzero : ∀ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i = 0 := by
        have hnonneg :
            ∀ i ∈ Finset.univ.filter (fun i => idx0 i = b), 0 ≤ w0 i := by
          intro i hi
          exact hw0_nonneg i
        exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum_weights
      have hsum_zero :
          ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp [hzero i hi]
      simp [y, hμ, hsum_zero]
    · have hμ_ne : μ b ≠ 0 := hμ
      have hsum :
          μ b • y b =
            μ b • ((1 / μ b) •
              ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i) := by
        simp [y, hμ]
      calc
        μ b • y b =
            μ b • ((1 / μ b) •
              ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i) := hsum
        _ = (μ b * (1 / μ b)) •
            ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i := by
            simp [smul_smul]
        _ = ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i := by
            simp [div_eq_mul_inv, hμ_ne]
  have hsum_s : ∑ b ∈ s, μ b = ∑ i, w0 i := by
    have hmaps :
        ∀ i ∈ (Finset.univ : Finset ι), idx0 i ∈ s := by
      intro i hi
      exact Finset.mem_image_of_mem idx0 (Finset.mem_univ i)
    simpa [μ] using
      (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι)) (t := s)
        (g := idx0) (f := w0) hmaps)
  have hsum_y : ∑ b ∈ s, μ b • y b = ∑ i, w0 i • z i := by
    have hmaps :
        ∀ i ∈ (Finset.univ : Finset ι), idx0 i ∈ s := by
      intro i hi
      exact Finset.mem_image_of_mem idx0 (Finset.mem_univ i)
    calc
      ∑ b ∈ s, μ b • y b =
          ∑ b ∈ s, ∑ i ∈ Finset.univ.filter (fun i => idx0 i = b), w0 i • z i := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            simp [hy_mul b hb]
      _ = ∑ i ∈ (Finset.univ : Finset ι), w0 i • z i := by
            simpa using
              (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι)) (t := s)
                (g := idx0) (f := fun i => w0 i • z i) hmaps)
      _ = ∑ i, w0 i • z i := by simp
  have hx_sum : x = ∑ b ∈ s, μ b • y b := by
    calc
      x = ∑ i, w0 i • z i := by
        simpa using hsum.symm
      _ = ∑ b ∈ s, μ b • y b := by
        symm
        exact hsum_y
  have hx_sum_t : x = ∑ b ∈ t, μ b • y b := by
    have hsum_t_eq :
        ∑ b ∈ t, μ b • y b = ∑ b ∈ s, μ b • y b := by
      have hsum' :
          ∑ b ∈ s.filter (fun b => μ b ≠ 0), μ b • y b = ∑ b ∈ s, μ b • y b := by
        refine (Finset.sum_filter_of_ne (s := s) (p := fun b => μ b ≠ 0)
          (f := fun b => μ b • y b) ?_)
        intro b hb hne
        by_contra hμ
        apply hne
        simp [hμ]
      simpa [t] using hsum'
    calc
      x = ∑ b ∈ s, μ b • y b := hx_sum
      _ = ∑ b ∈ t, μ b • y b := by
        symm
        exact hsum_t_eq
  let k : Nat := t.card
  let e : t ≃ Fin k := t.equivFin
  let idx : Fin k → I := fun j => (e.symm j).1
  let p : Fin k → Fin n → Real := fun j => y (e.symm j).1
  let w : Fin k → Real := fun j => μ (e.symm j).1
  have hidx : Function.Injective idx := by
    intro j1 j2 h
    apply e.symm.injective
    apply Subtype.ext
    simpa [idx] using h
  have hp' : ∀ j, p j ∈ Cᵢ (idx j) := by
    intro j
    have hb : (e.symm j).1 ∈ t := (e.symm j).2
    exact hy_mem _ hb
  have hw' : IsConvexWeights k w := by
    refine ⟨?_, ?_⟩
    · intro j
      exact hμ_nonneg _
    · have hsum_t :
          ∑ j, w j = ∑ b : t, μ b.1 := by
        simpa [w] using (Equiv.sum_comp e.symm (fun b : t => μ b.1))
      have hsum_t' : ∑ b : t, μ b.1 = ∑ b ∈ t, μ b := by
        symm
        refine Finset.sum_subtype (s := t) (p := fun b => b ∈ t) (f := μ) ?_
        intro b
        simp
      have hsum_t'' : ∑ b ∈ t, μ b = ∑ b ∈ s, μ b := by
        simpa [t] using (Finset.sum_filter_ne_zero (s := s) (f := μ))
      calc
        ∑ j, w j = ∑ b : t, μ b.1 := hsum_t
        _ = ∑ b ∈ t, μ b := hsum_t'
        _ = ∑ b ∈ s, μ b := hsum_t''
        _ = ∑ i, w0 i := hsum_s
        _ = 1 := hw0_sum
  have hx_eq : x = convexCombination n k p w := by
    have hx_subtype : x = ∑ b : t, μ b.1 • y b.1 := by
      have hsum_subtype :
          ∑ b ∈ t, μ b • y b = ∑ b : t, μ b.1 • y b.1 := by
        refine Finset.sum_subtype (s := t) (p := fun b => b ∈ t)
          (f := fun b => μ b • y b) ?_
        intro b
        simp
      calc
        x = ∑ b ∈ t, μ b • y b := hx_sum_t
        _ = ∑ b : t, μ b.1 • y b.1 := hsum_subtype
    have hsum_fin :
        ∑ j, w j • p j = ∑ b : t, μ b.1 • y b.1 := by
      simpa [w, p] using (Equiv.sum_comp e.symm (fun b : t => μ b.1 • y b.1))
    calc
      x = ∑ b : t, μ b.1 • y b.1 := hx_subtype
      _ = ∑ j, w j • p j := by
            symm
            exact hsum_fin
      _ = convexCombination n k p w := by
            simp [convexCombination]
  exact ⟨k, idx, p, w, hidx, hp', hw', hx_eq⟩

end Section17
end Chap04
