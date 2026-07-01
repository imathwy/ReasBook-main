/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part5

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- Finite-case contradiction in the non-`⊤` branch of `recessionCone_sum_epigraph_prod`. -/
lemma recessionCone_sum_epigraph_prod_finite_contra {n m : Nat}
    {f f0_plus : Fin m → (Fin n → Real) → EReal}
    {g : (Fin m → (Fin n → Real)) → EReal}
    (hg : g = fun x => Finset.univ.sum (fun i => f i (x i)))
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal))
    (_hnotbot0 : ∀ i : Fin m, ∀ x, f0_plus i x ≠ (⊥ : EReal))
    (_hrec_i :
      ∀ i : Fin m,
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i))
    {p : (Fin m → (Fin n → Real)) × Real} {i0 : Fin m} {a : Fin m → Real}
    {x0 : Fin n → Real} {μ0 t : Real}
    (hgt0 : f i0 (x0 + t • p.1 i0) > ((μ0 + t * a i0 : Real) : EReal))
    (_hx0 : f i0 x0 ≤ (μ0 : EReal))
    (ha_sum : Finset.univ.sum (fun i => a i) = p.2)
    {x : Fin m → (Fin n → Real)} {μ : Fin m → Real}
    (hxi0 : x i0 = x0) (hμi0 : μ i0 = μ0)
    (_hxle : ∀ i, f i (x i) ≤ (μ i : EReal))
    {ε : Fin m → Real}
    (hslack :
      ∀ i ≠ i0,
        ((μ i + t * a i - ε i : Real) : EReal) ≤ f i (x i + t • p.1 i))
    (hε :
      (Finset.univ.erase i0).sum (fun i => ε i) <
        (f i0 (x0 + t • p.1 i0)).toReal - (μ0 + t * a i0))
    (hmem''' :
      g (x + t • p.1) ≤ (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal))
    (htopg : ¬ ∃ i, f i (x i + t • p.1 i) = (⊤ : EReal)) :
    False := by
  classical
  let β : Fin m → EReal := fun i => f i (x i + t • p.1 i)
  let b : Fin m → Real := fun i => μ i + t * a i
  have hnot_top : ∀ i, β i ≠ (⊤ : EReal) := by
    intro i htopi
    exact htopg ⟨i, by simpa [β] using htopi⟩
  have hnot_bot : ∀ i, β i ≠ (⊥ : EReal) := by
    intro i
    exact hnotbot i (x i + t • p.1 i)
  have hgt : β i0 > (b i0 : EReal) := by
    simpa [β, b, hxi0, hμi0] using hgt0
  have hslack' : ∀ i ≠ i0, β i ≥ ((b i - ε i : Real) : EReal) := by
    intro i hi
    have h := hslack i hi
    simpa [β, b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hε' :
      (Finset.univ.erase i0).sum (fun i => ε i) <
        (β i0).toReal - b i0 := by
    simpa [β, b, hxi0, hμi0] using hε
  have hsum_gt :
      Finset.univ.sum (fun i => β i) > (Finset.univ.sum (fun i => b i) : EReal) :=
    ereal_strict_sum_from_one_component_with_slack (β := β) (b := b) (ε := ε) (i0 := i0)
      hnot_top hnot_bot hgt hslack' hε'
  have hsum_le :
      Finset.univ.sum (fun i => β i) ≤ (Finset.univ.sum (fun i => b i) : EReal) := by
    have hmem'''_sum := hmem'''
    simp [hg] at hmem'''_sum
    have hsum_b :
        Finset.univ.sum (fun i => b i) =
          Finset.univ.sum (fun i => μ i) + t * p.2 := by
      calc
        Finset.univ.sum (fun i => b i) =
            Finset.univ.sum (fun i => μ i + t * a i) := by rfl
        _ = Finset.univ.sum (fun i => μ i) +
              Finset.univ.sum (fun i => t * a i) := by
          simp [Finset.sum_add_distrib]
        _ = Finset.univ.sum (fun i => μ i) + t * Finset.univ.sum (fun i => a i) := by
          simp [Finset.mul_sum]
        _ = Finset.univ.sum (fun i => μ i) + t * p.2 := by
          simp [ha_sum]
    have hsum_b_ereal :
        Finset.univ.sum (fun i => (b i : EReal)) =
          (Finset.univ.sum (fun i => μ i) : EReal) + (t : EReal) * (p.2 : EReal) := by
      have hsum_b' :
          Finset.univ.sum (fun i => (b i : EReal)) =
            ((Finset.univ.sum (fun i => μ i) + t * p.2) : EReal) := by
        have hsum_b'' := congrArg (fun x : Real => (x : EReal)) hsum_b
        simpa [sum_coe_ereal] using hsum_b''
      simpa [EReal.coe_add, EReal.coe_mul, ← sum_coe_ereal] using hsum_b'
    rw [← sum_coe_ereal (s := Finset.univ) (f := fun i => μ i)] at hmem'''_sum
    rw [← hsum_b_ereal] at hmem'''_sum
    simpa [β] using hmem'''_sum
  exact (not_lt_of_ge hsum_le) hsum_gt

/-- A strict inequality at one component gives a strict inequality for the total sum. -/
lemma sum_lt_sum_of_one_lt {m : Nat} {a b : Fin m → Real} {i0 : Fin m}
    (hlt : a i0 < b i0) (hEq : ∀ i ≠ i0, a i = b i) :
    Finset.univ.sum (fun i => a i) < Finset.univ.sum (fun i => b i) := by
  classical
  have hsum_a :
      Finset.univ.sum (fun i => a i) =
        a i0 + (Finset.univ.erase i0).sum (fun i => a i) := by
    symm
    exact
      (Finset.add_sum_erase (s := Finset.univ) (f := fun i => a i) (a := i0) (by simp))
  have hsum_b :
      Finset.univ.sum (fun i => b i) =
        b i0 + (Finset.univ.erase i0).sum (fun i => b i) := by
    symm
    exact
      (Finset.add_sum_erase (s := Finset.univ) (f := fun i => b i) (a := i0) (by simp))
  have hsum_rest :
      (Finset.univ.erase i0).sum (fun i => a i) =
        (Finset.univ.erase i0).sum (fun i => b i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    simp [hEq i hne]
  calc
    Finset.univ.sum (fun i => a i) =
        a i0 + (Finset.univ.erase i0).sum (fun i => a i) := hsum_a
    _ = a i0 + (Finset.univ.erase i0).sum (fun i => b i) := by simp [hsum_rest]
    _ < b i0 + (Finset.univ.erase i0).sum (fun i => b i) := by
      exact add_lt_add_of_lt_of_le hlt (le_rfl)
    _ = Finset.univ.sum (fun i => b i) := by
      exact hsum_b.symm

/-- A strict inequality at one component of a finite `EReal` sum gives a strict inequality for the
total sum (when the other components agree with the real bounds). -/
lemma ereal_sum_lt_sum_of_one_lt {m : Nat} {β : Fin m → EReal} {b : Fin m → Real} {i0 : Fin m}
    (hbot : ∀ i, β i ≠ (⊥ : EReal)) (htop : ∀ i, β i ≠ (⊤ : EReal))
    (hlt : (b i0 : EReal) < β i0) (hEq : ∀ i ≠ i0, β i = (b i : EReal)) :
    Finset.univ.sum (fun i => β i) > (Finset.univ.sum (fun i => b i) : EReal) := by
  classical
  let rb : Fin m → Real := fun i => (β i).toReal
  have hβ_eq : ∀ i, β i = (rb i : EReal) := by
    intro i
    simpa [rb] using (EReal.coe_toReal (htop i) (hbot i)).symm
  have hEq' : ∀ i ≠ i0, b i = rb i := by
    intro i hi
    have hb : (b i : EReal) = (rb i : EReal) := by
      calc
        (b i : EReal) = β i := by
          symm
          exact hEq i hi
        _ = (rb i : EReal) := hβ_eq i
    have hb' := congrArg EReal.toReal hb
    simpa using hb'
  have hlt_real : b i0 < rb i0 := by
    have hlt' : (b i0 : EReal) < (rb i0 : EReal) := by
      simpa [hβ_eq i0] using hlt
    exact (EReal.coe_lt_coe_iff).1 hlt'
  have hsum_lt :
      Finset.univ.sum (fun i => b i) <
        Finset.univ.sum (fun i => rb i) :=
    sum_lt_sum_of_one_lt (i0 := i0) hlt_real hEq'
  have hsum_lt' :
      Finset.univ.sum (fun i => (b i : EReal)) <
        Finset.univ.sum (fun i => (rb i : EReal)) := by
    simpa [sum_coe_ereal] using (EReal.coe_lt_coe_iff).2 hsum_lt
  have hsum_eq :
      Finset.univ.sum (fun i => β i) =
        Finset.univ.sum (fun i => (rb i : EReal)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [hβ_eq i]
  have hsum_b :
      (Finset.univ.sum (fun i => b i) : EReal) =
        Finset.univ.sum (fun i => (b i : EReal)) := by
    simp [sum_coe_ereal]
  have hsum_lt'' :
      (Finset.univ.sum (fun i => b i) : EReal) <
        Finset.univ.sum (fun i => β i) := by
    simpa [hsum_eq, hsum_b] using hsum_lt'
  simpa [gt_iff_lt] using hsum_lt''

/-- Componentwise recession directions give a recession direction for the summed epigraph. -/
lemma recessionCone_sum_epigraph_prod_of_components {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    {g : (Fin m → (Fin n → Real)) → EReal}
    (hg : g = fun x => Finset.univ.sum (fun i => f i (x i)))
    (hm : 0 < m) {v : Fin m → (Fin n → Real)} {a : Fin m → Real}
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal))
    (hrec : ∀ i, (v i, a i) ∈
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i))) :
    (v, Finset.univ.sum (fun i => a i)) ∈
      Set.recessionCone {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
  intro x hx t ht
  have hxle : g x.1 ≤ (x.2 : EReal) := hx
  have hxle' :
      Finset.univ.sum (fun i => f i (x.1 i)) ≤ (x.2 : EReal) := by
    simpa [hg] using hxle
  have hbot : ∀ i, f i (x.1 i) ≠ (⊥ : EReal) := by
    intro i
    exact hnotbot i (x.1 i)
  obtain ⟨μ, hμle, hμsum⟩ :=
    split_real_sum_of_le (m := m) (hm := hm) (β := fun i => f i (x.1 i)) (α := x.2)
      hbot hxle'
  have hcomp :
      ∀ i,
        f i (x.1 i + t • v i) ≤ ((μ i + t * a i : Real) : EReal) := by
    intro i
    have hxmem :
        (x.1 i, μ i) ∈ epigraph (Set.univ : Set (Fin n → Real)) (f i) := by
      have hle : f i (x.1 i) ≤ (μ i : EReal) := hμle i
      exact (mem_epigraph_univ_iff (f := f i)).2 hle
    have hmem := (hrec i) hxmem ht
    have hmem' :
        f i (x.1 i + t • v i) ≤ ((μ i + t * a i : Real) : EReal) :=
      (mem_epigraph_univ_iff (f := f i)).1 hmem
    exact hmem'
  have hsum_le :
      Finset.univ.sum (fun i => f i (x.1 i + t • v i)) ≤
        Finset.univ.sum (fun i => ((μ i + t * a i : Real) : EReal)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hcomp i
  have hsum_real :
      Finset.univ.sum (fun i => (μ i + t * a i)) =
        x.2 + t * Finset.univ.sum (fun i => a i) := by
    calc
      Finset.univ.sum (fun i => (μ i + t * a i)) =
          (Finset.univ.sum (fun i => μ i)) +
            Finset.univ.sum (fun i => t * a i) := by
        simp [Finset.sum_add_distrib]
      _ = x.2 + t * Finset.univ.sum (fun i => a i) := by
        have hmul :
            Finset.univ.sum (fun i => t * a i) =
              t * Finset.univ.sum (fun i => a i) := by
          simpa using
            (Finset.mul_sum (s := Finset.univ) (f := fun i => a i) (a := t)).symm
        simp [hμsum, hmul]
  have hle :
      g (x.1 + t • v) ≤ (x.2 + t * Finset.univ.sum (fun i => a i) : Real) := by
    have hsum_le' :
        (Finset.univ.sum (fun i => f i (x.1 i + t • v i))) ≤
          (x.2 + t * Finset.univ.sum (fun i => a i) : Real) := by
      have hsum_real_ereal :
          Finset.univ.sum (fun i => ((μ i + t * a i : Real) : EReal)) =
            (x.2 : EReal) + (t : EReal) * (Finset.univ.sum (fun i => a i) : Real) := by
        have h := congrArg (fun r : Real => (r : EReal)) hsum_real
        simpa [EReal.coe_add, EReal.coe_mul, ← sum_coe_ereal] using h
      have hsum_le_expanded :
          Finset.univ.sum (fun i => f i (x.1 i + t • v i)) ≤
            (x.2 : EReal) + (t : EReal) * (Finset.univ.sum (fun i => a i) : Real) := by
        exact hsum_le.trans_eq hsum_real_ereal
      simpa [EReal.coe_add, EReal.coe_mul] using hsum_le_expanded
    simpa [hg] using hsum_le'
  simpa using hle

/-- Recession cone of the sum-epigraph on the product space. -/
lemma recessionCone_sum_epigraph_prod {n m : Nat}
    {f f0_plus : Fin m → (Fin n → Real) → EReal}
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal))
    (hnotbot0 : ∀ i : Fin m, ∀ x, f0_plus i x ≠ (⊥ : EReal))
    (hconv_i :
      ∀ i : Fin m,
        Convex Real (epigraph (Set.univ : Set (Fin n → Real)) (f i)))
    (hrec_i :
      ∀ i : Fin m,
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i)) :
    let g : (Fin m → (Fin n → Real)) → EReal :=
      fun x => Finset.univ.sum (fun i => f i (x i))
    let g0_plus : (Fin m → (Fin n → Real)) → EReal :=
      fun x => Finset.univ.sum (fun i => f0_plus i (x i))
    Set.recessionCone
        {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} =
      {p : (Fin m → (Fin n → Real)) × Real | g0_plus p.1 ≤ (p.2 : EReal)} := by
  classical
  intro g g0_plus
  ext p
  by_cases hm : m = 0
  · subst hm
    have hgoal :
        p ∈
            Set.recessionCone
              {p : (Fin 0 → (Fin n → Real)) × Real | (0 : EReal) ≤ (p.2 : EReal)} ↔
          (0 : EReal) ≤ (p.2 : EReal) := by
      constructor
      · intro hp
        have hmem :=
          hp (x := (0, (0 : Real))) (by simp) (t := 1) (by linarith)
        simpa using hmem
      · intro hp x hx t ht
        have hx' : (0 : Real) ≤ x.2 := (EReal.coe_le_coe_iff).1 hx
        have hp' : (0 : Real) ≤ p.2 := (EReal.coe_le_coe_iff).1 hp
        have hsum : 0 ≤ x.2 + t * p.2 := by nlinarith
        have hsum' :
            (0 : EReal) ≤ ((x.2 + t * p.2 : Real) : EReal) :=
          (EReal.coe_le_coe_iff).2 hsum
        change (0 : EReal) ≤ ((x.2 + t * p.2 : Real) : EReal)
        exact hsum'
    simpa [g, g0_plus] using hgoal
  · have hm' : 0 < m := Nat.pos_of_ne_zero hm
    constructor
    · intro hp
      have hne_epi :
          ∀ i : Fin m,
            Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) :=
        nonempty_epigraph_of_hrec (f := f) (f0_plus := f0_plus) hnotbot0 hrec_i
      have hbot : ∀ i, f0_plus i (p.1 i) ≠ (⊥ : EReal) := by
        intro i
        exact hnotbot0 i (p.1 i)
      by_contra hle
      have hgt :
          Finset.univ.sum (fun i => f0_plus i (p.1 i)) > (p.2 : EReal) := by
        have hgt' : g0_plus p.1 > (p.2 : EReal) := lt_of_not_ge hle
        simpa [g0_plus] using hgt'
      by_cases htop : ∃ i, f0_plus i (p.1 i) = (⊤ : EReal)
      · rcases htop with ⟨i0, htop⟩
        classical
        let a' : Fin m → Real := fun i =>
          if i = i0 then 0 else (f0_plus i (p.1 i)).toReal - 1
        have ha'_lt : ∀ i ≠ i0, ((a' i : Real) : EReal) < f0_plus i (p.1 i) := by
          intro i hi
          by_cases htopi : f0_plus i (p.1 i) = (⊤ : EReal)
          · have : ((a' i : Real) : EReal) < (⊤ : EReal) := by
              exact EReal.coe_lt_top (a' i)
            simpa [a', hi, htopi] using this
          · have hboti : f0_plus i (p.1 i) ≠ (⊥ : EReal) := hnotbot0 i (p.1 i)
            have hβ_eq :
                f0_plus i (p.1 i) =
                  ((f0_plus i (p.1 i)).toReal : EReal) := by
              simpa using (EReal.coe_toReal htopi hboti).symm
            have hlt_real : a' i < (f0_plus i (p.1 i)).toReal := by
              simp [a', hi]
            have hlt' :
                ((a' i : Real) : EReal) <
                  ((f0_plus i (p.1 i)).toReal : EReal) :=
              (EReal.coe_lt_coe_iff).2 hlt_real
            rw [hβ_eq]
            exact hlt'
        let a : Fin m → Real := fun i =>
          if i = i0 then p.2 - (Finset.univ.erase i0).sum (fun j => a' j) else a' i
        have ha_sum : Finset.univ.sum (fun i => a i) = p.2 := by
          have hsum_a :
              Finset.univ.sum (fun i => a i) =
                a i0 + (Finset.univ.erase i0).sum (fun i => a i) := by
            symm
            exact
              (Finset.add_sum_erase (s := Finset.univ) (f := fun i => a i) (a := i0)
                (by exact Finset.mem_univ i0))
          have hsum_erase :
              (Finset.univ.erase i0).sum (fun i => a i) =
                (Finset.univ.erase i0).sum (fun i => a' i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
            simp [a, a', hne]
          have ha_i0 : a i0 = p.2 - (Finset.univ.erase i0).sum (fun j => a' j) := by
            simp [a]
          calc
            Finset.univ.sum (fun i => a i) =
                a i0 + (Finset.univ.erase i0).sum (fun i => a i) := hsum_a
            _ = (p.2 - (Finset.univ.erase i0).sum (fun j => a' j)) +
                  (Finset.univ.erase i0).sum (fun i => a' i) := by
              simp [ha_i0, hsum_erase]
            _ = p.2 := by
              linarith
        have ha_lt : ∀ i ≠ i0, ((a i : Real) : EReal) < f0_plus i (p.1 i) := by
          intro i hi
          simpa [a, hi] using ha'_lt i hi
        have ha_i0 : ((a i0 : Real) : EReal) < f0_plus i0 (p.1 i0) := by
          simp [htop]
        have hnot_mem :
            (p.1 i0, a i0) ∉
              Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i0)) := by
          intro hmem
          have hmem' :
              (p.1 i0, a i0) ∈
                epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i0) := by
            simpa [hrec_i i0] using hmem
          have hle :
              f0_plus i0 (p.1 i0) ≤ (a i0 : EReal) :=
            (mem_epigraph_univ_iff (f := f0_plus i0)).1 hmem'
          exact (not_lt_of_ge hle) ha_i0
        rcases
            not_mem_recessionCone_epigraph_witness
              (f := f i0) (v := p.1 i0) (a := a i0) hnot_mem with
          ⟨x0, μ0, t, ht, hgt0, hx0⟩
        have htpos : 0 < t := by
          by_contra hle
          have ht0 : t = 0 := by
            exact le_antisymm (le_of_not_gt hle) ht
          subst ht0
          have : f i0 x0 > (μ0 : EReal) := by
            simpa using hgt0
          exact (not_lt_of_ge hx0) this
        by_cases htopi0 : f i0 (x0 + t • p.1 i0) = (⊤ : EReal)
        · classical
          choose q hq using hne_epi
          let x' : Fin m → (Fin n → Real) := fun i => (q i).1
          let μ' : Fin m → Real := fun i => (q i).2
          have hx' :
              ∀ i, (x' i, μ' i) ∈ epigraph (Set.univ : Set (Fin n → Real)) (f i) := by
            intro i
            simpa [x', μ'] using hq i
          let x : Fin m → (Fin n → Real) := fun i => if h : i = i0 then x0 else x' i
          let μ : Fin m → Real := fun i => if h : i = i0 then μ0 else μ' i
          have hxle : ∀ i, f i (x i) ≤ (μ i : EReal) := by
            intro i
            by_cases h : i = i0
            · subst h
              simpa [x, μ] using hx0
            · have hx'' : f i (x' i) ≤ (μ' i : EReal) :=
                (mem_epigraph_univ_iff (f := f i)).1 (hx' i)
              simpa [x, μ, h] using hx''
          have hxg :
              g x ≤ Finset.univ.sum (fun i => (μ i : EReal)) := by
            have hsum :
                Finset.univ.sum (fun i => f i (x i)) ≤
                  Finset.univ.sum (fun i => (μ i : EReal)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact hxle i
            dsimp [g]
            exact hsum
          have hmem' :
              (x, Finset.univ.sum (fun i => μ i)) ∈
                {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
            simpa [Set.mem_setOf_eq, sum_coe_ereal] using hxg
          have hmem'' := hp hmem' ht
          have hmem''' :
              g (x + t • p.1) ≤
                (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
            simpa using hmem''
          have hbot' :
              ∀ i ∈ (Finset.univ : Finset (Fin m)),
                f i (x i + t • p.1 i) ≠ (⊥ : EReal) := by
            intro i hi
            exact hnotbot i (x i + t • p.1 i)
          have hsum_top :
              Finset.univ.sum (fun i => f i (x i + t • p.1 i)) = (⊤ : EReal) :=
            sum_eq_top_of_eq_top (s := Finset.univ)
              (β := fun i => f i (x i + t • p.1 i))
              (i0 := i0) (by simp) (by simp [x, htopi0]) hbot'
          have htop_le :
              (⊤ : EReal) ≤
                (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
            simpa [g, hsum_top] using hmem'''
          exact (not_top_le_coe (Finset.univ.sum (fun i => μ i) + t * p.2)) htop_le
        · have hboti0 : f i0 (x0 + t • p.1 i0) ≠ (⊥ : EReal) :=
            hnotbot i0 (x0 + t • p.1 i0)
          have hβ_eq :
              f i0 (x0 + t • p.1 i0) =
                ((f i0 (x0 + t • p.1 i0)).toReal : EReal) := by
            simpa using (EReal.coe_toReal htopi0 hboti0).symm
          have hgt0' :
              (μ0 + t * a i0 : EReal) <
                ((f i0 (x0 + t • p.1 i0)).toReal : EReal) := by
            have hgt0'' :
                (μ0 + t * a i0 : EReal) < f i0 (x0 + t • p.1 i0) := by
              simpa [gt_iff_lt] using hgt0
            convert hgt0'' using 1
            exact hβ_eq.symm
          let gap : Real :=
            (f i0 (x0 + t • p.1 i0)).toReal - (μ0 + t * a i0)
          have hgap : 0 < gap := by
            have hgt0_real :
                μ0 + t * a i0 < (f i0 (x0 + t • p.1 i0)).toReal :=
              (EReal.coe_lt_coe_iff).1 hgt0'
            dsimp [gap]
            linarith
          let ε : Fin m → Real := fun i => if i = i0 then 0 else gap / (2 * (m : Real))
          have hdenom : 0 < (2 : Real) * (m : Real) := by
            have hmpos : (0 : Real) < (m : Real) := by exact_mod_cast hm'
            linarith
          have hεpos : ∀ i ≠ i0, 0 < ε i := by
            intro i hi
            have hpos : 0 < gap / (2 * (m : Real)) := by
              exact div_pos hgap hdenom
            simpa [ε, hi] using hpos
          have hrec_tight :
              ∀ i ≠ i0,
                ∃ x : Fin n → Real, ∃ μ : Real,
                  f i x ≤ (μ : EReal) ∧
                    ((μ + t * a i - ε i : Real) : EReal) ≤ f i (x + t • p.1 i) := by
            intro i hi
            have ha_i : ((a i : Real) : EReal) < f0_plus i (p.1 i) := ha_lt i hi
            exact
              recCone_tight_approx_at_t (f := f i) (f0_plus := f0_plus i) (hrec := hrec_i i)
                (hconv := hconv_i i) (v := p.1 i) (a := a i) ha_i (t := t) htpos (ε := ε i)
                (hε := hεpos i hi)
          classical
          choose x' μ' hx' using hrec_tight
          let x : Fin m → (Fin n → Real) := fun i => if h : i = i0 then x0 else x' i h
          let μ : Fin m → Real := fun i => if h : i = i0 then μ0 else μ' i h
          have hxi0 : x i0 = x0 := by
            simp [x]
          have hμi0 : μ i0 = μ0 := by
            simp [μ]
          have hxle : ∀ i, f i (x i) ≤ (μ i : EReal) := by
            intro i
            by_cases h : i = i0
            · subst h
              simpa [x, μ] using hx0
            · have hx'' : f i (x' i h) ≤ (μ' i h : EReal) :=
                (hx' i h).1
              simpa [x, μ, h] using hx''
          have hslack :
              ∀ i ≠ i0,
                ((μ i + t * a i - ε i : Real) : EReal) ≤ f i (x i + t • p.1 i) := by
            intro i hi
            have hx'' := (hx' i hi).2
            simpa [x, μ, hi] using hx''
          have hxg :
              g x ≤ Finset.univ.sum (fun i => (μ i : EReal)) := by
            have hsum :
                Finset.univ.sum (fun i => f i (x i)) ≤
                  Finset.univ.sum (fun i => (μ i : EReal)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact hxle i
            dsimp [g]
            exact hsum
          have hmem' :
              (x, Finset.univ.sum (fun i => μ i)) ∈
                {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
            simpa [Set.mem_setOf_eq, sum_coe_ereal] using hxg
          have hmem'' := hp hmem' ht
          have hmem''' :
              g (x + t • p.1) ≤
                (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
            simpa using hmem''
          -- If any component is `⊤`, the sum is `⊤` and we get a contradiction immediately.
          by_cases htopg :
              ∃ i, f i (x i + t • p.1 i) = (⊤ : EReal)
          · rcases htopg with ⟨i1, htop1⟩
            have hbot' :
                ∀ i ∈ (Finset.univ : Finset (Fin m)),
                  f i (x i + t • p.1 i) ≠ (⊥ : EReal) := by
              intro i hi
              exact hnotbot i (x i + t • p.1 i)
            have hsum_top :
                Finset.univ.sum (fun i => f i (x i + t • p.1 i)) = (⊤ : EReal) :=
              sum_eq_top_of_eq_top (s := Finset.univ)
                (β := fun i => f i (x i + t • p.1 i))
                (i0 := i1) (by simp) htop1 hbot'
            have htop_le :
                (⊤ : EReal) ≤
                  (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
              simpa [g, hsum_top] using hmem'''
            exact (not_top_le_coe (Finset.univ.sum (fun i => μ i) + t * p.2)) htop_le
          · have hε :
                (Finset.univ.erase i0).sum (fun i => ε i) <
                  (f i0 (x0 + t • p.1 i0)).toReal - (μ0 + t * a i0) := by
              have hsum_eps :
                  (Finset.univ.erase i0).sum (fun i => ε i) =
                    (m - 1 : Real) * (gap / (2 * (m : Real))) := by
                classical
                have hcard : (Finset.univ.erase i0).card = m - 1 := by
                  simp [Finset.card_erase_of_mem]
                have hcard_real :
                    ((Finset.univ.erase i0).card : Real) = (m - 1 : Real) := by
                  have hm1 : (1 : Nat) ≤ m := Nat.succ_le_iff.mp hm'
                  simp [hcard, Nat.cast_sub hm1, Nat.cast_one]
                calc
                  (Finset.univ.erase i0).sum (fun i => ε i) =
                      (Finset.univ.erase i0).sum (fun _ => gap / (2 * (m : Real))) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    have hi0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
                    simp [ε, hi0]
                  _ =
                      ((Finset.univ.erase i0).card : Real) *
                        (gap / (2 * (m : Real))) := by
                    simp [Finset.sum_const, mul_comm]
                  _ = (m - 1 : Real) * (gap / (2 * (m : Real))) := by
                    rw [hcard_real]
              have hnum_lt : (m - 1 : Real) < (2 : Real) * (m : Real) := by
                have hmpos : (0 : Real) < (m : Real) := by exact_mod_cast hm'
                linarith
              have hratio_lt :
                  (m - 1 : Real) / ((2 : Real) * (m : Real)) < 1 := by
                exact (div_lt_one hdenom).2 hnum_lt
              have hsum' :
                  (m - 1 : Real) * (gap / (2 * (m : Real))) =
                    gap * ((m - 1 : Real) / ((2 : Real) * (m : Real))) := by
                ring
              have hsum_lt :
                  (m - 1 : Real) * (gap / (2 * (m : Real))) < gap := by
                have h := mul_lt_mul_of_pos_left hratio_lt hgap
                simpa [hsum'] using h
              simpa [gap, hsum_eps] using hsum_lt
            exact
              recessionCone_sum_epigraph_prod_top_contra (f := f) (f0_plus := f0_plus) (g := g)
                (hg := rfl) hnotbot hnotbot0 hrec_i (p := p) (i0 := i0) htop (a := a)
                (x0 := x0) (μ0 := μ0) (t := t) hgt0 hx0 ha_sum (x := x) (μ := μ) hxi0
                hμi0 hxle (ε := ε) hslack hε hmem''' htopg
      · have hnot_top : ∀ i, f0_plus i (p.1 i) ≠ (⊤ : EReal) := by
          intro i htopi
          exact htop ⟨i, htopi⟩
        have hgt_real :
            Finset.univ.sum (fun i => (f0_plus i (p.1 i)).toReal) > p.2 := by
          exact
            (g0_plus_gt_toReal_sum (β := fun i => f0_plus i (p.1 i)) (α := p.2) hnot_top hbot).1
              hgt
        let i0 : Fin m := ⟨0, hm'⟩
        obtain ⟨a, ha_lt, ha_sum⟩ :=
          split_real_sum_of_gt_strict_all (m := m) (hm := hm') (r := fun i =>
            (f0_plus i (p.1 i)).toReal) (α := p.2) hgt_real
        have ha_lt_ereal : ∀ i, ((a i : Real) : EReal) < f0_plus i (p.1 i) := by
          intro i
          have hβ_eq :
              f0_plus i (p.1 i) =
                ((f0_plus i (p.1 i)).toReal : EReal) := by
            simpa using
              (EReal.coe_toReal (hnot_top i) (hbot i)).symm
          have hlt' :
              ((a i : Real) : EReal) <
                ((f0_plus i (p.1 i)).toReal : EReal) :=
            (EReal.coe_lt_coe_iff).2 (ha_lt i)
          rw [hβ_eq]
          exact hlt'
        have hnot_mem :
            (p.1 i0, a i0) ∉
              Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i0)) := by
          intro hmem
          have hmem' :
              (p.1 i0, a i0) ∈
                epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i0) := by
            simpa [hrec_i i0] using hmem
          have hle :
              f0_plus i0 (p.1 i0) ≤ (a i0 : EReal) :=
            (mem_epigraph_univ_iff (f := f0_plus i0)).1 hmem'
          exact (not_lt_of_ge hle) (ha_lt_ereal i0)
        rcases
            not_mem_recessionCone_epigraph_witness
              (f := f i0) (v := p.1 i0) (a := a i0) hnot_mem with
          ⟨x0, μ0, t, ht, hgt0, hx0⟩
        have htpos : 0 < t := by
          by_contra hle
          have ht0 : t = 0 := by
            exact le_antisymm (le_of_not_gt hle) ht
          subst ht0
          have : f i0 x0 > (μ0 : EReal) := by
            simpa using hgt0
          exact (not_lt_of_ge hx0) this
        by_cases htopi0 : f i0 (x0 + t • p.1 i0) = (⊤ : EReal)
        · classical
          choose q hq using hne_epi
          let x' : Fin m → (Fin n → Real) := fun i => (q i).1
          let μ' : Fin m → Real := fun i => (q i).2
          have hx' :
              ∀ i, (x' i, μ' i) ∈ epigraph (Set.univ : Set (Fin n → Real)) (f i) := by
            intro i
            simpa [x', μ'] using hq i
          let x : Fin m → (Fin n → Real) := fun i => if h : i = i0 then x0 else x' i
          let μ : Fin m → Real := fun i => if h : i = i0 then μ0 else μ' i
          have hxle : ∀ i, f i (x i) ≤ (μ i : EReal) := by
            intro i
            by_cases h : i = i0
            · subst h
              simpa [x, μ] using hx0
            · have hx'' : f i (x' i) ≤ (μ' i : EReal) :=
                (mem_epigraph_univ_iff (f := f i)).1 (hx' i)
              simpa [x, μ, h] using hx''
          have hxg :
              g x ≤ Finset.univ.sum (fun i => (μ i : EReal)) := by
            have hsum :
                Finset.univ.sum (fun i => f i (x i)) ≤
                  Finset.univ.sum (fun i => (μ i : EReal)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact hxle i
            dsimp [g]
            exact hsum
          have hmem' :
              (x, Finset.univ.sum (fun i => μ i)) ∈
                {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
            simpa [Set.mem_setOf_eq, sum_coe_ereal] using hxg
          have hmem'' := hp hmem' ht
          have hmem''' :
              g (x + t • p.1) ≤
                (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
            simpa using hmem''
          have hbot' :
              ∀ i ∈ (Finset.univ : Finset (Fin m)),
                f i (x i + t • p.1 i) ≠ (⊥ : EReal) := by
            intro i hi
            exact hnotbot i (x i + t • p.1 i)
          have hsum_top :
              Finset.univ.sum (fun i => f i (x i + t • p.1 i)) = (⊤ : EReal) :=
            sum_eq_top_of_eq_top (s := Finset.univ)
              (β := fun i => f i (x i + t • p.1 i))
              (i0 := i0) (by simp) (by simp [x, htopi0]) hbot'
          have htop_le :
              (⊤ : EReal) ≤
                (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
            simpa [g, hsum_top] using hmem'''
          exact (not_top_le_coe (Finset.univ.sum (fun i => μ i) + t * p.2)) htop_le
        · have hboti0 : f i0 (x0 + t • p.1 i0) ≠ (⊥ : EReal) :=
            hnotbot i0 (x0 + t • p.1 i0)
          have hβ_eq :
              f i0 (x0 + t • p.1 i0) =
                ((f i0 (x0 + t • p.1 i0)).toReal : EReal) := by
            simpa using (EReal.coe_toReal htopi0 hboti0).symm
          have hgt0' :
              (μ0 + t * a i0 : EReal) <
                ((f i0 (x0 + t • p.1 i0)).toReal : EReal) := by
            have hgt0'' :
                (μ0 + t * a i0 : EReal) < f i0 (x0 + t • p.1 i0) := by
              simpa [gt_iff_lt] using hgt0
            convert hgt0'' using 1
            exact hβ_eq.symm
          let gap : Real :=
            (f i0 (x0 + t • p.1 i0)).toReal - (μ0 + t * a i0)
          have hgap : 0 < gap := by
            have hgt0_real :
                μ0 + t * a i0 < (f i0 (x0 + t • p.1 i0)).toReal :=
              (EReal.coe_lt_coe_iff).1 hgt0'
            dsimp [gap]
            linarith
          let ε : Fin m → Real := fun i => if i = i0 then 0 else gap / (2 * (m : Real))
          have hdenom : 0 < (2 : Real) * (m : Real) := by
            have hmpos : (0 : Real) < (m : Real) := by exact_mod_cast hm'
            linarith
          have hεpos : ∀ i ≠ i0, 0 < ε i := by
            intro i hi
            have hpos : 0 < gap / (2 * (m : Real)) := by
              exact div_pos hgap hdenom
            simpa [ε, hi] using hpos
          have hrec_tight :
              ∀ i ≠ i0,
                ∃ x : Fin n → Real, ∃ μ : Real,
                  f i x ≤ (μ : EReal) ∧
                    ((μ + t * a i - ε i : Real) : EReal) ≤ f i (x + t • p.1 i) := by
            intro i hi
            have ha_i : ((a i : Real) : EReal) < f0_plus i (p.1 i) := ha_lt_ereal i
            exact
              recCone_tight_approx_at_t (f := f i) (f0_plus := f0_plus i) (hrec := hrec_i i)
                (hconv := hconv_i i) (v := p.1 i) (a := a i) ha_i (t := t) htpos (ε := ε i)
                (hε := hεpos i hi)
          classical
          choose x' μ' hx' using hrec_tight
          let x : Fin m → (Fin n → Real) := fun i => if h : i = i0 then x0 else x' i h
          let μ : Fin m → Real := fun i => if h : i = i0 then μ0 else μ' i h
          have hxi0 : x i0 = x0 := by
            simp [x]
          have hμi0 : μ i0 = μ0 := by
            simp [μ]
          have hxle : ∀ i, f i (x i) ≤ (μ i : EReal) := by
            intro i
            by_cases h : i = i0
            · subst h
              simpa [x, μ] using hx0
            · have hx'' : f i (x' i h) ≤ (μ' i h : EReal) :=
                (hx' i h).1
              simpa [x, μ, h] using hx''
          have hslack :
              ∀ i ≠ i0,
                ((μ i + t * a i - ε i : Real) : EReal) ≤ f i (x i + t • p.1 i) := by
            intro i hi
            have hx'' := (hx' i hi).2
            simpa [x, μ, hi] using hx''
          have hxg :
              g x ≤ Finset.univ.sum (fun i => (μ i : EReal)) := by
            have hsum :
                Finset.univ.sum (fun i => f i (x i)) ≤
                  Finset.univ.sum (fun i => (μ i : EReal)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact hxle i
            dsimp [g]
            exact hsum
          have hmem' :
              (x, Finset.univ.sum (fun i => μ i)) ∈
                {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
            simpa [Set.mem_setOf_eq, sum_coe_ereal] using hxg
          have hmem'' := hp hmem' ht
          have hmem''' :
              g (x + t • p.1) ≤
                (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
            simpa using hmem''
          -- If any component is `⊤`, the sum is `⊤` and we get a contradiction immediately.
          by_cases htopg :
              ∃ i, f i (x i + t • p.1 i) = (⊤ : EReal)
          · rcases htopg with ⟨i1, htop1⟩
            have hbot' :
                ∀ i ∈ (Finset.univ : Finset (Fin m)),
                  f i (x i + t • p.1 i) ≠ (⊥ : EReal) := by
              intro i hi
              exact hnotbot i (x i + t • p.1 i)
            have hsum_top :
                Finset.univ.sum (fun i => f i (x i + t • p.1 i)) = (⊤ : EReal) :=
              sum_eq_top_of_eq_top (s := Finset.univ)
                (β := fun i => f i (x i + t • p.1 i))
                (i0 := i1) (by simp) htop1 hbot'
            have htop_le :
                (⊤ : EReal) ≤
                  (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal) := by
              simpa [g, hsum_top] using hmem'''
            exact (not_top_le_coe (Finset.univ.sum (fun i => μ i) + t * p.2)) htop_le
          · have hε :
                (Finset.univ.erase i0).sum (fun i => ε i) <
                  (f i0 (x0 + t • p.1 i0)).toReal - (μ0 + t * a i0) := by
              have hsum_eps :
                  (Finset.univ.erase i0).sum (fun i => ε i) =
                    (m - 1 : Real) * (gap / (2 * (m : Real))) := by
                classical
                have hcard : (Finset.univ.erase i0).card = m - 1 := by
                  simp [Finset.card_erase_of_mem]
                have hcard_real :
                    ((Finset.univ.erase i0).card : Real) = (m - 1 : Real) := by
                  have hm1 : (1 : Nat) ≤ m := Nat.succ_le_iff.mp hm'
                  simp [hcard, Nat.cast_sub hm1, Nat.cast_one]
                calc
                  (Finset.univ.erase i0).sum (fun i => ε i) =
                      (Finset.univ.erase i0).sum (fun _ => gap / (2 * (m : Real))) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    have hi0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
                    simp [ε, hi0]
                  _ =
                      ((Finset.univ.erase i0).card : Real) *
                        (gap / (2 * (m : Real))) := by
                    simp [Finset.sum_const, mul_comm]
                  _ = (m - 1 : Real) * (gap / (2 * (m : Real))) := by
                    rw [hcard_real]
              have hnum_lt : (m - 1 : Real) < (2 : Real) * (m : Real) := by
                have hmpos : (0 : Real) < (m : Real) := by exact_mod_cast hm'
                linarith
              have hratio_lt :
                  (m - 1 : Real) / ((2 : Real) * (m : Real)) < 1 := by
                exact (div_lt_one hdenom).2 hnum_lt
              have hsum' :
                  (m - 1 : Real) * (gap / (2 * (m : Real))) =
                    gap * ((m - 1 : Real) / ((2 : Real) * (m : Real))) := by
                ring
              have hsum_lt :
                  (m - 1 : Real) * (gap / (2 * (m : Real))) < gap := by
                have h := mul_lt_mul_of_pos_left hratio_lt hgap
                simpa [hsum'] using h
              simpa [gap, hsum_eps] using hsum_lt
            exact
              recessionCone_sum_epigraph_prod_finite_contra (f := f) (f0_plus := f0_plus) (g := g)
                (hg := rfl) hnotbot hnotbot0 hrec_i (p := p) (i0 := i0) (a := a) (x0 := x0)
                (μ0 := μ0) (t := t) hgt0 hx0 ha_sum (x := x) (μ := μ) hxi0 hμi0 hxle
                (ε := ε) hslack hε hmem''' htopg
    · intro hp
      have hsplit :
          ∃ a : Fin m → Real,
            (∀ i, f0_plus i (p.1 i) ≤ (a i : EReal)) ∧
            Finset.univ.sum (fun i => a i) = p.2 := by
        have hsum :
            Finset.univ.sum (fun i => f0_plus i (p.1 i)) ≤ (p.2 : EReal) := by
          simpa [g0_plus] using hp
        have hbot : ∀ i, f0_plus i (p.1 i) ≠ (⊥ : EReal) := by
          intro i
          exact hnotbot0 i (p.1 i)
        exact split_real_sum_of_le (m := m) (hm := hm') (β := fun i => f0_plus i (p.1 i))
          (α := p.2) hbot hsum
      rcases hsplit with ⟨a, ha_le, ha_sum⟩
      have hrec :
          ∀ i, (p.1 i, a i) ∈
            Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
        intro i
        have hmem :
            (p.1 i, a i) ∈
              epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i) := by
          exact (mem_epigraph_univ_iff (f := f0_plus i)).2 (ha_le i)
        have hmem' :
            (p.1 i, a i) ∈
              Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
          simpa [hrec_i i] using hmem
        exact hmem'
      have hrec_sum :
          (p.1, Finset.univ.sum (fun i => a i)) ∈
            Set.recessionCone {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
        exact
          recessionCone_sum_epigraph_prod_of_components
            (f := f) (g := g) (hg := rfl) (hm := hm') (v := p.1) (a := a) hnotbot hrec
      simpa [ha_sum] using hrec_sum

end Section09
end Chap02
