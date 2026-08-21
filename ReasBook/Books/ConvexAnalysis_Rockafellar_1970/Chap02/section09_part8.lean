/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part7

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- In the two-function case, the zero-sum condition in the family corollary
follows from the positivity hypothesis on `f1_0_plus` and `f2_0_plus`. -/
lemma hzero_two
    {n : Nat} {f1_0_plus f2_0_plus : (Fin n → Real) → EReal}
    (hpos : ∀ z : Fin n → Real, z ≠ 0 → f1_0_plus z + f2_0_plus (-z) > (0 : EReal)) :
    ∀ z : Fin 2 → (Fin n → Real),
      (Finset.univ.sum (fun i =>
        (if i = 0 then f1_0_plus else f2_0_plus) (z i)) ≤ (0 : EReal)) →
      (Finset.univ.sum (fun i =>
        (if i = 0 then f1_0_plus else f2_0_plus) (-(z i))) > (0 : EReal)) →
      (Finset.univ.sum (fun i => z i) ≠ (0 : Fin n → Real)) := by
  classical
  intro z hzle hzgt hsum
  have hsum' : z 0 + z 1 = 0 := by
    simpa [Fin.sum_univ_two] using hsum
  have hz1 : z 1 = -z 0 := by
    have hsum'' : z 1 + z 0 = 0 := by
      simpa [add_comm] using hsum'
    exact eq_neg_of_add_eq_zero_left hsum''
  have hz0ne : z 0 ≠ 0 := by
    intro hz0
    have hz1zero : z 1 = 0 := by
      simp [hz0, hz1]
    have hzle' :
        f1_0_plus (0 : Fin n → Real) + f2_0_plus (0 : Fin n → Real) ≤ (0 : EReal) := by
      simpa [Fin.sum_univ_two, hz0, hz1zero] using hzle
    have hzgt' :
        f1_0_plus (0 : Fin n → Real) + f2_0_plus (0 : Fin n → Real) > (0 : EReal) := by
      simpa [Fin.sum_univ_two, hz0, hz1zero] using hzgt
    exact (not_lt_of_ge hzle') hzgt'
  have hzle' :
      f1_0_plus (z 0) + f2_0_plus (-z 0) ≤ (0 : EReal) := by
    simpa [Fin.sum_univ_two, hz1] using hzle
  have hzgt' : f1_0_plus (z 0) + f2_0_plus (-z 0) > (0 : EReal) :=
    hpos (z 0) hz0ne
  exact (not_lt_of_ge hzle') hzgt'

/-- For `Fin 2`, a decomposition `x = x' 0 + x' 1` rewrites the sum over the family
into the binary form. -/
lemma extract_two_attainer
    {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    {x : Fin n → Real} {x' : Fin 2 → (Fin n → Real)}
    (hsum : Finset.univ.sum (fun i => x' i) = x) :
    Finset.univ.sum (fun i => (if i = 0 then f1 else f2) (x' i)) =
      f1 (x - x' 1) + f2 (x' 1) := by
  have hsum' : x' 0 + x' 1 = x := by
    simpa [Fin.sum_univ_two] using hsum
  have hx0 : x' 0 = x - x' 1 := by
    funext i
    have hsum_i : x' 0 i + x' 1 i = x i := by
      simpa using congrArg (fun f => f i) hsum'
    simpa using (eq_sub_of_add_eq hsum_i)
  simp [Fin.sum_univ_two, hx0]

/-- Corollary 9.2.2. Let `f1` and `f2` be closed proper convex functions on `ℝ^n` such that
`(f1 0+)(z) + (f2 0+)(-z) > 0` for all `z ≠ 0`. Then `infimalConvolution f1 f2` is a closed
proper convex function, and for each `x` the infimum in
`(f1 square f2)(x) = inf_y { f1 (x - y) + f2 y }` is attained by some `y`. -/
theorem infimalConvolution_closed_proper_convex_recession
    {n : Nat} {f1 f2 f1_0_plus f2_0_plus : (Fin n → Real) → EReal}
    (hclosed1 : ClosedConvexFunction f1) (hclosed2 : ClosedConvexFunction f2)
    (hproper1 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f1)
    (hproper2 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f2)
    (hpos :
      ∀ z : Fin n → Real, z ≠ 0 → f1_0_plus z + f2_0_plus (-z) > (0 : EReal))
    (hrec1 :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f1) =
        epigraph (Set.univ : Set (Fin n → Real)) f1_0_plus)
    (hrec2 :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f2) =
        epigraph (Set.univ : Set (Fin n → Real)) f2_0_plus)
    (hpos1 : PositivelyHomogeneous f1_0_plus)
    (hpos2 : PositivelyHomogeneous f2_0_plus)
    (hproper0_1 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f1_0_plus)
    (hproper0_2 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f2_0_plus) :
    ClosedConvexFunction (infimalConvolution f1 f2) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (infimalConvolution f1 f2) ∧
      (∀ x : Fin n → Real,
        ∃ y : Fin n → Real, infimalConvolution f1 f2 x = f1 (x - y) + f2 y) := by
  classical
  let f : Fin 2 → (Fin n → Real) → EReal := fun i => if i = 0 then f1 else f2
  let f0 : Fin 2 → (Fin n → Real) → EReal := fun i =>
    if i = 0 then f1_0_plus else f2_0_plus
  have hclosed : ∀ i, ClosedConvexFunction (f i) := by
    intro i
    fin_cases i
    · simpa [f] using hclosed1
    · simpa [f] using hclosed2
  have hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i) := by
    intro i
    fin_cases i
    · simpa [f] using hproper1
    · simpa [f] using hproper2
  have hzero :
      ∀ z : Fin 2 → (Fin n → Real),
        (Finset.univ.sum (fun i => f0 i (z i)) ≤ (0 : EReal)) →
        (Finset.univ.sum (fun i => f0 i (-(z i))) > (0 : EReal)) →
        (Finset.univ.sum (fun i => z i) ≠ (0 : Fin n → Real)) := by
    intro z hzle hzgt
    have hzle' :
        Finset.univ.sum (fun i =>
          (if i = 0 then f1_0_plus else f2_0_plus) (z i)) ≤ (0 : EReal) := by
      simpa [f0] using hzle
    have hzgt' :
        Finset.univ.sum (fun i =>
          (if i = 0 then f1_0_plus else f2_0_plus) (-(z i))) > (0 : EReal) := by
      simpa [f0] using hzgt
    exact hzero_two (f1_0_plus := f1_0_plus) (f2_0_plus := f2_0_plus) hpos z hzle' hzgt'
  have hrec :
      ∀ i : Fin 2,
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) (f0 i) := by
    intro i
    fin_cases i
    · simpa [f, f0] using hrec1
    · simpa [f, f0] using hrec2
  have hpos_i : ∀ i : Fin 2, PositivelyHomogeneous (f0 i) := by
    intro i
    fin_cases i
    · simpa [f0] using hpos1
    · simpa [f0] using hpos2
  have hproper0_i :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f0 i) := by
    intro i
    fin_cases i
    · simpa [f0] using hproper0_1
    · simpa [f0] using hproper0_2
  have h :=
    infimalConvolutionFamily_closed_proper_convex_recession (f := f) (f0_plus := f0)
      hclosed hproper hrec hpos_i hproper0_i hzero (by decide : 0 < (2 : Nat))
  have h' :
      ClosedConvexFunction (infimalConvolutionFamily f) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (infimalConvolutionFamily f) ∧
        (∀ x : Fin n → Real,
          ∃ x' : Fin 2 → (Fin n → Real),
            Finset.univ.sum (fun i => x' i) = x ∧
              infimalConvolutionFamily f x =
                Finset.univ.sum (fun i => f i (x' i))) ∧
        infimalConvolutionFamily f0 = infimalConvolutionFamily f0 := by
    simpa using h
  have hEq : infimalConvolutionFamily f = infimalConvolution f1 f2 := by
    symm
    simpa [f] using
      (infimalConvolution_eq_infimalConvolutionFamily_two (f := f1) (g := f2))
  refine ⟨?_, ?_, ?_⟩
  · simpa [hEq] using h'.1
  · simpa [hEq] using h'.2.1
  · intro x
    obtain ⟨x', hsum, hEqInf⟩ := h'.2.2.1 x
    refine ⟨x' 1, ?_⟩
    have hsum' :
        Finset.univ.sum (fun i => (if i = 0 then f1 else f2) (x' i)) =
          f1 (x - x' 1) + f2 (x' 1) :=
      extract_two_attainer (f1 := f1) (f2 := f2) (x := x) (x' := x') hsum
    have hEqInf' :
        infimalConvolutionFamily f x = f1 (x - x' 1) + f2 (x' 1) := by
      have hEqInf'' :
          infimalConvolutionFamily f x =
            Finset.univ.sum (fun i => (if i = 0 then f1 else f2) (x' i)) := by
        simpa [f] using hEqInf
      simpa [hsum'] using hEqInf''
    simpa [hEq] using hEqInf'

/-- Rewrite the infimal convolution with an indicator as an infimum over the translate. -/
lemma infimalConvolution_indicator_neg_eq_sInf_translate
    {n : Nat} {f : (Fin n → Real) → EReal} {C : Set (Fin n → Real)}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x : Fin n → Real,
      infimalConvolution (indicatorFunction (-C)) f x =
        sInf { z : EReal |
          ∃ y : Fin n → Real, y ∈ Set.image (fun c => c + x) C ∧ z = f y } := by
  classical
  intro x
  -- Use the definition of the infimal convolution and compare the two sInf sets.
  simp [infimalConvolution]
  set S1 : Set EReal :=
    { z : EReal | ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
        z = indicatorFunction (-C) x1 + f x2 }
  set S2 : Set EReal :=
    { z : EReal | ∃ y : Fin n → Real, y ∈ Set.image (fun c => c + x) C ∧ z = f y }
  have h1 : sInf S1 ≤ sInf S2 := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨c, hc, rfl⟩
    refine sInf_le ?_
    refine ⟨-c, c + x, ?_, ?_⟩
    · simp [add_assoc, add_comm]
    · have hmem : (-c) ∈ -C := by simpa using hc
      simp [indicatorFunction, hmem]
  have h2 : sInf S2 ≤ sInf S1 := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨x1, x2, hsum, rfl⟩
    by_cases hx1 : x1 ∈ -C
    · have hx1C : -x1 ∈ C := by simpa using hx1
      have hx2mem : x2 ∈ Set.image (fun c => c + x) C := by
        refine ⟨-x1, hx1C, ?_⟩
        have hx2 : x2 = x - x1 := eq_sub_of_add_eq (by simpa [add_comm] using hsum)
        have hx2' : x + (-x1) = x2 := by
          simpa [sub_eq_add_neg] using hx2.symm
        simpa [add_comm] using hx2'
      have hmem : f x2 ∈ S2 := ⟨x2, hx2mem, rfl⟩
      have hle : sInf S2 ≤ f x2 := sInf_le hmem
      simpa [indicatorFunction, hx1] using hle
    · have hne : f x2 ≠ (⊥ : EReal) := hproper.2.2 x2 (by simp)
      have htop : indicatorFunction (-C) x1 + f x2 = (⊤ : EReal) := by
        have htop' : (⊤ : EReal) + f x2 = (⊤ : EReal) := EReal.top_add_of_ne_bot hne
        simpa [indicatorFunction, hx1] using htop'
      simp [htop]
  have hEq : sInf S1 = sInf S2 := le_antisymm h1 h2
  simpa [S1, S2] using hEq

/-- The indicator of a closed convex nonempty set is closed and proper. -/
lemma closedConvexFunction_indicator_neg
    {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex Real C) :
    ClosedConvexFunction (indicatorFunction (-C)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction (-C)) := by
  classical
  have hconv : ConvexFunction (indicatorFunction (-C)) :=
    convexFunction_indicator_of_convex (C := -C) hCconvex.neg
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction (-C)) := by
    have hne : Set.Nonempty (-C) := by
      rcases hCne with ⟨x, hx⟩
      refine ⟨-x, ?_⟩
      simpa using hx
    exact
      properConvexFunctionOn_indicator_of_convex_of_nonempty
        (C := -C) hCconvex.neg hne
  have hls : LowerSemicontinuous (indicatorFunction (-C)) := by
    refine (lowerSemicontinuous_iff_closed_sublevel (f := indicatorFunction (-C))).2 ?_
    intro α
    by_cases hα : (0 : Real) ≤ α
    · have hset :
        {x : Fin n → Real | indicatorFunction (-C) x ≤ (α : EReal)} = -C := by
        ext x
        by_cases hx : x ∈ -C
        · have hx' : -x ∈ C := by simpa using hx
          simp [indicatorFunction, hx', hα]
        · have hx' : -x ∉ C := by
            intro hxC
            exact hx (by simpa using hxC)
          simp [indicatorFunction, hx']
      have hneg : IsClosed (-C) := by
        have hcont : Continuous fun x : Fin n → Real => -x := by continuity
        have hclosed_pre : IsClosed ((fun x : Fin n → Real => -x) ⁻¹' C) :=
          hCclosed.preimage hcont
        simpa [Set.preimage, Set.neg] using hclosed_pre
      simpa [hset] using hneg
    · have hset :
        {x : Fin n → Real | indicatorFunction (-C) x ≤ (α : EReal)} = (∅ : Set (Fin n → Real)) := by
        ext x
        by_cases hx : x ∈ -C
        · have hx' : -x ∈ C := by simpa using hx
          have hα' : ¬ (0 : EReal) ≤ (α : EReal) := by
            simpa [EReal.coe_le_coe_iff] using hα
          simp [indicatorFunction, hx', hα']
        · have hx' : -x ∉ C := by
            intro hxC
            exact hx (by simpa using hxC)
          have hα' : ¬ (0 : EReal) ≤ (α : EReal) := by
            simpa [EReal.coe_le_coe_iff] using hα
          simp [indicatorFunction, hx']
      simp [hset]
  exact ⟨⟨hconv, hls⟩, hproper⟩

/-- Positive scaling preserves membership in the recession cone. -/
lemma recessionCone_smul_pos_fin {n : Nat} {C : Set (Fin n → Real)} {y : Fin n → Real}
    (hy : y ∈ Set.recessionCone C) {t : Real} (ht : 0 < t) :
    t • y ∈ Set.recessionCone C := by
  intro x hx s hs
  have hs' : 0 ≤ s * t := mul_nonneg hs (le_of_lt ht)
  have hmem := hy hx hs'
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hmem

/-- The recession cone of a convex set is convex (finite-dimensional version). -/
lemma recessionCone_convex_fin {n : Nat} {C : Set (Fin n → Real)}
    (hCconvex : Convex Real C) : Convex Real (Set.recessionCone C) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab x hx t ht
  have hx₁ : x + t • y₁ ∈ C := hy₁ hx ht
  have hx₂ : x + t • y₂ ∈ C := hy₂ hx ht
  have hcomb :
      a • (x + t • y₁) + b • (x + t • y₂) =
        x + t • (a • y₁ + b • y₂) := by
    ext i
    calc
      a * (x i + t * y₁ i) + b * (x i + t * y₂ i)
          = (a + b) * x i + t * (a * y₁ i + b * y₂ i) := by ring
      _ = x i + t * (a * y₁ i + b * y₂ i) := by simp [hab]
      _ = x i + t * a * y₁ i + t * b * y₂ i := by ring
      _ = x i + (t * a * y₁ i + t * b * y₂ i) := by
            simp [add_assoc]
      _ = (x + t • (a • y₁ + b • y₂)) i := by
            simp [smul_add, smul_smul, mul_assoc]
  have hmem :
      a • (x + t • y₁) + b • (x + t • y₂) ∈ C :=
    hCconvex hx₁ hx₂ ha hb hab
  exact hcomb.symm ▸ hmem

/-- The indicator of the recession cone is positively homogeneous and proper. -/
lemma indicator_recession_posHom_proper {n : Nat} {C : Set (Fin n → Real)}
    (hCconvex : Convex Real C) :
    PositivelyHomogeneous (indicatorFunction (-Set.recessionCone C)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (indicatorFunction (-Set.recessionCone C)) := by
  classical
  have hconv : Convex Real (-Set.recessionCone C) := by
    have hconv' : Convex Real (Set.recessionCone C) :=
      recessionCone_convex_fin (C := C) hCconvex
    simpa using hconv'.neg
  have hne : Set.Nonempty (-Set.recessionCone C) := by
    refine ⟨0, ?_⟩
    have hzero : (0 : Fin n → Real) ∈ Set.recessionCone C := by
      intro x hx t ht
      simpa using hx
    simpa using hzero
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (indicatorFunction (-Set.recessionCone C)) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (C := -Set.recessionCone C) hconv hne
  have hpos : PositivelyHomogeneous (indicatorFunction (-Set.recessionCone C)) := by
    intro x t ht
    by_cases hx : x ∈ -Set.recessionCone C
    · have hxR : -x ∈ Set.recessionCone C := by simpa using hx
      have hxR' : -(t • x) ∈ Set.recessionCone C := by
        have hsmul :
            t • (-x) ∈ Set.recessionCone C :=
          recessionCone_smul_pos_fin (C := C) (y := -x) hxR ht
        simpa [smul_neg] using hsmul
      have hx' : t • x ∈ -Set.recessionCone C := by
        simpa using hxR'
      simp [indicatorFunction, hx, hx']
    · have hx' : t • x ∉ -Set.recessionCone C := by
        intro hx'
        have hxR : -(t • x) ∈ Set.recessionCone C := by simpa using hx'
        have htinv : 0 < t⁻¹ := inv_pos.2 ht
        have hxR' :
            t⁻¹ • (-(t • x)) ∈ Set.recessionCone C :=
          recessionCone_smul_pos_fin (C := C) (y := -(t • x)) hxR htinv
        have htne : t ≠ 0 := ne_of_gt ht
        have hxR'' : -x ∈ Set.recessionCone C := by
          simpa [smul_smul, htne, inv_mul_cancel, mul_comm, mul_left_comm, mul_assoc,
            smul_neg] using hxR'
        exact hx (by simpa using hxR'')
      have htop1 : indicatorFunction (-Set.recessionCone C) x = (⊤ : EReal) := by
        simp [indicatorFunction, hx]
      have htop2 : indicatorFunction (-Set.recessionCone C) (t • x) = (⊤ : EReal) := by
        simp [indicatorFunction, hx']
      have ht' : (0 : EReal) < (t : EReal) := (EReal.coe_pos).2 ht
      calc
        indicatorFunction (-Set.recessionCone C) (t • x) = (⊤ : EReal) := htop2
        _ = (t : EReal) * (⊤ : EReal) := by
          symm
          exact EReal.mul_top_of_pos ht'
        _ = (t : EReal) * indicatorFunction (-Set.recessionCone C) x := by
          simp [htop1]
  exact ⟨hpos, hproper⟩

/-- The recession cone of the indicator epigraph is the epigraph of the recession indicator. -/
lemma recessionCone_epigraph_indicator_neg {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) :
    Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (indicatorFunction (-C))) =
      epigraph (Set.univ : Set (Fin n → Real))
        (indicatorFunction (-Set.recessionCone C)) := by
  classical
  set E : Set ((Fin n → Real) × Real) := {p | -p.1 ∈ C ∧ 0 ≤ p.2}
  set E0 : Set ((Fin n → Real) × Real) := {p | -p.1 ∈ Set.recessionCone C ∧ 0 ≤ p.2}
  have hE :
      epigraph (Set.univ : Set (Fin n → Real)) (indicatorFunction (-C)) = E := by
    ext p
    constructor
    · intro hp
      have hle :
          indicatorFunction (-C) p.1 ≤ (p.2 : EReal) :=
        (mem_epigraph_univ_iff (f := indicatorFunction (-C))).1 hp
      by_cases hpC : -p.1 ∈ C
      · have hpC' : p.1 ∈ -C := by simpa using hpC
        have hle' : (0 : EReal) ≤ (p.2 : EReal) := by
          simpa [indicatorFunction, hpC'] using hle
        have hle'' : 0 ≤ p.2 := (EReal.coe_le_coe_iff).1 hle'
        exact ⟨hpC, hle''⟩
      · have hpC' : p.1 ∉ -C := by
          intro hpC'
          exact hpC (by simpa using hpC')
        have htop : (⊤ : EReal) ≤ (p.2 : EReal) := by
          convert hle using 1
          simp [indicatorFunction, hpC']
        exact (not_top_le_coe p.2 htop).elim
    · rintro ⟨hpC, hp2⟩
      have hpC' : p.1 ∈ -C := by simpa using hpC
      have hle' : (0 : EReal) ≤ (p.2 : EReal) := (EReal.coe_le_coe_iff).2 hp2
      exact
        (mem_epigraph_univ_iff (f := indicatorFunction (-C))).2
          (by simpa [indicatorFunction, hpC'] using hle')
  have hE0 :
      epigraph (Set.univ : Set (Fin n → Real)) (indicatorFunction (-Set.recessionCone C)) = E0 := by
    ext p
    constructor
    · intro hp
      have hle :
          indicatorFunction (-Set.recessionCone C) p.1 ≤ (p.2 : EReal) :=
        (mem_epigraph_univ_iff (f := indicatorFunction (-Set.recessionCone C))).1 hp
      by_cases hpC : -p.1 ∈ Set.recessionCone C
      · have hpC' : p.1 ∈ -Set.recessionCone C := by simpa using hpC
        have hle' : (0 : EReal) ≤ (p.2 : EReal) := by
          simpa [indicatorFunction, hpC'] using hle
        have hle'' : 0 ≤ p.2 := (EReal.coe_le_coe_iff).1 hle'
        exact ⟨hpC, hle''⟩
      · have hpC' : p.1 ∉ -Set.recessionCone C := by
          intro hpC'
          exact hpC (by simpa using hpC')
        have htop : (⊤ : EReal) ≤ (p.2 : EReal) := by
          convert hle using 1
          simp [indicatorFunction, hpC']
        exact (not_top_le_coe p.2 htop).elim
    · rintro ⟨hpC, hp2⟩
      have hpC' : p.1 ∈ -Set.recessionCone C := by simpa using hpC
      have hle' : (0 : EReal) ≤ (p.2 : EReal) := (EReal.coe_le_coe_iff).2 hp2
      exact
        (mem_epigraph_univ_iff (f := indicatorFunction (-Set.recessionCone C))).2
          (by simpa [indicatorFunction, hpC'] using hle')
  have hrec : Set.recessionCone E = E0 := by
    ext p
    constructor
    · intro hp
      have hp1 : -p.1 ∈ Set.recessionCone C := by
        intro x hx t ht
        have hmem : ((-x : Fin n → Real), (0 : Real)) ∈ E := by
          simp [E, hx]
        have hmem' := hp hmem ht
        have hmem'' :
            -(-x + t • p.1) ∈ C ∧ 0 ≤ (0 : Real) + t * p.2 := by
          simpa [E] using hmem'
        have hmemC' : x + t • (-p.1) ∈ C := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_neg] using hmem''.1
        exact hmemC'
      rcases hCne with ⟨c, hc⟩
      have hmem : ((-c : Fin n → Real), (0 : Real)) ∈ E := by
        simp [E, hc]
      have hmem' := hp hmem (by simp : (0 : Real) ≤ (1 : Real))
      have hmem'' :
          -(-c + (1 : Real) • p.1) ∈ C ∧ 0 ≤ (0 : Real) + (1 : Real) * p.2 := by
        simpa [E] using hmem'
      have hp2 : 0 ≤ p.2 := by
        simpa using hmem''.2
      exact ⟨hp1, hp2⟩
    · rintro ⟨hp1, hp2⟩ x hx t ht
      have hx' : -x.1 ∈ C ∧ 0 ≤ x.2 := by
        simpa [E] using hx
      have hx1' : -x.1 ∈ C := by
        simpa using hx'.1
      have hmemC : -x.1 + t • (-p.1) ∈ C := hp1 hx1' ht
      have hx1'' : -(x.1 + t • p.1) ∈ C := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_neg] using hmemC
      have hx1''' : -(t • p.1) + -x.1 ∈ C := by
        simpa [neg_add, add_comm, add_left_comm, add_assoc] using hx1''
      have hx2'' : 0 ≤ x.2 + t * p.2 :=
        add_nonneg hx'.2 (mul_nonneg ht hp2)
      exact (by simpa [E] using ⟨hx1''', hx2''⟩)
  calc
    Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (indicatorFunction (-C))) =
        Set.recessionCone E := by
      simp [hE]
    _ = E0 := hrec
    _ =
        epigraph (Set.univ : Set (Fin n → Real))
          (indicatorFunction (-Set.recessionCone C)) := by
      simp [hE0]

/-- Positivity from a recession-direction separation hypothesis. -/
lemma indicator_recession_hpos_from_noCommon
    {n : Nat} {f0_plus : (Fin n → Real) → EReal} {C : Set (Fin n → Real)}
    (hproper0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hnoCommon :
      ∀ z : Fin n → Real, z ≠ 0 →
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm z ∈
          Set.recessionCone
            (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm C) →
        f0_plus z > (0 : EReal)) :
    ∀ z : Fin n → Real, z ≠ 0 →
      indicatorFunction (-Set.recessionCone C) z + f0_plus (-z) > (0 : EReal) := by
  classical
  intro z hz
  by_cases hzrec : z ∈ -Set.recessionCone C
  · have hzrec' : -z ∈ Set.recessionCone C := by simpa using hzrec
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    have hrec :
        e.symm (-z) ∈ Set.recessionCone (Set.image e.symm C) := by
      have hEq := recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C)
      change e.symm (-z) ∈ Set.recessionCone (Set.image e.symm.toLinearEquiv C)
      rw [hEq]
      refine ⟨-z, hzrec', ?_⟩
      simp
    have hpos : f0_plus (-z) > (0 : EReal) := hnoCommon (-z) (by simpa using hz) hrec
    simpa [indicatorFunction, hzrec] using hpos
  · have hne_bot : f0_plus (-z) ≠ (⊥ : EReal) := by
      exact hproper0.2.2 (-z) (by simp)
    have htop : indicatorFunction (-Set.recessionCone C) z + f0_plus (-z) = (⊤ : EReal) := by
      have htop' : (⊤ : EReal) + f0_plus (-z) = (⊤ : EReal) := EReal.top_add_of_ne_bot hne_bot
      simpa [indicatorFunction, hzrec] using htop'
    simp [htop]

/-- Example 9.2.2.2. For `f = f₂` closed proper convex and `f₁` the indicator function of
`-C` with `C` nonempty closed convex, `(f₁ □ f)(x) = inf { δ(x - y | -C) + f(y) | y ∈ ℝ^n }`
and equals `inf { f(y) | y ∈ (C + x) }`. If `f` and `C` have no common direction of
recession, then the infimum over the translate `C + x` is attained for each `x`, and the
resulting function of `x` is lower semicontinuous and convex. -/
theorem infimalConvolution_indicator_neg_example
    {n : Nat} {f f0_plus : (Fin n → Real) → EReal} {C : Set (Fin n → Real)}
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hrec2 :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) =
        epigraph (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos2 : PositivelyHomogeneous f0_plus)
    (hproper0_2 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex Real C)
    (hnoCommon :
      ∀ z : Fin n → Real, z ≠ 0 →
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm z ∈
          Set.recessionCone
            (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm C) →
        f0_plus z > (0 : EReal)) :
    infimalConvolution (indicatorFunction (-C)) f =
        (fun x =>
          sInf { z : EReal |
            ∃ y : Fin n → Real, y ∈ Set.image (fun c => c + x) C ∧ z = f y }) ∧
      ClosedConvexFunction (infimalConvolution (indicatorFunction (-C)) f) ∧
      (∀ x : Fin n → Real,
        ∃ y : Fin n → Real,
          y ∈ Set.image (fun c => c + x) C ∧
            infimalConvolution (indicatorFunction (-C)) f x = f y) := by
  classical
  have hInd := closedConvexFunction_indicator_neg (n := n) (C := C) hCne hCclosed hCconvex
  have hInd0 := indicator_recession_posHom_proper (n := n) (C := C) hCconvex
  have hpos :
      ∀ z : Fin n → Real, z ≠ 0 →
        indicatorFunction (-Set.recessionCone C) z + f0_plus (-z) > (0 : EReal) :=
    indicator_recession_hpos_from_noCommon (f0_plus := f0_plus) (C := C) hproper0_2 hnoCommon
  have hrec1 :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (indicatorFunction (-C))) =
        epigraph (Set.univ : Set (Fin n → Real))
          (indicatorFunction (-Set.recessionCone C)) :=
    recessionCone_epigraph_indicator_neg (n := n) (C := C) hCne
  have hmain :=
    infimalConvolution_closed_proper_convex_recession
      (f1 := indicatorFunction (-C)) (f2 := f)
      (f1_0_plus := indicatorFunction (-Set.recessionCone C)) (f2_0_plus := f0_plus)
      hInd.1 hclosed hInd.2 hproper hpos hrec1 hrec2 hInd0.1 hpos2 hInd0.2 hproper0_2
  refine ⟨?_, ?_, ?_⟩
  · funext x
    simpa using
      (infimalConvolution_indicator_neg_eq_sInf_translate (f := f) (C := C) hproper x)
  · exact hmain.1
  · intro x
    obtain ⟨y, hy⟩ := hmain.2.2 x
    set S : Set EReal :=
      { z : EReal | ∃ y : Fin n → Real, y ∈ Set.image (fun c => c + x) C ∧ z = f y }
    have hsInf :
        infimalConvolution (indicatorFunction (-C)) f x = sInf S := by
      simpa [S] using
        (infimalConvolution_indicator_neg_eq_sInf_translate (f := f) (C := C) hproper x)
    by_cases hyC : x - y ∈ -C
    · have hyC' : y - x ∈ C := by
        have : -(x - y) ∈ C := by simpa using hyC
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hyCx : y ∈ Set.image (fun c => c + x) C := by
        refine ⟨y - x, hyC', ?_⟩
        simp [sub_eq_add_neg, add_comm]
      have hy' :
          infimalConvolution (indicatorFunction (-C)) f x = f y := by
        simpa [indicatorFunction, hyC] using hy
      exact ⟨y, hyCx, hy'⟩
    · have hne_bot : f y ≠ (⊥ : EReal) := hproper.2.2 y (by simp)
      have htop' : (⊤ : EReal) + f y = (⊤ : EReal) := EReal.top_add_of_ne_bot hne_bot
      have htop :
          infimalConvolution (indicatorFunction (-C)) f x = (⊤ : EReal) := by
        have htop'' :
            infimalConvolution (indicatorFunction (-C)) f x =
              (⊤ : EReal) + f y := by
          simpa [indicatorFunction, hyC] using hy
        simpa [htop'] using htop''
      rcases hCne with ⟨c, hc⟩
      have hmem : c + x ∈ Set.image (fun c => c + x) C := ⟨c, hc, rfl⟩
      have hle : sInf S ≤ f (c + x) :=
        sInf_le ⟨c + x, hmem, rfl⟩
      have hsInf' : sInf S = (⊤ : EReal) := by
        simpa [htop] using hsInf.symm
      have htop_le : (⊤ : EReal) ≤ f (c + x) := by
        simpa [hsInf'] using hle
      have hfy : f (c + x) = (⊤ : EReal) := (top_le_iff).1 htop_le
      exact ⟨c + x, hmem, by simp [htop, hfy]⟩

/-- The set of values of `f` above a point `x` in the coordinatewise order. -/
def coordinatewiseInfSet {n : Nat} (f : (Fin n → Real) → EReal) (x : Fin n → Real) :
    Set EReal :=
  { z : EReal | ∃ y : Fin n → Real, x ≤ y ∧ z = f y }

/-- A larger base point yields a smaller coordinatewise infimum set. -/
lemma coordinatewiseInfSet_mono {n : Nat} {f : (Fin n → Real) → EReal}
    {x x' : Fin n → Real} (hxx' : x ≤ x') :
    coordinatewiseInfSet f x' ⊆ coordinatewiseInfSet f x := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  exact ⟨y, le_trans hxx' hy, rfl⟩

/-- The coordinatewise infimum is bounded above by `f`. -/
lemma coordinatewiseInf_le_self {n : Nat} {f : (Fin n → Real) → EReal} (x : Fin n → Real) :
    sInf (coordinatewiseInfSet f x) ≤ f x := by
  refine sInf_le ?_
  exact ⟨x, le_rfl, rfl⟩

/-- The coordinatewise infimum is monotone. -/
lemma coordinatewiseInf_monotone {n : Nat} {f : (Fin n → Real) → EReal} :
    Monotone (fun x => sInf (coordinatewiseInfSet f x)) := by
  intro x x' hxx'
  have hsubset : coordinatewiseInfSet f x' ⊆ coordinatewiseInfSet f x :=
    coordinatewiseInfSet_mono (f := f) hxx'
  exact sInf_le_sInf hsubset

/-- Any monotone minorant of `f` lies below the coordinatewise infimum. -/
lemma coordinatewiseInf_greatest {n : Nat} {f : (Fin n → Real) → EReal}
    {h : (Fin n → Real) → EReal}
    (hle : ∀ x : Fin n → Real, h x ≤ f x) (hmono : Monotone h) :
    ∀ x : Fin n → Real, h x ≤ sInf (coordinatewiseInfSet f x) := by
  intro x
  refine le_sInf ?_
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  exact le_trans (hmono hy) (hle y)

/-- The non-negative orthant is nonempty, closed, and convex. -/
lemma nonnegOrthant_closed_convex_nonempty {n : Nat} :
    Set.Nonempty (Set.Ici (0 : Fin n → Real)) ∧
      IsClosed (Set.Ici (0 : Fin n → Real)) ∧
      Convex Real (Set.Ici (0 : Fin n → Real)) := by
  refine ⟨⟨0, by simp⟩, ?_, ?_⟩
  · simpa using (isClosed_Ici : IsClosed (Set.Ici (0 : Fin n → Real)))
  · simpa using (convex_Ici (r := (0 : Fin n → Real)))

/-- Translating the non-negative orthant by `x` gives the coordinatewise upper set. -/
lemma image_add_nonnegOrthant_eq_ge {n : Nat} (x : Fin n → Real) :
    Set.image (fun c => c + x) (Set.Ici (0 : Fin n → Real)) =
      { y : Fin n → Real | x ≤ y } := by
  classical
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    intro i
    have hc' : (0 : Fin n → Real) ≤ c := by
      simpa using hc
    have hle : x i ≤ c i + x i := le_add_of_nonneg_left (hc' i)
    simpa using hle
  · intro hy
    refine ⟨y - x, ?_, ?_⟩
    · have hc : (0 : Fin n → Real) ≤ y - x := by
        intro i
        exact sub_nonneg.mpr (hy i)
      simpa using hc
    · funext i
      simp [sub_add_cancel]

/-- The recession cone of the non-negative orthant lies in the orthant. -/
lemma recessionCone_nonnegOrthant_subset {n : Nat} :
    Set.recessionCone (Set.Ici (0 : Fin n → Real)) ⊆ Set.Ici (0 : Fin n → Real) := by
  intro z hz
  have hmem0 : (0 : Fin n → Real) ∈ Set.Ici (0 : Fin n → Real) := by simp
  have hz' :
      (0 : Fin n → Real) + (1 : Real) • z ∈ Set.Ici (0 : Fin n → Real) :=
    hz (x := (0 : Fin n → Real)) hmem0 (t := (1 : Real)) (by simp)
  simpa using hz'

/-- Nonnegative recession directions yield the no-common-recession hypothesis. -/
lemma hnoCommon_of_hnoNonneg {n : Nat} {f0_plus : (Fin n → Real) → EReal}
    (hnoNonneg :
      ∀ z : Fin n → Real, z ≠ 0 → (∀ i, 0 ≤ z i) → f0_plus z > (0 : EReal)) :
    ∀ z : Fin n → Real, z ≠ 0 →
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm z ∈
        Set.recessionCone
          (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
            (Set.Ici (0 : Fin n → Real))) →
      f0_plus z > (0 : EReal) := by
  classical
  intro z hz hrec
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  have hrec' :
      z ∈ Set.recessionCone (Set.Ici (0 : Fin n → Real)) := by
    have hEq :=
      recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv)
        (C := (Set.Ici (0 : Fin n → Real)))
    have hrec'' :
        e.symm z ∈ e.symm '' Set.recessionCone (Set.Ici (0 : Fin n → Real)) := by
      change
        (e.symm.toLinearEquiv) z ∈
          (e.symm.toLinearEquiv) '' Set.recessionCone (Set.Ici (0 : Fin n → Real))
      rw [← hEq]
      simpa using hrec
    rcases hrec'' with ⟨z', hz', hz'eq⟩
    have hz'': z' = z := by
      exact e.symm.injective hz'eq
    simpa [hz''] using hz'
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    have hzC :
        z ∈ Set.Ici (0 : Fin n → Real) :=
      (recessionCone_nonnegOrthant_subset (n := n)) hrec'
    have hzC' : (0 : Fin n → Real) ≤ z := by simpa using hzC
    intro i
    exact hzC' i
  exact hnoNonneg z hz hz_nonneg

/-- The coordinatewise infimum set is the translate-based infimum set. -/
lemma coordinatewiseInfSet_eq_translate {n : Nat} {f : (Fin n → Real) → EReal}
    (x : Fin n → Real) :
    coordinatewiseInfSet f x =
      { z : EReal |
        ∃ y : Fin n → Real,
          y ∈ Set.image (fun c => c + x) (Set.Ici (0 : Fin n → Real)) ∧ z = f y } := by
  classical
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    have : y ∈ { y : Fin n → Real | x ≤ y } := hy
    simpa [image_add_nonnegOrthant_eq_ge (x := x)] using this
  · rintro ⟨y, hy, rfl⟩
    have : x ≤ y := by
      have : y ∈ { y : Fin n → Real | x ≤ y } := by
        simpa [image_add_nonnegOrthant_eq_ge (x := x)] using hy
      exact this
    exact ⟨y, this, rfl⟩

/-- Example 9.2.2.3. Taking `C` to be the non-negative orthant of `ℝ^n`, we have
`C + x = { y | y ≥ x }` for each `x`. If `f` is a closed proper convex function on `ℝ^n`
whose recession cone contains no non-negative non-zero vectors, then the infimum in
`g(x) = inf { f(y) | y ≥ x }` is attained for each `x`, and `g` is a closed proper convex
function. Moreover, `g` is the greatest function with `g ≤ f` and `g` coordinatewise
non-decreasing. -/
theorem coordinatewiseInfimum_closed_proper_convex
    {n : Nat} {f f0_plus : (Fin n → Real) → EReal}
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hrec2 :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) =
        epigraph (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos2 : PositivelyHomogeneous f0_plus)
    (hproper0_2 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hnoNonneg :
      ∀ z : Fin n → Real, z ≠ 0 → (∀ i, 0 ≤ z i) → f0_plus z > (0 : EReal)) :
    let g : (Fin n → Real) → EReal :=
      fun x => sInf (coordinatewiseInfSet f x)
    ClosedConvexFunction g ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g ∧
      (∀ x : Fin n → Real, ∃ y : Fin n → Real, x ≤ y ∧ g x = f y) ∧
      (∀ x : Fin n → Real, g x ≤ f x) ∧
      Monotone g ∧
      (∀ h : (Fin n → Real) → EReal,
        (∀ x : Fin n → Real, h x ≤ f x) → Monotone h →
          ∀ x : Fin n → Real, h x ≤ g x) := by
  classical
  let g : (Fin n → Real) → EReal := fun x => sInf (coordinatewiseInfSet f x)
  have hle : ∀ x : Fin n → Real, g x ≤ f x := by
    intro x
    dsimp [g]
    exact coordinatewiseInf_le_self (f := f) x
  have hmono : Monotone g := by
    dsimp [g]
    exact coordinatewiseInf_monotone (f := f)
  have hgreatest :
      ∀ h : (Fin n → Real) → EReal,
        (∀ x : Fin n → Real, h x ≤ f x) → Monotone h →
          ∀ x : Fin n → Real, h x ≤ g x := by
    intro h hle' hmono'
    intro x
    dsimp [g]
    exact coordinatewiseInf_greatest (f := f) (h := h) hle' hmono' x
  have hC :
      Set.Nonempty (Set.Ici (0 : Fin n → Real)) ∧
        IsClosed (Set.Ici (0 : Fin n → Real)) ∧
        Convex Real (Set.Ici (0 : Fin n → Real)) := by
    simpa using (nonnegOrthant_closed_convex_nonempty (n := n))
  have hnoCommon :
      ∀ z : Fin n → Real, z ≠ 0 →
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm z ∈
          Set.recessionCone
            (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
              (Set.Ici (0 : Fin n → Real))) →
        f0_plus z > (0 : EReal) := by
    simpa using (hnoCommon_of_hnoNonneg (n := n) (f0_plus := f0_plus) hnoNonneg)
  let C : Set (Fin n → Real) := Set.Ici (0 : Fin n → Real)
  have hmain :=
    infimalConvolution_indicator_neg_example (f := f) (f0_plus := f0_plus) (C := C)
      hclosed hproper hrec2 hpos2 hproper0_2 hC.1 hC.2.1 hC.2.2 hnoCommon
  have hEq : infimalConvolution (indicatorFunction (-C)) f = g := by
    funext x
    have h1 :=
      infimalConvolution_indicator_neg_eq_sInf_translate (f := f) (C := C) hproper x
    simpa [g, coordinatewiseInfSet_eq_translate (f := f) (x := x), C] using h1
  have hclosed_g : ClosedConvexFunction g := by
    simpa [hEq] using hmain.2.1
  have hattain :
      ∀ x : Fin n → Real, ∃ y : Fin n → Real, x ≤ y ∧ g x = f y := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hmain.2.2 x
    have hy' : x ≤ y := by
      have : y ∈ { y : Fin n → Real | x ≤ y } := by
        simpa [image_add_nonnegOrthant_eq_ge (x := x), C] using hy
      exact this
    refine ⟨y, hy', ?_⟩
    simpa [hEq] using hxy
  have hproper_g : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g := by
    have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) g := by
      simpa [ConvexFunction] using hclosed_g.1
    have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) g) := by
      rcases hproper.2.1 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hle' : g p.1 ≤ f p.1 := hle p.1
      have hfp : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := f)).1 hp
      exact (mem_epigraph_univ_iff (f := g)).2 (le_trans hle' hfp)
    have hbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), g x ≠ (⊥ : EReal) := by
      intro x hx
      obtain ⟨y, hy, hgy⟩ := hattain x
      have hne_bot : f y ≠ (⊥ : EReal) := hproper.2.2 y (by simp)
      simpa [hgy] using hne_bot
    exact ⟨hconv, hne, hbot⟩
  refine ⟨hclosed_g, hproper_g, hattain, hle, hmono, hgreatest⟩

/-- Non-`⊥` is preserved by finite sums. -/
lemma finset_sum_ne_bot_of_forall {α : Type*} (s : Finset α)
    (f : α → EReal) (h : ∀ a ∈ s, f a ≠ (⊥ : EReal)) : s.sum f ≠ (⊥ : EReal) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a s ha hs h
    have hfa : f a ≠ (⊥ : EReal) := h a (by simp [ha])
    have hsum : s.sum f ≠ (⊥ : EReal) := hs (by
      intro b hb
      exact h b (by simp [hb]))
    simpa [Finset.sum_insert, ha] using add_ne_bot_of_notbot hfa hsum

/-- Non-`⊤` is preserved by finite sums. -/
lemma finset_sum_ne_top_of_forall {α : Type*} (s : Finset α)
    (f : α → EReal) (h : ∀ a ∈ s, f a ≠ (⊤ : EReal)) : s.sum f ≠ (⊤ : EReal) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a s ha hs h
    have hfa : f a ≠ (⊤ : EReal) := h a (by simp [ha])
    have hsum : s.sum f ≠ (⊤ : EReal) := hs (by
      intro b hb
      exact h b (by simp [hb]))
    simpa [Finset.sum_insert, ha] using EReal.add_ne_top hfa hsum

/-- The effective domain of a finite sum is the intersection of the effective domains,
assuming no summand takes the value `⊥`. -/
lemma effectiveDomain_sum_eq_iInter_univ
    {n m : Nat} {f : Fin m → (Fin n → Real) → EReal}
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal)) :
    effectiveDomain (Set.univ : Set (Fin n → Real))
      (fun x => Finset.univ.sum (fun i => f i x)) =
        ⋂ i, effectiveDomain (Set.univ : Set (Fin n → Real)) (f i) := by
  classical
  ext x; constructor
  · intro hx
    have hx' :
        Finset.univ.sum (fun i => f i x) ≠ (⊤ : EReal) := by
      have hx' :
          x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧
            Finset.univ.sum (fun i => f i x) < (⊤ : EReal)} := by
        simpa [effectiveDomain_eq] using hx
      exact (lt_top_iff_ne_top).1 hx'.2
    have hx_i : ∀ i, f i x ≠ (⊤ : EReal) := by
      intro i htop
      have hsum_ne_bot :
          (Finset.univ.erase i).sum (fun j => f j x) ≠ (⊥ : EReal) := by
        refine finset_sum_ne_bot_of_forall (s := Finset.univ.erase i)
          (f := fun j => f j x) ?_
        intro a ha
        exact hnotbot a x
      have htop' :
          (⊤ : EReal) + (Finset.univ.erase i).sum (fun j => f j x) = (⊤ : EReal) :=
        EReal.top_add_of_ne_bot hsum_ne_bot
      have hsum_eq :
          f i x + (Finset.univ.erase i).sum (fun j => f j x) =
            Finset.univ.sum (fun j => f j x) := by
        simpa using
          (Finset.add_sum_erase (s := Finset.univ) (f := fun j => f j x) (a := i) (by simp))
      have : Finset.univ.sum (fun j => f j x) = (⊤ : EReal) := by
        calc
          Finset.univ.sum (fun j => f j x) =
              f i x + (Finset.univ.erase i).sum (fun j => f j x) := by
            symm
            exact hsum_eq
          _ = (⊤ : EReal) + (Finset.univ.erase i).sum (fun j => f j x) := by
            simp [htop]
          _ = (⊤ : EReal) := htop'
      exact hx' this
    refine Set.mem_iInter.2 ?_
    intro i
    have hx_i' : f i x < (⊤ : EReal) := (lt_top_iff_ne_top).2 (hx_i i)
    have hx_dom :
        x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f i x < (⊤ : EReal)} :=
      ⟨by simp, hx_i'⟩
    simpa [effectiveDomain_eq] using hx_dom
  · intro hx
    have hx_i : ∀ i, f i x ≠ (⊤ : EReal) := by
      intro i
      have hx' :
          x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (f i) :=
        (Set.mem_iInter.1 hx) i
      have hx'' :
          x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f i x < (⊤ : EReal)} := by
        simpa [effectiveDomain_eq] using hx'
      exact (lt_top_iff_ne_top).1 hx''.2
    have hsum_ne_top :
        Finset.univ.sum (fun i => f i x) ≠ (⊤ : EReal) := by
      refine finset_sum_ne_top_of_forall (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => f i x) ?_
      intro a ha
      exact hx_i a
    have hx_sum :
        Finset.univ.sum (fun i => f i x) < (⊤ : EReal) :=
      (lt_top_iff_ne_top).2 hsum_ne_top
    have hx_dom :
        x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧
          Finset.univ.sum (fun i => f i x) < (⊤ : EReal)} :=
      ⟨by simp, hx_sum⟩
    simpa [effectiveDomain_eq] using hx_dom

end Section09
end Chap02
