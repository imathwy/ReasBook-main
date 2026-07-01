/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part4

open scoped Pointwise

section Chap03
section Section13

/-- For a probability vector `x` (nonnegative with total mass `1`), `dotProduct x xStar` is bounded
above by the supremum of the coordinates of `xStar`. -/
lemma section13_dotProduct_le_sSup_coord_of_simplex {n : Nat} (x xStar : Fin n → Real)
    (hx0 : ∀ j : Fin n, 0 ≤ x j)
    (hsum : Finset.univ.sum (fun j : Fin n => x j) = (1 : Real)) :
    dotProduct x xStar ≤ sSup (Set.range fun j : Fin n => xStar j) := by
  classical
  set μ : Real := sSup (Set.range fun j : Fin n => xStar j)
  have hμ : ∀ j : Fin n, xStar j ≤ μ := by
    intro j
    have hbdd : BddAbove (Set.range fun j : Fin n => xStar j) :=
      (Set.finite_range (fun j : Fin n => xStar j)).bddAbove
    have hj : xStar j ∈ Set.range fun j : Fin n => xStar j := ⟨j, rfl⟩
    simpa [μ] using (le_csSup hbdd hj)
  have hsumle :
      (Finset.univ.sum fun j : Fin n => x j * xStar j) ≤
        (Finset.univ.sum fun j : Fin n => x j * μ) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact mul_le_mul_of_nonneg_left (hμ j) (hx0 j)
  have hsumμ :
      (Finset.univ.sum fun j : Fin n => x j * μ) =
        (Finset.univ.sum fun j : Fin n => x j) * μ := by
    simpa using
      (Finset.sum_mul (s := (Finset.univ : Finset (Fin n))) (f := fun j : Fin n => x j) (a := μ)).symm
  calc
    dotProduct x xStar = Finset.univ.sum (fun j : Fin n => x j * xStar j) := by simp [dotProduct]
    _ ≤ Finset.univ.sum (fun j : Fin n => x j * μ) := hsumle
    _ = (Finset.univ.sum (fun j : Fin n => x j)) * μ := hsumμ
    _ = (1 : Real) * μ := by simp [hsum]
    _ = μ := by simp [μ]

/-- On the finite type `Fin n` with `0 < n`, the supremum of the coordinate range is achieved by
some coordinate. -/
lemma section13_exists_coord_eq_sSup {n : Nat} (xStar : Fin n → Real) (hn : 0 < n) :
    ∃ j0 : Fin n, xStar j0 = sSup (Set.range fun j : Fin n => xStar j) := by
  classical
  have hne : (Set.range fun j : Fin n => xStar j).Nonempty := by
    refine ⟨xStar ⟨0, hn⟩, ?_⟩
    exact ⟨⟨0, hn⟩, rfl⟩
  have hmem :
      sSup (Set.range fun j : Fin n => xStar j) ∈ Set.range fun j : Fin n => xStar j :=
    Set.Nonempty.csSup_mem hne (Set.finite_range (fun j : Fin n => xStar j))
  rcases hmem with ⟨j0, hj0⟩
  exact ⟨j0, hj0⟩

/-- A simplex vertex `Pi.single j0 1` has nonnegative coordinates summing to `1`, and its dot
product with `xStar` is the `j0`-th coordinate. -/
lemma section13_simplexVertex_mem_and_dotProduct {n : Nat} (j0 : Fin n) (xStar : Fin n → Real) :
    (∀ j : Fin n, 0 ≤ Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real) j) ∧
      (Finset.univ.sum
          (fun j : Fin n => Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real) j) =
        (1 : Real)) ∧
        dotProduct (Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real)) xStar = xStar j0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases h : j = j0
    · subst h
      simp
    · simp [h]
  · simp
  · simp

/-- Text 13.2.6: As further examples, the support functions of the sets

`C₁ = {x = (ξ₁, …, ξₙ) | (∀ j, 0 ≤ ξⱼ) ∧ (ξ₁ + ⋯ + ξₙ = 1)}`,

`C₂ = {x = (ξ₁, …, ξₙ) | |ξ₁| + ⋯ + |ξₙ| ≤ 1}`,

`C₃ = {x = (ξ₁, ξ₂) | ξ₁ < 0 ∧ ξ₂ ≤ ξ₁⁻¹}`,

`C₄ = {x = (ξ₁, ξ₂) | 2 ξ₁ + ξ₂² ≤ 0}`,

are given by the following formulas. (Here we use `supportFunctionEReal` so that `⊤` represents
`+∞`.) -/
theorem supportFunctionEReal_C1_eq_sSup_coord {n : Nat} (xStar : Fin n → Real) :
    0 < n →
      let C₁ : Set (Fin n → Real) :=
        {x | (∀ j : Fin n, 0 ≤ x j) ∧ (Finset.univ.sum (fun j : Fin n => x j) = (1 : Real))}
      supportFunctionEReal C₁ xStar =
        ((sSup (Set.range fun j : Fin n => xStar j) : Real) : EReal) := by
  intro hn
  classical
  dsimp
  set C₁ : Set (Fin n → Real) :=
    {x | (∀ j : Fin n, 0 ≤ x j) ∧ (Finset.univ.sum (fun j : Fin n => x j) = (1 : Real))}
  have hsup_le :
      supportFunctionEReal C₁ xStar ≤
        ((sSup (Set.range fun j : Fin n => xStar j) : Real) : EReal) := by
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxC₁, rfl⟩
    rcases hxC₁ with ⟨hx0, hxsum⟩
    exact
      (EReal.coe_le_coe_iff.2
        (section13_dotProduct_le_sSup_coord_of_simplex (x := x) (xStar := xStar) hx0 hxsum))
  have hle_sup :
      ((sSup (Set.range fun j : Fin n => xStar j) : Real) : EReal) ≤
        supportFunctionEReal C₁ xStar := by
    rcases section13_exists_coord_eq_sSup (xStar := xStar) hn with ⟨j0, hj0⟩
    have hv := section13_simplexVertex_mem_and_dotProduct (j0 := j0) (xStar := xStar)
    rcases hv with ⟨hv0, hvsum, hvdot⟩
    have hvC₁ : Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real) ∈ C₁ := ⟨hv0, hvsum⟩
    have hvdot' :
        dotProduct (Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real)) xStar =
          sSup (Set.range fun j : Fin n => xStar j) := by
      exact hvdot.trans hj0
    unfold supportFunctionEReal
    have hle :
        ((dotProduct (Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real)) xStar : Real) : EReal) ≤
          sSup {z : EReal | ∃ x ∈ C₁, z = ((dotProduct x xStar : Real) : EReal)} :=
      le_sSup ⟨Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real), hvC₁, rfl⟩
    simpa [hvdot'] using hle
  exact le_antisymm hsup_le hle_sup

/-- For `x` in the `ℓ¹` unit ball, `dotProduct x xStar` is bounded above by the `ℓ∞` norm of
`xStar`, expressed as `sSup (range fun j ↦ |xStar j|)`. -/
lemma section13_dotProduct_le_sSup_abs_coord_of_l1Ball {n : Nat} (x xStar : Fin n → Real)
    (hn : 0 < n) (hx : Finset.univ.sum (fun j : Fin n => |x j|) ≤ (1 : Real)) :
    dotProduct x xStar ≤ sSup (Set.range fun j : Fin n => |xStar j|) := by
  classical
  set μ : Real := sSup (Set.range fun j : Fin n => |xStar j|)
  have hbdd : BddAbove (Set.range fun j : Fin n => |xStar j|) :=
    (Set.finite_range (fun j : Fin n => |xStar j|)).bddAbove
  have hμ : ∀ j : Fin n, |xStar j| ≤ μ := by
    intro j
    have hj : |xStar j| ∈ Set.range fun j : Fin n => |xStar j| := ⟨j, rfl⟩
    simpa [μ] using (le_csSup hbdd hj)
  have hμ0 : 0 ≤ μ := by
    have hj0 : |xStar ⟨0, hn⟩| ≤ μ := hμ ⟨0, hn⟩
    exact le_trans (abs_nonneg _) hj0
  have hdot_le :
      dotProduct x xStar ≤ (Finset.univ.sum (fun j : Fin n => |x j|)) * μ := by
    have hsum_abs :
        |Finset.univ.sum (fun j : Fin n => x j * xStar j)| ≤
          Finset.univ.sum (fun j : Fin n => |x j * xStar j|) := by
      simpa using
        (Finset.abs_sum_le_sum_abs (f := fun j : Fin n => x j * xStar j)
          (s := (Finset.univ : Finset (Fin n))))
    calc
      dotProduct x xStar ≤ |dotProduct x xStar| := le_abs_self _
      _ = |Finset.univ.sum (fun j : Fin n => x j * xStar j)| := by simp [dotProduct]
      _ ≤ Finset.univ.sum (fun j : Fin n => |x j * xStar j|) := hsum_abs
      _ = Finset.univ.sum (fun j : Fin n => |x j| * |xStar j|) := by simp [abs_mul]
      _ ≤ Finset.univ.sum (fun j : Fin n => |x j| * μ) := by
        refine Finset.sum_le_sum ?_
        intro j _hj
        exact mul_le_mul_of_nonneg_left (hμ j) (abs_nonneg (x j))
      _ = (Finset.univ.sum (fun j : Fin n => |x j|)) * μ := by
        simpa using
          (Finset.sum_mul (s := (Finset.univ : Finset (Fin n))) (f := fun j : Fin n => |x j|)
              (a := μ)).symm
  have hmul : (Finset.univ.sum (fun j : Fin n => |x j|)) * μ ≤ μ := by
    have h := mul_le_mul_of_nonneg_right hx hμ0
    simpa [one_mul] using h
  have : dotProduct x xStar ≤ μ := le_trans hdot_le hmul
  simpa [μ] using this

/-- The signed coordinate vector `Pi.single j0 (±1)` has `ℓ¹` norm `1`, hence lies in the
`ℓ¹` unit ball. -/
lemma section13_l1Ball_single_sign_mem {n : Nat} (xStar : Fin n → Real) (j0 : Fin n) :
    Finset.univ.sum
        (fun j : Fin n =>
          |Pi.single (M := fun _ : Fin n => Real) j0
              (if 0 ≤ xStar j0 then (1 : Real) else -1) j|)
      ≤ (1 : Real) := by
  classical
  set s : Real := if 0 ≤ xStar j0 then (1 : Real) else -1
  have hsum :
      Finset.univ.sum
          (fun j : Fin n =>
            |Pi.single (M := fun _ : Fin n => Real) j0 s j|) =
        |s| := by
    simpa [s, Pi.single_eq_same] using
      (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n))) (a := j0)
        (f := fun j : Fin n => |Pi.single (M := fun _ : Fin n => Real) j0 s j|)
        (h₀ := by
          intro j _hj hjne
          simp [Pi.single_eq_of_ne hjne])
        (h₁ := by
          intro hj0
          exact (hj0 (Finset.mem_univ j0)).elim))
  have hsabs : |s| = (1 : Real) := by
    by_cases h : 0 ≤ xStar j0 <;> simp [s, h]
  -- `hsum` gives the `ℓ¹` norm, which is `1`.
  simp [hsum, hsabs]

/-- The dot product of the signed coordinate vector `Pi.single j0 (±1)` with `xStar` equals
`|xStar j0|`. -/
lemma section13_dotProduct_single_sign_eq_abs {n : Nat} (xStar : Fin n → Real) (j0 : Fin n) :
    dotProduct
        (Pi.single (M := fun _ : Fin n => Real) j0 (if 0 ≤ xStar j0 then (1 : Real) else -1))
        xStar =
      |xStar j0| := by
  classical
  by_cases h : 0 ≤ xStar j0
  · have hdot :
        dotProduct (Pi.single (M := fun _ : Fin n => Real) j0 (1 : Real)) xStar = xStar j0 := by
      simp [single_one_dotProduct (i := j0) (v := xStar)]
    simp [h, hdot, abs_of_nonneg h]
  · have hlt : xStar j0 < 0 := lt_of_not_ge h
    have hdot :
        dotProduct (Pi.single (M := fun _ : Fin n => Real) j0 (-1 : Real)) xStar = -xStar j0 := by
      simp [single_dotProduct (v := xStar) (x := (-1 : Real)) (i := j0)]
    simp [h, hdot, abs_of_neg hlt]

/-- Text 13.2.6 (support function of `C₂`): for the `ℓ¹` unit ball
`C₂ = {x | ∑ j, |xⱼ| ≤ 1}`, the support function is `max_j |xStarⱼ|`. -/
theorem supportFunctionEReal_C2_eq_sSup_abs_coord {n : Nat} (xStar : Fin n → Real) :
    0 < n →
      let C₂ : Set (Fin n → Real) :=
        {x | Finset.univ.sum (fun j : Fin n => |x j|) ≤ (1 : Real)}
      supportFunctionEReal C₂ xStar =
        ((sSup (Set.range fun j : Fin n => |xStar j|) : Real) : EReal) := by
  intro hn
  classical
  dsimp
  set C₂ : Set (Fin n → Real) :=
    {x | Finset.univ.sum (fun j : Fin n => |x j|) ≤ (1 : Real)}
  have hsup_le :
      supportFunctionEReal C₂ xStar ≤
        ((sSup (Set.range fun j : Fin n => |xStar j|) : Real) : EReal) := by
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxC₂, rfl⟩
    exact
      (EReal.coe_le_coe_iff.2
        (section13_dotProduct_le_sSup_abs_coord_of_l1Ball (x := x) (xStar := xStar) hn hxC₂))
  have hle_sup :
      ((sSup (Set.range fun j : Fin n => |xStar j|) : Real) : EReal) ≤
        supportFunctionEReal C₂ xStar := by
    rcases
        section13_exists_coord_eq_sSup (xStar := fun j : Fin n => |xStar j|) hn with
      ⟨j0, hj0⟩
    let x0 : Fin n → Real :=
      Pi.single (M := fun _ : Fin n => Real) j0 (if 0 ≤ xStar j0 then (1 : Real) else -1)
    have hx0C₂ : x0 ∈ C₂ := by
      dsimp [C₂, x0]
      exact section13_l1Ball_single_sign_mem (xStar := xStar) (j0 := j0)
    have hx0dot : dotProduct x0 xStar = |xStar j0| := by
      simpa [x0] using (section13_dotProduct_single_sign_eq_abs (xStar := xStar) (j0 := j0))
    have hx0dot' : dotProduct x0 xStar = sSup (Set.range fun j : Fin n => |xStar j|) := by
      exact hx0dot.trans hj0
    unfold supportFunctionEReal
    have hle :
        ((dotProduct x0 xStar : Real) : EReal) ≤
          sSup {z : EReal | ∃ x ∈ C₂, z = ((dotProduct x xStar : Real) : EReal)} :=
      le_sSup ⟨x0, hx0C₂, rfl⟩
    simpa [hx0dot'] using hle
  exact le_antisymm hsup_le hle_sup

/-- If one coordinate of `xStar` is negative, then the support function of `C₃` is `⊤`. -/
lemma section13_supportFunctionEReal_C3_eq_top_of_neg_coord (xStar : Fin 2 → Real)
    (hneg : xStar 0 < 0 ∨ xStar 1 < 0) :
    let C₃ : Set (Fin 2 → Real) := {x | x 0 < 0 ∧ x 1 ≤ (x 0)⁻¹}
    supportFunctionEReal C₃ xStar = ⊤ := by
  classical
  dsimp
  set C₃ : Set (Fin 2 → Real) := {x | x 0 < 0 ∧ x 1 ≤ (x 0)⁻¹}
  unfold supportFunctionEReal
  refine (sSup_eq_top.2 ?_)
  intro b hbtop
  cases b using EReal.rec with
  | top =>
      exfalso
      simp at hbtop
  | bot =>
      let x : Fin 2 → Real := fun i => if i = 0 then (-1 : Real) else (-1 : Real)
      have hxC₃ : x ∈ C₃ := by
        dsimp [C₃, x]
        constructor <;> simp
      refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
      exact EReal.bot_lt_coe (dotProduct x xStar)
  | coe r =>
      rcases hneg with h0neg | h1neg
      · -- Make `x₀` large negative.
        let c₀ : Real := -xStar 0
        have hc₀ : 0 < c₀ := by
          dsimp [c₀]
          linarith
        let t : Real := max 1 ((r + |xStar 1|) / c₀ + 1)
        have ht1 : (1 : Real) ≤ t := le_max_left _ _
        have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1
        let x : Fin 2 → Real := fun i => if i = 0 then -t else (-t)⁻¹
        have hxC₃ : x ∈ C₃ := by
          dsimp [C₃, x]
          constructor
          · simpa using (neg_neg_of_pos htpos)
          · simp
        have hdot :
            dotProduct x xStar = t * c₀ + (-xStar 1) / t := by
          simp [dotProduct, x, Fin.sum_univ_two, c₀, div_eq_mul_inv, mul_comm]
        have hrt : r + |xStar 1| < t * c₀ := by
          have hle : (r + |xStar 1|) / c₀ + 1 ≤ t := le_max_right _ _
          have hle' : ((r + |xStar 1|) / c₀ + 1) * c₀ ≤ t * c₀ :=
            mul_le_mul_of_nonneg_right hle (le_of_lt hc₀)
          have hc₀0 : c₀ ≠ 0 := ne_of_gt hc₀
          have hmul :
              ((r + |xStar 1|) / c₀ + 1) * c₀ = (r + |xStar 1|) + c₀ := by
            calc
                  ((r + |xStar 1|) / c₀ + 1) * c₀ =
                      ((r + |xStar 1|) / c₀) * c₀ + 1 * c₀ := by
                    simp [add_mul]
              _ = (r + |xStar 1|) + c₀ := by
                    have hdiv : ((r + |xStar 1|) / c₀) * c₀ = (r + |xStar 1|) := by
                      calc
                        ((r + |xStar 1|) / c₀) * c₀ = ((r + |xStar 1|) * c₀) / c₀ := by
                          simp [div_mul_eq_mul_div]
                        _ = (r + |xStar 1|) := by
                          simp [hc₀0]
                    simp [hdiv]
          have hlt : r + |xStar 1| < ((r + |xStar 1|) / c₀ + 1) * c₀ := by
            calc
              r + |xStar 1| < (r + |xStar 1|) + c₀ :=
                lt_add_of_pos_right (r + |xStar 1|) hc₀
              _ = ((r + |xStar 1|) / c₀ + 1) * c₀ := by symm; exact hmul
          exact lt_of_lt_of_le hlt hle'
        have habs : -|xStar 1| ≤ (-xStar 1) / t := by
          have ht0 : 0 < t := htpos
          have habsdiv : |xStar 1| / t ≤ |xStar 1| :=
            div_le_self (abs_nonneg (xStar 1)) ht1
          have habsdiv' : -|xStar 1| ≤ (-|xStar 1|) / t := by
            simpa [neg_div] using (neg_le_neg habsdiv)
          have habs_le : (-|xStar 1|) / t ≤ (-xStar 1) / t := by
            have : -|xStar 1| ≤ -xStar 1 := by
              simpa using (neg_le_neg (le_abs_self (xStar 1)))
            exact div_le_div_of_nonneg_right this (le_of_lt ht0)
          exact le_trans habsdiv' habs_le
        have hrlt : r < dotProduct x xStar := by
          have hlower : t * c₀ - |xStar 1| ≤ dotProduct x xStar := by
            have : t * c₀ - |xStar 1| ≤ t * c₀ + (-xStar 1) / t := by
              linarith [habs]
            simpa [hdot, sub_eq_add_neg] using this
          have : r < t * c₀ - |xStar 1| := by linarith [hrt]
          exact lt_of_lt_of_le this hlower
        refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
        exact (EReal.coe_lt_coe_iff.2 hrlt)
      · -- Make `x₁` large negative.
        let c₁ : Real := -xStar 1
        have hc₁ : 0 < c₁ := by
          dsimp [c₁]
          linarith
        let t : Real := max 1 ((r + xStar 0) / c₁ + 1)
        have ht1 : (1 : Real) ≤ t := le_max_left _ _
        let x : Fin 2 → Real := fun i => if i = 0 then (-1 : Real) else -t
        have hxC₃ : x ∈ C₃ := by
          dsimp [C₃, x]
          constructor
          · simp
          · have : -t ≤ (-1 : Real) := neg_le_neg ht1
            simpa using this
        have hdot : dotProduct x xStar = -xStar 0 + t * c₁ := by
          simp [dotProduct, x, Fin.sum_univ_two, c₁, mul_comm]
        have hrt : r + xStar 0 < t * c₁ := by
          have hle : (r + xStar 0) / c₁ + 1 ≤ t := le_max_right _ _
          have hle' : ((r + xStar 0) / c₁ + 1) * c₁ ≤ t * c₁ :=
            mul_le_mul_of_nonneg_right hle (le_of_lt hc₁)
          have hc₁0 : c₁ ≠ 0 := ne_of_gt hc₁
          have hmul : ((r + xStar 0) / c₁ + 1) * c₁ = (r + xStar 0) + c₁ := by
            calc
              ((r + xStar 0) / c₁ + 1) * c₁ = ((r + xStar 0) / c₁) * c₁ + 1 * c₁ := by
                simp [add_mul]
              _ = (r + xStar 0) + c₁ := by
                have hdiv : ((r + xStar 0) / c₁) * c₁ = (r + xStar 0) := by
                  calc
                    ((r + xStar 0) / c₁) * c₁ = ((r + xStar 0) * c₁) / c₁ := by
                      simp [div_mul_eq_mul_div]
                    _ = (r + xStar 0) := by
                      simp [hc₁0]
                simp [hdiv]
          have hlt : r + xStar 0 < ((r + xStar 0) / c₁ + 1) * c₁ := by
            calc
              r + xStar 0 < (r + xStar 0) + c₁ :=
                lt_add_of_pos_right (r + xStar 0) hc₁
              _ = ((r + xStar 0) / c₁ + 1) * c₁ := by symm; exact hmul
          exact lt_of_lt_of_le hlt hle'
        have hrlt : r < dotProduct x xStar := by
          have : r < -xStar 0 + t * c₁ := by linarith [hrt]
          simpa [hdot] using this
        refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
        exact (EReal.coe_lt_coe_iff.2 hrlt)

/-- For `x ∈ C₃` and `xStar ≥ 0`, the dot product is bounded above by
`-2 * sqrt (xStar 0 * xStar 1)`. -/
lemma section13_dotProduct_le_supportBound_C3 (x xStar : Fin 2 → Real)
    (hx0 : x 0 < 0) (hx1 : x 1 ≤ (x 0)⁻¹) (hxStar0 : 0 ≤ xStar 0) (hxStar1 : 0 ≤ xStar 1) :
    dotProduct x xStar ≤ -2 * Real.sqrt (xStar 0 * xStar 1) := by
  set t : Real := -x 0
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hx0' : x 0 = -t := by simp [t]
  have hx1' : x 1 ≤ -t⁻¹ := by
    simpa [hx0', inv_neg] using hx1
  have hdot : dotProduct x xStar = x 0 * xStar 0 + x 1 * xStar 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  have hAMGM : 2 * Real.sqrt (xStar 0 * xStar 1) ≤ xStar 0 * t + xStar 1 / t := by
    have ha : 0 ≤ xStar 0 * t := mul_nonneg hxStar0 (le_of_lt ht)
    have hb : 0 ≤ xStar 1 / t := by
      have : 0 ≤ t⁻¹ := le_of_lt (inv_pos.2 ht)
      simpa [div_eq_mul_inv, mul_comm] using mul_nonneg hxStar1 this
    have ht0 : t ≠ 0 := ht.ne'
    have hsq :
        (Real.sqrt (xStar 0 * xStar 1)) ^ 2 = (xStar 0 * t) * (xStar 1 / t) := by
      have hnonneg : 0 ≤ xStar 0 * xStar 1 := mul_nonneg hxStar0 hxStar1
      have hsqrt : (Real.sqrt (xStar 0 * xStar 1)) ^ 2 = xStar 0 * xStar 1 := by
        simpa using Real.sq_sqrt hnonneg
      -- Cancel `t` in the product.
      have hprod : (xStar 0 * t) * (xStar 1 / t) = xStar 0 * xStar 1 := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm, ht0]
      simp [hsqrt, hprod]
    simpa [pow_two, two_mul] using (two_mul_le_add_of_sq_eq_mul ha hb hsq)
  have hfinal : -(xStar 0 * t + xStar 1 / t) ≤ -2 * Real.sqrt (xStar 0 * xStar 1) := by
    have h := neg_le_neg hAMGM
    -- `h : -(xStar 0 * t + xStar 1 / t) ≤ -(2 * sqrt(..))`
    simpa [neg_mul, mul_assoc, mul_comm] using h
  have hx1mul : x 1 * xStar 1 ≤ (-t⁻¹) * xStar 1 :=
    mul_le_mul_of_nonneg_right hx1' hxStar1
  have hdot_le :
      x 0 * xStar 0 + x 1 * xStar 1 ≤ x 0 * xStar 0 + (-t⁻¹) * xStar 1 :=
    add_le_add_right hx1mul (x 0 * xStar 0)
  have hneg : x 0 * xStar 0 + (-t⁻¹) * xStar 1 = -(xStar 0 * t + xStar 1 / t) := by
    simp [hx0', div_eq_mul_inv, add_comm, mul_comm]
  calc
    dotProduct x xStar = x 0 * xStar 0 + x 1 * xStar 1 := hdot
    _ ≤ x 0 * xStar 0 + (-t⁻¹) * xStar 1 := hdot_le
    _ = -(xStar 0 * t + xStar 1 / t) := hneg
    _ ≤ -2 * Real.sqrt (xStar 0 * xStar 1) := hfinal

/-- If `xStar ≥ 0` and `xStar 0 * xStar 1 = 0`, then the support function of `C₃` is `0`. -/
lemma section13_supportFunctionEReal_C3_eq_zero_of_nonneg_and_mul_eq_zero (xStar : Fin 2 → Real)
    (hxStar0 : 0 ≤ xStar 0) (hxStar1 : 0 ≤ xStar 1) (hprod : xStar 0 * xStar 1 = 0) :
    let C₃ : Set (Fin 2 → Real) := {x | x 0 < 0 ∧ x 1 ≤ (x 0)⁻¹}
    supportFunctionEReal C₃ xStar = (0 : EReal) := by
  classical
  dsimp
  set C₃ : Set (Fin 2 → Real) := {x | x 0 < 0 ∧ x 1 ≤ (x 0)⁻¹}
  have hsup_le : supportFunctionEReal C₃ xStar ≤ (0 : EReal) := by
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxC₃, rfl⟩
    rcases hxC₃ with ⟨hx0, hx1⟩
    have hle :
        dotProduct x xStar ≤ -2 * Real.sqrt (xStar 0 * xStar 1) :=
      section13_dotProduct_le_supportBound_C3 (x := x) (xStar := xStar) hx0 hx1 hxStar0 hxStar1
    have hle' : dotProduct x xStar ≤ 0 := by
      simpa [hprod] using hle
    exact (EReal.coe_le_coe_iff.2 hle')
  have h0le : (0 : EReal) ≤ supportFunctionEReal C₃ xStar := by
    unfold supportFunctionEReal
    refine le_of_forall_lt ?_
    intro c hc
    cases c using EReal.rec with
    | top =>
        exfalso
        simp at hc
    | bot =>
        let x : Fin 2 → Real := fun i => if i = 0 then (-1 : Real) else (-1 : Real)
        have hxC₃ : x ∈ C₃ := by
          dsimp [C₃, x]
          constructor <;> simp
        refine (lt_sSup_iff.2 ?_)
        refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
        exact EReal.bot_lt_coe (dotProduct x xStar)
    | coe r =>
        have hr : r < 0 := by
          simpa using (EReal.coe_lt_coe_iff.1 hc)
        have hr2 : r < r / 2 := by linarith
        have hzero : xStar 0 = 0 ∨ xStar 1 = 0 := by
          exact mul_eq_zero.mp hprod
        rcases hzero with hx0 | hx1
        · by_cases hx1' : xStar 1 = 0
          · -- `xStar = 0`: any point gives dot product `0`.
            let x : Fin 2 → Real := fun i => if i = 0 then (-1 : Real) else (-1 : Real)
            have hxC₃ : x ∈ C₃ := by
              dsimp [C₃, x]
              constructor <;> simp
            refine (lt_sSup_iff.2 ?_)
            refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
            have : dotProduct x xStar = 0 := by
              simp [dotProduct, x, Fin.sum_univ_two, hx0, hx1']
            simpa [this] using (show (r : EReal) < (0 : EReal) from (EReal.coe_lt_coe_iff.2 hr))
          · -- Vary `x₁` to make the dot product any negative real.
            have hxStar1pos : 0 < xStar 1 := lt_of_le_of_ne hxStar1 (Ne.symm hx1')
            let y : Real := (r / 2) / xStar 1
            have hyneg : y < 0 := div_neg_of_neg_of_pos (by linarith [hr]) hxStar1pos
            let x : Fin 2 → Real := fun i => if i = 0 then y⁻¹ else y
            have hxC₃ : x ∈ C₃ := by
              dsimp [C₃, x]
              constructor
              · simpa using (inv_lt_zero.2 hyneg)
              · simp
            have hdot : dotProduct x xStar = r / 2 := by
              have hx' : dotProduct x xStar = y * xStar 1 := by
                simp [dotProduct, x, Fin.sum_univ_two, hx0]
              have hxStar1ne : xStar 1 ≠ 0 := hx1'
              have hy : y * xStar 1 = r / 2 := by
                calc
                  y * xStar 1 = ((r / 2) / xStar 1) * xStar 1 := by rfl
                  _ = (r / 2) * xStar 1 / xStar 1 := by
                    simpa using (div_mul_eq_mul_div (r / 2) (xStar 1) (xStar 1))
                  _ = r / 2 := by
                    simpa using (mul_div_cancel_right₀ (r / 2) hxStar1ne)
              exact hx'.trans hy
            refine (lt_sSup_iff.2 ?_)
            refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
            have hrlt : r < dotProduct x xStar := by
              simpa [hdot] using hr2
            exact (EReal.coe_lt_coe_iff.2 hrlt)
        · by_cases hx0' : xStar 0 = 0
          · -- `xStar = 0`: any point gives dot product `0`.
            let x : Fin 2 → Real := fun i => if i = 0 then (-1 : Real) else (-1 : Real)
            have hxC₃ : x ∈ C₃ := by
              dsimp [C₃, x]
              constructor <;> simp
            refine (lt_sSup_iff.2 ?_)
            refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
            have : dotProduct x xStar = 0 := by
              simp [dotProduct, x, Fin.sum_univ_two, hx0', hx1]
            simpa [this] using (show (r : EReal) < (0 : EReal) from (EReal.coe_lt_coe_iff.2 hr))
          · -- Vary `x₀` to make the dot product any negative real.
            have hxStar0pos : 0 < xStar 0 := lt_of_le_of_ne hxStar0 (Ne.symm hx0')
            let x0 : Real := (r / 2) / xStar 0
            have hx0neg : x0 < 0 := div_neg_of_neg_of_pos (by linarith [hr]) hxStar0pos
            let x : Fin 2 → Real := fun i => if i = 0 then x0 else x0⁻¹
            have hxC₃ : x ∈ C₃ := by
              dsimp [C₃, x]
              constructor
              · simpa [x0] using hx0neg
              · simp
            have hdot : dotProduct x xStar = r / 2 := by
              have hx' : dotProduct x xStar = x0 * xStar 0 := by
                simp [dotProduct, x, Fin.sum_univ_two, hx1]
              have hxStar0ne : xStar 0 ≠ 0 := hx0'
              have hx0mul : x0 * xStar 0 = r / 2 := by
                calc
                  x0 * xStar 0 = ((r / 2) / xStar 0) * xStar 0 := by rfl
                  _ = (r / 2) * xStar 0 / xStar 0 := by
                    simpa using (div_mul_eq_mul_div (r / 2) (xStar 0) (xStar 0))
                  _ = r / 2 := by
                    simpa using (mul_div_cancel_right₀ (r / 2) hxStar0ne)
              exact hx'.trans hx0mul
            refine (lt_sSup_iff.2 ?_)
            refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₃, rfl⟩, ?_⟩
            have hrlt : r < dotProduct x xStar := by
              simpa [hdot] using hr2
            exact (EReal.coe_lt_coe_iff.2 hrlt)
  exact le_antisymm hsup_le h0le

/-- When `xStar 0, xStar 1 > 0`, the bound `-2 * sqrt (xStar 0 * xStar 1)` is attained on `C₃`. -/
lemma section13_exists_C3_point_dotProduct_eq_supportBound (xStar : Fin 2 → Real)
    (hxStar0 : 0 < xStar 0) (hxStar1 : 0 < xStar 1) :
    ∃ x : Fin 2 → Real,
      x 0 < 0 ∧ x 1 ≤ (x 0)⁻¹ ∧ dotProduct x xStar = -2 * Real.sqrt (xStar 0 * xStar 1) := by
  let sa : Real := Real.sqrt (xStar 0)
  let sb : Real := Real.sqrt (xStar 1)
  have hsa_pos : 0 < sa := Real.sqrt_pos.2 hxStar0
  have hsb_pos : 0 < sb := Real.sqrt_pos.2 hxStar1
  have hsa0 : sa ≠ 0 := (Real.sqrt_ne_zero (le_of_lt hxStar0)).2 (ne_of_gt hxStar0)
  have hsb0 : sb ≠ 0 := (Real.sqrt_ne_zero (le_of_lt hxStar1)).2 (ne_of_gt hxStar1)
  let t : Real := sb / sa
  have htpos : 0 < t := div_pos hsb_pos hsa_pos
  let x : Fin 2 → Real := fun i => if i = 0 then -t else (-t)⁻¹
  have hx0 : x 0 < 0 := by
    simp [x, htpos]
  have hx1 : x 1 ≤ (x 0)⁻¹ := by
    simp [x]
  refine ⟨x, hx0, hx1, ?_⟩
  have hxStar0' : xStar 0 = sa * sa := by
    simpa [sa, mul_comm, mul_left_comm, mul_assoc] using (Real.mul_self_sqrt (le_of_lt hxStar0)).symm
  have hxStar1' : xStar 1 = sb * sb := by
    simpa [sb, mul_comm, mul_left_comm, mul_assoc] using (Real.mul_self_sqrt (le_of_lt hxStar1)).symm
  have hmul0 : xStar 0 * t = sa * sb := by
    calc
      xStar 0 * t = xStar 0 * (sb / sa) := by rfl
      _ = xStar 0 * sb / sa := by simp [mul_div_assoc]
      _ = (sa * sa) * sb / sa := by simp [hxStar0']
      _ = sa * (sa * sb) / sa := by simp [mul_assoc]
      _ = sa * sb := by
        simpa [mul_assoc] using (mul_div_cancel_left₀ (sa * sb) hsa0)
  have hdiv1 : xStar 1 / t = sa * sb := by
    calc
      xStar 1 / t = xStar 1 / (sb / sa) := by rfl
      _ = xStar 1 * sa / sb := by
        simpa using (div_div_eq_mul_div (xStar 1) sb sa)
      _ = (sb * sb) * sa / sb := by simp [hxStar1']
      _ = sb * (sb * sa) / sb := by simp [mul_assoc]
      _ = sb * sa := by
        simpa [mul_assoc] using (mul_div_cancel_left₀ (sb * sa) hsb0)
      _ = sa * sb := by ring
  have hsqrt : Real.sqrt (xStar 0 * xStar 1) = sa * sb := by
    have hx0nonneg : 0 ≤ xStar 0 := le_of_lt hxStar0
    simpa [sa, sb] using (Real.sqrt_mul hx0nonneg (xStar 1))
  calc
    dotProduct x xStar = (-t) * xStar 0 + (-t)⁻¹ * xStar 1 := by
      simp [dotProduct, x, Fin.sum_univ_two]
    _ = -(xStar 0 * t + xStar 1 / t) := by
      simp [inv_neg, div_eq_mul_inv, add_comm, mul_comm]
    _ = -(sa * sb + sa * sb) := by simp [hmul0, hdiv1]
    _ = -2 * (sa * sb) := by ring
    _ = -2 * Real.sqrt (xStar 0 * xStar 1) := by simp [hsqrt]

/-- Text 13.2.6 (support function of `C₃`): for
`C₃ = {x = (ξ₁, ξ₂) | ξ₁ < 0 ∧ ξ₂ ≤ ξ₁⁻¹}`, one has
`δ^*(xStar | C₃) = -2 * sqrt (ξ₁^* ξ₂^*)` if `xStar ≥ 0`, and `+∞` otherwise. -/
theorem supportFunctionEReal_C3_eq_piecewise (xStar : Fin 2 → Real) :
    let C₃ : Set (Fin 2 → Real) := {x | x 0 < 0 ∧ x 1 ≤ (x 0)⁻¹}
    supportFunctionEReal C₃ xStar =
      if (0 ≤ xStar 0 ∧ 0 ≤ xStar 1) then
        ((-2 * Real.sqrt (xStar 0 * xStar 1) : Real) : EReal)
      else
        ⊤ := by
  classical
  by_cases hnonneg : (0 ≤ xStar 0 ∧ 0 ≤ xStar 1)
  · have hx0 : 0 ≤ xStar 0 := hnonneg.1
    have hx1 : 0 ≤ xStar 1 := hnonneg.2
    -- Reduce to an explicit set.
    dsimp
    set C₃ : Set (Fin 2 → Real) := {x | x 0 < 0 ∧ x 1 ≤ (x 0)⁻¹}
    have hsup_le :
        supportFunctionEReal C₃ xStar ≤
          ((-2 * Real.sqrt (xStar 0 * xStar 1) : Real) : EReal) := by
      unfold supportFunctionEReal
      refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hxC₃, rfl⟩
      rcases hxC₃ with ⟨hx0', hx1'⟩
      have hle :
          dotProduct x xStar ≤ -2 * Real.sqrt (xStar 0 * xStar 1) :=
        section13_dotProduct_le_supportBound_C3 (x := x) (xStar := xStar) hx0' hx1' hx0 hx1
      exact (EReal.coe_le_coe_iff.2 hle)
    have hle_sup :
        ((-2 * Real.sqrt (xStar 0 * xStar 1) : Real) : EReal) ≤
          supportFunctionEReal C₃ xStar := by
      by_cases hpos : (0 < xStar 0 ∧ 0 < xStar 1)
      · rcases
          section13_exists_C3_point_dotProduct_eq_supportBound (xStar := xStar) hpos.1 hpos.2 with
          ⟨x, hx0', hx1', hdot⟩
        unfold supportFunctionEReal
        have hxmem :
            ((dotProduct x xStar : Real) : EReal) ∈
              {z : EReal | ∃ x ∈ C₃, z = ((dotProduct x xStar : Real) : EReal)} :=
          ⟨x, ⟨hx0', hx1'⟩, rfl⟩
        have hle : ((dotProduct x xStar : Real) : EReal) ≤
            sSup {z : EReal | ∃ x ∈ C₃, z = ((dotProduct x xStar : Real) : EReal)} :=
          le_sSup hxmem
        simpa [hdot] using hle
      · have hzero : xStar 0 * xStar 1 = 0 := by
          have : ¬ 0 < xStar 0 ∨ ¬ 0 < xStar 1 := not_and_or.1 hpos
          rcases this with h0 | h1'
          · have hx0eq : xStar 0 = 0 := le_antisymm (le_of_not_gt h0) hx0
            simp [hx0eq]
          · have hx1eq : xStar 1 = 0 := le_antisymm (le_of_not_gt h1') hx1
            simp [hx1eq]
        have hsupp0 :
            supportFunctionEReal C₃ xStar = (0 : EReal) :=
          section13_supportFunctionEReal_C3_eq_zero_of_nonneg_and_mul_eq_zero (xStar := xStar) hx0 hx1
            hzero
        -- Reduce to `0 ≤ 0` after rewriting both sides.
        rw [hsupp0]
        simp [hzero]
    simpa [hnonneg, C₃] using (le_antisymm hsup_le hle_sup)
  · dsimp
    have hneg : xStar 0 < 0 ∨ xStar 1 < 0 := by
      have : ¬ 0 ≤ xStar 0 ∨ ¬ 0 ≤ xStar 1 := not_and_or.1 hnonneg
      rcases this with h0 | h1
      · exact Or.inl (lt_of_not_ge h0)
      · exact Or.inr (lt_of_not_ge h1)
    simpa [hnonneg] using (section13_supportFunctionEReal_C3_eq_top_of_neg_coord (xStar := xStar) hneg)

/-- For `0 < a`, the concave quadratic `t ↦ (-(t^2)/2) * a + t * b` is bounded above by
`b^2 / (2 * a)`. -/
lemma section13_neg_mul_sq_div_two_add_mul_le (a b t : Real) (ha : 0 < a) :
    (-(t ^ 2) / 2) * a + t * b ≤ b ^ 2 / (2 * a) := by
  have ha2 : 0 < 2 * a := by linarith
  have hsq : 0 ≤ (a * t - b) ^ 2 := sq_nonneg (a * t - b)
  have hsq' : 0 ≤ a ^ 2 * t ^ 2 - 2 * a * b * t + b ^ 2 := by
    have h :
        (a * t - b) ^ 2 = a ^ 2 * t ^ 2 - 2 * a * b * t + b ^ 2 := by
      ring
    simpa [h] using hsq
  have hineq : 2 * a * b * t - a ^ 2 * t ^ 2 ≤ b ^ 2 := by
    linarith [hsq']
  refine (le_div_iff₀ ha2).2 ?_
  have hmul :
      ((-(t ^ 2) / 2) * a + t * b) * (2 * a) = 2 * a * b * t - a ^ 2 * t ^ 2 := by
    ring
  simpa [hmul] using hineq

/-- For `x ∈ C₄` and `0 < xStar 0`, the dot product is bounded above by
`(xStar 1)^2 / (2 * xStar 0)`. -/
lemma section13_dotProduct_le_supportBound_C4 (x xStar : Fin 2 → Real)
    (hxC4 : (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0) (hxStar0 : 0 < xStar 0) :
    dotProduct x xStar ≤ (xStar 1) ^ 2 / (2 * xStar 0) := by
  have hx0 : x 0 ≤ -(x 1) ^ 2 / 2 := by
    linarith
  have hx0mul :
      x 0 * xStar 0 ≤ (-(x 1) ^ 2 / 2) * xStar 0 :=
    mul_le_mul_of_nonneg_right hx0 (le_of_lt hxStar0)
  have hdot : dotProduct x xStar = x 0 * xStar 0 + x 1 * xStar 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  have hle1 :
      dotProduct x xStar ≤ (-(x 1) ^ 2 / 2) * xStar 0 + x 1 * xStar 1 := by
    calc
      dotProduct x xStar = x 0 * xStar 0 + x 1 * xStar 1 := hdot
      _ ≤ (-(x 1) ^ 2 / 2) * xStar 0 + x 1 * xStar 1 :=
        add_le_add_left hx0mul (x 1 * xStar 1)
  have hle2 :
      (-(x 1) ^ 2 / 2) * xStar 0 + x 1 * xStar 1 ≤ (xStar 1) ^ 2 / (2 * xStar 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (section13_neg_mul_sq_div_two_add_mul_le (a := xStar 0) (b := xStar 1) (t := x 1) hxStar0)
  exact le_trans hle1 hle2

/-- For `0 < xStar 0`, there exists a point of `C₄` attaining the bound
`(xStar 1)^2 / (2 * xStar 0)` in the dot product. -/
lemma section13_exists_C4_point_dotProduct_eq_supportBound (xStar : Fin 2 → Real)
    (hxStar0 : 0 < xStar 0) :
    ∃ x : Fin 2 → Real, ((2 : Real) * x 0 + (x 1) ^ 2 ≤ 0) ∧
      dotProduct x xStar = (xStar 1) ^ 2 / (2 * xStar 0) := by
  let t : Real := xStar 1 / xStar 0
  let x : Fin 2 → Real := fun i => if i = 0 then -(t ^ 2) / 2 else t
  refine ⟨x, ?_, ?_⟩
  · have hx0 : x 0 = -(t ^ 2) / 2 := by simp [x]
    have hx1 : x 1 = t := by simp [x]
    have : (2 : Real) * x 0 + (x 1) ^ 2 = 0 := by
      simp [hx0, hx1]
      ring
    linarith
  · have hx0 : x 0 = -(t ^ 2) / 2 := by simp [x]
    have hx1 : x 1 = t := by simp [x]
    have hxStar0ne : xStar 0 ≠ 0 := ne_of_gt hxStar0
    simp [dotProduct, Fin.sum_univ_two, hx0, hx1, t]
    field_simp [hxStar0ne]
    ring

/-- If `xStar 0 < 0`, then the support function of `C₄` is `⊤`. -/
lemma section13_supportFunctionEReal_C4_eq_top_of_xStar0_lt_zero (xStar : Fin 2 → Real)
    (h0 : xStar 0 < 0) :
    let C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
    supportFunctionEReal C₄ xStar = ⊤ := by
  classical
  dsimp
  set C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
  unfold supportFunctionEReal
  refine sSup_eq_top.2 ?_
  intro b hbtop
  cases b using EReal.rec with
  | top =>
      exfalso
      simp at hbtop
  | bot =>
      let x : Fin 2 → Real := fun i => if i = 0 then (-1 : Real) else 0
      have hxC₄ : x ∈ C₄ := by
        dsimp [C₄, x]
        simp
      refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₄, rfl⟩, ?_⟩
      exact EReal.bot_lt_coe (dotProduct x xStar)
  | coe r =>
      let c₀ : Real := -xStar 0
      have hc₀ : 0 < c₀ := by
        dsimp [c₀]
        linarith
      let t : Real := max 1 ((r + 1) / c₀)
      have ht1 : (1 : Real) ≤ t := le_max_left _ _
      let x : Fin 2 → Real := fun i => if i = 0 then -t else 0
      have hxC₄ : x ∈ C₄ := by
        dsimp [C₄, x]
        have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
        nlinarith
      have hdot : dotProduct x xStar = t * c₀ := by
        simp [dotProduct, x, c₀, mul_comm]
      have hmul : r + 1 ≤ t * c₀ := by
        have : (r + 1) / c₀ ≤ t := le_max_right _ _
        exact (div_le_iff₀ hc₀).1 this
      have hrlt : r < dotProduct x xStar := by
        have : r < t * c₀ := by linarith [hmul]
        simpa [hdot] using this
      refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₄, rfl⟩, ?_⟩
      exact (EReal.coe_lt_coe_iff.2 hrlt)

/-- If `xStar 0 = 0` and `xStar 1 ≠ 0`, then the support function of `C₄` is `⊤`. -/
lemma section13_supportFunctionEReal_C4_eq_top_of_xStar0_eq_zero_and_xStar1_ne_zero
    (xStar : Fin 2 → Real) (h0 : xStar 0 = 0) (h1 : xStar 1 ≠ 0) :
    let C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
    supportFunctionEReal C₄ xStar = ⊤ := by
  classical
  dsimp
  set C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
  unfold supportFunctionEReal
  refine sSup_eq_top.2 ?_
  intro b hbtop
  cases b using EReal.rec with
  | top =>
      exfalso
      simp at hbtop
  | bot =>
      let x : Fin 2 → Real := fun _ => 0
      have hxC₄ : x ∈ C₄ := by
        dsimp [C₄, x]
        simp
      refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₄, rfl⟩, ?_⟩
      exact EReal.bot_lt_coe (dotProduct x xStar)
  | coe r =>
      let c₁ : Real := |xStar 1|
      have hc₁ : 0 < c₁ := by
        simpa [c₁] using (abs_pos.2 h1)
      let t : Real := max 1 ((r + 1) / c₁)
      let x1 : Real := if 0 ≤ xStar 1 then t else -t
      let x0 : Real := -(x1 ^ 2) / 2
      let x : Fin 2 → Real := fun i => if i = 0 then x0 else x1
      have hxC₄ : x ∈ C₄ := by
        dsimp [C₄, x, x0]
        have : (2 : Real) * (-(x1 ^ 2) / 2) + x1 ^ 2 = 0 := by
          ring
        linarith
      have hx1mul : dotProduct x xStar = c₁ * t := by
        have hdot : dotProduct x xStar = x1 * xStar 1 := by
          simp [dotProduct, x, Fin.sum_univ_two, h0]
        -- Choose the sign of `x1` so that `x1 * xStar 1 = |xStar 1| * t`.
        have hx : x1 * xStar 1 = c₁ * t := by
          by_cases hs : 0 ≤ xStar 1
          · simp [x1, c₁, hs, abs_of_nonneg hs, mul_comm]
          · have hs' : xStar 1 < 0 := lt_of_not_ge hs
            simp [x1, c₁, hs, abs_of_neg hs', mul_comm]
        exact hdot.trans hx
      have hmul : r + 1 ≤ t * c₁ := by
        have : (r + 1) / c₁ ≤ t := le_max_right _ _
        exact (div_le_iff₀ hc₁).1 this
      have hrlt : r < dotProduct x xStar := by
        have : r < t * c₁ := by linarith [hmul]
        -- Rewrite `t * c₁` as `c₁ * t`.
        have : r < c₁ * t := by simpa [mul_comm] using this
        simpa [hx1mul] using this
      refine ⟨((dotProduct x xStar : Real) : EReal), ⟨x, hxC₄, rfl⟩, ?_⟩
      exact (EReal.coe_lt_coe_iff.2 hrlt)

/-- If `xStar = 0`, then the support function of `C₄` is `0`. -/
lemma section13_supportFunctionEReal_C4_eq_zero_of_xStar_eq_zero (xStar : Fin 2 → Real)
    (h0 : xStar 0 = 0) (h1 : xStar 1 = 0) :
    let C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
    supportFunctionEReal C₄ xStar = (0 : EReal) := by
  classical
  dsimp
  set C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
  have hsup_le : supportFunctionEReal C₄ xStar ≤ (0 : EReal) := by
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxC₄, rfl⟩
    have : dotProduct x xStar = 0 := by
      simp [dotProduct, Fin.sum_univ_two, h0, h1]
    simp [this]
  have hle_sup : (0 : EReal) ≤ supportFunctionEReal C₄ xStar := by
    unfold supportFunctionEReal
    let x : Fin 2 → Real := fun _ => 0
    have hxC₄ : x ∈ C₄ := by
      dsimp [C₄, x]
      simp
    have hdot : dotProduct x xStar = 0 := by
      simp [dotProduct, x]
    have hxmem :
        (0 : EReal) ∈
          {z : EReal | ∃ x ∈ C₄, z = ((dotProduct x xStar : Real) : EReal)} := by
      refine ⟨x, hxC₄, ?_⟩
      simp [hdot]
    have : (0 : EReal) ≤ sSup {z : EReal | ∃ x ∈ C₄, z = ((dotProduct x xStar : Real) : EReal)} :=
      le_sSup hxmem
    simpa using this
  exact le_antisymm hsup_le hle_sup

/-- Text 13.2.6 (support function of `C₄`): for
`C₄ = {x = (ξ₁, ξ₂) | 2 ξ₁ + ξ₂² ≤ 0}`, one has
`δ^*(xStar | C₄) = (ξ₂^*)² / (2 * ξ₁^*)` if `ξ₁^* > 0`, `0` if `xStar = 0`, and `+∞`
otherwise. -/
theorem supportFunctionEReal_C4_eq_piecewise (xStar : Fin 2 → Real) :
    let C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
    supportFunctionEReal C₄ xStar =
      if xStar 0 > 0 then
        (((xStar 1) ^ 2 / (2 * xStar 0) : Real) : EReal)
      else if xStar 0 = 0 ∧ xStar 1 = 0 then
        (0 : EReal)
      else
        ⊤ := by
  classical
  dsimp
  set C₄ : Set (Fin 2 → Real) := {x | (2 : Real) * x 0 + (x 1) ^ 2 ≤ 0}
  by_cases hx0pos : xStar 0 > 0
  · have hxStar0 : 0 < xStar 0 := by simpa using hx0pos
    simp [hx0pos]
    have hsup_le :
        supportFunctionEReal C₄ xStar ≤
          (((xStar 1) ^ 2 / (2 * xStar 0) : Real) : EReal) := by
      unfold supportFunctionEReal
      refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hxC₄, rfl⟩
      have hle :
          dotProduct x xStar ≤ (xStar 1) ^ 2 / (2 * xStar 0) :=
        section13_dotProduct_le_supportBound_C4 (x := x) (xStar := xStar) hxC₄ hxStar0
      exact (EReal.coe_le_coe_iff.2 hle)
    have hle_sup :
        (((xStar 1) ^ 2 / (2 * xStar 0) : Real) : EReal) ≤
          supportFunctionEReal C₄ xStar := by
      rcases
          section13_exists_C4_point_dotProduct_eq_supportBound (xStar := xStar) hxStar0 with
        ⟨x, hxC₄, hdot⟩
      unfold supportFunctionEReal
      have hxmem :
          ((dotProduct x xStar : Real) : EReal) ∈
            {z : EReal | ∃ x ∈ C₄, z = ((dotProduct x xStar : Real) : EReal)} :=
        ⟨x, hxC₄, rfl⟩
      have hle :
          ((dotProduct x xStar : Real) : EReal) ≤
            sSup {z : EReal | ∃ x ∈ C₄, z = ((dotProduct x xStar : Real) : EReal)} :=
        le_sSup hxmem
      simpa [hdot] using hle
    exact le_antisymm hsup_le hle_sup
  · have hx0le : xStar 0 ≤ 0 := le_of_not_gt hx0pos
    by_cases hzero : xStar 0 = 0 ∧ xStar 1 = 0
    · simp [hzero]
      simpa [C₄] using
        (section13_supportFunctionEReal_C4_eq_zero_of_xStar_eq_zero (xStar := xStar) hzero.1 hzero.2)
    · simp [hx0pos, hzero]
      have hcases : xStar 0 < 0 ∨ (xStar 0 = 0 ∧ xStar 1 ≠ 0) := by
        by_cases hx0eq : xStar 0 = 0
        · refine Or.inr ⟨hx0eq, ?_⟩
          intro hx1eq
          exact hzero ⟨hx0eq, hx1eq⟩
        · exact Or.inl (lt_of_le_of_ne hx0le hx0eq)
      rcases hcases with hx0neg | hx0eq
      · simpa [C₄] using
          (section13_supportFunctionEReal_C4_eq_top_of_xStar0_lt_zero (xStar := xStar) hx0neg)
      · simpa [C₄] using
          (section13_supportFunctionEReal_C4_eq_top_of_xStar0_eq_zero_and_xStar1_ne_zero
            (xStar := xStar) hx0eq.1 hx0eq.2)

/-- For the `EReal`-valued support function, an upper bound by a real `μ` is equivalent to a
pointwise upper bound on all dot products defining the supremum. -/
lemma section13_supportFunctionEReal_effectiveDomain_le_coe_iff {n : Nat}
    (f : (Fin n → Real) → EReal) (y : Fin n → Real) (μ : Real) :
    supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) y ≤ (μ : EReal) ↔
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, (dotProduct x y : Real) ≤ μ := by
  classical
  constructor
  · intro hle x hx
    have hxle :
        ((dotProduct x y : Real) : EReal) ≤
          sSup
            {z : EReal |
              ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f,
                z = ((dotProduct x y : Real) : EReal)} :=
      le_sSup ⟨x, hx, rfl⟩
    have : ((dotProduct x y : Real) : EReal) ≤ (μ : EReal) := le_trans hxle hle
    exact (EReal.coe_le_coe_iff.1 this)
  · intro hle
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact (EReal.coe_le_coe_iff.2 (hle x hx))

/-- For the `sSup`-of-differences recession formula, bounding by a real `μ` is equivalent to a
uniform pointwise bound on each difference term. -/
lemma section13_recessionSup_le_coe_iff {n : Nat}
    (g : (Fin n → Real) → EReal) (g0_plus : (Fin n → Real) → EReal)
    (hg0_plus :
      ∀ y : Fin n → Real,
        g0_plus y =
          sSup
            {r : EReal |
              ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g,
                r = g (x + y) - g x})
    (y : Fin n → Real) (μ : Real) :
    g0_plus y ≤ (μ : EReal) ↔
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g, g (x + y) - g x ≤ (μ : EReal) := by
  classical
  constructor
  · intro hle x hx
    have hxle :
        g (x + y) - g x ≤
          sSup
            {r : EReal |
              ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g, r = g (x + y) - g x} :=
      le_sSup ⟨x, hx, rfl⟩
    have : g (x + y) - g x ≤ (μ : EReal) := le_trans hxle (by simpa [hg0_plus y] using hle)
    exact this
  · intro hle
    have hsup :
        sSup
            {r : EReal |
              ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g, r = g (x + y) - g x} ≤
          (μ : EReal) := by
      refine sSup_le ?_
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact hle x hx
    simpa [hg0_plus y] using hsup

/-- The dot product is additive in the second argument, hence it commutes with `nsmul` there. -/
lemma section13_dotProduct_nsmul_right {n : Nat} (x y : Fin n → Real) (m : ℕ) :
    dotProduct x (m • y) = (m : Real) * dotProduct x y := by
  classical
  -- Package `z ↦ ⟪x,z⟫` as an additive homomorphism and use `map_nsmul`.
  let φ : (Fin n → Real) →+ Real :=
    { toFun := fun z => dotProduct x z
      map_zero' := by
        simp
      map_add' := by
        intro z w
        simp }
  have h := φ.map_nsmul y m
  -- Rewrite the `nsmul` on the right-hand side as multiplication in `Real`.
  simpa [φ, nsmul_eq_mul] using h

/-- If all dot products `⟪x,y⟫` over `x ∈ dom f` are bounded by `μ`, then every difference
`f*(xStar+y) - f*(xStar)` with `xStar ∈ dom f*` is bounded by `μ`. -/
lemma section13_fenchelConjugate_add_le_add_supportFunctionEReal {n : Nat}
    (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {y : Fin n → Real} {μ : Real}
    (hxy :
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, (dotProduct x y : Real) ≤ μ) :
    ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f),
      fenchelConjugate n f (xStar + y) - fenchelConjugate n f xStar ≤ (μ : EReal) := by
  classical
  intro xStar hxStar
  -- It suffices to bound `f*(xStar+y)` by `μ + f*(xStar)`.
  have hxStar_ne_top :
      fenchelConjugate n f xStar ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real)))
      (f := fenchelConjugate n f) hxStar
  have hxStar_ne_bot :
      fenchelConjugate n f xStar ≠ (⊥ : EReal) := by
    -- `f*` is proper when `f` is proper.
    have hfStar :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
      proper_fenchelConjugate_of_proper (n := n) (f := f) hf
    exact hfStar.2.2 xStar (by simp)
  have hle_add :
      fenchelConjugate n f (xStar + y) ≤ (μ : EReal) + fenchelConjugate n f xStar := by
    -- Use the `iSup` presentation of the conjugate.
    rw [fenchelConjugate_eq_iSup (n := n) (f := f) (xStar := xStar + y)]
    refine iSup_le ?_
    intro x
    by_cases hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f
    · have hx_ne_top :
          f x ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
      have hx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      set fx : Real := (f x).toReal
      have hfx : (fx : EReal) = f x := by
        simpa [fx] using (EReal.coe_toReal (x := f x) hx_ne_top hx_ne_bot)
      -- `⟪x,xStar⟫ - f x ≤ f*(xStar)` and `⟪x,y⟫ ≤ μ`.
      have hxStar_le :
          ((dotProduct x xStar : Real) : EReal) - f x ≤ fenchelConjugate n f xStar :=
        le_sSup ⟨x, rfl⟩
      have hy_le : ((dotProduct x y : Real) : EReal) ≤ (μ : EReal) :=
        (EReal.coe_le_coe_iff.2 (hxy x hx))
      -- Combine and reorder.
      have hterm :
          ((dotProduct x (xStar + y) : Real) : EReal) - f x ≤
            fenchelConjugate n f xStar + (μ : EReal) := by
        have hdot :
            ((dotProduct x (xStar + y) : Real) : EReal) =
              ((dotProduct x xStar : Real) : EReal) + ((dotProduct x y : Real) : EReal) := by
          -- Expand along the second argument.
          simp [dotProduct_add]
        -- Rewrite the term and use monotonicity of addition.
        calc
          ((dotProduct x (xStar + y) : Real) : EReal) - f x
              = (((dotProduct x xStar : Real) : EReal) - f x) + ((dotProduct x y : Real) : EReal) := by
                  -- Rearrangement in a commutative additive monoid.
                  simp [sub_eq_add_neg, add_left_comm, add_comm]
          _ ≤ fenchelConjugate n f xStar + (μ : EReal) := by
                  exact add_le_add hxStar_le hy_le
      -- Finish by commuting the sum.
      simpa [add_comm, add_left_comm, add_assoc] using hterm
    · -- Outside `dom f`, `f x = ⊤` (since `f` is proper on `univ`), so the range term is `⊥`.
      have hx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      have hx_top : f x = (⊤ : EReal) := by
        -- Not in effective domain means not `< ⊤`, so (with no `⊥`) it must be `⊤`.
        by_contra hx_ne_top
        have hx_dom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
          refine ⟨(f x).toReal, ?_⟩
          refine And.intro (by trivial) ?_
          simpa using (EReal.le_coe_toReal (x := f x) hx_ne_top)
        exact hx hx_dom
      simp [hx_top]
  have h1 : fenchelConjugate n f xStar ≠ (⊥ : EReal) ∨ (μ : EReal) ≠ ⊤ := Or.inr (by simp)
  have h2 : fenchelConjugate n f xStar ≠ (⊤ : EReal) ∨ (μ : EReal) ≠ ⊥ := Or.inr (by simp)
  exact (EReal.sub_le_iff_le_add h1 h2).2 (by simpa [add_assoc, add_comm, add_left_comm] using hle_add)

/-- Theorem 13.3: Let `f` be a proper convex function. The support function of `dom f` is the
recession function `(f^*)0+` of the conjugate `f^*`. If `f` is closed, the support function of
`dom f^*` is the recession function `f0+` of `f`. -/
theorem supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate {n : Nat}
    (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (fStar0_plus : (Fin n → Real) → EReal)
    (hfStar0_plus :
      ∀ y : Fin n → Real,
        fStar0_plus y =
          sSup
            {r : EReal |
              ∃ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f),
                r = fenchelConjugate n f (xStar + y) - fenchelConjugate n f xStar}) :
    supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) = fStar0_plus := by
  classical
  funext y
  refine EReal.eq_of_forall_le_coe_iff (a := supportFunctionEReal
      (effectiveDomain (Set.univ : Set (Fin n → Real)) f) y) (b := fStar0_plus y) (fun μ => ?_)
  -- Compare the same real upper bounds on both sides.
  constructor
  · intro hsup
    -- Convert the support-function bound into a pointwise dot-product bound.
    have hxy :
        ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, (dotProduct x y : Real) ≤ μ :=
      (section13_supportFunctionEReal_effectiveDomain_le_coe_iff (f := f) (y := y) (μ := μ)).1 hsup
    -- Use the recession `sSup` inequality characterization.
    have hrecession :
        fStar0_plus y ≤ (μ : EReal) ↔
          ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f),
            fenchelConjugate n f (xStar + y) - fenchelConjugate n f xStar ≤ (μ : EReal) :=
      section13_recessionSup_le_coe_iff (g := fenchelConjugate n f) (g0_plus := fStar0_plus)
        (hg0_plus := hfStar0_plus) (y := y) (μ := μ)
    refine (hrecession.2 ?_)
    exact
      section13_fenchelConjugate_add_le_add_supportFunctionEReal (f := f) (hf := hf) (y := y)
        (μ := μ) hxy
  · intro hrec
    -- Goal: bound the support function by showing every `⟪x,y⟫` is ≤ μ.
    have hrecession :
        fStar0_plus y ≤ (μ : EReal) ↔
          ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f),
            fenchelConjugate n f (xStar + y) - fenchelConjugate n f xStar ≤ (μ : EReal) :=
      section13_recessionSup_le_coe_iff (g := fenchelConjugate n f) (g0_plus := fStar0_plus)
        (hg0_plus := hfStar0_plus) (y := y) (μ := μ)
    have hdiff := (hrecession.1 hrec)
    -- Use the epigraph of `f*` and the fact that the bound holds at every base point in `dom f*`.
    let fStar : (Fin n → Real) → EReal := fenchelConjugate n f
    -- Unfold the epigraph of `f*` as an intersection of epigraphs of its affine pieces.
    let hPiece : (Fin n → Real) → (Fin n → Real) → EReal :=
      fun x xStar => ((dotProduct x xStar : Real) : EReal) - f x
    have hepigraph :
        epigraph (Set.univ : Set (Fin n → Real)) fStar =
          ⋂ x : Fin n → Real, epigraph (Set.univ : Set (Fin n → Real)) (hPiece x) := by
      -- `f*` is the pointwise supremum of the affine pieces `hPiece x`.
      have hsup :
          (fun xStar : Fin n → Real => iSup (fun x : Fin n → Real => hPiece x xStar)) =
            fStar := by
        funext xStar
        simp [fenchelConjugate_eq_iSup, fStar, hPiece]
      -- Convert epigraphs using `epigraph_iSup_eq_iInter_univ`.
      simpa [hsup] using
        (epigraph_iSup_eq_iInter_univ (f := fun x => hPiece x))
    -- A one-step bound at every `xStar ∈ dom f*` yields translation invariance of the epigraph.
    have hstep :
        ∀ {xStar : Fin n → Real} {α : Real},
          ((xStar, α) : (Fin n → Real) × Real) ∈ epigraph (Set.univ : Set (Fin n → Real)) fStar →
            ((xStar + y, α + μ) : (Fin n → Real) × Real) ∈
              epigraph (Set.univ : Set (Fin n → Real)) fStar := by
      intro xStar α hxepi
      have hxdom : xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) fStar := ⟨α, hxepi⟩
      have hsub : fStar (xStar + y) - fStar xStar ≤ (μ : EReal) := by
        simpa [fStar] using hdiff xStar hxdom
      have h1 : fStar xStar ≠ (⊥ : EReal) ∨ (μ : EReal) ≠ ⊤ := Or.inr (by simp)
      have h2 : fStar xStar ≠ (⊤ : EReal) ∨ (μ : EReal) ≠ ⊥ := Or.inr (by simp)
      have hadd : fStar (xStar + y) ≤ (μ : EReal) + fStar xStar :=
        (EReal.sub_le_iff_le_add h1 h2).1 hsub
      have hxle : fStar xStar ≤ (α : EReal) :=
        (mem_epigraph_univ_iff (f := fStar)).1 hxepi
      have : fStar (xStar + y) ≤ (μ : EReal) + (α : EReal) :=
        le_trans hadd (add_le_add_right hxle (μ : EReal))
      have : fStar (xStar + y) ≤ ((α + μ : Real) : EReal) := by
        simpa [add_assoc, add_comm, add_left_comm] using this
      exact (mem_epigraph_univ_iff (f := fStar)).2 this
    -- Choose a basepoint in `epi f*` and iterate the translation.
    have hfStar :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fStar :=
      by simpa [fStar] using (proper_fenchelConjugate_of_proper (n := n) (f := f) hf)
    rcases hfStar.2.1 with ⟨⟨x0, α0⟩, hx0epi⟩
    have hx0_all :
        ∀ m : ℕ,
          ((x0 + m • y, α0 + (m : Real) * μ) : (Fin n → Real) × Real) ∈
            epigraph (Set.univ : Set (Fin n → Real)) fStar := by
      intro m
      induction m with
      | zero =>
          simpa using hx0epi
      | succ m ih =>
          have hnext := hstep (xStar := x0 + m • y) (α := α0 + (m : Real) * μ) ih
          -- Simplify the successor expressions.
          simpa [succ_nsmul, Nat.cast_succ, add_assoc, add_left_comm, add_comm, add_mul, mul_add] using hnext
    -- Deduce `⟪x,y⟫ ≤ μ` for every `x ∈ dom f`.
    have hxy :
        ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, (dotProduct x y : Real) ≤ μ := by
      intro x hx
      have hx_ne_top : f x ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
      have hx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      set fx : Real := (f x).toReal
      have hfx : (fx : EReal) = f x := by
        simpa [fx] using (EReal.coe_toReal (x := f x) hx_ne_top hx_ne_bot)
      -- Extract the pointwise inequalities along the translated epigraph points.
      have hx_piece :
          ∀ m : ℕ,
            hPiece x (x0 + m • y) ≤ ((α0 + (m : Real) * μ : Real) : EReal) := by
        intro m
        have hx0m_epi :
            ((x0 + m • y, α0 + (m : Real) * μ) : (Fin n → Real) × Real) ∈
              ⋂ z : Fin n → Real, epigraph (Set.univ : Set (Fin n → Real)) (hPiece z) := by
          simpa [hepigraph] using (hx0_all m)
        have hx0m_x :
            ((x0 + m • y, α0 + (m : Real) * μ) : (Fin n → Real) × Real) ∈
              epigraph (Set.univ : Set (Fin n → Real)) (hPiece x) :=
          (Set.mem_iInter.1 hx0m_epi) x
        exact (mem_epigraph_univ_iff (f := hPiece x)).1 hx0m_x
      -- Convert the epigraph inequalities into real inequalities.
      have hx_real :
          ∀ m : ℕ,
            dotProduct x (x0 + m • y) - fx ≤ α0 + (m : Real) * μ := by
        intro m
        have : ((dotProduct x (x0 + m • y) - fx : Real) : EReal) ≤ ((α0 + (m : Real) * μ : Real) : EReal) := by
          simpa [hPiece, hfx, EReal.coe_sub] using hx_piece m
        exact (EReal.coe_le_coe_iff.1 this)
      -- If `⟪x,y⟫ > μ`, the affine inequality fails for large translates.
      by_contra hle
      have hlt : μ < dotProduct x y := lt_of_not_ge hle
      set δ : Real := dotProduct x y - μ
      have hδpos : 0 < δ := sub_pos.2 hlt
      have hδne : δ ≠ 0 := ne_of_gt hδpos
      set K : Real := α0 - (dotProduct x x0 - fx)
      -- From each epigraph inequality, get `(m:ℝ) * δ ≤ K`.
      have hK : ∀ m : ℕ, (m : Real) * δ ≤ K := by
        intro m
        have hm :
            dotProduct x x0 + (m : Real) * dotProduct x y - fx ≤ α0 + (m : Real) * μ := by
          have hdot :
              dotProduct x (x0 + m • y) =
                dotProduct x x0 + (m : Real) * dotProduct x y := by
            calc
              dotProduct x (x0 + m • y) = dotProduct x x0 + dotProduct x (m • y) :=
                dotProduct_add x x0 (m • y)
              _ = dotProduct x x0 + (m : Real) * dotProduct x y := by
                rw [section13_dotProduct_nsmul_right (x := x) (y := y) (m := m)]
          -- Rewrite `hx_real m` using `hdot`.
          have hm0 := hx_real m
          rw [hdot] at hm0
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hm0
        have hm' :
            (dotProduct x x0 + (m : Real) * dotProduct x y - fx) - (dotProduct x x0 - fx) ≤
              (α0 + (m : Real) * μ) - (dotProduct x x0 - fx) :=
          sub_le_sub_right hm (dotProduct x x0 - fx)
        have hm'' : (m : Real) * dotProduct x y ≤ K + (m : Real) * μ := by
          have hlhs :
              (dotProduct x x0 + (m : Real) * dotProduct x y - fx) - (dotProduct x x0 - fx) =
                (m : Real) * dotProduct x y := by ring
          have hrhs :
              (α0 + (m : Real) * μ) - (dotProduct x x0 - fx) = K + (m : Real) * μ := by
            simp [K]
            ring
          simpa [hlhs, hrhs] using hm'
        have hm''' :
            (m : Real) * dotProduct x y - (m : Real) * μ ≤ K := by
          have hm4 :
              (m : Real) * dotProduct x y - (m : Real) * μ ≤ (K + (m : Real) * μ) - (m : Real) * μ :=
            sub_le_sub_right hm'' ((m : Real) * μ)
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hm4
        -- Rewrite the left-hand side as `(m:ℝ) * δ`.
        simpa [δ, mul_sub] using hm'''
      -- Choose `m` with `K < (m:ℝ) * δ` and contradict `hK m`.
      rcases exists_nat_gt (K / δ) with ⟨m, hmgt⟩
      have hmul : (K / δ) * δ < (m : Real) * δ := mul_lt_mul_of_pos_right hmgt hδpos
      have hKlt : K < (m : Real) * δ := by
        -- `K = (K/δ) * δ` since `δ ≠ 0`.
        have : (K / δ) * δ = K := by
          field_simp [hδne]
        simpa [this] using hmul
      have : ¬ (m : Real) * δ ≤ K := not_le_of_gt hKlt
      exact this (hK m)
    exact
      (section13_supportFunctionEReal_effectiveDomain_le_coe_iff (f := f) (y := y) (μ := μ)).2 hxy

/-- Theorem 13.3 (closed case): if `f` is closed, then the support function of `dom f^*` is the
recession function `f0+` of `f`. -/
theorem supportFunctionEReal_effectiveDomain_fenchelConjugate_eq_recession {n : Nat}
    (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hclosed : ClosedConvexFunction f)
    (f0_plus : (Fin n → Real) → EReal)
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup
            {r : EReal |
              ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f,
                r = f (x + y) - f x}) :
    supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) =
        f0_plus := by
  classical
  -- Apply the first part of Theorem 13.3 to `g := f*`.
  let g : (Fin n → Real) → EReal := fenchelConjugate n f
  have hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hcl : clConv n f = f :=
    clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hclosed.2) (hf_proper := hf)
  have hbiconj : fenchelConjugate n g = f := by
    -- `f** = clConv f = f` under closedness.
    have : fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
      fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)
    simpa [g, hcl] using this
  -- Provide the recession formula for the conjugate of `g`, which is `f** = f`.
  have hg0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup
            {r : EReal |
              ∃ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n g),
                r = fenchelConjugate n g (xStar + y) - fenchelConjugate n g xStar} := by
    intro y
    -- Rewrite `fenchelConjugate n g` as `f`.
    simpa [hbiconj] using (hf0_plus y)
  simpa [g] using
    (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate (n := n) (f := g) (hf := hg)
      (fStar0_plus := f0_plus) (hfStar0_plus := hg0_plus))

end Section13
end Chap03
