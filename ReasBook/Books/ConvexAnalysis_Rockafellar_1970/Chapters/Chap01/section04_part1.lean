/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xuran Sun, Zaiwen Wen
-/

import Mathlib

open scoped Matrix Topology

section Chap01
section Section04

/-- Definition 4.1: Let `f` be a function with values in `R` union
`{plus or minus infinity}` whose domain is a subset `S` of `R^n`. The set
`{(x, mu) | x in S, mu in R, mu >= f x}` is called the epigraph of `f`,
denoted `epi f`. -/
def epigraph {n : Nat} (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    Set (Prod (Fin n -> Real) Real) :=
  {p | And (S p.1) (f p.1 <= (p.2 : EReal))}

/-- Definition 4.2: A function `f` on `S` is a convex function if `epi f` is
convex as a subset of `R^{n+1}`. -/
def ConvexFunctionOn {n : Nat} (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    Prop :=
  Convex ℝ (epigraph S f)

/-- If `x ∈ S` and `f x ≤ μ`, then `(x, μ)` belongs to the epigraph. -/
lemma epigraph_mem_of_le_aux {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real} {μ : Real}
    (hx : x ∈ S) (hμ : f x ≤ (μ : EReal)) : (x, μ) ∈ epigraph S f := by
  exact And.intro hx hμ

/-- Convexity of the epigraph yields convex combinations of its points. -/
lemma convex_combo_mem_epigraph_aux {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} {x y : Fin n → Real} {μ v t : Real}
    (hconv : Convex ℝ (epigraph S f))
    (hx : (x, μ) ∈ epigraph S f) (hy : (y, v) ∈ epigraph S f)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • (x, μ) + t • (y, v) ∈ epigraph S f := by
  have ht1' : 0 ≤ (1 - t) := by linarith
  have hsum : (1 - t) + t = (1 : Real) := by ring
  simpa using hconv hx hy ht1' ht0 hsum

/-- Unpack epigraph membership of a convex combination. -/
lemma epigraph_combo_proj_aux {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} {x y : Fin n → Real} {μ v t : Real} :
    ((1 - t) • (x, μ) + t • (y, v)) ∈ epigraph S f →
      ((1 - t) • x + t • y) ∈ S ∧
        f ((1 - t) • x + t • y) ≤
          (((1 - t) * μ + t * v : Real) : EReal) := by
  intro hmem
  have hmem' :
      S ((1 - t) • (x, μ) + t • (y, v)).1 ∧
        f ((1 - t) • (x, μ) + t • (y, v)).1 ≤
          (((1 - t) • (x, μ) + t • (y, v)).2 : EReal) := by
    simpa [epigraph] using hmem
  rcases hmem' with ⟨hS, hle⟩
  refine ⟨?_, ?_⟩
  · simpa using hS
  · simpa [smul_eq_mul] using hle

/-- Convexity of the epigraph gives a real upper bound along segments. -/
lemma epigraph_combo_ineq_aux {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} {x y : Fin n → Real} {μ v t : Real}
    (hconv : Convex ℝ (epigraph S f))
    (hx : x ∈ S) (hy : y ∈ S)
    (hμ : f x ≤ (μ : EReal)) (hv : f y ≤ (v : EReal))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • x + t • y) ≤ (((1 - t) * μ + t * v : Real) : EReal) := by
  have hx_epi : (x, μ) ∈ epigraph S f := epigraph_mem_of_le_aux (x := x) (μ := μ) hx hμ
  have hy_epi : (y, v) ∈ epigraph S f := epigraph_mem_of_le_aux (x := y) (μ := v) hy hv
  have hmem :
      (1 - t) • (x, μ) + t • (y, v) ∈ epigraph S f :=
    convex_combo_mem_epigraph_aux (x := x) (y := y) (μ := μ) (v := v) (t := t)
      hconv hx_epi hy_epi ht0 ht1
  exact (epigraph_combo_proj_aux (x := x) (y := y) (μ := μ) (v := v) (t := t) hmem).2

/-- Theorem 4.1: Let `f` be a function from `C` to `(-∞, +∞]`, where `C` is convex.
Then `f` is convex on `C` iff
`f ((1 - λ) • x + λ • y) ≤ (1 - λ) * f x + λ * f y` for `0 < λ < 1`,
for every `x` and `y` in `C`. -/
theorem convexFunctionOn_iff_segment_inequality {n : Nat} {C : Set (Fin n -> Real)}
    {f : (Fin n -> Real) → EReal} (hC : Convex ℝ C)
    (hnotbot : ∀ x ∈ C, f x ≠ ⊥) :
    ConvexFunctionOn C f ↔
      ∀ x ∈ C, ∀ y ∈ C, ∀ t : Real, 0 < t → t < 1 →
        f ((1 - t) • x + t • y) ≤
          ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
  constructor
  · intro hf x hx y hy t ht0 ht1
    have hconv : Convex ℝ (epigraph C f) := by
      simpa [ConvexFunctionOn] using hf
    have ht0' : 0 ≤ t := le_of_lt ht0
    have ht1' : t ≤ 1 := le_of_lt ht1
    have ht0E : (0 : EReal) < (t : EReal) := (EReal.coe_pos).2 ht0
    have ht1E : (0 : EReal) < ((1 - t) : EReal) :=
      (EReal.coe_pos).2 (sub_pos.mpr ht1)
    by_cases hx_top : f x = ⊤
    · have hne : ((t : Real) : EReal) * f y ≠ ⊥ := by
        by_cases hy_top : f y = ⊤
        · have htop : ((t : Real) : EReal) * f y = ⊤ := by
            simpa [hy_top] using (EReal.mul_top_of_pos ht0E)
          simp [htop]
        · have hy_bot : f y ≠ ⊥ := hnotbot y hy
          have hfy :
              ((t : Real) : EReal) * f y = ((t * (f y).toReal : Real) : EReal) := by
            have hfy' : ((f y).toReal : EReal) = f y :=
              EReal.coe_toReal hy_top hy_bot
            calc
              ((t : Real) : EReal) * f y =
                  ((t : Real) : EReal) * ((f y).toReal : EReal) := by
                    simp [hfy']
              _ = ((t * (f y).toReal : Real) : EReal) := by
                    simp [EReal.coe_mul]
          simpa [hfy] using (EReal.coe_ne_bot (t * (f y).toReal))
      have htop :
          ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y = ⊤ := by
        have hfx : ((1 - t : Real) : EReal) * f x = ⊤ := by
          simpa [hx_top] using (EReal.mul_top_of_pos ht1E)
        calc
          ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y =
              ⊤ + ((t : Real) : EReal) * f y := by
                rw [hfx]
          _ = ⊤ := EReal.top_add_of_ne_bot hne
      calc
        f ((1 - t) • x + t • y) ≤ ⊤ := le_top
        _ = ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
              symm; exact htop
    · by_cases hy_top : f y = ⊤
      · have hne : ((1 - t : Real) : EReal) * f x ≠ ⊥ := by
          have hx_bot : f x ≠ ⊥ := hnotbot x hx
          have hfx :
              ((1 - t : Real) : EReal) * f x =
                (((1 - t) * (f x).toReal : Real) : EReal) := by
            have hfx' : ((f x).toReal : EReal) = f x :=
              EReal.coe_toReal hx_top hx_bot
            calc
              ((1 - t : Real) : EReal) * f x =
                  ((1 - t : Real) : EReal) * ((f x).toReal : EReal) := by
                    simp [hfx']
              _ = (((1 - t) * (f x).toReal : Real) : EReal) := by
                    simp [EReal.coe_mul]
          have hne' :
              (((1 - t) * (f x).toReal : Real) : EReal) ≠ ⊥ :=
            EReal.coe_ne_bot ((1 - t) * (f x).toReal)
          intro hbot
          apply hne'
          have hbot' := hbot
          rw [hfx] at hbot'
          exact hbot'
        have htop :
            ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y = ⊤ := by
          have hfy : ((t : Real) : EReal) * f y = ⊤ := by
            simpa [hy_top] using (EReal.mul_top_of_pos ht0E)
          calc
            ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y =
                ((1 - t : Real) : EReal) * f x + ⊤ := by simp [hfy]
            _ = ⊤ := EReal.add_top_of_ne_bot hne
        calc
          f ((1 - t) • x + t • y) ≤ ⊤ := le_top
          _ = ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
                symm; exact htop
      · have hx_bot : f x ≠ ⊥ := hnotbot x hx
        have hy_bot : f y ≠ ⊥ := hnotbot y hy
        have hμ : f x ≤ (f x).toReal := EReal.le_coe_toReal hx_top
        have hv : f y ≤ (f y).toReal := EReal.le_coe_toReal hy_top
        have hle :=
          epigraph_combo_ineq_aux (S := C) (f := f) (x := x) (y := y)
            (μ := (f x).toReal) (v := (f y).toReal) hconv hx hy hμ hv ht0' ht1'
        have hfx : ((f x).toReal : EReal) = f x :=
          EReal.coe_toReal hx_top hx_bot
        have hfy : ((f y).toReal : EReal) = f y :=
          EReal.coe_toReal hy_top hy_bot
        have hcoeff :
            (((1 - t) * (f x).toReal + t * (f y).toReal : Real) : EReal) =
              ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
          calc
            (((1 - t) * (f x).toReal + t * (f y).toReal : Real) : EReal) =
                (((1 - t) * (f x).toReal : Real) : EReal) +
                  ((t * (f y).toReal : Real) : EReal) := by
                    simp [EReal.coe_add]
            _ = ((1 - t : Real) : EReal) * ((f x).toReal : EReal) +
                ((t : Real) : EReal) * ((f y).toReal : EReal) := by
                  simp [EReal.coe_mul]
            _ = ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
                  simp [hfx, hfy]
        simpa [hcoeff] using hle
  · intro hseg p hp q hq a b ha hb hab
    rcases p with ⟨x, μ⟩
    rcases q with ⟨y, v⟩
    have hx : x ∈ C := hp.1
    have hy : y ∈ C := hq.1
    have hμ : f x ≤ (μ : EReal) := hp.2
    have hv : f y ≤ (v : EReal) := hq.2
    have hmemC : (a • x + b • y) ∈ C := hC hx hy ha hb hab
    have hle :
        f (a • x + b • y) ≤ ((a * μ + b * v : Real) : EReal) := by
      by_cases h0 : b = 0
      · subst h0
        have ha' : a = 1 := by linarith [hab]
        subst ha'
        simpa using hμ
      by_cases h1 : b = 1
      · subst h1
        have ha' : a = 0 := by linarith [hab]
        subst ha'
        simpa using hv
      have hb0 : 0 < b := lt_of_le_of_ne hb (Ne.symm h0)
      have hb1 : b < 1 := lt_of_le_of_ne (by linarith : b ≤ 1) h1
      have ha' : a = 1 - b := by linarith
      have hseg' := hseg x hx y hy b hb0 hb1
      have hseg'' :
          f (a • x + b • y) ≤
            ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y := by
        simpa [ha', smul_eq_mul] using hseg'
      have hnonneg1 : (0 : EReal) ≤ ((1 - b : Real) : EReal) :=
        (EReal.coe_nonneg).2 (by linarith [ha, hb, hab])
      have hnonneg2 : (0 : EReal) ≤ ((b : Real) : EReal) :=
        (EReal.coe_nonneg).2 hb
      have hmul1 :
          ((1 - b : Real) : EReal) * f x ≤ ((1 - b : Real) : EReal) * μ := by
        exact mul_le_mul_of_nonneg_left hμ hnonneg1
      have hmul2 :
          ((b : Real) : EReal) * f y ≤ ((b : Real) : EReal) * v := by
        exact mul_le_mul_of_nonneg_left hv hnonneg2
      have hmul := add_le_add hmul1 hmul2
      have hle' :
          f (a • x + b • y) ≤ ((1 - b : Real) : EReal) * μ + ((b : Real) : EReal) * v :=
        hseg''.trans hmul
      have hcoeff :
          ((1 - b : Real) : EReal) * μ + ((b : Real) : EReal) * v =
            ((a * μ + b * v : Real) : EReal) := by
        calc
          ((1 - b : Real) : EReal) * μ + ((b : Real) : EReal) * v =
              ((a : Real) : EReal) * μ + ((b : Real) : EReal) * v := by
                simp [ha']
          _ = ((a * μ + b * v : Real) : EReal) := by
                calc
                  ((a : Real) : EReal) * μ + ((b : Real) : EReal) * v =
                      ((a * μ : Real) : EReal) + ((b * v : Real) : EReal) := by
                        simp [EReal.coe_mul]
                  _ = ((a * μ + b * v : Real) : EReal) := by
                        simp [EReal.coe_add]
      calc
        f (a • x + b • y) ≤ ((1 - b : Real) : EReal) * μ + ((b : Real) : EReal) * v := hle'
        _ = ((a * μ + b * v : Real) : EReal) := hcoeff
    exact ⟨hmemC, hle⟩

/-- Choose a real bound between an `EReal` value and a real upper bound. -/
lemma ereal_exists_real_between_of_lt {u : EReal} {α : Real} (h : u < (α : EReal)) :
    ∃ μ : Real, u ≤ (μ : EReal) ∧ μ < α := by
  rcases (EReal.lt_iff_exists_real_btwn).1 h with ⟨μ, hμ, hμ'⟩
  refine ⟨μ, le_of_lt hμ, ?_⟩
  exact (EReal.coe_lt_coe_iff).1 hμ'

/-- Strict inequality for convex combinations of real bounds in `EReal`. -/
lemma ereal_convex_combo_lt_of_lt {μ α v β t : Real} (hμ : μ < α) (hv : v < β)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ((1 - t : Real) : EReal) * (μ : EReal) + ((t : Real) : EReal) * (v : EReal) <
      ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
  have h1 : (1 - t) * μ < (1 - t) * α := by
    have ht1' : 0 < 1 - t := sub_pos.mpr ht1
    exact mul_lt_mul_of_pos_left hμ ht1'
  have h2 : t * v < t * β := by
    exact mul_lt_mul_of_pos_left hv ht0
  have h : (1 - t) * μ + t * v < (1 - t) * α + t * β := by
    exact add_lt_add h1 h2
  have h' :
      (((1 - t) * μ + t * v : Real) : EReal) <
        (((1 - t) * α + t * β : Real) : EReal) :=
    (EReal.coe_lt_coe_iff).2 h
  simpa [EReal.coe_mul, EReal.coe_add] using h'

/-- Strict segment bounds yield a non-strict bound with real upper bounds. -/
lemma segment_inequality_le_of_strict {n : Nat} {f : (Fin n → Real) → EReal}
    (hstrict : ∀ x y : (Fin n → Real), ∀ α β : Real, ∀ t : Real,
        f x < (α : EReal) → f y < (β : EReal) → 0 < t → t < 1 →
          f ((1 - t) • x + t • y) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal)) :
    ∀ x y : (Fin n → Real), ∀ μ v t : Real,
      f x ≤ (μ : EReal) → f y ≤ (v : EReal) → 0 < t → t < 1 →
        f ((1 - t) • x + t • y) ≤
          (((1 - t) * μ + t * v : Real) : EReal) := by
  intro x y μ v t hμ hv ht0 ht1
  refine (EReal.le_of_forall_lt_iff_le).1 ?_
  intro z hz
  let w : Real := (1 - t) * μ + t * v
  have hz' : w < z := by
    have hz'' : ((w : Real) : EReal) < (z : EReal) := by
      simpa [w] using hz
    exact (EReal.coe_lt_coe_iff).1 hz''
  let ε : Real := z - w
  have hε : 0 < ε := sub_pos.mpr hz'
  have hμlt : f x < ((μ + ε : Real) : EReal) := by
    have hμlt' : (μ : EReal) < ((μ + ε : Real) : EReal) := by
      have : μ < μ + ε := by linarith [hε]
      exact (EReal.coe_lt_coe_iff).2 this
    exact lt_of_le_of_lt hμ hμlt'
  have hvlt : f y < ((v + ε : Real) : EReal) := by
    have hvlt' : (v : EReal) < ((v + ε : Real) : EReal) := by
      have : v < v + ε := by linarith [hε]
      exact (EReal.coe_lt_coe_iff).2 this
    exact lt_of_le_of_lt hv hvlt'
  have hstrict' :=
    hstrict x y (μ + ε) (v + ε) t hμlt hvlt ht0 ht1
  have hcoeff : (1 - t) * (μ + ε) + t * (v + ε) = z := by
    dsimp [ε, w]
    ring
  have hstrict'' :
      f ((1 - t) • x + t • y) < (z : EReal) := by
    have hstrict''' :
        f ((1 - t) • x + t • y) <
          (((1 - t) * (μ + ε) + t * (v + ε) : Real) : EReal) := by
      simpa [EReal.coe_add, EReal.coe_mul] using hstrict'
    simpa [hcoeff] using hstrict'''
  exact le_of_lt hstrict''

/-- Theorem 4.2: Let `f` be a function from `ℝ^n` to `[-∞, +∞]`. Then `f` is convex
iff `f ((1 - λ) • x + λ • y) < (1 - λ) * α + λ * β` for `0 < λ < 1`,
whenever `f x < α` and `f y < β`. -/
theorem convexFunctionOn_univ_iff_strict_inequality {n : Nat}
    {f : (Fin n -> Real) → EReal} :
    ConvexFunctionOn (Set.univ) f ↔
      ∀ x y : (Fin n → Real), ∀ α β : Real, ∀ t : Real,
        f x < (α : EReal) → f y < (β : EReal) →
        0 < t → t < 1 →
          f ((1 - t) • x + t • y) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
  constructor
  · intro hconv x y α β t hfx hfy ht0 ht1
    rcases ereal_exists_real_between_of_lt hfx with ⟨μ, hμ, hμ_lt⟩
    rcases ereal_exists_real_between_of_lt hfy with ⟨v, hv, hv_lt⟩
    have hconv' : Convex ℝ (epigraph Set.univ f) := by
      simpa [ConvexFunctionOn] using hconv
    have ht0' : 0 ≤ t := le_of_lt ht0
    have ht1' : t ≤ 1 := le_of_lt ht1
    have hle :=
      epigraph_combo_ineq_aux (S := Set.univ) (f := f) (x := x) (y := y)
        (μ := μ) (v := v) hconv' (by simp) (by simp) hμ hv ht0' ht1'
    have hle' :
        f ((1 - t) • x + t • y) ≤
          ((1 - t : Real) : EReal) * (μ : EReal) + ((t : Real) : EReal) * (v : EReal) := by
      simpa [EReal.coe_mul, EReal.coe_add] using hle
    have hlt :=
      ereal_convex_combo_lt_of_lt (μ := μ) (α := α) (v := v) (β := β) hμ_lt hv_lt ht0 ht1
    exact lt_of_le_of_lt hle' hlt
  · intro hstrict
    unfold ConvexFunctionOn
    intro p hp q hq a b ha hb hab
    rcases p with ⟨x, μ⟩
    rcases q with ⟨y, v⟩
    have hμ : f x ≤ (μ : EReal) := hp.2
    have hv : f y ≤ (v : EReal) := hq.2
    have hle :
        f (a • x + b • y) ≤ ((a * μ + b * v : Real) : EReal) := by
      by_cases h0 : b = 0
      · subst h0
        have ha' : a = 1 := by linarith [hab]
        subst ha'
        simpa using hμ
      by_cases h1 : b = 1
      · subst h1
        have ha' : a = 0 := by linarith [hab]
        subst ha'
        simpa using hv
      have hb0 : 0 < b := lt_of_le_of_ne hb (Ne.symm h0)
      have hb1 : b < 1 := lt_of_le_of_ne (by linarith : b ≤ 1) h1
      have ha' : a = 1 - b := by linarith
      have hseg :=
        segment_inequality_le_of_strict (f := f) hstrict x y μ v b hμ hv hb0 hb1
      simpa [ha', smul_eq_mul] using hseg
    have hmem : (a • x + b • y) ∈ (Set.univ : Set (Fin n → Real)) := by
      simp
    exact ⟨hmem, hle⟩

/-- Distribute a finite nonnegative scalar over a finite `EReal` sum. -/
lemma EReal.mul_sum_of_nonneg_of_ne_top {α : Type*} {s : Finset α} {a : EReal}
    (ha : 0 ≤ a) (ha_top : a ≠ ⊤) (f : α → EReal) :
    a * (Finset.sum s f) = Finset.sum s (fun i => a * f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi hs
    simp [hi, hs, EReal.left_distrib_of_nonneg_of_ne_top ha ha_top]

/-- If nonnegative weights sum to one and the head weight is one, all tail weights vanish. -/
lemma tail_weights_zero_of_head_eq_one {m : Nat} {w : Fin (m + 1) → Real}
    (hw : ∀ i, 0 ≤ w i) (hsum : (∑ i : Fin (m + 1), w i) = 1) (h0 : w 0 = 1) :
    ∀ i : Fin m, w (Fin.succ i) = 0 := by
  classical
  have hsum' : (∑ i : Fin m, w (Fin.succ i)) = 0 := by
    have hsum'' : w 0 + ∑ i : Fin m, w (Fin.succ i) = 1 := by
      simpa [Fin.sum_univ_succ] using hsum
    linarith [h0, hsum'']
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ w (Fin.succ i) := by
    intro i hi
    exact hw _
  have hzero :
      ∀ i ∈ (Finset.univ : Finset (Fin m)), w (Fin.succ i) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 (by simpa using hsum')
  intro i
  simpa using hzero i (by simp)

/-- Jensen inequality from convexity on the whole space. -/
lemma jensen_inequality_of_convexFunctionOn_univ {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (Set.univ) f) (hnotbot : ∀ x, f x ≠ ⊥) :
    ∀ m : Nat, ∀ w : Fin m → Real, ∀ x : Fin m → (Fin n → Real),
      (∀ i, 0 ≤ w i) → (Finset.univ.sum (fun i => w i) = 1) →
        f (Finset.univ.sum (fun i => w i • x i)) ≤
          Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i)) := by
  classical
  intro m
  induction m with
  | zero =>
      intro w x hw hsum
      simp at hsum
  | succ m ih =>
      intro w x hw hsum
      let t : Real := w 0
      have ht : t = w 0 := rfl
      have ht0 : 0 ≤ t := by simpa [t] using hw 0
      have hsum_succ : t + ∑ i : Fin m, w (Fin.succ i) = 1 := by
        simpa [t, Fin.sum_univ_succ] using hsum
      by_cases ht_zero : t = 0
      · have hsum_tail : (∑ i : Fin m, w (Fin.succ i)) = 1 := by
          linarith [hsum_succ, ht_zero]
        have hw' : ∀ i : Fin m, 0 ≤ w (Fin.succ i) := by
          intro i; exact hw _
        have hih :=
          ih (w := fun i => w (Fin.succ i)) (x := fun i => x (Fin.succ i)) hw' hsum_tail
        simpa [t, ht_zero, Fin.sum_univ_succ] using hih
      · by_cases ht_one : t = 1
        · have h0 : w 0 = 1 := by simpa [t] using ht_one
          have htail_zero :
              ∀ i : Fin m, w (Fin.succ i) = 0 :=
            tail_weights_zero_of_head_eq_one (w := w) hw hsum h0
          have hsum_x :
              (∑ i : Fin (m + 1), w i • x i) = x 0 := by
            simp [Fin.sum_univ_succ, h0, htail_zero]
          have hsum_f :
              (∑ i : Fin (m + 1), ((w i : Real) : EReal) * f (x i)) = f (x 0) := by
            simp [Fin.sum_univ_succ, h0, htail_zero]
          simp [hsum_x, hsum_f]
        · have htail_nonneg : 0 ≤ ∑ i : Fin m, w (Fin.succ i) := by
            refine Finset.sum_nonneg ?_
            intro i hi
            exact hw _
          have ht_le1 : t ≤ 1 := by
            linarith [hsum_succ, htail_nonneg]
          have ht_pos : 0 < t := by
            exact lt_of_le_of_ne ht0 (Ne.symm ht_zero)
          have ht_lt1 : t < 1 := by
            exact lt_of_le_of_ne ht_le1 ht_one
          have hne : (1 - t) ≠ 0 := by
            linarith [ht_lt1]
          have ht1_pos : 0 < 1 - t := sub_pos.mpr ht_lt1
          let w' : Fin m → Real := fun i => w (Fin.succ i) / (1 - t)
          let x' : Fin m → (Fin n → Real) := fun i => x (Fin.succ i)
          have hsum_tail : (∑ i : Fin m, w (Fin.succ i)) = 1 - t := by
            linarith [hsum_succ]
          have hsum_w' : (∑ i : Fin m, w' i) = 1 := by
            have hsum_w' :
                (∑ i : Fin m, w' i) =
                  (∑ i : Fin m, w (Fin.succ i)) / (1 - t) := by
              simpa [w'] using
                (Finset.sum_div (s := Finset.univ)
                    (f := fun i : Fin m => w (Fin.succ i)) (a := 1 - t)).symm
            calc
              (∑ i : Fin m, w' i) =
                  (∑ i : Fin m, w (Fin.succ i)) / (1 - t) := hsum_w'
              _ = (1 - t) / (1 - t) := by simp [hsum_tail]
              _ = (1 : Real) := by simp [hne]
          have hw' : ∀ i : Fin m, 0 ≤ w' i := by
            intro i
            exact div_nonneg (hw _) (le_of_lt ht1_pos)
          have hih := ih (w := w') (x := x') hw' hsum_w'
          have hcoeff : ∀ i : Fin m, w (Fin.succ i) = (1 - t) * w' i := by
            intro i
            calc
              w (Fin.succ i) = (1 - t) * (w (Fin.succ i) / (1 - t)) := by
                field_simp [hne]
              _ = (1 - t) * w' i := by rfl
          have hsum_x :
              (∑ i : Fin (m + 1), w i • x i) =
                (1 - t) • (∑ i : Fin m, w' i • x' i) + t • x 0 := by
            have htail :
                (∑ i : Fin m, w (Fin.succ i) • x (Fin.succ i)) =
                  (1 - t) • (∑ i : Fin m, w' i • x' i) := by
              calc
                (∑ i : Fin m, w (Fin.succ i) • x (Fin.succ i)) =
                    ∑ i : Fin m, (1 - t) • (w' i • x' i) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      simp [x', hcoeff i, smul_smul]
                _ = (1 - t) • (∑ i : Fin m, w' i • x' i) := by
                      simpa using
                        (Finset.smul_sum (s := Finset.univ)
                            (f := fun i : Fin m => w' i • x' i) (r := 1 - t)).symm
            calc
              (∑ i : Fin (m + 1), w i • x i) =
                  w 0 • x 0 + ∑ i : Fin m, w (Fin.succ i) • x (Fin.succ i) := by
                    simp [Fin.sum_univ_succ]
              _ = t • x 0 + (1 - t) • (∑ i : Fin m, w' i • x' i) := by
                    rw [← ht, htail]
              _ = (1 - t) • (∑ i : Fin m, w' i • x' i) + t • x 0 := by
                    ac_rfl
          have hsum_f :
              (∑ i : Fin (m + 1), ((w i : Real) : EReal) * f (x i)) =
                ((1 - t : Real) : EReal) *
                    (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) +
                  ((t : Real) : EReal) * f (x 0) := by
            have hmul :
                ((1 - t : Real) : EReal) *
                    (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) =
                  ∑ i : Fin m,
                    ((1 - t : Real) : EReal) * (((w' i : Real) : EReal) * f (x' i)) := by
              have hnonneg : (0 : EReal) ≤ ((1 - t : Real) : EReal) := by
                exact (EReal.coe_nonneg.mpr (sub_nonneg.mpr ht_le1))
              exact
                EReal.mul_sum_of_nonneg_of_ne_top (s := Finset.univ)
                  (a := ((1 - t : Real) : EReal)) hnonneg (EReal.coe_ne_top _) _
            have htail :
                (∑ i : Fin m, ((w (Fin.succ i) : Real) : EReal) * f (x (Fin.succ i))) =
                  ((1 - t : Real) : EReal) *
                    (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) := by
              calc
                (∑ i : Fin m, ((w (Fin.succ i) : Real) : EReal) * f (x (Fin.succ i))) =
                    ∑ i : Fin m,
                      ((1 - t : Real) : EReal) * (((w' i : Real) : EReal) * f (x' i)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      simp [x', hcoeff i, EReal.coe_mul, mul_assoc]
                _ =
                    ((1 - t : Real) : EReal) *
                      (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) := by
                      simpa using hmul.symm
            calc
              (∑ i : Fin (m + 1), ((w i : Real) : EReal) * f (x i)) =
                  ((w 0 : Real) : EReal) * f (x 0) +
                    ∑ i : Fin m, ((w (Fin.succ i) : Real) : EReal) * f (x (Fin.succ i)) := by
                      simp [Fin.sum_univ_succ]
              _ = ((t : Real) : EReal) * f (x 0) +
                    ((1 - t : Real) : EReal) *
                      (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) := by
                      rw [← ht, htail]
              _ =
                    ((1 - t : Real) : EReal) *
                      (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) +
                      ((t : Real) : EReal) * f (x 0) := by
                      simp [add_comm]
          have hsegment :=
            (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
                (hC := convex_univ) (hnotbot := by
                  intro x hx; simpa using hnotbot x)).1 hf
          have hmul :
              ((1 - t : Real) : EReal) * f (∑ i : Fin m, w' i • x' i) ≤
                ((1 - t : Real) : EReal) *
                  (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) := by
            have hnonneg : (0 : EReal) ≤ ((1 - t : Real) : EReal) := by
              exact (EReal.coe_nonneg.mpr (sub_nonneg.mpr ht_le1))
            exact mul_le_mul_of_nonneg_left hih hnonneg
          calc
            f (∑ i : Fin (m + 1), w i • x i) =
                f ((1 - t) • (∑ i : Fin m, w' i • x' i) + t • x 0) := by
                  rw [hsum_x]
            _ ≤
                ((1 - t : Real) : EReal) * f (∑ i : Fin m, w' i • x' i) +
                  ((t : Real) : EReal) * f (x 0) := by
                  simpa using
                    hsegment (∑ i : Fin m, w' i • x' i) (by simp) (x 0) (by simp) t ht_pos ht_lt1
            _ ≤
                ((1 - t : Real) : EReal) *
                  (∑ i : Fin m, ((w' i : Real) : EReal) * f (x' i)) +
                  ((t : Real) : EReal) * f (x 0) := by
                  exact add_le_add hmul le_rfl
            _ = ∑ i : Fin (m + 1), ((w i : Real) : EReal) * f (x i) := by
                  rw [← hsum_f]

/-- Jensen inequality for `m = 2` yields the segment inequality. -/
lemma segment_inequality_of_jensen {n : Nat} {f : (Fin n → Real) → EReal}
    (hjensen :
      ∀ m : Nat, ∀ w : Fin m → Real, ∀ x : Fin m → (Fin n → Real),
        (∀ i, 0 ≤ w i) → (Finset.univ.sum (fun i => w i) = 1) →
          f (Finset.univ.sum (fun i => w i • x i)) ≤
            Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i))) :
    ∀ x y : (Fin n → Real), ∀ t : Real, 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤
        ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
  classical
  intro x y t ht0 ht1
  let w : Fin 2 → Real := fun i => if i = 0 then 1 - t else t
  let z : Fin 2 → (Fin n → Real) := fun i => if i = 0 then x else y
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i <;> simp [w, ht0.le, sub_nonneg.mpr ht1.le]
  have hsum : (∑ i : Fin 2, w i) = 1 := by
    simp [w, Fin.sum_univ_two]
  have h := hjensen 2 w z hw (by simpa using hsum)
  simpa [w, z, Fin.sum_univ_two] using h

/-- Theorem 4.3 (Jensen's Inequality): Let `f` be a function from `R^n` to
`(-∞, +∞]`. Then `f` is convex iff
`f (lambda_1 x_1 + ... + lambda_m x_m) ≤ lambda_1 f x_1 + ... + lambda_m f x_m`
whenever `lambda_1, ..., lambda_m ≥ 0` and `lambda_1 + ... + lambda_m = 1`. -/
theorem convexFunctionOn_univ_iff_jensen_inequality {n : Nat}
    (f : (Fin n → Real) → EReal) (hnotbot : ∀ x, f x ≠ ⊥) :
    ConvexFunctionOn (Set.univ) f ↔
      ∀ m : Nat, ∀ w : Fin m → Real, ∀ x : Fin m → (Fin n → Real),
        (∀ i, 0 ≤ w i) → (Finset.univ.sum (fun i => w i) = 1) →
          f (Finset.univ.sum (fun i => w i • x i)) ≤
            Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i)) := by
  constructor
  · intro hf
    exact jensen_inequality_of_convexFunctionOn_univ (f := f) hf hnotbot
  · intro hjensen
    refine (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
      (hC := convex_univ) (hnotbot := by intro x hx; simpa using hnotbot x)).2 ?_
    intro x _ y _ t ht0 ht1
    simpa using (segment_inequality_of_jensen (f := f) hjensen x y t ht0 ht1)

/-- Definition 4.3: An affine function on `S` is a function which is finite,
convex, and concave. -/
def AffineFunctionOn {n : Nat} (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    Prop :=
  (∀ x ∈ S, f x ≠ ⊥ ∧ f x ≠ ⊤) ∧
    ConvexFunctionOn S f ∧
    Convex ℝ {p : Prod (Fin n -> Real) Real | p.1 ∈ S ∧ ((p.2 : EReal) <= f p.1)}

/-- On an open interval, the derivative within equals the usual derivative. -/
lemma derivWithin_Ioo_eq_deriv {g : ℝ → ℝ} {α β x : ℝ} (hx : x ∈ Set.Ioo α β) :
    derivWithin g (Set.Ioo α β) x = deriv g x := by
  simpa using (derivWithin_of_isOpen (f := g) (s := Set.Ioo α β) isOpen_Ioo hx)

/-- Nonnegative second derivative implies convexity on an open interval. -/
lemma convexOn_Ioo_of_second_deriv_nonneg {f : ℝ → ℝ} {α β : ℝ}
    (hcont : ContDiffOn ℝ 2 f (Set.Ioo α β))
    (hderiv2 : ∀ x ∈ Set.Ioo α β, 0 ≤ deriv (deriv f) x) :
    ConvexOn ℝ (Set.Ioo α β) f := by
  have hcont_deriv : ContinuousOn (deriv f) (Set.Ioo α β) :=
    hcont.continuousOn_deriv_of_isOpen (hs := isOpen_Ioo) (hn := by decide)
  have hdiff_deriv : DifferentiableOn ℝ (deriv f) (Set.Ioo α β) := by
    have hcont' : ContDiffOn ℝ 1 (deriv f) (Set.Ioo α β) :=
      hcont.deriv_of_isOpen (m := 1) (hs := isOpen_Ioo) (hmn := by decide)
    exact hcont'.differentiableOn_one
  have hmono : MonotoneOn (deriv f) (Set.Ioo α β) := by
    refine monotoneOn_of_deriv_nonneg (D := Set.Ioo α β) (hD := convex_Ioo α β)
      (f := deriv f) hcont_deriv ?_ ?_
    · simpa [interior_Ioo] using hdiff_deriv
    · simpa [interior_Ioo] using hderiv2
  have hcont_f : ContinuousOn f (Set.Ioo α β) := hcont.continuousOn
  have hdiff_f : DifferentiableOn ℝ f (Set.Ioo α β) :=
    hcont.differentiableOn (by decide)
  refine (MonotoneOn.convexOn_of_deriv (D := Set.Ioo α β) (hD := convex_Ioo α β)
    (f := f) hcont_f ?_ ?_)
  · simpa [interior_Ioo] using hdiff_f
  · simpa [interior_Ioo] using hmono

/-- Convexity on an open interval forces a nonnegative second derivative. -/
lemma second_deriv_nonneg_of_convexOn_Ioo {f : ℝ → ℝ} {α β : ℝ}
    (hcont : ContDiffOn ℝ 2 f (Set.Ioo α β)) (hconv : ConvexOn ℝ (Set.Ioo α β) f) :
    ∀ x ∈ Set.Ioo α β, 0 ≤ deriv (deriv f) x := by
  intro x hx
  have hdiff_f : DifferentiableOn ℝ f (Set.Ioo α β) :=
    hcont.differentiableOn (by decide)
  have hdiff_at : ∀ y ∈ Set.Ioo α β, DifferentiableAt ℝ f y := by
    intro y hy
    exact hdiff_f.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hmono : MonotoneOn (deriv f) (Set.Ioo α β) :=
    hconv.monotoneOn_deriv hdiff_at
  have hnonneg : 0 ≤ derivWithin (deriv f) (Set.Ioo α β) x :=
    (MonotoneOn.derivWithin_nonneg (g := deriv f) (s := Set.Ioo α β) (x := x) hmono)
  simpa [derivWithin_Ioo_eq_deriv (g := deriv f) (α := α) (β := β) (x := x) hx] using hnonneg

/-- Theorem 4.4: Let `f` be a twice continuously differentiable real-valued function on an
open interval `(α, β)`. Then `f` is convex iff its second derivative `f''` is
nonnegative throughout `(α, β)`. -/
theorem convexOn_interval_iff_second_deriv_nonneg {f : ℝ → ℝ} {α β : ℝ}
    (hcont : ContDiffOn ℝ 2 f (Set.Ioo α β)) :
    ConvexOn ℝ (Set.Ioo α β) f ↔
      ∀ x ∈ Set.Ioo α β, 0 ≤ deriv (deriv f) x := by
  constructor
  · intro hconv
    exact second_deriv_nonneg_of_convexOn_Ioo (hcont := hcont) hconv
  · intro hderiv2
    exact convexOn_Ioo_of_second_deriv_nonneg (hcont := hcont) hderiv2

/-- Restricting a `C^2` function to a line is `C^2` on any interval contained in `C`. -/
lemma contDiffOn_line_restrict {n : Nat} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiffOn ℝ 2 f C) {y z : Fin n → ℝ} {a b : ℝ}
    (hmem : ∀ t ∈ Set.Ioo a b, y + t • z ∈ C) :
    ContDiffOn ℝ 2 (fun t : ℝ => f (y + t • z)) (Set.Ioo a b) := by
  have hid : ContDiffOn ℝ 2 (fun t : ℝ => t) (Set.Ioo a b) := by
    simpa using (contDiffOn_id : ContDiffOn ℝ 2 (id : ℝ → ℝ) (Set.Ioo a b))
  have hconsty : ContDiffOn ℝ 2 (fun _ : ℝ => y) (Set.Ioo a b) := contDiffOn_const
  have hconstz : ContDiffOn ℝ 2 (fun _ : ℝ => z) (Set.Ioo a b) := contDiffOn_const
  have hsmul : ContDiffOn ℝ 2 (fun t : ℝ => t • z) (Set.Ioo a b) := hid.smul hconstz
  have hline : ContDiffOn ℝ 2 (fun t : ℝ => y + t • z) (Set.Ioo a b) := hconsty.add hsmul
  have hmaps : Set.MapsTo (fun t : ℝ => y + t • z) (Set.Ioo a b) C := by
    intro t ht
    exact hmem t ht
  simpa [Function.comp] using hcont.comp hline hmaps

/-- An open set contains a small open interval of a line through any point. -/
lemma exists_line_interval_subset {n : Nat} {C : Set (Fin n → ℝ)} (hopen : IsOpen C)
    {x : Fin n → ℝ} (hx : x ∈ C) (z : Fin n → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioo (-ε) ε, x + t • z ∈ C := by
  have hcont : Continuous fun t : ℝ => x + t • z := by
    simpa using (continuous_const.add (continuous_id.smul continuous_const))
  have hopen_pre : IsOpen ((fun t : ℝ => x + t • z) ⁻¹' C) := hopen.preimage hcont
  have hmem : (0 : ℝ) ∈ (fun t : ℝ => x + t • z) ⁻¹' C := by
    simpa using hx
  have hnhds : (fun t : ℝ => x + t • z) ⁻¹' C ∈ 𝓝 (0 : ℝ) :=
    hopen_pre.mem_nhds hmem
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, εpos, hball⟩
  refine ⟨ε, εpos, ?_⟩
  intro t ht
  have ht' : t ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Real.ball_eq_Ioo] using ht
  exact hball ht'

/-- Convexity of a function on `C` implies convexity of its restriction
to any line segment in `C`. -/
lemma convexOn_line_restrict {n : Nat} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hconv : ConvexOn ℝ C f) {y z : Fin n → ℝ} {a b : ℝ}
    (hmem : ∀ t ∈ Set.Ioo a b, y + t • z ∈ C) :
    ConvexOn ℝ (Set.Ioo a b) (fun t : ℝ => f (y + t • z)) := by
  refine ⟨convex_Ioo a b, ?_⟩
  intro t ht u hu α β hα hβ hsum
  have htC : y + t • z ∈ C := hmem t ht
  have huC : y + u • z ∈ C := hmem u hu
  have hineq := hconv.2 htC huC hα hβ hsum
  have hcombo :
      α • (y + t • z) + β • (y + u • z) = y + (α * t + β * u) • z := by
    ext i
    calc
      (α • (y + t • z) + β • (y + u • z)) i =
          α * (y i + t * z i) + β * (y i + u * z i) := by
            simp [smul_add, smul_smul, mul_add, mul_assoc]
      _ = (α + β) * y i + (α * t + β * u) * z i := by ring
      _ = y i + (α * t + β * u) * z i := by simp [hsum]
      _ = (y + (α • t + β • u) • z) i := by
            simp [smul_eq_mul]
  have hineq' := hineq
  rw [hcombo] at hineq'
  simpa [smul_eq_mul] using hineq'

/-- The Hessian matrix defined by iterated coordinate derivatives. -/
noncomputable def hessianMatrix {n : Nat} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      f (x + s • (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) +
        t • (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)))) 0) 0

/-- Over `ℝ`, the quadratic form in `Matrix.PosSemidef` uses no conjugation. -/
lemma posSemidef_iff_real {n : Nat} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.PosSemidef M ↔ M.IsHermitian ∧ ∀ x, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := M))

/-- Derivative along a line equals the Fréchet derivative applied to the direction. -/
lemma line_deriv_eq_fderiv {n : Nat} {f : (Fin n → ℝ) → ℝ} {y z : Fin n → ℝ} {t : ℝ}
    (hderiv : DifferentiableAt ℝ f (y + t • z)) :
    deriv (fun s : ℝ => f (y + s • z)) t = (fderiv ℝ f (y + t • z)) z := by
  have hline : HasFDerivAt (fun s : ℝ => y + s • z)
      ((1 : ℝ →L[ℝ] ℝ).smulRight z) t := by
    have hsmul : HasFDerivAt (fun s : ℝ => s • z) ((1 : ℝ →L[ℝ] ℝ).smulRight z) t := by
      simpa using ((1 : ℝ →L[ℝ] ℝ).smulRight z).hasFDerivAt
    simpa using hsmul.const_add y
  have hcomp :
      HasFDerivAt (fun s : ℝ => f (y + s • z))
        ((fderiv ℝ f (y + t • z)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight z)) t :=
    (hderiv.hasFDerivAt.comp t hline)
  have hderiv' :
      HasDerivAt (fun s : ℝ => f (y + s • z))
        (((fderiv ℝ f (y + t • z)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight z)) 1) t :=
    hcomp.hasDerivAt
  have hderiv'' := hderiv'.deriv
  simpa using hderiv''

/-- Coordinate second derivatives match the second Fréchet derivative on basis vectors. -/
lemma hessian_entry_eq_fderiv {n : Nat} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hcont : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    hessianMatrix f x i j =
      (fderiv ℝ (fderiv ℝ f) x)
        (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
        (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) := by
  classical
  let ei : Fin n → ℝ := Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)
  let ej : Fin n → ℝ := Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)
  let g : ℝ → ℝ := fun t => deriv (fun s : ℝ => f (x + s • ei + t • ej)) 0
  let h : ℝ → ℝ := fun t => (fderiv ℝ f (x + t • ej)) ei
  rcases (hcont.contDiffOn' (m := (2 : ℕ)) (hm := le_rfl) (h' := by simp)) with
    ⟨u, hu_open, hx_u, hcont_u⟩
  have hcont_u' : ContDiffOn ℝ 2 f u := by
    simpa using hcont_u
  have hmem : {t : ℝ | x + t • ej ∈ u} ∈ 𝓝 (0 : ℝ) := by
    have hcont_line : Continuous fun t : ℝ => x + t • ej := by
      simpa using (continuous_const.add (continuous_id.smul continuous_const))
    have hopen_pre : IsOpen ((fun t : ℝ => x + t • ej) ⁻¹' u) :=
      hu_open.preimage hcont_line
    have h0 : (0 : ℝ) ∈ (fun t : ℝ => x + t • ej) ⁻¹' u := by
      simpa using hx_u
    exact hopen_pre.mem_nhds h0
  have hEq : g =ᶠ[𝓝 (0 : ℝ)] h := by
    refine Filter.mem_of_superset hmem ?_
    intro t ht
    have hcont_t : ContDiffAt ℝ 2 f (x + t • ej) :=
      hcont_u'.contDiffAt (hu_open.mem_nhds ht)
    have hdiff_t : DifferentiableAt ℝ f (x + t • ej) :=
      hcont_t.differentiableAt (by decide)
    have hline :=
      line_deriv_eq_fderiv (y := x + t • ej) (z := ei) (t := 0) (by simpa using hdiff_t)
    simpa [g, h, add_comm, add_left_comm, add_assoc] using hline
  have hderiv_eq : deriv g 0 = deriv h 0 := (Filter.EventuallyEq.deriv_eq hEq)
  have hcont_fderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hcont.fderiv_right (m := 1) (hmn := by decide)
  have hdiff_fderiv : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hcont_fderiv.differentiableAt (by decide)
  have hdiff_const : DifferentiableAt ℝ (fun _ : Fin n → ℝ => ei) x := by
    simp
  have hdiff_apply : DifferentiableAt ℝ (fun y : Fin n → ℝ => (fderiv ℝ f y) ei) x :=
    hdiff_fderiv.clm_apply hdiff_const
  have hderiv_h' :
      deriv h 0 = (fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ f y) ei) x) ej := by
    simpa [h] using
      (line_deriv_eq_fderiv (y := x) (z := ej) (t := 0)
        (hderiv := by simpa using hdiff_apply))
  have hcalc :
      fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ f y) ei) x =
        (fderiv ℝ f x).comp (fderiv ℝ (fun _ : Fin n → ℝ => ei) x) +
          (fderiv ℝ (fderiv ℝ f) x).flip ei := by
    simpa using
      (fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : Fin n → ℝ => ei)
        (hc := hdiff_fderiv) (hu := hdiff_const))
  have hderiv_h :
      deriv h 0 = (fderiv ℝ (fderiv ℝ f) x) ej ei := by
    calc
      deriv h 0 =
          (fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ f y) ei) x) ej := hderiv_h'
      _ =
          ((fderiv ℝ f x).comp (fderiv ℝ (fun _ : Fin n → ℝ => ei) x) +
            (fderiv ℝ (fderiv ℝ f) x).flip ei) ej := by
              simp [hcalc]
      _ = (fderiv ℝ (fderiv ℝ f) x) ej ei := by
            simp [ContinuousLinearMap.flip_apply, fderiv_const_apply]
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hcont.isSymmSndFDerivAt (hn := by simp)
  have hfinal :
      hessianMatrix f x i j = (fderiv ℝ (fderiv ℝ f) x) ei ej := by
    calc
      hessianMatrix f x i j = deriv g 0 := by
        simp [hessianMatrix, g, ei, ej, add_comm, add_left_comm]
      _ = deriv h 0 := hderiv_eq
      _ = (fderiv ℝ (fderiv ℝ f) x) ej ei := hderiv_h
      _ = (fderiv ℝ (fderiv ℝ f) x) ei ej := by
        simpa using hsymm ej ei
  simpa [ei, ej] using hfinal

/-- Second derivatives along lines are given by the Hessian quadratic form. -/
lemma line_second_deriv_eq_quadratic_form {n : Nat} {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hopen : IsOpen C) (hcont : ContDiffOn ℝ 2 f C)
    {y z : Fin n → ℝ} {t : ℝ} (ht : y + t • z ∈ C) :
    deriv (deriv (fun s : ℝ => f (y + s • z))) t =
      star z ⬝ᵥ (hessianMatrix f (y + t • z) *ᵥ z) := by
  classical
  have hcontx : ContDiffAt ℝ 2 f (y + t • z) := hcont.contDiffAt (hopen.mem_nhds ht)
  let g : ℝ → ℝ := fun s => deriv (fun r : ℝ => f (y + r • z)) s
  let h : ℝ → ℝ := fun s => (fderiv ℝ f (y + s • z)) z
  have hmem : {s : ℝ | y + s • z ∈ C} ∈ 𝓝 t := by
    have hcont_line : Continuous fun s : ℝ => y + s • z := by
      simpa using (continuous_const.add (continuous_id.smul continuous_const))
    have hopen_pre : IsOpen ((fun s : ℝ => y + s • z) ⁻¹' C) := hopen.preimage hcont_line
    have ht' : t ∈ (fun s : ℝ => y + s • z) ⁻¹' C := by
      simpa using ht
    exact hopen_pre.mem_nhds ht'
  have hEq : g =ᶠ[𝓝 t] h := by
    refine Filter.mem_of_superset hmem ?_
    intro s hs
    have hcont_s : ContDiffAt ℝ 2 f (y + s • z) := hcont.contDiffAt (hopen.mem_nhds hs)
    have hdiff_s : DifferentiableAt ℝ f (y + s • z) :=
      hcont_s.differentiableAt (by decide)
    simpa [g, h] using (line_deriv_eq_fderiv (y := y) (z := z) (t := s) hdiff_s)
  have hderiv_eq : deriv g t = deriv h t := (Filter.EventuallyEq.deriv_eq hEq)
  have hcont_fderiv : ContDiffAt ℝ 1 (fderiv ℝ f) (y + t • z) :=
    hcontx.fderiv_right (m := 1) (hmn := by decide)
  have hdiff_fderiv : DifferentiableAt ℝ (fderiv ℝ f) (y + t • z) :=
    hcont_fderiv.differentiableAt (by decide)
  have hdiff_const : DifferentiableAt ℝ (fun _ : Fin n → ℝ => z) (y + t • z) := by
    simp
  have hdiff_apply :
      DifferentiableAt ℝ (fun x : Fin n → ℝ => (fderiv ℝ f x) z) (y + t • z) :=
    hdiff_fderiv.clm_apply hdiff_const
  have hderiv_h' :
      deriv h t = (fderiv ℝ (fun x : Fin n → ℝ => (fderiv ℝ f x) z) (y + t • z)) z := by
    simpa [h] using
      (line_deriv_eq_fderiv (y := y) (z := z) (t := t) (hderiv := hdiff_apply))
  have hcalc :
      fderiv ℝ (fun x : Fin n → ℝ => (fderiv ℝ f x) z) (y + t • z) =
        (fderiv ℝ f (y + t • z)).comp (fderiv ℝ (fun _ : Fin n → ℝ => z) (y + t • z)) +
          (fderiv ℝ (fderiv ℝ f) (y + t • z)).flip z := by
    simpa using
      (fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : Fin n → ℝ => z)
        (hc := hdiff_fderiv) (hu := hdiff_const))
  have hderiv_h :
      deriv h t = (fderiv ℝ (fderiv ℝ f) (y + t • z)) z z := by
    calc
      deriv h t =
          (fderiv ℝ (fun x : Fin n → ℝ => (fderiv ℝ f x) z) (y + t • z)) z := hderiv_h'
      _ =
          ((fderiv ℝ f (y + t • z)).comp (fderiv ℝ (fun _ : Fin n → ℝ => z) (y + t • z)) +
            (fderiv ℝ (fderiv ℝ f) (y + t • z)).flip z) z := by
              simp [hcalc]
      _ = (fderiv ℝ (fderiv ℝ f) (y + t • z)) z z := by
            simp [ContinuousLinearMap.flip_apply, fderiv_const_apply]
  have hderiv_line :
      deriv (deriv (fun s : ℝ => f (y + s • z))) t =
        (fderiv ℝ (fderiv ℝ f) (y + t • z)) z z := by
    calc
      deriv (deriv (fun s : ℝ => f (y + s • z))) t = deriv g t := by
        rfl
      _ = deriv h t := hderiv_eq
      _ = (fderiv ℝ (fderiv ℝ f) (y + t • z)) z z := hderiv_h
  let B := fderiv ℝ (fderiv ℝ f) (y + t • z)
  have hentry :
      ∀ i j,
        B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
          (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) =
          hessianMatrix f (y + t • z) i j := by
    intro i j
    simpa [B] using
      (hessian_entry_eq_fderiv (hcont := hcontx) i j).symm
  have hz : z = ∑ i, Pi.single (M := fun _ : Fin n => ℝ) i (z i) := by
    simpa using (Finset.univ_sum_single z).symm
  have hsingle :
      ∀ i, Pi.single (M := fun _ : Fin n => ℝ) i (z i) =
        z i • Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ) := by
    intro i
    ext j
    by_cases hji : j = i
    · subst hji
      simp [Pi.single]
    · simp [Pi.single, hji]
  have hsum1 :
      B z = ∑ i, z i • B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) := by
    have hsum :=
      map_sum (g := (B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →L[ℝ] ℝ))
        (f := fun i => Pi.single (M := fun _ : Fin n => ℝ) i (z i))
        (s := Finset.univ)
    have hsum' :
        B z = ∑ i, B (Pi.single (M := fun _ : Fin n => ℝ) i (z i)) := by
      have hsum' := hsum
      rw [← hz] at hsum'
      exact hsum'
    calc
      B z = ∑ i, B (Pi.single (M := fun _ : Fin n => ℝ) i (z i)) := hsum'
      _ = ∑ i, z i • B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              B (Pi.single (M := fun _ : Fin n => ℝ) i (z i)) =
                  B (z i • Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) := by
                    simp [hsingle i]
              _ = z i • B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) := by
                    simp [map_smul]
  have hsum1z :
      B z z = (∑ i, z i • B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))) z := by
    simpa using congrArg (fun g' => g' z) hsum1
  have hsum2 :
      (∑ i, z i • B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))) z =
        ∑ i, z i * B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) z := by
    simp [Finset.sum_apply, smul_eq_mul]
  have hsum3 :
      ∀ i,
        B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) z =
          ∑ j, z j *
            B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
              (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) := by
    intro i
    have hsum :=
      map_sum
        (g := (B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) :
          (Fin n → ℝ) →ₗ[ℝ] ℝ))
        (f := fun j => Pi.single (M := fun _ : Fin n => ℝ) j (z j))
        (s := Finset.univ)
    have hsum' :
        B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) z =
          ∑ j, B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
            (Pi.single (M := fun _ : Fin n => ℝ) j (z j)) := by
      have hsum' := hsum
      rw [← hz] at hsum'
      exact hsum'
    calc
      B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) z =
          ∑ j, B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
            (Pi.single (M := fun _ : Fin n => ℝ) j (z j)) := hsum'
      _ = ∑ j, z j *
            B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
              (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            calc
              B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
                  (Pi.single (M := fun _ : Fin n => ℝ) j (z j)) =
                    B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
                      (z j • Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) := by
                        simp [hsingle j]
              _ = z j •
                    B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
                      (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) := by
                    simp [map_smul]
              _ = z j *
                    B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
                      (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) := by
                    simp [smul_eq_mul]
  have hsumB :
      B z z =
        ∑ i, ∑ j, z i *
          B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
            (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) * z j := by
    calc
      B z z = (∑ i, z i • B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))) z := hsum1z
      _ = ∑ i, z i * B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) z := hsum2
      _ = ∑ i, z i *
            (∑ j, z j *
              B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
                (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hsum3 i]
      _ = ∑ i, ∑ j, z i *
            B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
              (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) * z j := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [Finset.mul_sum, mul_comm, mul_left_comm]
  have hquad' :
      star z ⬝ᵥ (hessianMatrix f (y + t • z) *ᵥ z) =
        ∑ i, ∑ j, z i * hessianMatrix f (y + t • z) i j * z j := by
    have hstar : (star z : Fin n → ℝ) = z := by
      ext i
      simp
    calc
      star z ⬝ᵥ (hessianMatrix f (y + t • z) *ᵥ z) =
          Matrix.toBilin' (hessianMatrix f (y + t • z)) z z := by
            simpa [hstar] using
              (Matrix.toBilin'_apply' (M := hessianMatrix f (y + t • z)) (v := z) (w := z)).symm
      _ = ∑ i, ∑ j, z i * hessianMatrix f (y + t • z) i j * z j := by
            simpa using
              (Matrix.toBilin'_apply (M := hessianMatrix f (y + t • z)) (x := z) (y := z))
  have hquad :
      B z z = star z ⬝ᵥ (hessianMatrix f (y + t • z) *ᵥ z) := by
    calc
      B z z =
          ∑ i, ∑ j, z i *
            B (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
              (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)) * z j := hsumB
      _ = ∑ i, ∑ j, z i * hessianMatrix f (y + t • z) i j * z j := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hentry i j]
      _ = star z ⬝ᵥ (hessianMatrix f (y + t • z) *ᵥ z) := by
            simpa using hquad'.symm
  calc
    deriv (deriv (fun s : ℝ => f (y + s • z))) t =
        (fderiv ℝ (fderiv ℝ f) (y + t • z)) z z := hderiv_line
    _ = star z ⬝ᵥ (hessianMatrix f (y + t • z) *ᵥ z) := by
        simpa [B] using hquad

/-- The Hessian matrix is Hermitian at points of an open `C^2` set. -/
lemma hessian_symm {n : Nat} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hopen : IsOpen C) (hcont : ContDiffOn ℝ 2 f C) {x : Fin n → ℝ} (hx : x ∈ C) :
    (hessianMatrix f x).IsHermitian := by
  classical
  have hcontx : ContDiffAt ℝ 2 f x := hcont.contDiffAt (hopen.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hcontx.isSymmSndFDerivAt (hn := by simp)
  refine (Matrix.IsHermitian.ext_iff).2 ?_
  intro i j
  have hentry_ij := hessian_entry_eq_fderiv (hcont := hcontx) i j
  have hentry_ji := hessian_entry_eq_fderiv (hcont := hcontx) j i
  have hsymm' :=
    hsymm
      (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
      (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ))
  simpa [hentry_ij, hentry_ji] using hsymm'.symm

/-- Convexity implies positive semidefiniteness of the Hessian. -/
lemma hessian_posSemidef_of_convexOn {n : Nat} {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hopen : IsOpen C)
    (hcont : ContDiffOn ℝ 2 f C) (hconv : ConvexOn ℝ C f) :
    ∀ x ∈ C, Matrix.PosSemidef (hessianMatrix f x) := by
  intro x hx
  have hsymm : (hessianMatrix f x).IsHermitian :=
    hessian_symm (hopen := hopen) (hcont := hcont) hx
  refine (posSemidef_iff_real (M := hessianMatrix f x)).2 ?_
  refine ⟨hsymm, ?_⟩
  intro z
  rcases exists_line_interval_subset (hopen := hopen) (x := x) (z := z) hx with ⟨ε, εpos, hmem⟩
  have hcont_line :
      ContDiffOn ℝ 2 (fun t : ℝ => f (x + t • z)) (Set.Ioo (-ε) ε) :=
    contDiffOn_line_restrict (hcont := hcont) (y := x) (z := z) (a := -ε) (b := ε) hmem
  have hconv_line :
      ConvexOn ℝ (Set.Ioo (-ε) ε) (fun t : ℝ => f (x + t • z)) :=
    convexOn_line_restrict (hconv := hconv) (y := x) (z := z) (a := -ε) (b := ε) hmem
  have hderiv2 :
      ∀ t ∈ Set.Ioo (-ε) ε,
        0 ≤ deriv (deriv (fun s : ℝ => f (x + s • z))) t :=
    (convexOn_interval_iff_second_deriv_nonneg
      (f := fun t : ℝ => f (x + t • z)) (α := -ε) (β := ε) (hcont := hcont_line)).1
      hconv_line
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    exact ⟨by linarith, by linarith⟩
  have hnonneg : 0 ≤ deriv (deriv (fun s : ℝ => f (x + s • z))) 0 :=
    hderiv2 0 h0
  have hline_eq :
      deriv (deriv (fun s : ℝ => f (x + s • z))) 0 =
        star z ⬝ᵥ (hessianMatrix f x *ᵥ z) := by
    simpa using
      (line_second_deriv_eq_quadratic_form (hopen := hopen) (hcont := hcont)
        (y := x) (z := z) (t := 0) (ht := by simpa using hx))
  have hquad_nonneg : 0 ≤ star z ⬝ᵥ (hessianMatrix f x *ᵥ z) := by
    simpa [hline_eq] using hnonneg
  simpa using hquad_nonneg

/-- Positive semidefinite Hessian implies convexity. -/
lemma convexOn_of_hessian_posSemidef {n : Nat} {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hC : Convex ℝ C) (hopen : IsOpen C)
    (hcont : ContDiffOn ℝ 2 f C)
    (hpos : ∀ x ∈ C, Matrix.PosSemidef (hessianMatrix f x)) :
    ConvexOn ℝ C f := by
  refine ⟨hC, ?_⟩
  intro x hx y hy a b ha hb hab
  set z : Fin n → ℝ := y - x
  let g : ℝ → ℝ := fun t => f (x + t • z)
  have hmem_Icc : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • z ∈ C := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hmem' : (1 - t) • x + t • y ∈ C := by
      have hsum : (1 - t) + t = 1 := by linarith
      exact hC hx hy (by linarith) ht0 hsum
    have hcombo : x + t • z = (1 - t) • x + t • y := by
      ext i
      simp [z, sub_eq_add_neg]
      ring
    simpa [hcombo] using hmem'
  have hmem_Ioo : ∀ t ∈ Set.Ioo (0 : ℝ) 1, x + t • z ∈ C := by
    intro t ht
    exact hmem_Icc t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hcont_line : ContDiffOn ℝ 2 g (Set.Ioo 0 1) :=
    contDiffOn_line_restrict (hcont := hcont) (y := x) (z := z) (a := 0) (b := 1) hmem_Ioo
  have hcont_f : ContinuousOn f C := hcont.continuousOn
  have hcont_line_map : Continuous fun t : ℝ => x + t • z := by
    simpa using (continuous_const.add (continuous_id.smul continuous_const))
  have hcont_g : ContinuousOn g (Set.Icc 0 1) := by
    have hmaps : Set.MapsTo (fun t : ℝ => x + t • z) (Set.Icc 0 1) C := by
      intro t ht
      exact hmem_Icc t ht
    simpa [g] using hcont_f.comp hcont_line_map.continuousOn hmaps
  have hdiff_g : DifferentiableOn ℝ g (Set.Ioo 0 1) :=
    hcont_line.differentiableOn (by decide)
  have hcont_deriv : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 1) :=
    hcont_line.deriv_of_isOpen isOpen_Ioo (by decide)
  have hdiff_deriv : DifferentiableOn ℝ (deriv g) (Set.Ioo 0 1) :=
    hcont_deriv.differentiableOn (by decide)
  have hnonneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ deriv^[2] g t := by
    intro t ht
    have htC : x + t • z ∈ C := hmem_Ioo t ht
    have hpos_t := hpos (x + t • z) htC
    have hquad_nonneg :
        0 ≤ star z ⬝ᵥ (hessianMatrix f (x + t • z) *ᵥ z) :=
      by
        have hquad_nonneg' :
            0 ≤ z ⬝ᵥ (hessianMatrix f (x + t • z) *ᵥ z) :=
          (posSemidef_iff_real (M := hessianMatrix f (x + t • z))).1 hpos_t |>.2 z
        simpa using hquad_nonneg'
    have hline_eq :
        deriv (deriv (fun s : ℝ => f (x + s • z))) t =
          star z ⬝ᵥ (hessianMatrix f (x + t • z) *ᵥ z) := by
      simpa [g] using
        (line_second_deriv_eq_quadratic_form (hopen := hopen) (hcont := hcont)
          (y := x) (z := z) (t := t) htC)
    have hnonneg' : 0 ≤ deriv (deriv (fun s : ℝ => f (x + s • z))) t := by
      simpa [hline_eq] using hquad_nonneg
    simpa [g] using hnonneg'
  have hconv_line : ConvexOn ℝ (Set.Icc 0 1) g :=
    convexOn_of_deriv2_nonneg (D := Set.Icc 0 1) (hD := convex_Icc 0 1)
      (hf := hcont_g) (hf' := by simpa [interior_Icc] using hdiff_g)
      (hf'' := by simpa [interior_Icc] using hdiff_deriv)
      (hf''_nonneg := by simpa [interior_Icc] using hnonneg)
  have ha' : a = 1 - b := by linarith
  have hcombo : x + b • z = (1 - b) • x + b • y := by
    ext i
    simp [z, sub_eq_add_neg]
    ring
  have hcombo' : x + b • z = a • x + b • y := by
    simpa [ha'] using hcombo
  have hxy : x + z = y := by
    ext i
    simp [z, sub_eq_add_neg]
  have hineq := hconv_line.2 (x := 0) (y := 1) (by simp) (by simp) ha hb hab
  have hineq' : f (a • x + b • y) ≤ a * f x + b * f y := by
    simpa [g, hcombo', hxy, smul_eq_mul] using hineq
  simpa [smul_eq_mul] using hineq'

/-- Theorem 4.5: Let `f` be a twice continuously differentiable real-valued function on an open
convex set `C` in `ℝ^n`. Then `f` is convex on `C` iff its Hessian matrix
`Q_x = (q_ij(x))` with `q_ij(x) = ∂^2 f / ∂ ξ_i ∂ ξ_j (x)` is positive semidefinite
for every `x ∈ C`. -/
theorem convexOn_iff_hessian_posSemidef {n : Nat} {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hC : Convex ℝ C) (hopen : IsOpen C)
    (hcont : ContDiffOn ℝ 2 f C) :
    ConvexOn ℝ C f ↔
      ∀ x ∈ C,
        Matrix.PosSemidef (fun i j : Fin n =>
          deriv (fun t : ℝ => deriv (fun s : ℝ =>
            f (x + s • (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) +
              t • (Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ)))) 0) 0) := by
  classical
  constructor
  · intro hconv x hx
    have hpos := hessian_posSemidef_of_convexOn (hopen := hopen)
      (hcont := hcont) hconv x hx
    simpa [hessianMatrix] using hpos
  · intro hpos
    have hconv := convexOn_of_hessian_posSemidef (hC := hC) (hopen := hopen)
      (hcont := hcont) (by simpa [hessianMatrix] using hpos)
    simpa using hconv

/-- Lift real convexity to `ConvexFunctionOn` for finite-valued functions. -/
lemma convexFunctionOn_of_convexOn_real {n : Nat} {S : Set (Fin n → ℝ)}
    {g : (Fin n → ℝ) → ℝ} (hg : ConvexOn ℝ S g) :
    ConvexFunctionOn S (fun x => (g x : EReal)) := by
  unfold ConvexFunctionOn
  simpa [epigraph, EReal.coe_le_coe_iff] using
    (hg.convex_epigraph : Convex ℝ {p : (Fin n → ℝ) × ℝ | p.1 ∈ S ∧ g p.1 ≤ p.2})

/-- Extending by `⊤` outside a convex domain preserves convexity on `Set.univ`. -/
lemma convexFunctionOn_univ_if_top {n : Nat} {C : Set (Fin n → ℝ)}
    {g : (Fin n → ℝ) → ℝ} (hg : ConvexOn ℝ C g) :
    ConvexFunctionOn Set.univ (fun x => by
      classical
      exact if x ∈ C then (g x : EReal) else (⊤ : EReal)) := by
  classical
  have hconv : ConvexFunctionOn C (fun x => (g x : EReal)) :=
    convexFunctionOn_of_convexOn_real (S := C) hg
  unfold ConvexFunctionOn at hconv ⊢
  have hset :
      epigraph Set.univ (fun x => if x ∈ C then (g x : EReal) else (⊤ : EReal)) =
        epigraph C (fun x => (g x : EReal)) := by
    ext p; by_cases hp : p.1 ∈ C
    · constructor
      · intro h
        have h' : Set.univ p.1 ∧ (g p.1 : EReal) ≤ (p.2 : EReal) := by
          simpa [epigraph, hp] using h
        exact ⟨hp, h'.2⟩
      · intro h
        have hle : (if p.1 ∈ C then (g p.1 : EReal) else ⊤) ≤ (p.2 : EReal) := by
          simpa [hp] using h.2
        exact ⟨by simpa using (Set.mem_univ p.1), hle⟩
    · constructor
      · intro h
        have h' : Set.univ p.1 ∧
            (if p.1 ∈ C then (g p.1 : EReal) else ⊤) ≤ (p.2 : EReal) := by
          simpa [epigraph] using h
        have hle : (⊤ : EReal) ≤ (p.2 : EReal) := by
          simpa [if_neg hp] using h'.2
        have htop : (p.2 : EReal) = ⊤ := top_le_iff.mp hle
        exact (EReal.coe_ne_top _ htop).elim
      · intro h
        exact (hp h.1).elim
  simpa [hset] using hconv

/-- Pull back convexity along the coordinate projection on `Fin 1`. -/
lemma convexOn_comp_proj {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f) :
    ConvexOn ℝ ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' s)
      (fun x : Fin 1 → ℝ => f (x 0)) := by
  simpa [Function.comp, LinearMap.proj_apply] using
    (hf.comp_linearMap (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0))

/-- `x ↦ x^p` is convex on `(0, ∞)` for `p ≤ 0`. -/
lemma convexOn_rpow_Ioi_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) := by
  by_cases hp0 : p = 0
  · subst hp0
    simpa [Real.rpow_zero] using
      (convexOn_const (c := (1 : ℝ)) (hs := convex_Ioi (0 : ℝ)))
  have hconc_log : ConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => Real.log x) :=
    strictConcaveOn_log_Ioi.concaveOn
  have hconv_neglog : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => -Real.log x) := by
    exact (neg_convexOn_iff (f := fun x : ℝ => Real.log x) (s := Set.Ioi 0)).2 hconc_log
  have hconv_plog : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => p * Real.log x) := by
    have h := (ConvexOn.smul (c := -p) (hc := by linarith) hconv_neglog)
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have himage : (fun x : ℝ => p * Real.log x) '' (Set.Ioi 0) = Set.univ := by
    ext y; constructor
    · intro hy; exact Set.mem_univ y
    · intro hy
      refine ⟨Real.exp (y / p), Real.exp_pos (y / p), ?_⟩
      have : p * (y / p) = y := by field_simp [hp0]
      simp [Real.log_exp, this]
  have hconv_exp :
      ConvexOn ℝ ((fun x : ℝ => p * Real.log x) '' Set.Ioi 0) Real.exp := by
    simpa [himage] using (convexOn_exp : ConvexOn ℝ Set.univ Real.exp)
  have hmono_exp :
      MonotoneOn Real.exp ((fun x : ℝ => p * Real.log x) '' Set.Ioi 0) := by
    intro x hx y hy hxy
    exact Real.exp_monotone hxy
  have hconv_comp :
      ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => Real.exp (p * Real.log x)) :=
    ConvexOn.comp (g := Real.exp) (f := fun x : ℝ => p * Real.log x) (s := Set.Ioi 0)
      hconv_exp hconv_plog hmono_exp
  refine hconv_comp.congr ?_
  intro x hx
  have hx' : 0 < x := hx
  simp [Real.rpow_def_of_pos, hx', mul_comm]

/-- `x ↦ x^p` is antitone on `(0, ∞)` for `p ≤ 0`. -/
lemma antitoneOn_rpow_Ioi_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    AntitoneOn (fun x : ℝ => x ^ p) (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos hx hxy hp

/-- `x ↦ a^2 - x^2` is concave on `(-a, a)`. -/
lemma concaveOn_sub_sq_Ioo (a : ℝ) :
    ConcaveOn ℝ (Set.Ioo (-a) a) (fun x : ℝ => a ^ 2 - x ^ 2) := by
  have hconv_sq : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ (2 : ℕ)) := by
    simpa using
      (Even.convexOn_pow (𝕜 := ℝ) (n := 2) (hn := by decide))
  have hconv_sq' :
      ConvexOn ℝ (Set.Ioo (-a) a) (fun x : ℝ => x ^ (2 : ℕ)) :=
    hconv_sq.subset (by intro x hx; trivial) (convex_Ioo (-a) a)
  have hconc_neg_sq : ConcaveOn ℝ (Set.Ioo (-a) a) (fun x : ℝ => -(x ^ (2 : ℕ))) := by
    exact
      (neg_concaveOn_iff (f := fun x : ℝ => x ^ (2 : ℕ)) (s := Set.Ioo (-a) a)).2 hconv_sq'
  have hconc := hconc_neg_sq.add_const (a ^ 2)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hconc

/-- Image of `x ↦ a^2 - x^2` on `(-a, a)` is `(0, a^2]`. -/
lemma image_sub_sq_Ioo {a : ℝ} (ha : 0 < a) :
    (fun x : ℝ => a ^ 2 - x ^ 2) '' Set.Ioo (-a) a = Set.Ioc 0 (a ^ 2) := by
  ext y; constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx2 : x ^ 2 < a ^ 2 := by
      exact sq_lt_sq' hx.1 hx.2
    have hpos : 0 < a ^ 2 - x ^ 2 := by linarith
    have hle : a ^ 2 - x ^ 2 ≤ a ^ 2 := by linarith [sq_nonneg x]
    exact ⟨hpos, hle⟩
  · intro hy
    rcases hy with ⟨hypos, hyle⟩
    let x : ℝ := Real.sqrt (a ^ 2 - y)
    have hxnonneg : 0 ≤ x := by
      dsimp [x]; exact Real.sqrt_nonneg _
    have hx2 : x ^ 2 = a ^ 2 - y := by
      have hnonneg : 0 ≤ a ^ 2 - y := by linarith
      simpa [x] using (Real.sq_sqrt hnonneg)
    have hx2lt : x ^ 2 < a ^ 2 := by
      have : a ^ 2 - y < a ^ 2 := by linarith [hypos]
      simpa [hx2] using this
    have hxlt : x < a := by
      have ha_nonneg : 0 ≤ a := le_of_lt ha
      exact (sq_lt_sq₀ hxnonneg ha_nonneg).1 (by simpa using hx2lt)
    have hxmem : x ∈ Set.Ioo (-a) a := by
      refine ⟨?_, hxlt⟩
      have hneg : -a < 0 := by linarith [ha]
      exact lt_of_lt_of_le hneg hxnonneg
    have hxeq : a ^ 2 - x ^ 2 = y := by linarith [hx2]
    exact ⟨x, hxmem, hxeq⟩

/-- Example 4.4.1: Here are some functions on `Real` whose convexity is a consequence of
Theorem 4.4: (i) `f(x) = exp(alpha * x)` for `-infty < alpha < infty`;
(ii) `f(x) = x^p` if `x >= 0`, `f(x) = infty` if `x < 0`, where `1 <= p < infty`;
(iii) `f(x) = -x^p` if `x >= 0`, `f(x) = infty` if `x < 0`, where `0 <= p <= 1`;
(iv) `f(x) = x^p` if `x > 0`, `f(x) = infty` if `x <= 0`, where `-infty < p <= 0`;
(v) `f(x) = (alpha^2 - x^2)^(-1/2)` if `|x| < alpha`,
`f(x) = infty` if `|x| >= alpha`, where `alpha > 0`;
(vi) `f(x) = -log x` if `x > 0`, `f(x) = infty` if `x <= 0`. -/
lemma convexFunctionOn_example_functions :
    (∀ a : Real,
      ConvexFunctionOn (Set.univ) (fun x : Fin 1 → Real =>
        (Real.exp (a * x 0) : EReal))) ∧
    (∀ p : Real, 1 ≤ p →
      ConvexFunctionOn (Set.univ) (fun x : Fin 1 → Real =>
        if 0 ≤ x 0 then ((Real.rpow (x 0) p : Real) : EReal) else (⊤ : EReal))) ∧
    (∀ p : Real, 0 ≤ p → p ≤ 1 →
      ConvexFunctionOn (Set.univ) (fun x : Fin 1 → Real =>
        if 0 ≤ x 0 then ((- Real.rpow (x 0) p : Real) : EReal) else (⊤ : EReal))) ∧
    (∀ p : Real, p ≤ 0 →
      ConvexFunctionOn (Set.univ) (fun x : Fin 1 → Real =>
        if 0 < x 0 then ((Real.rpow (x 0) p : Real) : EReal) else (⊤ : EReal))) ∧
    (∀ a : Real, 0 < a →
      ConvexFunctionOn (Set.univ) (fun x : Fin 1 → Real =>
        if |x 0| < a then
          ((Real.rpow (a ^ 2 - (x 0) ^ 2) (-((1 : Real) / 2)) : Real) : EReal)
        else (⊤ : EReal))) ∧
    ConvexFunctionOn (Set.univ) (fun x : Fin 1 → Real =>
      if 0 < x 0 then ((- Real.log (x 0) : Real) : EReal) else (⊤ : EReal)) := by
  classical
  refine And.intro ?h1 ?hrest1
  · intro a
    have hconv_exp : ConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (a * x)) := by
      simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc] using
        (convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ a))
    have hconv_fin : ConvexOn ℝ Set.univ (fun x : Fin 1 → ℝ => Real.exp (a * x 0)) := by
      simpa using
        (convexOn_comp_proj (s := Set.univ) (f := fun x : ℝ => Real.exp (a * x)) hconv_exp)
    simpa using (convexFunctionOn_of_convexOn_real (S := Set.univ) hconv_fin)
  · refine And.intro ?h2 ?hrest2
    · intro p hp
      let C : Set (Fin 1 → ℝ) := {x | 0 ≤ x 0}
      have hconv_rpow : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ p) :=
        convexOn_rpow hp
      have hconv_fin' :
          ConvexOn ℝ ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ici 0)
            (fun x : Fin 1 → ℝ => (x 0) ^ p) := by
        simpa using
          (convexOn_comp_proj (s := Set.Ici 0) (f := fun x : ℝ => x ^ p) hconv_rpow)
      have hC :
          C = ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ici 0) := by
        ext x; simp [C, Set.mem_Ici]
      have hconv_fin : ConvexOn ℝ C (fun x : Fin 1 → ℝ => (x 0) ^ p) := by
        simpa [hC] using hconv_fin'
      have hconvE :
          ConvexFunctionOn Set.univ (fun x : Fin 1 → ℝ =>
            if x ∈ C then ((x 0) ^ p : ℝ) else (⊤ : EReal)) :=
        convexFunctionOn_univ_if_top (C := C) (g := fun x : Fin 1 → ℝ => (x 0) ^ p) hconv_fin
      simpa [C] using hconvE
    · refine And.intro ?h3 ?hrest3
      · intro p hp0 hp1
        let C : Set (Fin 1 → ℝ) := {x | 0 ≤ x 0}
        have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ p) :=
          Real.concaveOn_rpow hp0 hp1
        have hconv_neg : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => -(x ^ p)) := by
          exact (neg_convexOn_iff (f := fun x : ℝ => x ^ p) (s := Set.Ici 0)).2 hconc
        have hconv_fin' :
            ConvexOn ℝ ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ici 0)
              (fun x : Fin 1 → ℝ => -(x 0) ^ p) := by
          simpa using
            (convexOn_comp_proj (s := Set.Ici 0) (f := fun x : ℝ => -(x ^ p)) hconv_neg)
        have hC :
            C = ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ici 0) := by
          ext x; simp [C, Set.mem_Ici]
        have hconv_fin : ConvexOn ℝ C (fun x : Fin 1 → ℝ => -(x 0) ^ p) := by
          simpa [hC] using hconv_fin'
        have hconvE :
            ConvexFunctionOn Set.univ (fun x : Fin 1 → ℝ =>
              if x ∈ C then ((-(x 0) ^ p : ℝ) : EReal) else (⊤ : EReal)) :=
          convexFunctionOn_univ_if_top (C := C) (g := fun x : Fin 1 → ℝ => -(x 0) ^ p) hconv_fin
        simpa [C] using hconvE
      · refine And.intro ?h4 ?hrest4
        · intro p hp
          let C : Set (Fin 1 → ℝ) := {x | 0 < x 0}
          have hconv_rpow : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) :=
            convexOn_rpow_Ioi_of_nonpos hp
          have hconv_fin' :
              ConvexOn ℝ ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ioi 0)
                (fun x : Fin 1 → ℝ => (x 0) ^ p) := by
            simpa using
              (convexOn_comp_proj (s := Set.Ioi 0) (f := fun x : ℝ => x ^ p) hconv_rpow)
          have hC :
              C = ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ioi 0) := by
            ext x; simp [C, Set.mem_Ioi]
          have hconv_fin : ConvexOn ℝ C (fun x : Fin 1 → ℝ => (x 0) ^ p) := by
            simpa [hC] using hconv_fin'
          have hconvE :
              ConvexFunctionOn Set.univ (fun x : Fin 1 → ℝ =>
                if x ∈ C then ((x 0) ^ p : ℝ) else (⊤ : EReal)) :=
            convexFunctionOn_univ_if_top (C := C) (g := fun x : Fin 1 → ℝ => (x 0) ^ p) hconv_fin
          simpa [C] using hconvE
        · refine And.intro ?h5 ?h6
          · intro a ha
            let C : Set (Fin 1 → ℝ) := {x | |x 0| < a}
            have hconc_sub : ConcaveOn ℝ (Set.Ioo (-a) a) (fun x : ℝ => a ^ 2 - x ^ 2) :=
              concaveOn_sub_sq_Ioo a
            have hconv_rpow :
                ConvexOn ℝ (Set.Ioi 0) (fun y : ℝ => y ^ (-((1 : ℝ) / 2))) :=
              convexOn_rpow_Ioi_of_nonpos (by linarith)
            have hanti_rpow :
                AntitoneOn (fun y : ℝ => y ^ (-((1 : ℝ) / 2))) (Set.Ioi 0) :=
              antitoneOn_rpow_Ioi_of_nonpos (by linarith)
            have himage :
                (fun x : ℝ => a ^ 2 - x ^ 2) '' Set.Ioo (-a) a = Set.Ioc 0 (a ^ 2) :=
              image_sub_sq_Ioo (a := a) ha
            have hconv_image :
                Convex ℝ ((fun x : ℝ => a ^ 2 - x ^ 2) '' Set.Ioo (-a) a) := by
              simpa [himage] using (convex_Ioc (0 : ℝ) (a ^ 2))
            have hsubset :
                (fun x : ℝ => a ^ 2 - x ^ 2) '' Set.Ioo (-a) a ⊆ Set.Ioi 0 := by
              intro y hy
              have : y ∈ Set.Ioc 0 (a ^ 2) := by simpa [himage] using hy
              exact this.1
            have hconv_rpow' :
                ConvexOn ℝ ((fun x : ℝ => a ^ 2 - x ^ 2) '' Set.Ioo (-a) a)
                  (fun y : ℝ => y ^ (-((1 : ℝ) / 2))) :=
              hconv_rpow.subset hsubset hconv_image
            have hanti_rpow' :
                AntitoneOn (fun y : ℝ => y ^ (-((1 : ℝ) / 2)))
                  ((fun x : ℝ => a ^ 2 - x ^ 2) '' Set.Ioo (-a) a) := by
              intro x hx y hy hxy
              exact hanti_rpow (hsubset hx) (hsubset hy) hxy
            have hconv_comp :
                ConvexOn ℝ (Set.Ioo (-a) a)
                  (fun x : ℝ => (a ^ 2 - x ^ 2) ^ (-((1 : ℝ) / 2))) :=
              ConvexOn.comp_concaveOn
                (g := fun y : ℝ => y ^ (-((1 : ℝ) / 2)))
                (f := fun x : ℝ => a ^ 2 - x ^ 2) (s := Set.Ioo (-a) a)
                hconv_rpow' hconc_sub hanti_rpow'
            have hconv_fin' :
                ConvexOn ℝ
                  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ioo (-a) a)
                  (fun x : Fin 1 → ℝ => (a ^ 2 - (x 0) ^ 2) ^ (-((1 : ℝ) / 2))) := by
              simpa using
                (convexOn_comp_proj (s := Set.Ioo (-a) a)
                  (f := fun x : ℝ => (a ^ 2 - x ^ 2) ^ (-((1 : ℝ) / 2))) hconv_comp)
            have hC :
                C = ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ioo (-a) a) := by
              ext x; simp [C, abs_lt, Set.mem_Ioo]
            have hconv_fin :
                ConvexOn ℝ C (fun x : Fin 1 → ℝ => (a ^ 2 - (x 0) ^ 2) ^ (-((1 : ℝ) / 2))) := by
              simpa [hC] using hconv_fin'
            have hconvE :
                ConvexFunctionOn Set.univ (fun x : Fin 1 → ℝ =>
                  if x ∈ C then
                    ((a ^ 2 - (x 0) ^ 2) ^ (-((1 : ℝ) / 2)) : ℝ)
                  else (⊤ : EReal)) :=
              convexFunctionOn_univ_if_top
                (C := C) (g := fun x : Fin 1 → ℝ => (a ^ 2 - (x 0) ^ 2) ^ (-((1 : ℝ) / 2)))
                hconv_fin
            simpa [C] using hconvE
          · let C : Set (Fin 1 → ℝ) := {x | 0 < x 0}
            have hconc_log : ConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => Real.log x) :=
              strictConcaveOn_log_Ioi.concaveOn
            have hconv_neglog :
                ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => -Real.log x) := by
              exact (neg_convexOn_iff (f := fun x : ℝ => Real.log x) (s := Set.Ioi 0)).2 hconc_log
            have hconv_fin' :
                ConvexOn ℝ ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ioi 0)
                  (fun x : Fin 1 → ℝ => -Real.log (x 0)) := by
              simpa using
                (convexOn_comp_proj (s := Set.Ioi 0) (f := fun x : ℝ => -Real.log x) hconv_neglog)
            have hC :
                C = ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ⁻¹' Set.Ioi 0) := by
              ext x; simp [C, Set.mem_Ioi]
            have hconv_fin :
                ConvexOn ℝ C (fun x : Fin 1 → ℝ => -Real.log (x 0)) := by
              simpa [hC] using hconv_fin'
            have hconvE :
                ConvexFunctionOn Set.univ (fun x : Fin 1 → ℝ =>
                  if x ∈ C then ((-Real.log (x 0) : ℝ) : EReal) else (⊤ : EReal)) :=
              convexFunctionOn_univ_if_top (C := C) (g := fun x : Fin 1 → ℝ => -Real.log (x 0))
                hconv_fin
            simpa [C] using hconvE

/-- Definition 4.4: The effective domain of a convex function `f` on `S`, denoted `dom f`,
is the projection of `epi f` onto `R^n`; equivalently,
`dom f = {x | ∃ μ, (x, μ) ∈ epi f} = {x | f x < +infty}`. -/
def effectiveDomain {n : Nat} (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    Set (Fin n -> Real) :=
  {x | ∃ μ : Real, (x, μ) ∈ epigraph S f}

lemma effectiveDomain_eq {n : Nat} (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    effectiveDomain S f = {x | x ∈ S ∧ f x < (⊤ : EReal)} := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨μ, hμ⟩
    refine ⟨hμ.1, ?_⟩
    have hne : f x ≠ (⊤ : EReal) := by
      intro htop
      have htop_le : (⊤ : EReal) ≤ (μ : EReal) := by
        simpa [htop] using hμ.2
      exact (EReal.coe_ne_top μ) ((top_le_iff).1 htop_le)
    exact (lt_top_iff_ne_top).2 hne
  · intro hx
    rcases hx with ⟨hxS, hlt⟩
    have hne : f x ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 hlt
    refine ⟨(f x).toReal, ?_⟩
    refine And.intro hxS ?_
    simpa using (EReal.le_coe_toReal (x := f x) hne)

/-- The effective domain is the projection of the epigraph onto the first coordinate. -/
lemma effectiveDomain_eq_image_fst {n : Nat} (S : Set (Fin n -> Real))
    (f : (Fin n -> Real) -> EReal) :
    effectiveDomain S f =
      (LinearMap.fst ℝ (Fin n -> Real) Real) '' epigraph S f := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨μ, hμ⟩
    refine ⟨(x, μ), hμ, ?_⟩
    simp
  · intro hx
    rcases hx with ⟨p, hp, rfl⟩
    refine ⟨p.2, ?_⟩
    simpa using hp

/-- The image of the epigraph under the first projection is convex. -/
lemma convex_image_fst_epigraph {n : Nat} {S : Set (Fin n -> Real)}
    {f : (Fin n -> Real) -> EReal} (hf : ConvexFunctionOn S f) :
    Convex ℝ ((LinearMap.fst ℝ (Fin n -> Real) Real) '' epigraph S f) := by
  have hconv : Convex ℝ (epigraph S f) := by
    simpa [ConvexFunctionOn] using hf
  simpa using hconv.linear_image (LinearMap.fst ℝ (Fin n -> Real) Real)

end Section04
end Chap01
