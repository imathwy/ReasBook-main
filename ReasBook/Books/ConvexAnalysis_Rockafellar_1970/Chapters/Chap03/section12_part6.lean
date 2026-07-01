/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part5

section Chap03
section Section12

/-- Nonnegativity of the dot product of a vector with itself. -/
lemma dotProduct_self_nonneg {n : Nat} (v : Fin n → Real) : 0 ≤ v ⬝ᵥ v := by
  classical
  -- `v ⬝ᵥ v = ∑ i, v i * v i`.
  simpa [dotProduct] using
    (Finset.sum_nonneg (s := Finset.univ) (f := fun i : Fin n => v i * v i)
      (fun i _hi => mul_self_nonneg (v i)))

/-- The key inequality for the conjugate of `quadraticHalfInner`:
`⟪x, x*⟫ - (1/2)⟪x, x⟫ ≤ (1/2)⟪x*, x*⟫`. -/
lemma range_term_quadraticHalfInner_le (n : Nat) (x xStar : Fin n → Real) :
    ((x ⬝ᵥ xStar : Real) : EReal) - quadraticHalfInner n x ≤ quadraticHalfInner n xStar := by
  classical
  -- First prove the real inequality `⟪x,x*⟫ ≤ (1/2)⟪x,x⟫ + (1/2)⟪x*,x*⟫` by summing
  -- `2ab ≤ a^2 + b^2` componentwise.
  have h2 :
      2 * (x ⬝ᵥ xStar : Real) ≤ (x ⬝ᵥ x) + (xStar ⬝ᵥ xStar) := by
    have hsum :
        (Finset.univ.sum fun i : Fin n => 2 * (x i * xStar i)) ≤
          Finset.univ.sum fun i : Fin n => x i * x i + xStar i * xStar i := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have : 0 ≤ (x i - xStar i) ^ 2 := sq_nonneg (x i - xStar i)
      nlinarith [this]
    -- Rewrite both sides back into dot products.
    -- Left: `∑ 2*(x_i*x*_i) = 2 * ∑ (x_i*x*_i)`.
    -- Right: `∑ (x_i^2 + (x*_i)^2) = ∑ x_i^2 + ∑ (x*_i)^2`.
    simpa [dotProduct, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, add_assoc, add_comm,
      add_left_comm] using hsum
  have hreal :
      (x ⬝ᵥ xStar : Real) - (1 / 2 : Real) * (x ⬝ᵥ x) ≤
        (1 / 2 : Real) * (xStar ⬝ᵥ xStar) := by
    linarith [h2]
  -- Cast the real inequality into `EReal` and normalize the expression.
  have hE :
      (((x ⬝ᵥ xStar : Real) - (1 / 2 : Real) * (x ⬝ᵥ x) : Real) : EReal) ≤
        (((1 / 2 : Real) * (xStar ⬝ᵥ xStar) : Real) : EReal) := by
    exact_mod_cast hreal
  -- Rewrite the goal into the coerced real inequality above.
  simpa [quadraticHalfInner, EReal.coe_sub, EReal.coe_mul, mul_assoc, mul_left_comm, mul_comm] using
    hE

/-- The Fenchel conjugate of `w(x) = (1/2)⟪x,x⟫` is itself. -/
lemma fenchelConjugate_quadraticHalfInner (n : Nat) :
    fenchelConjugate n (quadraticHalfInner n) = quadraticHalfInner n := by
  classical
  ext xStar
  unfold fenchelConjugate
  refine le_antisymm ?_ ?_
  · -- Upper bound: every range term is bounded by `w(x*)`.
    refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    exact range_term_quadraticHalfInner_le n x xStar
  · -- Lower bound: evaluate the supremum at the maximizer `x = x*`.
    have hle :
        ((xStar ⬝ᵥ xStar : Real) : EReal) - quadraticHalfInner n xStar ≤
          sSup
            (Set.range fun x : Fin n → Real =>
              ((x ⬝ᵥ xStar : Real) : EReal) - quadraticHalfInner n x) :=
      le_sSup ⟨xStar, rfl⟩
    have hterm :
        ((xStar ⬝ᵥ xStar : Real) : EReal) - quadraticHalfInner n xStar =
          quadraticHalfInner n xStar := by
      -- `⟪x*,x*⟫ - (1/2)⟪x*,x*⟫ = (1/2)⟪x*,x*⟫`.
      set a : Real := (xStar ⬝ᵥ xStar : Real)
      have ha : a - (1 / 2 : Real) * a = (1 / 2 : Real) * a := by ring
      calc
        ((xStar ⬝ᵥ xStar : Real) : EReal) - quadraticHalfInner n xStar
            = ((a : Real) : EReal) - (((1 / 2 : Real) * a : Real) : EReal) := by
                simp [quadraticHalfInner, a]
        _ = ((a - (1 / 2 : Real) * a : Real) : EReal) := by
              exact (EReal.coe_sub a ((1 / 2 : Real) * a)).symm
        _ = (((1 / 2 : Real) * a : Real) : EReal) := by
              exact_mod_cast ha
        _ = quadraticHalfInner n xStar := by simp [quadraticHalfInner, a]
    -- Conclude by rewriting with `hterm`.
    simpa [hterm] using hle

/-- The quadratic function `w(x) = (1/2)⟪x,x⟫` is convex on `ℝ^n`. -/
lemma convexFunction_quadraticHalfInner (n : Nat) : ConvexFunction (quadraticHalfInner n) := by
  classical
  -- Use the segment-inequality characterization on `Set.univ`.
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)), quadraticHalfInner n x ≠ (⊥ : EReal) := by
    intro x _hx
    dsimp [quadraticHalfInner]
    exact EReal.coe_ne_bot _
  -- `ConvexFunction` is `ConvexFunctionOn Set.univ`.
  have hseg :=
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real)))
        (f := quadraticHalfInner n) (hC := (by simpa using (convex_univ : Convex ℝ (Set.univ))))
        hnotbot).2
  -- Provide the segment inequality.
  refine hseg (fun x _hx y _hy t ht0 ht1 => ?_)
  -- Reduce to a real inequality since `quadraticHalfInner` is finite everywhere.
  have ht0' : 0 < (t : Real) := ht0
  have ht1' : 0 < (1 - t : Real) := sub_pos.mpr ht1
  -- Real inequality: `w((1-t)x+ty) ≤ (1-t)w(x) + t w(y)`.
  have hreal :
      (1 / 2 : Real) *
            (((1 - t) • x + t • y) ⬝ᵥ ((1 - t) • x + t • y) : Real) ≤
          (1 - t) * ((1 / 2 : Real) * (x ⬝ᵥ x)) + t * ((1 / 2 : Real) * (y ⬝ᵥ y)) := by
    -- It suffices to show `z·z ≤ (1-t)(x·x) + t(y·y)`.
    have hreal' :
        (((1 - t) • x + t • y) ⬝ᵥ ((1 - t) • x + t • y) : Real) ≤
          (1 - t) * (x ⬝ᵥ x) + t * (y ⬝ᵥ y) := by
      -- Expand the left-hand side using bilinearity of `dotProduct`.
      -- Then `RHS - LHS = t(1-t) * ((x-y)·(x-y)) ≥ 0`.
      have hxmy_nonneg : 0 ≤ (x - y) ⬝ᵥ (x - y) := dotProduct_self_nonneg (v := x - y)
      have ht_nonneg : 0 ≤ t * (1 - t) := by nlinarith [ht0.le, ht1.le]
      have hdiff :
          (1 - t) * (x ⬝ᵥ x) + t * (y ⬝ᵥ y) -
              (((1 - t) • x + t • y) ⬝ᵥ ((1 - t) • x + t • y) : Real) =
            t * (1 - t) * ((x - y) ⬝ᵥ (x - y)) := by
        -- Normalize dot products and then `ring`.
        -- The simp step uses bilinearity plus `dotProduct_comm`.
        simp
          [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm,
            dotProduct_add, dotProduct_smul, dotProduct_comm]
        ring
      have hge : 0 ≤
          (1 - t) * (x ⬝ᵥ x) + t * (y ⬝ᵥ y) -
              (((1 - t) • x + t • y) ⬝ᵥ ((1 - t) • x + t • y) : Real) := by
        -- Rewrite using `hdiff`.
        rw [hdiff]
        exact mul_nonneg ht_nonneg hxmy_nonneg
      linarith
    -- Reinsert the factor `1/2`.
    nlinarith [hreal']
  -- Cast the real inequality into `EReal` and simplify.
  have hE :
      (((1 / 2 : Real) *
              (((1 - t) • x + t • y) ⬝ᵥ ((1 - t) • x + t • y) : Real) : Real) : EReal) ≤
        (((1 - t) * ((1 / 2 : Real) * (x ⬝ᵥ x)) + t * ((1 / 2 : Real) * (y ⬝ᵥ y)) : Real) :
          EReal) := by
    exact_mod_cast hreal
  -- Match the statement expected by `convexFunctionOn_iff_segment_inequality`.
  simpa [quadraticHalfInner, EReal.coe_add, EReal.coe_mul, mul_add, add_mul, add_assoc, add_comm,
    add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hE

/-- If `f* = f`, then `f` is pointwise bounded below by `w(x) = (1/2)⟪x,x⟫`. -/
lemma quadraticHalfInner_le_of_fenchelConjugate_eq_self (n : Nat)
    (f : (Fin n → Real) → EReal) (hf : fenchelConjugate n f = f) :
    ∀ x : Fin n → Real, quadraticHalfInner n x ≤ f x := by
  classical
  intro x
  have hfix : fenchelConjugate n f x = f x := by
    simpa using congrArg (fun g => g x) hf
  -- Use the defining inequality `range term ≤ sSup` at `xStar = x` and `x = x`.
  have hx :
      ((x ⬝ᵥ x : Real) : EReal) - f x ≤ f x := by
    have hx' :
        ((x ⬝ᵥ x : Real) : EReal) - f x ≤ fenchelConjugate n f x := by
      unfold fenchelConjugate
      exact le_sSup ⟨x, rfl⟩
    simpa [hfix] using hx'
  by_cases htop : f x = ⊤
  · simp [quadraticHalfInner, htop]
  by_cases hbot : f x = ⊥
  · -- `((x·x) : EReal) - ⊥ = ⊤`, contradicting `⊤ ≤ ⊥`.
    have : ¬ (((⊤ : EReal) ≤ (⊥ : EReal))) := by simp
    have hcontra : (⊤ : EReal) ≤ (⊥ : EReal) := by
      have hx' := hx
      simp [hbot] at hx'
    exact (this hcontra).elim
  -- Finite real value: convert to a real inequality.
  have hcoe : ((f x).toReal : EReal) = f x := EReal.coe_toReal htop hbot
  set r : Real := (f x).toReal
  have hfr : f x = (r : EReal) := by simpa [r] using hcoe.symm
  have hx' : ((x ⬝ᵥ x : Real) : EReal) - (r : EReal) ≤ (r : EReal) := by
    simpa [hfr] using hx
  have hx'' : (x ⬝ᵥ x : Real) - r ≤ r := by
    -- Rewrite the subtraction in `EReal` back to `Real`.
    have hxE : (((x ⬝ᵥ x : Real) : EReal) - (r : EReal)) ≤ (r : EReal) := hx'
    have hxE' := hxE
    rw [(EReal.coe_sub (x ⬝ᵥ x : Real) r).symm] at hxE'
    exact (EReal.coe_le_coe_iff).1 hxE'
  have hw : (1 / 2 : Real) * (x ⬝ᵥ x) ≤ r := by
    linarith [hx'']
  -- Cast back to `EReal` and rewrite `r` as `f x`.
  have hwE :
      (((1 / 2 : Real) * (x ⬝ᵥ x) : Real) : EReal) ≤ (r : EReal) := by
    exact_mod_cast hw
  simpa [quadraticHalfInner, hfr] using hwE

/-- Text 12.2.9: The fixed-point identity `f* = f` for Fenchel conjugation has a unique solution
in the class of convex functions on `ℝ^n`, namely `f = w` where
`w(x) = (1/2) * ⟪x, x⟫`. Here `f*` is `fenchelConjugate n f`. -/
theorem fenchelConjugate_eq_self_unique_solution (n : Nat) :
    (ConvexFunction (quadraticHalfInner n) ∧
        fenchelConjugate n (quadraticHalfInner n) = quadraticHalfInner n) ∧
      ∀ f : (Fin n → Real) → EReal,
        ConvexFunction f → fenchelConjugate n f = f → f = quadraticHalfInner n := by
  refine ⟨?_, ?_⟩
  · exact ⟨convexFunction_quadraticHalfInner n, fenchelConjugate_quadraticHalfInner n⟩
  · intro f _hfConvex hfFix
    -- First show `w ≤ f` from the fixed-point identity.
    have hwle : ∀ x : Fin n → Real, quadraticHalfInner n x ≤ f x :=
      quadraticHalfInner_le_of_fenchelConjugate_eq_self n f hfFix
    -- Conjugation reverses order, so `f = f* ≤ w* = w`.
    have hanti := fenchelConjugate_antitone (n := n)
    have hfle : ∀ x : Fin n → Real, f x ≤ quadraticHalfInner n x := by
      intro x
      have := hanti (a := quadraticHalfInner n) (b := f) hwle x
      -- Rewrite using `f* = f` and `w* = w`.
      simpa [hfFix, fenchelConjugate_quadraticHalfInner n] using this
    -- Conclude by pointwise antisymmetry.
    funext x
    exact le_antisymm (hfle x) (hwle x)

/-- Text 12.1.3: Let `f_{-∞}` and `f_{+∞}` denote the constant functions on `ℝ^n` taking values
`-∞` and `+∞` respectively. Then they are conjugate to each other (with conjugation given here by
`fenchelConjugate`), i.e. `(f_{-∞})^* = f_{+∞}` and `(f_{+∞})^* = f_{-∞}`. -/
def constNegInf (n : Nat) : (Fin n → Real) → EReal :=
  fun _ => (⊥ : EReal)

/-- The constant function on `ℝ^n` with value `+∞`. -/
def constPosInf (n : Nat) : (Fin n → Real) → EReal :=
  fun _ => (⊤ : EReal)

/-- The Fenchel conjugate of the constant `-∞` function is pointwise `+∞`. -/
lemma fenchelConjugate_constNegInf_apply (n : Nat) (xStar : Fin n → Real) :
    fenchelConjugate n (constNegInf n) xStar = (⊤ : EReal) := by
  classical
  simp [fenchelConjugate, constNegInf]

/-- The Fenchel conjugate of the constant `+∞` function is pointwise `-∞`. -/
lemma fenchelConjugate_constPosInf_apply (n : Nat) (xStar : Fin n → Real) :
    fenchelConjugate n (constPosInf n) xStar = (⊥ : EReal) := by
  classical
  simp [fenchelConjugate, constPosInf]

/-- For `f_{-∞}` the constant function `x ↦ -∞` on `ℝ^n`, its Fenchel conjugate is `f_{+∞}`. -/
theorem fenchelConjugate_constNegInf (n : Nat) :
    fenchelConjugate n (constNegInf n) = constPosInf n := by
  ext xStar
  simpa [constPosInf] using fenchelConjugate_constNegInf_apply n xStar

/-- For `f_{+∞}` the constant function `x ↦ +∞` on `ℝ^n`, its Fenchel conjugate is `f_{-∞}`. -/
theorem fenchelConjugate_constPosInf (n : Nat) :
    fenchelConjugate n (constPosInf n) = constNegInf n := by
  ext xStar
  simpa [constNegInf] using fenchelConjugate_constPosInf_apply n xStar

/-- Rewriting a dot product after applying the inverse linear equivalence, using the assumed
adjoint relation. -/
lemma dotProduct_linearEquiv_symm_eq (n : Nat) (A AStar : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real))
    (hAStar : ∀ x y : Fin n → Real, (A x) ⬝ᵥ y = x ⬝ᵥ AStar y) (y v : Fin n → Real) :
    (A.symm y) ⬝ᵥ v = y ⬝ᵥ AStar.symm v := by
  -- Apply the adjoint identity to `x = A⁻¹ y` and `y = (A*)⁻¹ v`, then simplify.
  simpa using (hAStar (A.symm y) (AStar.symm v)).symm

/-- Cancel a finite real constant on the right in an `EReal` inequality. -/
lemma ereal_add_coe_le_coe_iff_cancel (t : EReal) (c μ : Real) :
    t + (c : EReal) ≤ (μ : EReal) ↔ t ≤ ((μ - c : Real) : EReal) := by
  have hc : AddLECancellable (c : EReal) := EReal.addLECancellable_coe c
  have hμ' : ((μ - c : Real) : EReal) + (c : EReal) = (μ : EReal) := by
    have hreal : (μ - c : Real) + c = μ := by ring
    have hE : (((μ - c : Real) + c : Real) : EReal) = (μ : EReal) :=
      congrArg (fun r : Real => (r : EReal)) hreal
    -- Rewrite only the left-hand side of `hE` into `+` in `EReal`.
    have hE' := hE
    rw [EReal.coe_add] at hE'
    exact hE'
  have hμ : (μ : EReal) = ((μ - c : Real) : EReal) + (c : EReal) := hμ'.symm
  constructor
  · intro h
    have h' := h
    -- Rewrite `μ` as `(μ - c) + c` and cancel `+ c`.
    rw [hμ] at h'
    exact (hc.add_le_add_iff_right).1 h'
  · intro h
    have h' : t + (c : EReal) ≤ ((μ - c : Real) : EReal) + (c : EReal) :=
      (hc.add_le_add_iff_right).2 h
    -- Rewrite back and conclude.
    have h'' := h'
    rw [← hμ] at h''
    exact h''

/-- Change-of-variables lemma for the affine-minorant characterization used in Theorem 12.3. -/
lemma affineTransform_pointwise_inequality_iff (n : Nat) (h : (Fin n → Real) → EReal)
    (A AStar : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real))
    (hAStar : ∀ x y : Fin n → Real, (A x) ⬝ᵥ y = x ⬝ᵥ AStar y) (a aStar : Fin n → Real)
    (α : Real) (xStar : Fin n → Real) (μ : Real) :
    let b' : Fin n → Real := AStar.symm (xStar - aStar)
    let μ' : Real := μ + α - (a ⬝ᵥ (xStar - aStar))
    (∀ x : Fin n → Real,
          ((x ⬝ᵥ xStar - μ : Real) : EReal) ≤
            h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal)) ↔
      (∀ y : Fin n → Real, ((y ⬝ᵥ b' - μ' : Real) : EReal) ≤ h y) := by
  classical
  dsimp
  set b' : Fin n → Real := AStar.symm (xStar - aStar) with hb'
  set μ' : Real := μ + α - (a ⬝ᵥ (xStar - aStar)) with hμ'
  constructor
  · intro hx y
    -- Substitute `x = A⁻¹ y + a`.
    let x : Fin n → Real := A.symm y + a
    have hx0 := hx x
    -- Put the inequality in the form `u + c ≤ v + c` and cancel the real constant `c`.
    set c : Real := x ⬝ᵥ aStar + α
    have hc : AddLECancellable (c : EReal) := EReal.addLECancellable_coe c
    have hlhs :
        ((x ⬝ᵥ xStar - μ : Real) : EReal) =
          ((x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) : EReal) + (c : EReal) := by
      have hreal :
          (x ⬝ᵥ xStar - μ : Real) =
            (x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) + (x ⬝ᵥ aStar + α) := by
        -- Expand `x ⬝ᵥ (xStar - aStar)` and `ring`.
        simp [dotProduct_sub]
        ring
      -- Coerce to `EReal` and rewrite the sum as `+`.
      simpa [c, EReal.coe_add] using congrArg (fun r : Real => (r : EReal)) hreal
    have hrhs :
        h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal) =
          h (A (x - a)) + (c : EReal) := by
      -- Combine the two real constants into a single coerced real.
      simp [c, add_assoc, EReal.coe_add]
    have hx1 :
        ((x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) : EReal) ≤ h (A (x - a)) := by
      have hx' :
          ((x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) : EReal) + (c : EReal) ≤
            h (A (x - a)) + (c : EReal) := by
        have hx'' := hx0
        -- Rewrite the left side into the `↑(x ⬝ᵥ xStar - μ)` form.
        rw [(EReal.coe_sub (x ⬝ᵥ xStar) μ).symm] at hx''
        -- Rewrite both sides as `… + (c : EReal)`.
        rw [hlhs] at hx''
        rw [hrhs] at hx''
        exact hx''
      exact (hc.add_le_add_iff_right).1 hx'
    have hAx : A (x - a) = y := by
      simp [x, sub_eq_add_neg, add_assoc]
    -- Identify the range-term after substitution.
    have hdot_inv :
        (A.symm y) ⬝ᵥ (xStar - aStar) = y ⬝ᵥ b' := by
      simpa [hb'] using
        (dotProduct_linearEquiv_symm_eq (n := n) (A := A) (AStar := AStar) hAStar y (xStar - aStar))
    have hterm :
        (x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) = y ⬝ᵥ b' - μ' := by
      calc
        (x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) =
            ((A.symm y + a) ⬝ᵥ (xStar - aStar) - (μ + α) : Real) := by
              simp [x]
        _ =
            ((A.symm y) ⬝ᵥ (xStar - aStar) + a ⬝ᵥ (xStar - aStar) - (μ + α) : Real) := by
              -- Use linearity in the left argument without expanding the `xStar - aStar` term.
              have hadd :
                  (A.symm y + a) ⬝ᵥ (xStar - aStar) =
                    (A.symm y) ⬝ᵥ (xStar - aStar) + a ⬝ᵥ (xStar - aStar) := by
                simpa using (add_dotProduct (u := A.symm y) (v := a) (w := xStar - aStar))
              simp [hadd]
        _ = (y ⬝ᵥ b' + a ⬝ᵥ (xStar - aStar) - (μ + α) : Real) := by simp [hdot_inv]
        _ = (y ⬝ᵥ b' - (μ + α - a ⬝ᵥ (xStar - aStar)) : Real) := by ring
        _ = y ⬝ᵥ b' - μ' := by simp [hμ']
    -- Finish.
    have hx1' := hx1
    rw [hterm] at hx1'
    rw [hAx] at hx1'
    exact hx1'
  · intro hy x
    -- Set `y = A(x-a)` and use the hypothesis on `y`.
    set y : Fin n → Real := A (x - a)
    have hy0 : ((y ⬝ᵥ b' - μ' : Real) : EReal) ≤ h y := hy y
    -- Rewrite the left-hand side in terms of `x`.
    have hdot :
        y ⬝ᵥ b' = (x - a) ⬝ᵥ (xStar - aStar) := by
      -- Apply the adjoint identity to `x-a` and `(A*)⁻¹(x*-a*)`.
      simpa [y, hb'] using (hAStar (x - a) (AStar.symm (xStar - aStar)))
    have hterm :
        (y ⬝ᵥ b' - μ' : Real) = x ⬝ᵥ (xStar - aStar) - (μ + α) := by
      calc
        (y ⬝ᵥ b' - μ' : Real) =
            ((x - a) ⬝ᵥ (xStar - aStar) - μ' : Real) := by simp [hdot]
        _ = (x ⬝ᵥ (xStar - aStar) - a ⬝ᵥ (xStar - aStar) - μ' : Real) := by
              simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
        _ = (x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) := by
              simp [hμ']
    have hy1 :
        ((x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) : EReal) ≤ h (A (x - a)) := by
      have : ((x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) : EReal) ≤ h y := by
        simpa [hterm] using hy0
      simpa [y] using this
    -- Add back the cancelled real constant.
    set c : Real := x ⬝ᵥ aStar + α
    have hc : AddLECancellable (c : EReal) := EReal.addLECancellable_coe c
    have hlhs :
        ((x ⬝ᵥ xStar - μ : Real) : EReal) =
          ((x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) : EReal) + (c : EReal) := by
      have hreal :
          (x ⬝ᵥ xStar - μ : Real) =
            (x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) + (x ⬝ᵥ aStar + α) := by
        simp [dotProduct_sub]
        ring
      simpa [c, EReal.coe_add] using congrArg (fun r : Real => (r : EReal)) hreal
    have hrhs :
        h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal) =
          h (A (x - a)) + (c : EReal) := by
      simp [c, add_assoc, EReal.coe_add]
    have hx' :
        ((x ⬝ᵥ (xStar - aStar) - (μ + α) : Real) : EReal) + (c : EReal) ≤
          h (A (x - a)) + (c : EReal) :=
      (hc.add_le_add_iff_right).2 hy1
    -- Rewrite back to the original affine inequality.
    have hx'' := hx'
    rw [← hlhs] at hx''
    rw [← hrhs] at hx''
    exact hx''

/-- Upper-bound equivalence for the Fenchel conjugate under the affine transformation in
Theorem 12.3. -/
lemma fenchelConjugate_affineTransform_le_coe_iff (n : Nat) (h : (Fin n → Real) → EReal)
    (A AStar : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real))
    (hAStar : ∀ x y : Fin n → Real, (A x) ⬝ᵥ y = x ⬝ᵥ AStar y) (a aStar : Fin n → Real)
    (α : Real) (xStar : Fin n → Real) (μ : Real) :
    let f : (Fin n → Real) → EReal :=
      fun x => h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal)
    let b' : Fin n → Real := AStar.symm (xStar - aStar)
    let μ' : Real := μ + α - (a ⬝ᵥ (xStar - aStar))
    fenchelConjugate n f xStar ≤ (μ : EReal) ↔ fenchelConjugate n h b' ≤ (μ' : EReal) := by
  classical
  dsimp
  set b' : Fin n → Real := AStar.symm (xStar - aStar) with hb'
  set μ' : Real := μ + α - (a ⬝ᵥ (xStar - aStar)) with hμ'
  -- Expand both sides using the affine-minorant characterization.
  constructor
  · intro hμ
    have hx :
        ∀ x : Fin n → Real,
          ((x ⬝ᵥ xStar - μ : Real) : EReal) ≤
            h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal) :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n)
            (f := fun x => h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal)) (b := xStar)
            (μ := μ)).1 hμ
    have hy :
        ∀ y : Fin n → Real, ((y ⬝ᵥ b' - μ' : Real) : EReal) ≤ h y := by
      simpa [hb', hμ'] using
        (affineTransform_pointwise_inequality_iff (n := n) (h := h) (A := A) (AStar := AStar)
              hAStar (a := a) (aStar := aStar) (α := α) (xStar := xStar) (μ := μ)).1 hx
    exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := h) (b := b') (μ := μ')).2 hy
  · intro hμ
    have hy :
        ∀ y : Fin n → Real, ((y ⬝ᵥ b' - μ' : Real) : EReal) ≤ h y :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := h) (b := b') (μ := μ')).1 hμ
    have hx :
        ∀ x : Fin n → Real,
          ((x ⬝ᵥ xStar - μ : Real) : EReal) ≤
            h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal) := by
      simpa [hb', hμ'] using
        (affineTransform_pointwise_inequality_iff (n := n) (h := h) (A := A) (AStar := AStar)
              hAStar (a := a) (aStar := aStar) (α := α) (xStar := xStar) (μ := μ)).2 hy
    exact
      (fenchelConjugate_le_coe_iff_affine_le (n := n)
            (f := fun x => h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal)) (b := xStar)
            (μ := μ)).2 hx

/-- Theorem 12.3. Let `h` be a convex function on `ℝ^n`, and define
`f(x) = h(A(x - a)) + ⟪x, a^*⟫ + α`, where `A` is a one-to-one linear transformation of `ℝ^n`,
`a` and `a^*` are vectors in `ℝ^n`, and `α ∈ ℝ`. Then
`f^*(x^*) = h^*(A^{*-1}(x^* - a^*)) + ⟪x^*, a⟫ + α^*`, where `A^*` is the adjoint of `A` and
`α^* = -α - ⟪a, a^*⟫`. Here `f^*` and `h^*` are represented by `fenchelConjugate`. -/
theorem fenchelConjugate_affineTransform (n : Nat) (h : (Fin n → Real) → EReal)
    (A : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real))
    (AStar : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real))
    (hAStar : ∀ x y : Fin n → Real, (A x) ⬝ᵥ y = x ⬝ᵥ AStar y) (a aStar : Fin n → Real)
    (α : Real) :
    let f : (Fin n → Real) → EReal :=
      fun x => h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal)
    let αStar : Real := -α - (a ⬝ᵥ aStar)
    fenchelConjugate n f =
      fun xStar =>
        fenchelConjugate n h (AStar.symm (xStar - aStar)) + ((xStar ⬝ᵥ a : Real) : EReal) +
          (αStar : EReal) := by
  classical
  -- Unfold the `let`-bindings.
  dsimp
  funext xStar
  -- Compare `EReal` values via their real upper bounds.
  refine
    EReal.eq_of_forall_le_coe_iff (a := fenchelConjugate n
        (fun x => h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal)) xStar)
      (b :=
        fenchelConjugate n h (AStar.symm (xStar - aStar)) + ((xStar ⬝ᵥ a : Real) : EReal) +
          ((-α - (a ⬝ᵥ aStar) : Real) : EReal))
      (fun μ => ?_)
  -- Rewrite the right-hand side inequality by cancelling the real affine correction.
  have hcancel :
      (fenchelConjugate n h (AStar.symm (xStar - aStar)) + ((xStar ⬝ᵥ a : Real) : EReal) +
              ((-α - (a ⬝ᵥ aStar) : Real) : EReal) ≤ (μ : EReal)) ↔
        fenchelConjugate n h (AStar.symm (xStar - aStar)) ≤
          ((μ + α - (a ⬝ᵥ (xStar - aStar)) : Real) : EReal) := by
    -- Combine the two real constants into one.
    have hadd :
        (fenchelConjugate n h (AStar.symm (xStar - aStar)) + ((xStar ⬝ᵥ a : Real) : EReal) +
              ((-α - (a ⬝ᵥ aStar) : Real) : EReal)) =
          fenchelConjugate n h (AStar.symm (xStar - aStar)) +
            ((xStar ⬝ᵥ a + (-α - (a ⬝ᵥ aStar)) : Real) : EReal) := by
      simp [add_assoc, EReal.coe_add]
    -- `μ - (xStar·a + α*) = μ + α - a·(xStar-a*)`.
    have hμ' :
        (μ - (xStar ⬝ᵥ a + (-α - (a ⬝ᵥ aStar)) : Real) : Real) =
          (μ + α - (a ⬝ᵥ (xStar - aStar)) : Real) := by
      -- Use commutativity of the dot product to match the book's `a·x*` notation.
      simp [sub_eq_add_neg, dotProduct_comm]
      ring
    -- Apply cancellation for `EReal` addition by a real.
    -- First rewrite to the single-constant form, then cancel.
    simpa [hadd, hμ', add_assoc] using
      (ereal_add_coe_le_coe_iff_cancel
            (t := fenchelConjugate n h (AStar.symm (xStar - aStar)))
            (c := (xStar ⬝ᵥ a + (-α - (a ⬝ᵥ aStar)) : Real)) (μ := μ))
  -- The left-hand side inequality is equivalent to the shifted inequality for `h*`.
  have hshift :
      (fenchelConjugate n
            (fun x => h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal)) xStar ≤
          (μ : EReal)) ↔
        fenchelConjugate n h (AStar.symm (xStar - aStar)) ≤
          ((μ + α - (a ⬝ᵥ (xStar - aStar)) : Real) : EReal) := by
    simpa using
      (fenchelConjugate_affineTransform_le_coe_iff (n := n) (h := h) (A := A) (AStar := AStar)
            hAStar (a := a) (aStar := aStar) (α := α) (xStar := xStar) (μ := μ))
  -- Combine the equivalences.
  constructor
  · intro hμ
    have := (hshift).1 hμ
    exact (hcancel).2 this
  · intro hμ
    have := (hcancel).1 hμ
    exact (hshift).2 this

/-- Simplify the Fenchel-conjugate range term for a Tucker-type partial affine function.

Outside the primal constraint set, the function value is `⊤` and the range term is `⊥`. -/
lemma range_term_partialAffine_tucker_simp (n m : Nat) (α00 : Real) (α0 : Fin n → Real)
    (αi0 : Fin m → Real) (α : Fin m → Fin n → Real) (x xStar : Fin (n + m) → Real) :
    let f : (Fin (n + m) → Real) → EReal :=
      fun y =>
        if _ :
            (∀ i : Fin m,
              y (Fin.natAdd n i) =
                (∑ j : Fin n, α i j * y (Fin.castAdd m j)) - αi0 i) then
          ((∑ j : Fin n, α0 j * y (Fin.castAdd m j) - α00 : Real) : EReal)
        else
          ⊤
    (((x ⬝ᵥ xStar : Real) : EReal) - f x) =
      if _ :
          (∀ i : Fin m,
            x (Fin.natAdd n i) =
              (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) then
        ((x ⬝ᵥ xStar - (∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00) : Real) : EReal)
      else
        ⊥ := by
  classical
  dsimp
  by_cases hx :
      (∀ i : Fin m,
        x (Fin.natAdd n i) =
          (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i)
  · -- Feasible: subtracting a real value stays finite.
    simp [hx]
  · -- Infeasible: subtracting `⊤` yields `⊥`.
    simp [hx]

/-- Expand the real expression `⟪x,x*⟫ - f(x)` for a Tucker-type partial affine function under the
primal feasibility constraint, grouping the free coordinates `x (Fin.castAdd m ·)`. -/
lemma range_term_partialAffine_tucker_real_formula (n m : Nat) (α00 : Real) (α0 : Fin n → Real)
    (αi0 : Fin m → Real) (α : Fin m → Fin n → Real) (x xStar : Fin (n + m) → Real)
    (hx :
      ∀ i : Fin m,
        x (Fin.natAdd n i) =
          (∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) :
    let xHead : Fin n → Real := fun j => x (Fin.castAdd m j)
    let coeff : Fin n → Real :=
      fun j =>
        xStar (Fin.castAdd m j) + (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j
    let const : Real := α00 - (∑ i : Fin m, αi0 i * xStar (Fin.natAdd n i))
    x ⬝ᵥ xStar - (∑ j : Fin n, α0 j * xHead j - α00) =
      (∑ j : Fin n, xHead j * coeff j) + const := by
  classical
  dsimp
  -- Split the dot product into head and tail sums, and rewrite the tail coordinates using `hx`.
  have hdot :
      x ⬝ᵥ xStar =
        (∑ j : Fin n, x (Fin.castAdd m j) * xStar (Fin.castAdd m j)) +
          (∑ i : Fin m,
              ((∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) *
                xStar (Fin.natAdd n i)) := by
    simp [dotProduct, Fin.sum_univ_add, hx]
  -- Separate the tail sum into the part linear in the head variables and the constant part.
  have htail :
      (∑ i : Fin m,
          ((∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) * xStar (Fin.natAdd n i)) =
        (∑ i : Fin m,
              (∑ j : Fin n, α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i)) -
          (∑ i : Fin m, αi0 i * xStar (Fin.natAdd n i)) := by
    simp [sub_mul, Finset.sum_sub_distrib]
  -- Swap the order of summation in the bilinear term.
  have hswap :
      (∑ i : Fin m,
          (∑ j : Fin n, α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i)) =
        ∑ j : Fin n, x (Fin.castAdd m j) * (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) := by
    -- Expand the inner sum and swap, then factor out the head coordinate.
    calc
      (∑ i : Fin m,
          (∑ j : Fin n, α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i)) =
          ∑ i : Fin m,
            ∑ j : Fin n, (α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simpa [mul_assoc] using
                (Finset.sum_mul (s := Finset.univ)
                  (f := fun j : Fin n => α i j * x (Fin.castAdd m j))
                  (a := xStar (Fin.natAdd n i)))
      _ = ∑ j : Fin n,
            ∑ i : Fin m, (α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i) := by
            simpa using
              (Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))
                (t := (Finset.univ : Finset (Fin n)))
                (f := fun i j => (α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i)))
      _ = ∑ j : Fin n,
            x (Fin.castAdd m j) * (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            -- Factor `x (Fin.castAdd m j)` out of the sum over `i`.
            calc
              (∑ i : Fin m, (α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i)) =
                  ∑ i : Fin m,
                    x (Fin.castAdd m j) * (α i j * xStar (Fin.natAdd n i)) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                simp [mul_left_comm, mul_comm]
              _ = x (Fin.castAdd m j) * (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) := by
                simpa using
                  (Finset.mul_sum (a := x (Fin.castAdd m j)) (s := Finset.univ)
                    (f := fun i : Fin m => α i j * xStar (Fin.natAdd n i))).symm
  -- Assemble and group by head variables.
  calc
    x ⬝ᵥ xStar - (∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00) =
        ((∑ j : Fin n, x (Fin.castAdd m j) * xStar (Fin.castAdd m j)) +
            (∑ i : Fin m,
                ((∑ j : Fin n, α i j * x (Fin.castAdd m j)) - αi0 i) *
                  xStar (Fin.natAdd n i))) -
          (∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00) := by
        simp [hdot]
    _ =
        ((∑ j : Fin n, x (Fin.castAdd m j) * xStar (Fin.castAdd m j)) +
            ((∑ i : Fin m,
                  (∑ j : Fin n, α i j * x (Fin.castAdd m j)) * xStar (Fin.natAdd n i)) -
              (∑ i : Fin m, αi0 i * xStar (Fin.natAdd n i)))) -
          (∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00) := by
        simp [htail]
    _ =
        ((∑ j : Fin n, x (Fin.castAdd m j) * xStar (Fin.castAdd m j)) +
            (∑ j : Fin n,
              x (Fin.castAdd m j) * (∑ i : Fin m, α i j * xStar (Fin.natAdd n i))) -
            (∑ i : Fin m, αi0 i * xStar (Fin.natAdd n i))) -
          (∑ j : Fin n, α0 j * x (Fin.castAdd m j) - α00) := by
        simp [hswap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ =
        ((∑ j : Fin n,
              x (Fin.castAdd m j) *
                (xStar (Fin.castAdd m j) + (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j)) +
            (α00 - (∑ i : Fin m, αi0 i * xStar (Fin.natAdd n i)))) := by
        -- Group the head sums and collect the remaining constant term.
        ring_nf
        -- Normalize the grouped head sum using linearity of `∑`.
        -- The remaining goals are purely about distributing multiplication over addition/subtraction.
        simp [Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]
    _ = (∑ j : Fin n,
            x (Fin.castAdd m j) *
              (xStar (Fin.castAdd m j) + (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j)) +
          (α00 - (∑ i : Fin m, αi0 i * xStar (Fin.natAdd n i))) := by
        rfl

/-- The dual feasibility constraint in Tucker form is equivalent to vanishing of the
coefficients of the free primal variables in the conjugate range term. -/
lemma tucker_dualConstraint_iff_coeff_eq_zero (n m : Nat) (α0 : Fin n → Real)
    (α : Fin m → Fin n → Real) (xStar : Fin (n + m) → Real) :
    let coeff : Fin n → Real :=
      fun j =>
        xStar (Fin.castAdd m j) + (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j
    (∀ j : Fin n,
        xStar (Fin.castAdd m j) =
          (∑ i : Fin m, (-α i j) * xStar (Fin.natAdd n i)) + α0 j) ↔
      (∀ j : Fin n, coeff j = 0) := by
  classical
  dsimp
  constructor
  · intro hxStar j
    -- Substitute the dual constraint and simplify the coefficient.
    calc
      xStar (Fin.castAdd m j) + (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j
          =
          ((∑ i : Fin m, (-α i j) * xStar (Fin.natAdd n i)) + α0 j) +
              (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j := by
              simp [hxStar j]
      _ = (∑ i : Fin m, (-α i j) * xStar (Fin.natAdd n i)) +
            (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) := by
            ring
      _ = 0 := by
            simp
  · intro hcoeff j
    -- Extract the equality `xStar_head = α0 - ∑ α * tail` from `coeff j = 0`.
    have h0 : xStar (Fin.castAdd m j) + (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) - α0 j = 0 :=
      hcoeff j
    have hx :
        xStar (Fin.castAdd m j) =
          α0 j - (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) := by
      linarith [h0]
    -- Rewrite the right-hand side as a sum over `(-α)`.
    calc
      xStar (Fin.castAdd m j)
          = α0 j - (∑ i : Fin m, α i j * xStar (Fin.natAdd n i)) := hx
      _ = (∑ i : Fin m, (-α i j) * xStar (Fin.natAdd n i)) + α0 j := by
        simp [sub_eq_add_neg, add_comm]

/-- If some coefficient in a linear form is nonzero, we can choose the variables to make the form
arbitrarily large (even achieving any prescribed value up to a constant shift). -/
lemma exists_head_makes_linear_combo_arbitrarily_large {n : Nat} (coeff : Fin n → Real)
    (const : Real) (hcoeff : ∃ j : Fin n, coeff j ≠ 0) :
    ∀ μ : Real, ∃ xHead : Fin n → Real, μ ≤ (∑ j : Fin n, xHead j * coeff j) + const := by
  classical
  intro μ
  rcases hcoeff with ⟨j, hj⟩
  let t : Real := (μ - const) / coeff j
  refine ⟨fun k : Fin n => if k = j then t else 0, ?_⟩
  have hsum :
      (∑ k : Fin n, (if k = j then t else 0) * coeff k) = t * coeff j := by
    simp
  have ht : t * coeff j = μ - const := by
    dsimp [t]
    field_simp [hj]
  -- Conclude by computation.
  have : (∑ k : Fin n, (if k = j then t else 0) * coeff k) + const = μ := by
    calc
      (∑ k : Fin n, (if k = j then t else 0) * coeff k) + const
          = (t * coeff j) + const := by simp
      _ = (μ - const) + const := by simp [ht]
      _ = μ := by ring
  exact le_of_eq this.symm

end Section12
end Chap03
