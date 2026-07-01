/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part8

section Chap03
section Section12

/-- Translation identity for the shifted argument: rewrite `quadraticHalfLinear n Q (x - a)` in
terms of `quadraticHalfLinear n Q x`, plus a linear term and a constant, assuming dot-product
symmetry of `Q`. -/
lemma quadraticHalfLinear_translate_sub_of_dotProduct_symmetric {n : Nat}
    (Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real))
    (hQsymm : ∀ x y : Fin n → Real, (Q x) ⬝ᵥ y = x ⬝ᵥ Q y) :
    ∀ a x : Fin n → Real,
      quadraticHalfLinear n Q (x - a) =
        quadraticHalfLinear n Q x + ((x ⬝ᵥ (-Q a) : Real) : EReal) +
          (((1 / 2 : Real) * (a ⬝ᵥ Q a) : Real) : EReal) := by
  classical
  intro a x
  -- Work in `Real`, then coerce to `EReal`.
  have hax : (a ⬝ᵥ Q x : Real) = (x ⬝ᵥ Q a : Real) := by
    calc
      (a ⬝ᵥ Q x : Real) = (Q x ⬝ᵥ a : Real) := by simp [dotProduct_comm]
      _ = (x ⬝ᵥ Q a : Real) := by simpa using (hQsymm x a)
  have h_expand :
      (x - a) ⬝ᵥ Q (x - a) =
        (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ Q a : Real) + (a ⬝ᵥ Q a : Real) := by
    calc
      (x - a) ⬝ᵥ Q (x - a) =
          (x ⬝ᵥ Q x : Real) - (x ⬝ᵥ Q a : Real) - (a ⬝ᵥ Q x : Real) + (a ⬝ᵥ Q a : Real) := by
            simp [sub_eq_add_neg, add_dotProduct, dotProduct_add, map_add, map_neg, add_assoc,
              add_comm, add_left_comm]
      _ = (x ⬝ᵥ Q x : Real) - 2 * (x ⬝ᵥ Q a : Real) + (a ⬝ᵥ Q a : Real) := by
            nlinarith [hax]
  have hreal :
      (1 / 2 : Real) * ((x - a) ⬝ᵥ Q (x - a) : Real) =
        (1 / 2 : Real) * (x ⬝ᵥ Q x : Real) - (x ⬝ᵥ Q a : Real) +
          (1 / 2 : Real) * (a ⬝ᵥ Q a : Real) := by
    rw [h_expand]
    ring
  have hE :
      (((1 / 2 : Real) * ((x - a) ⬝ᵥ Q (x - a)) : Real) : EReal) =
        (((1 / 2 : Real) * (x ⬝ᵥ Q x) : Real) : EReal) + ((x ⬝ᵥ (-Q a) : Real) : EReal) +
          (((1 / 2 : Real) * (a ⬝ᵥ Q a) : Real) : EReal) := by
    -- Coerce the real identity into `EReal` and rewrite `-(x ⬝ᵥ Q a)` as `x ⬝ᵥ (-Q a)`.
    have hxneg : (x ⬝ᵥ (-Q a) : Real) = -(x ⬝ᵥ Q a : Real) := by
      simp [dotProduct]
    have hE' :
        (((1 / 2 : Real) * ((x - a) ⬝ᵥ Q (x - a)) : Real) : EReal) =
          (((1 / 2 : Real) * (x ⬝ᵥ Q x) : Real) : EReal) + ((-(x ⬝ᵥ Q a) : Real) : EReal) +
            (((1 / 2 : Real) * (a ⬝ᵥ Q a) : Real) : EReal) := by
      exact_mod_cast hreal
    simpa [hxneg, add_assoc, add_left_comm, add_comm] using hE'
  simpa [quadraticHalfLinear, add_assoc, add_left_comm, add_comm] using hE

/-- Convexity of the square function: `t ↦ ((1 - t)a + t b)^2` lies below the chord between
`a^2` and `b^2` for `t ∈ [0,1]`. -/
lemma sq_segment_le (a b t : Real) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) * a + t * b) ^ 2 ≤ (1 - t) * (a ^ 2) + t * (b ^ 2) := by
  have h : 0 ≤ t * (1 - t) * (a - b) ^ 2 := by
    have : 0 ≤ t * (1 - t) := by nlinarith
    exact mul_nonneg this (sq_nonneg (a - b))
  -- Expand and simplify.
  nlinarith [h]

/-- A weighted diagonal quadratic function with nonnegative weights is a proper convex function
on `ℝ^n`. -/
lemma properConvexFunctionOn_diagonalQuadratic {n : Nat} (d : Fin n → Real)
    (hd : ∀ i : Fin n, 0 ≤ d i) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x =>
        (((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real) : EReal)) := by
  classical
  let q : (Fin n → Real) → EReal :=
    fun x => (((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real) : EReal)
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), q x ≠ (⊥ : EReal) := by
    intro x hx
    simpa [q] using
      (EReal.coe_ne_bot ((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real))
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) q := by
    refine
      (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := q)
          (hC := convex_univ) (hnotbot := hnotbot)).2 ?_
    intro x hx y hy t ht0 ht1
    -- Reduce to a real inequality.
    have ht0' : 0 ≤ t := le_of_lt ht0
    have ht1' : t ≤ 1 := le_of_lt ht1
    have hsq :
        ∀ i : Fin n,
          ((1 - t) * x i + t * y i) ^ 2 ≤ (1 - t) * (x i) ^ 2 + t * (y i) ^ 2 := by
      intro i
      simpa [mul_assoc, mul_left_comm, mul_comm] using sq_segment_le (a := x i) (b := y i)
        (t := t) ht0' ht1'
    have hterm :
        ∀ i : Fin n,
          d i * (((1 - t) * x i + t * y i) ^ 2) ≤
            d i * ((1 - t) * (x i) ^ 2 + t * (y i) ^ 2) := by
      intro i
      exact mul_le_mul_of_nonneg_left (hsq i) (hd i)
    have hsum :
        ∑ i : Fin n, d i * (((1 - t) * x i + t * y i) ^ 2) ≤
          ∑ i : Fin n, d i * ((1 - t) * (x i) ^ 2 + t * (y i) ^ 2) := by
      exact Finset.sum_le_sum (fun i hi => hterm i)
    have hsum' :
        ∑ i : Fin n, d i * ((1 - t) * (x i) ^ 2 + t * (y i) ^ 2) =
          (1 - t) * (∑ i : Fin n, d i * (x i) ^ 2) + t * (∑ i : Fin n, d i * (y i) ^ 2) := by
      -- Distribute and factor.
      simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm,
        mul_comm]
    have hreal :
        (1 / 2 : Real) * (∑ i : Fin n, d i * (((1 - t) * x i + t * y i) ^ 2)) ≤
          (1 - t) * ((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2)) +
            t * ((1 / 2 : Real) * (∑ i : Fin n, d i * (y i) ^ 2)) := by
      have : (1 / 2 : Real) * (∑ i : Fin n, d i * (((1 - t) * x i + t * y i) ^ 2)) ≤
          (1 / 2 : Real) *
            ((1 - t) * (∑ i : Fin n, d i * (x i) ^ 2) + t * (∑ i : Fin n, d i * (y i) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (le_trans hsum (le_of_eq hsum')) (by norm_num)
      -- Rearrange scalar factors.
      nlinarith
    -- Coerce to `EReal` and finish.
    have hE : q ((1 - t) • x + t • y) ≤
        ((1 - t : Real) : EReal) * q x + ((t : Real) : EReal) * q y := by
      -- `q` is real-valued, so `simp` turns the inequality into `hreal`.
      simpa [q, smul_eq_mul, Pi.add_apply, Pi.smul_apply, add_mul, mul_add, EReal.coe_add,
        EReal.coe_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        using (show (( (1 / 2 : Real) * (∑ i : Fin n, d i * (((1 - t) * x i + t * y i) ^ 2))
            : Real) : EReal) ≤
          ((( (1 - t) * ((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2)) +
              t * ((1 / 2 : Real) * (∑ i : Fin n, d i * (y i) ^ 2)) : Real) : EReal)) from
          (by exact_mod_cast hreal))
    simpa [q] using hE
  refine ⟨hconv, ?_, ?_⟩
  · refine ⟨(0, ((1 / 2 : Real) * (∑ i : Fin n, d i * (0 : Real) ^ 2) : Real)), ?_⟩
    refine And.intro (by trivial) ?_
    simp
  · intro x hx
    exact hnotbot x (by simp)

/-- Elementary partial quadratic convex functions are proper convex on `Set.univ`. -/
lemma properConvexFunctionOn_elementaryPartialQuadratic {n : Nat}
    {h : (Fin n → Real) → EReal} (hElem : IsElementaryPartialQuadraticConvexFunction n h) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h := by
  classical
  rcases hElem with ⟨d, L, hd, rfl⟩
  have hq : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x => (((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real) : EReal)) :=
    properConvexFunctionOn_diagonalQuadratic (n := n) d hd
  have hind :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (indicatorFunction (L : Set (Fin n → Real))) := by
    -- A submodule is convex and nonempty (contains `0`).
    have hconv : Convex ℝ (L : Set (Fin n → Real)) := by
      simpa using L.convex
    have hne : Set.Nonempty (L : Set (Fin n → Real)) := ⟨0, by simp⟩
    simpa using
      (properConvexFunctionOn_indicator_of_convex_of_nonempty (n := n) (C := (L : Set (Fin n → Real)))
        hconv hne)
  -- Convexity of the sum follows from Theorem 5.2.
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x =>
          (((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real) : EReal) +
            indicatorFunction (L : Set (Fin n → Real)) x) := by
    exact convexFunctionOn_add_of_proper (n := n) (f1 := fun x =>
      (((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real) : EReal))
      (f2 := indicatorFunction (L : Set (Fin n → Real))) hq hind
  refine ⟨hconv, ?_, ?_⟩
  · refine ⟨(0, 0), ?_⟩
    refine And.intro (by trivial) ?_
    simp [indicatorFunction]
  · intro x hx
    by_cases hxL : x ∈ (L : Set (Fin n → Real))
    ·
      simpa [indicatorFunction, hxL] using
        (EReal.coe_ne_bot ((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real))
    ·
      simpa [indicatorFunction, hxL] using
        (EReal.coe_ne_bot ((1 / 2 : Real) * (∑ i : Fin n, d i * (x i) ^ 2) : Real))

/-- Precomposition by a linear equivalence preserves proper convexity on `Set.univ`. -/
lemma properConvexFunctionOn_precomp_linearEquiv {n : Nat}
    (A : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real)) {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => f (A x)) := by
  classical
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => f (A x)) := by
    -- Convexity is stable under linear precomposition (Theorem 5.7).
    exact convexFunctionOn_precomp_linearMap (n := n) (m := n) (A := A.toLinearMap) f hf.1
  have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (fun x => f (A x))) := by
    rcases hf.2.1 with ⟨p, hp⟩
    have hp_mem : (Set.univ : Set (Fin n → Real)) p.1 ∧ f p.1 ≤ (p.2 : EReal) := by
      simpa [epigraph] using hp
    have hp' : f p.1 ≤ (p.2 : EReal) := hp_mem.2
    refine ⟨(A.symm p.1, p.2), ?_⟩
    refine And.intro (by trivial) ?_
    simpa [A.apply_symm_apply] using hp'
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), f (A x) ≠ (⊥ : EReal) := by
    intro x hx
    exact hf.2.2 (A x) (by simp)
  exact ⟨hconv, hne, hnotbot⟩

/-- Translating the input preserves proper convexity on `Set.univ`. -/
lemma properConvexFunctionOn_translate {n : Nat} (a : Fin n → Real)
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => f (x - a)) := by
  classical
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), f (x - a) ≠ (⊥ : EReal) := by
    intro x hx
    exact hf.2.2 (x - a) (by simp)
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => f (x - a)) := by
    -- Use the segment inequality characterization and rewrite by translation.
    refine
      (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := fun x => f (x - a))
          (hC := convex_univ) (hnotbot := hnotbot)).2 ?_
    intro x hx y hy t ht0 ht1
    have hseg :=
      (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
          (hC := convex_univ) (hnotbot := hf.2.2)).1 hf.1 (x - a) (by simp) (y - a) (by simp) t
        ht0 ht1
    have hlin : ((1 - t) • x + t • y) - a = (1 - t) • (x - a) + t • (y - a) := by
      -- Affine combination commutes with translation.
      ext i
      simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg, smul_eq_mul, add_mul]
      ring
    simpa [hlin] using hseg
  have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (fun x => f (x - a))) := by
    rcases hf.2.1 with ⟨p, hp⟩
    have hp_mem : (Set.univ : Set (Fin n → Real)) p.1 ∧ f p.1 ≤ (p.2 : EReal) := by
      simpa [epigraph] using hp
    have hp' : f p.1 ≤ (p.2 : EReal) := hp_mem.2
    refine ⟨(p.1 + a, p.2), ?_⟩
    refine And.intro (by trivial) ?_
    simpa [add_sub_cancel] using hp'
  exact ⟨hconv, hne, hnotbot⟩

/-- The affine function `x ↦ ⟪x, v⟫ + α` is a proper convex function on `Set.univ`. -/
lemma properConvexFunctionOn_affine_dotProduct {n : Nat} (v : Fin n → Real) (α : Real) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x => ((x ⬝ᵥ v + α : Real) : EReal)) := by
  classical
  let g : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ v + α : Real) : EReal)
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), g x ≠ (⊥ : EReal) := by
    intro x hx
    dsimp [g]
    exact EReal.coe_ne_bot (x ⬝ᵥ v + α)
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) g := by
    refine
      (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := g)
          (hC := convex_univ) (hnotbot := hnotbot)).2 ?_
    intro x hx y hy t ht0 ht1
    have hlin :
        ((1 - t) • x + t • y) ⬝ᵥ v + α =
          (1 - t) * (x ⬝ᵥ v + α) + t * (y ⬝ᵥ v + α) := by
      calc
        ((1 - t) • x + t • y) ⬝ᵥ v + α =
            (((1 - t) • x) ⬝ᵥ v) + ((t • y) ⬝ᵥ v) + α := by
              simp [add_dotProduct, add_assoc]
        _ = (1 - t) * (x ⬝ᵥ v) + t * (y ⬝ᵥ v) + α := by
              simp [smul_dotProduct, smul_eq_mul, add_assoc, mul_comm]
        _ = (1 - t) * (x ⬝ᵥ v + α) + t * (y ⬝ᵥ v + α) := by ring
    -- The desired inequality holds as an equality in `EReal` (everything is finite).
    have hreal :
        g ((1 - t) • x + t • y) =
          ((1 - t : Real) : EReal) * g x + ((t : Real) : EReal) * g y := by
      dsimp [g]
      -- Cast the real identity `hlin` into `EReal` and rewrite the right-hand side using
      -- `EReal.coe_add`/`EReal.coe_mul`.
      have hlinE :
          (((((1 - t) • x + t • y) ⬝ᵥ v + α) : Real) : EReal) =
            ((((1 - t) * (x ⬝ᵥ v + α) + t * (y ⬝ᵥ v + α) : Real)) : EReal) := by
        exact_mod_cast hlin
      calc
        (((((1 - t) • x + t • y) ⬝ᵥ v + α) : Real) : EReal) =
            ((((1 - t) * (x ⬝ᵥ v + α) + t * (y ⬝ᵥ v + α) : Real)) : EReal) := hlinE
        _ =
            (((((1 - t) * (x ⬝ᵥ v + α) : Real)) : EReal)) +
              ((((t * (y ⬝ᵥ v + α) : Real)) : EReal)) := by
              simp [EReal.coe_add]
        _ =
            ((1 - t : Real) : EReal) * (((x ⬝ᵥ v + α : Real) : EReal)) +
              ((t : Real) : EReal) * (((y ⬝ᵥ v + α : Real) : EReal)) := by
              simp [EReal.coe_mul]
    exact le_of_eq hreal
  refine ⟨hconv, ?_, ?_⟩
  · refine ⟨(0, (α : Real)), ?_⟩
    refine And.intro (by trivial) ?_
    simp
  · intro x hx
    dsimp [g]
    exact EReal.coe_ne_bot (x ⬝ᵥ v + α)

/-- Text 12.3.3: Characterization of partial quadratic convex functions by affine change of
coordinates to an elementary partial quadratic convex function plus a linear term. -/
theorem isPartialQuadraticConvexFunction_iff_exists_elementary_affine (n : Nat)
    (f : (Fin n → Real) → EReal) :
    IsPartialQuadraticConvexFunction n f ↔
      ∃ (h : (Fin n → Real) → EReal) (A : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real))
        (a aStar : Fin n → Real) (α : Real),
        IsElementaryPartialQuadraticConvexFunction n h ∧
          f =
            fun x =>
              h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal) := by
  classical
  constructor
  · intro hf
    rcases hf with ⟨hfprop, Q, b, c, M, hpsd, hfEq⟩
    -- Extract a base point `a ∈ M` from properness.
    let r : (Fin n → Real) → EReal :=
      fun x => quadraticHalfLinear n Q x + ((x ⬝ᵥ b : Real) : EReal) + (c : EReal)
    have hr_ne_bot : ∀ x : Fin n → Real, r x ≠ (⊥ : EReal) := by
      intro x
      have :
          r x =
            (((1 / 2 : Real) * (x ⬝ᵥ Q x) + (x ⬝ᵥ b) + c : Real) : EReal) := by
        simp [r, quadraticHalfLinear]
      simpa [this] using
        (EReal.coe_ne_bot ((1 / 2 : Real) * (x ⬝ᵥ Q x) + (x ⬝ᵥ b) + c))
    have hMne : ∃ a : Fin n → Real, a ∈ M := by
      refine
        exists_mem_affineSubspace_of_proper_of_eq_indicator (f := f) (r := r) (M := M) hfprop
          hr_ne_bot ?_
      -- The `r` term is exactly the finite part of the given representation of `f`.
      simpa [r] using hfEq
    rcases hMne with ⟨a, haM⟩
    have hind :
        ∀ x : Fin n → Real,
          indicatorFunction (M : Set (Fin n → Real)) x =
            indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) :=
      indicatorFunction_affineSubspace_eq_indicator_direction_sub (M := M) haM
    have hfEq' :
        f =
          fun x =>
            quadraticHalfLinear n Q x + ((x ⬝ᵥ b : Real) : EReal) + (c : EReal) +
              indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) := by
      funext x
      simp [hfEq, hind x]
    -- From here one should:
    -- (1) replace `Q` by its symmetric part without changing `x ⬝ᵥ Q x`,
    -- (2) diagonalize the resulting quadratic form by a linear equivalence `A`,
    -- (3) transport the direction submodule by `A`,
    -- and (4) collect linear/constant terms into `aStar` and `α`.
    -- This is the remaining (nontrivial) linear-algebra step of Text 12.3.3.
    rcases linearMap_symmPart_dotProduct_preserves_quadratic (n := n) Q with
      ⟨Qs, hQs_symm, hQs_quad⟩
    have hpsdQs : ∀ x : Fin n → Real, 0 ≤ x ⬝ᵥ Qs x := by
      intro x
      simpa [hQs_quad x] using hpsd x
    have hfEqQs :
        f =
          fun x =>
            quadraticHalfLinear n Qs x + ((x ⬝ᵥ b : Real) : EReal) + (c : EReal) +
              indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) := by
      funext x
      -- `quadraticHalfLinear` depends only on `x ⬝ᵥ Q x`.
      have hq :
          quadraticHalfLinear n Q x = quadraticHalfLinear n Qs x := by
        simp [quadraticHalfLinear, hQs_quad x]
      simp [hfEq', hq]
    -- Translate the symmetric quadratic term so everything depends on `(x - a)`.
    have htrans :
        ∀ x : Fin n → Real,
          quadraticHalfLinear n Qs x =
            quadraticHalfLinear n Qs (x - a) + ((x ⬝ᵥ Qs a : Real) : EReal) +
              (((-(1 / 2 : Real)) * (a ⬝ᵥ Qs a) : Real) : EReal) :=
      quadraticHalfLinear_translate_of_dotProduct_symmetric (Q := Qs) hQs_symm a
    -- Diagonalize the dot-product symmetric positive semidefinite operator `Qs`.
    rcases
        exists_linearEquiv_diagonalize_psd_dotProduct (n := n) (Q := Qs) hQs_symm hpsdQs with
      ⟨A, d, hd, hdiag⟩
    -- Transport the direction submodule by `A.symm` so that it matches the `A (x-a)` coordinates.
    let L' : Submodule ℝ (Fin n → Real) := (M.direction).comap (A.symm.toLinearMap)
    let h : (Fin n → Real) → EReal :=
      fun z =>
        (((1 / 2 : Real) * (∑ i : Fin n, d i * (z i) ^ 2) : Real) : EReal) +
          indicatorFunction (L' : Set (Fin n → Real)) z
    refine ⟨h, A, a, (Qs a + b), (c + (-(1 / 2 : Real)) * (a ⬝ᵥ Qs a)), ?_, ?_⟩
    · refine ⟨d, L', hd, rfl⟩
    · -- Rewrite `f` into the required normal form.
      funext x
      have hquad :
          quadraticHalfLinear n Qs (x - a) =
            (((1 / 2 : Real) * (∑ i : Fin n, d i * (A (x - a) i) ^ 2) : Real) : EReal) := by
        unfold quadraticHalfLinear
        -- Rewrite the quadratic form using the diagonalization identity.
        rw [hdiag (x - a)]
      have hind :
          indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) =
            indicatorFunction (L' : Set (Fin n → Real)) (A (x - a)) := by
        -- Use `indicatorFunction_submodule_comap_linearEquiv` with `A.symm`.
        have :=
          indicatorFunction_submodule_comap_linearEquiv (n := n) (L := M.direction) (A := A.symm)
            (A (x - a))
        -- The lemma gives `indicator L' (A (x-a)) = indicator (M.direction) (x-a)`.
        simpa [L'] using this.symm
      -- Assemble all pieces without letting `simp` expand dot products aggressively.
      calc
        f x =
            quadraticHalfLinear n Qs x + ((x ⬝ᵥ b : Real) : EReal) + (c : EReal) +
              indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) := by
              simp [hfEqQs, add_assoc]
        _ =
            quadraticHalfLinear n Qs (x - a) + ((x ⬝ᵥ Qs a : Real) : EReal) +
                (((-(1 / 2 : Real)) * (a ⬝ᵥ Qs a) : Real) : EReal) +
              ((x ⬝ᵥ b : Real) : EReal) + (c : EReal) +
                indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) := by
              -- Rewrite the quadratic term using `htrans`.
              simp [htrans x, add_left_comm, add_comm]
        _ =
            quadraticHalfLinear n Qs (x - a) +
                indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) +
              ((x ⬝ᵥ (Qs a + b) : Real) : EReal) +
                ((c + (-(1 / 2 : Real)) * (a ⬝ᵥ Qs a) : Real) : EReal) := by
              -- Collect linear and constant terms.
              simp [dotProduct_add, add_assoc, add_left_comm, add_comm]
        _ =
            h (A (x - a)) + ((x ⬝ᵥ (Qs a + b) : Real) : EReal) +
              ((c + (-(1 / 2 : Real)) * (a ⬝ᵥ Qs a) : Real) : EReal) := by
              -- Rewrite the quadratic+indicator part into `h (A (x - a))`,
              -- then add the affine term.
              have hcore :
                  quadraticHalfLinear n Qs (x - a) +
                      indicatorFunction (M.direction : Set (Fin n → Real)) (x - a) =
                    h (A (x - a)) := by
                dsimp [h]
                rw [hquad, hind]
                rfl
              simpa using
                congrArg
                  (fun t =>
                    t + ((x ⬝ᵥ (Qs a + b) : Real) : EReal) +
                      ((c + (-(1 / 2 : Real)) * (a ⬝ᵥ Qs a) : Real) : EReal)) hcore
  · rintro ⟨h, A, a, aStar, α, hElem, hfEq⟩
    -- The reverse direction requires pushing the elementary diagonal quadratic and linear-subspace
    -- indicator through an affine change of variables, and rewriting it in the defining
    -- `q + δ(·|M)` form of `IsPartialQuadraticConvexFunction`.
    -- This is another bookkeeping-heavy linear-algebra step.
    -- First, establish proper convexity of `f` from the assumed normal form.
    have hhprop : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h :=
      properConvexFunctionOn_elementaryPartialQuadratic (n := n) (h := h) hElem
    have hhA :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => h (A x)) :=
      properConvexFunctionOn_precomp_linearEquiv (n := n) (A := A) hhprop
    have hhAT :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => h (A (x - a))) :=
      properConvexFunctionOn_translate (n := n) (a := a) hhA
    have hAffine :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (fun x => ((x ⬝ᵥ aStar + α : Real) : EReal)) :=
      properConvexFunctionOn_affine_dotProduct (n := n) (v := aStar) (α := α)
    have hfConvex :
        ConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (fun x => h (A (x - a)) + ((x ⬝ᵥ aStar + α : Real) : EReal)) := by
      exact
        convexFunctionOn_add_of_proper (n := n) (f1 := fun x => h (A (x - a)))
          (f2 := fun x => ((x ⬝ᵥ aStar + α : Real) : EReal)) hhAT hAffine
    have hfEq' :
        f =
          fun x =>
            h (A (x - a)) + ((x ⬝ᵥ aStar + α : Real) : EReal) := by
      funext x
      -- Combine the linear and constant terms into a single real coercion.
      simp [hfEq, add_assoc, add_comm, sub_eq_add_neg]
    have hf_notbot :
        ∀ x ∈ (Set.univ : Set (Fin n → Real)), f x ≠ (⊥ : EReal) := by
      intro x hx
      -- Both summands are never `⊥`.
      have h1 : h (A (x - a)) ≠ (⊥ : EReal) := hhAT.2.2 x (by simp)
      have h2 : ((x ⬝ᵥ aStar + α : Real) : EReal) ≠ (⊥ : EReal) := by simp
      simpa [hfEq', add_assoc] using add_ne_bot_of_notbot h1 h2
    have hf_epi : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f) := by
      -- Extract a point in the epigraph of `h` and transport it through `x ↦ A (x - a)`.
      rcases hhprop.2.1 with ⟨p, hp⟩
      have hp_mem : (Set.univ : Set (Fin n → Real)) p.1 ∧ h p.1 ≤ (p.2 : EReal) := by
        simpa [epigraph] using hp
      have hp_le : h p.1 ≤ (p.2 : EReal) := hp_mem.2
      let x0 : Fin n → Real := A.symm p.1 + a
      let μ0 : Real := p.2 + (x0 ⬝ᵥ aStar) + α
      refine ⟨(x0, μ0), ?_⟩
      have hx0 : (Set.univ : Set (Fin n → Real)) x0 := by trivial
      have hAx0 : A (x0 - a) = p.1 := by
        simp [x0, sub_eq_add_neg, add_left_comm, add_comm]
      have hle1 : h (A (x0 - a)) ≤ (p.2 : EReal) := by simpa [hAx0] using hp_le
      have hle2 :
          h (A (x0 - a)) + ((x0 ⬝ᵥ aStar + α : Real) : EReal) ≤ (μ0 : EReal) := by
        have :=
          add_le_add_right hle1 ((x0 ⬝ᵥ aStar + α : Real) : EReal)
        -- Rewrite the right-hand side as `μ0`.
        simpa [μ0, add_assoc, add_left_comm, add_comm, EReal.coe_add] using this
      simpa [epigraph, hfEq', hx0] using And.intro hx0 hle2
    have hfprop : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      refine ⟨?_, hf_epi, hf_notbot⟩
      -- Convexity follows from `hfConvex` and `hfEq'`.
      simpa [hfEq'] using hfConvex

    -- Now rewrite `f` in the `q + δ(·|M)` form of `IsPartialQuadraticConvexFunction`.
    rcases hElem with ⟨d, L, hd, hdef⟩
    -- Build `Q` so that `x ⬝ᵥ Q x = ∑ i, d i * (A x i)^2`.
    rcases exists_Q_of_linearEquiv_diag (n := n) (A := A) (d := d) with ⟨Q, hQsymm, hQquad⟩
    let L' : Submodule ℝ (Fin n → Real) := L.comap A.toLinearMap
    let M : AffineSubspace ℝ (Fin n → Real) := AffineSubspace.mk' a L'
    have haM : a ∈ M := by simp [M]
    have hpsdQ : ∀ x : Fin n → Real, 0 ≤ x ⬝ᵥ Q x := by
      intro x
      rw [hQquad x]
      refine Finset.sum_nonneg ?_
      intro i hi
      exact mul_nonneg (hd i) (sq_nonneg (A x i))
    -- Convert the `h`-term into `quadraticHalfLinear` plus an indicator in the original variables.
    have hf_form :
        f =
          fun x =>
            quadraticHalfLinear n Q x + ((x ⬝ᵥ (aStar - Q a) : Real) : EReal) +
                ((α + (1 / 2 : Real) * (a ⬝ᵥ Q a) : Real) : EReal) +
              indicatorFunction (M : Set (Fin n → Real)) x := by
      funext x
      -- Start from the given form of `f`.
      have hf0 :
          f x = h (A (x - a)) + ((x ⬝ᵥ aStar : Real) : EReal) + (α : EReal) := by
        simp [hfEq]
      -- Rewrite `h` using the elementary model.
      have hhx : h (A (x - a)) =
          (((1 / 2 : Real) * (∑ i : Fin n, d i * (A (x - a) i) ^ 2) : Real) : EReal) +
            indicatorFunction (L : Set (Fin n → Real)) (A (x - a)) := by
        simp [hdef]
      -- Replace the diagonal quadratic by `quadraticHalfLinear`.
      have hquad :
          (((1 / 2 : Real) * (∑ i : Fin n, d i * (A (x - a) i) ^ 2) : Real) : EReal) =
            quadraticHalfLinear n Q (x - a) := by
        unfold quadraticHalfLinear
        rw [hQquad (x - a)]
      -- Transport the subspace indicator back through `A`.
      have hind :
          indicatorFunction (L : Set (Fin n → Real)) (A (x - a)) =
            indicatorFunction (L' : Set (Fin n → Real)) (x - a) := by
        have :=
          indicatorFunction_submodule_comap_linearEquiv (n := n) (L := L) (A := A) (x - a)
        -- The lemma gives `indicator L' (x-a) = indicator L (A (x-a))`.
        simpa [L'] using this.symm
      -- Replace `indicator L' (x-a)` by `indicator M x`.
      have hindM :
          indicatorFunction (L' : Set (Fin n → Real)) (x - a) =
            indicatorFunction (M : Set (Fin n → Real)) x := by
        simpa [M] using
          (indicatorFunction_affineSubspace_eq_indicator_direction_sub (n := n) (M := M) (a := a)
                haM x).symm
      -- Translate the quadratic term from `(x-a)` to `x` and collect linear/constant terms.
      have htrans :=
        quadraticHalfLinear_translate_sub_of_dotProduct_symmetric (n := n) (Q := Q) hQsymm a x
      have hlin_real :
          (x ⬝ᵥ (aStar - Q a) : Real) = (x ⬝ᵥ aStar : Real) + (x ⬝ᵥ (-Q a) : Real) := by
        calc
          (x ⬝ᵥ (aStar - Q a) : Real) = (x ⬝ᵥ aStar : Real) - (x ⬝ᵥ Q a : Real) := by
            exact dotProduct_sub x aStar (Q a)
          _ = (x ⬝ᵥ aStar : Real) + (x ⬝ᵥ (-Q a) : Real) := by
            have hxneg : (x ⬝ᵥ (-Q a) : Real) = -(x ⬝ᵥ Q a : Real) := by
              exact dotProduct_neg x (Q a)
            simp [sub_eq_add_neg, hxneg]
      have hlin_E :
          ((x ⬝ᵥ (aStar - Q a) : Real) : EReal) =
            ((x ⬝ᵥ aStar : Real) : EReal) + ((x ⬝ᵥ (-Q a) : Real) : EReal) := by
        rw [hlin_real]
        simp [EReal.coe_add]
      have hconst_E :
          ((α + (1 / 2 : Real) * (a ⬝ᵥ Q a) : Real) : EReal) =
            (α : EReal) + (((1 / 2 : Real) * (a ⬝ᵥ Q a) : Real) : EReal) := by
        simp [EReal.coe_add]
      -- Rewrite and finish by associativity/commutativity of addition.
      rw [hf0, hhx, hquad, hind, hindM, htrans]
      -- Expand the collected linear and constant terms on the right-hand side.
      rw [hlin_E, hconst_E]
      abel
    refine ⟨hfprop, ?_⟩
    refine ⟨Q, (aStar - Q a), (α + (1 / 2 : Real) * (a ⬝ᵥ Q a)), M, hpsdQ, ?_⟩
    exact hf_form

/-- Negation turns `iInf` into `iSup` in `EReal`. -/
lemma ereal_iSup_neg_eq_neg_iInf {ι : Sort*} (g : ι → EReal) :
    (iSup fun i => -g i) = - (iInf fun i => g i) := by
  -- Use the order isomorphism `x ↦ -x` into the order dual.
  have hmap :
      OrderDual.ofDual (EReal.negOrderIso (iInf fun i => g i)) =
        OrderDual.ofDual (iInf fun i => EReal.negOrderIso (g i)) :=
    congrArg (fun z => OrderDual.ofDual z) (EReal.negOrderIso.map_iInf g)
  have hneg : -(iInf fun i => g i) = iSup fun i => -g i := by
    calc
      -(iInf fun i => g i) = OrderDual.ofDual (EReal.negOrderIso (iInf fun i => g i)) := by
        -- Avoid `simp` unfolding `map_iInf` here (which would make this step circular).
        dsimp [EReal.negOrderIso]
      _ = OrderDual.ofDual (iInf fun i => EReal.negOrderIso (g i)) := by
        exact hmap
      _ = iSup fun i => OrderDual.ofDual (EReal.negOrderIso (g i)) := by
        exact (ofDual_iInf (f := fun i => EReal.negOrderIso (g i)))
      _ = iSup fun i => -g i := by
        simp [EReal.negOrderIso]
  simpa using hneg.symm

/-- The value of the Fenchel conjugate at `0` is the negative of the infimum of `f`. -/
lemma fenchelConjugate_zero_eq_neg_iInf (n : Nat) (f : (Fin n → Real) → EReal) :
    fenchelConjugate n f 0 = - (iInf fun x : Fin n → Real => f x) := by
  simp [fenchelConjugate_eq_iSup, ereal_iSup_neg_eq_neg_iInf, sub_eq_add_neg]

/-- For closed proper convex `f`, the infimum of the Fenchel conjugate is `-f 0`. -/
lemma iInf_fenchelConjugate_eq_neg_eval_zero (n : Nat) (f : (Fin n → Real) → EReal)
    (hf_closed : LowerSemicontinuous f) (hf_convex : ConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (iInf fun xStar : Fin n → Real => fenchelConjugate n f xStar) = -f 0 := by
  -- Use biconjugacy `f** = f` (since `f` is closed and proper).
  have hbiconj_cl :
      fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
    (fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n := n) (f := f) hf_convex).2.2.2
  have hcl : clConv n f = f :=
    clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hf_closed)
      (hf_proper := hf_proper)
  have hbiconj : fenchelConjugate n (fenchelConjugate n f) = f := by
    simpa [hcl] using hbiconj_cl
  -- Evaluate at `0` and rewrite using `fenchelConjugate_zero_eq_neg_iInf`.
  have h0 :
      f 0 =
        - (iInf fun xStar : Fin n → Real => fenchelConjugate n f xStar) := by
    simpa [hbiconj] using (fenchelConjugate_zero_eq_neg_iInf (n := n) (f := fenchelConjugate n f))
  -- Negate both sides to solve for the `iInf`.
  simpa using (congrArg Neg.neg h0).symm

/-- Text 12.3.4: Let `f` be a closed proper convex function on `ℝ^n`. Then
`inf_x f x = f 0 = 0` if and only if `inf_{x*} f* x* = f* 0 = 0`, where `f*` is the Fenchel
conjugate (here `f* = fenchelConjugate n f`). -/
theorem inf_eq_at_zero_iff_conjugate_inf_eq_at_zero (n : Nat) (f : (Fin n → Real) → EReal)
    (hf_closed : LowerSemicontinuous f) (hf_convex : ConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ((iInf fun x : Fin n → Real => f x) = f 0 ∧ f 0 = 0) ↔
      ((iInf fun xStar : Fin n → Real => fenchelConjugate n f xStar) =
            fenchelConjugate n f 0 ∧
          fenchelConjugate n f 0 = 0) := by
  constructor
  · rintro ⟨hinf_eq, hf0⟩
    have hinf0 : (iInf fun x : Fin n → Real => f x) = 0 := by
      simpa [hf0] using hinf_eq
    have hconj0 : fenchelConjugate n f 0 = 0 := by
      rw [fenchelConjugate_zero_eq_neg_iInf (n := n) (f := f), hinf0]
      simp
    have hinf_conj0 : (iInf fun xStar : Fin n → Real => fenchelConjugate n f xStar) = 0 := by
      rw [iInf_fenchelConjugate_eq_neg_eval_zero (n := n) (f := f) hf_closed hf_convex hf_proper,
        hf0]
      simp
    refine ⟨?_, hconj0⟩
    simp [hinf_conj0, hconj0]
  · rintro ⟨hinf_eq, hconj0⟩
    have hinf_conj0 : (iInf fun xStar : Fin n → Real => fenchelConjugate n f xStar) = 0 := by
      simpa [hconj0] using hinf_eq
    have hf0 : f 0 = 0 := by
      have h :
          (iInf fun xStar : Fin n → Real => fenchelConjugate n f xStar) = -f 0 :=
        iInf_fenchelConjugate_eq_neg_eval_zero (n := n) (f := f) hf_closed hf_convex hf_proper
      have hneg : -f 0 = 0 := by
        calc
          -f 0 = (iInf fun xStar : Fin n → Real => fenchelConjugate n f xStar) := by simpa using h.symm
          _ = 0 := hinf_conj0
      simpa [neg_neg] using congrArg Neg.neg hneg
    have hinf0 : (iInf fun x : Fin n → Real => f x) = 0 := by
      have h0 :
          fenchelConjugate n f 0 = - (iInf fun x : Fin n → Real => f x) :=
        fenchelConjugate_zero_eq_neg_iInf (n := n) (f := f)
      have hneg : - (iInf fun x : Fin n → Real => f x) = 0 := by
        calc
          - (iInf fun x : Fin n → Real => f x) = fenchelConjugate n f 0 := by simpa using h0.symm
          _ = 0 := hconj0
      simpa [neg_neg] using congrArg Neg.neg hneg
    refine ⟨?_, hf0⟩
    simp [hinf0, hf0]

/-- Defn 12.3: A function `f` on `ℝ^n` is *symmetric* (or *even*) if it satisfies
`f (-x) = f x` for all `x ∈ ℝ^n`. -/
abbrev IsSymmetricFunction {α : Type*} (n : Nat) (f : (Fin n → Real) → α) : Prop :=
  Function.Even f

/-- Reindex an `iSup` by the involution `x ↦ -x`. -/
lemma iSup_comp_neg {α β : Type*} [AddGroup α] [CompleteLattice β] (g : α → β) :
    (iSup fun x => g (-x)) = iSup g := by
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    exact le_iSup g (-x)
  · refine iSup_le ?_
    intro x
    simpa using (le_iSup (fun y => g (-y)) (-x))

/-- If `f` is even, then its Fenchel conjugate `f*` is even. -/
lemma fenchelConjugate_even_of_even (n : Nat) {f : (Fin n → Real) → EReal}
    (hf : Function.Even f) : Function.Even (fenchelConjugate n f) := by
  intro xStar
  -- Rewrite `f* (-x*)` as an `iSup`, then reindex by `x ↦ -x`.
  calc
    fenchelConjugate n f (-xStar) =
        iSup (fun x : Fin n → Real => ((x ⬝ᵥ (-xStar) : Real) : EReal) - f x) := by
          simp [fenchelConjugate_eq_iSup]
    _ =
        iSup (fun x : Fin n → Real => ((((-x) ⬝ᵥ (-xStar) : Real) : EReal) - f (-x))) := by
          symm
          exact (iSup_comp_neg (g := fun x : Fin n → Real => ((x ⬝ᵥ (-xStar) : Real) : EReal) - f x))
    _ =
        iSup (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) := by
          refine iSup_congr fun x => ?_
          -- First simplify the dot product, then use evenness of `f`.
          have hx : f (-x) = f x := hf x
          simpa [neg_dotProduct_neg] using congrArg (fun t => ((x ⬝ᵥ xStar : Real) : EReal) - t) hx
    _ = fenchelConjugate n f xStar := by
          simp [fenchelConjugate_eq_iSup]

/-- If the Fenchel conjugate of `f` is even, then the closed convex envelope `clConv n f` is even. -/
lemma even_clConv_of_even_fenchelConjugate (n : Nat) {f : (Fin n → Real) → EReal}
    (hf_convex : ConvexFunction f) (hEvenConj : Function.Even (fenchelConjugate n f)) :
    Function.Even (clConv n f) := by
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
    (fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n := n) (f := f) hf_convex).2.2.2
  have hEven_bi : Function.Even (fenchelConjugate n (fenchelConjugate n f)) :=
    fenchelConjugate_even_of_even (n := n) (f := fenchelConjugate n f) hEvenConj
  simpa [hbiconj] using hEven_bi

/-- For closed proper convex `f`, evenness of its Fenchel conjugate implies evenness of `f`. -/
lemma even_of_even_fenchelConjugate_of_closedProperConvex (n : Nat) {f : (Fin n → Real) → EReal}
    (hf_closed : LowerSemicontinuous f) (hf_convex : ConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hEvenConj : Function.Even (fenchelConjugate n f)) : Function.Even f := by
  have hEven_cl : Function.Even (clConv n f) :=
    even_clConv_of_even_fenchelConjugate (n := n) (f := f) hf_convex hEvenConj
  have hcl : clConv n f = f :=
    clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hf_closed)
      (hf_proper := hf_proper)
  simpa [hcl] using hEven_cl

/-- Text 12.3.5: Let `f` be a closed proper convex function on `ℝ^n`. Then `f` is symmetric (i.e.
`f (-x) = f x` for all `x`) if and only if its conjugate `f*` is symmetric (here
`f* = fenchelConjugate n f`). -/
theorem isSymmetricFunction_iff_isSymmetricFunction_fenchelConjugate (n : Nat)
    (f : (Fin n → Real) → EReal)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : ConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    IsSymmetricFunction n f ↔ IsSymmetricFunction n (fenchelConjugate n f) := by
  constructor
  · intro hfEven
    exact fenchelConjugate_even_of_even (n := n) (f := f) (by simpa [IsSymmetricFunction] using hfEven)
  · intro hconjEven
    have hEvenConj : Function.Even (fenchelConjugate n f) := by
      simpa [IsSymmetricFunction] using hconjEven
    have hEven_f : Function.Even f :=
      even_of_even_fenchelConjugate_of_closedProperConvex (n := n) (f := f)
        (hf_closed := hf_closed) (hf_convex := hf_convex) (hf_proper := hf_proper)
        hEvenConj
    simpa [IsSymmetricFunction] using hEven_f

/-- Text 12.3.5: A function `f` on `ℝ^n` is symmetric with respect to all orthogonal
transformations (rotationally symmetric) if and only if it has the form
`f x = g (‖x‖)`, for some function `g` on `[0, +∞)`, where `‖·‖` is the Euclidean norm.

Furthermore, for such an `f`, it is a closed proper convex function on `ℝ^n` if and only if
`g` satisfies:

1. `g` is convex on `[0, +∞)`;
2. `g` is non-decreasing;
3. `g` is lower semicontinuous;
4. `g 0` is finite. -/
def IsRotationallySymmetric {α : Type*} (n : Nat) (f : (Fin n → Real) → α) : Prop :=
  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
  ∀ O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), ∀ x : Fin n → Real,
    f (eL (O (eL.symm x))) = f x

/-- The Euclidean norm on `Fin n → ℝ`, defined via the equivalence with `EuclideanSpace`. -/
noncomputable def euclidNorm (n : Nat) (x : Fin n → Real) : Real :=
  ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖

/-- The nonnegative ray in `Fin 1 → ℝ` used to model `[0, +∞)`. -/
def nonnegRay : Set (Fin 1 → Real) := {r : Fin 1 → Real | 0 ≤ r 0}

/-- The nonnegative ray `nonnegRay` is convex. -/
lemma convex_nonnegRay : Convex ℝ (nonnegRay) := by
  intro r hr s hs a b ha hb hab
  dsimp [nonnegRay] at hr hs ⊢
  have : 0 ≤ (a • r + b • s) 0 := by
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_nonneg (mul_nonneg ha hr) (mul_nonneg hb hs)
  simpa using this

/-- In Euclidean space, vectors of equal norm are related by some linear isometry. -/
lemma exists_linearIsometryEquiv_euclideanSpace_apply_eq_of_norm_eq (n : Nat)
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : ‖x‖ = ‖y‖) :
    ∃ O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), O x = y := by
  classical
  by_cases hn : n = 0
  · subst hn
    have hx : x = 0 := Subsingleton.elim x 0
    have hy : y = 0 := Subsingleton.elim y 0
    subst hx; subst hy
    exact ⟨LinearIsometryEquiv.refl ℝ _, by simp⟩
  ·
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hx : x = 0
    · subst hx
      have hy : y = 0 := by
        have hy_norm : ‖y‖ = 0 := by simpa using hxy.symm
        simpa [norm_eq_zero] using hy_norm
      refine ⟨LinearIsometryEquiv.refl ℝ _, ?_⟩
      simp [hy]
    ·
      have hx0 : ‖x‖ ≠ 0 := by simpa [norm_eq_zero] using hx
      have hy0 : ‖y‖ ≠ 0 := by
        intro hy0
        apply hx0
        simpa [hxy] using hy0
      let ux : EuclideanSpace ℝ (Fin n) := (‖x‖)⁻¹ • x
      let uy : EuclideanSpace ℝ (Fin n) := (‖y‖)⁻¹ • y
      have hux : ‖ux‖ = 1 := by
        calc
          ‖ux‖ = ‖(‖x‖)⁻¹‖ * ‖x‖ := by simpa [ux] using (norm_smul (‖x‖)⁻¹ x)
          _ = (‖x‖)⁻¹ * ‖x‖ := by
                simp [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x))]
          _ = 1 := inv_mul_cancel₀ hx0
      have huy : ‖uy‖ = 1 := by
        calc
          ‖uy‖ = ‖(‖y‖)⁻¹‖ * ‖y‖ := by simpa [uy] using (norm_smul (‖y‖)⁻¹ y)
          _ = (‖y‖)⁻¹ * ‖y‖ := by
                simp [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg y))]
          _ = 1 := inv_mul_cancel₀ hy0

      let i0 : Fin n := ⟨0, hn'⟩
      let s : Set (Fin n) := ({i0} : Set (Fin n))
      let vx : Fin n → EuclideanSpace ℝ (Fin n) := fun i => if i = i0 then ux else 0
      let vy : Fin n → EuclideanSpace ℝ (Fin n) := fun i => if i = i0 then uy else 0

      have hvx : Orthonormal ℝ (s.restrict vx) := by
        classical
        rw [orthonormal_iff_ite]
        rintro ⟨i, hi⟩ ⟨j, hj⟩
        have hi' : i = i0 := by simpa [s] using hi
        have hj' : j = i0 := by simpa [s] using hj
        subst hi'
        subst hj'
        simp [vx, hux]

      have hvy : Orthonormal ℝ (s.restrict vy) := by
        classical
        rw [orthonormal_iff_ite]
        rintro ⟨i, hi⟩ ⟨j, hj⟩
        have hi' : i = i0 := by simpa [s] using hi
        have hj' : j = i0 := by simpa [s] using hj
        subst hi'
        subst hj'
        simp [vy, huy]

      have hcard :
          Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
        simp
      obtain ⟨bx, hbx⟩ :=
        Orthonormal.exists_orthonormalBasis_extension_of_card_eq
          (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (ι := Fin n) (card_ι := hcard)
          (v := vx) (s := s) hvx
      obtain ⟨bY, hbY⟩ :=
        Orthonormal.exists_orthonormalBasis_extension_of_card_eq
          (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (ι := Fin n) (card_ι := hcard)
          (v := vy) (s := s) hvy

      have hbx0 : bx i0 = ux := by
        have : bx i0 = vx i0 := hbx i0 (by simp [s])
        simpa [vx] using this
      have hbY0 : bY i0 = uy := by
        have : bY i0 = vy i0 := hbY i0 (by simp [s])
        simpa [vy] using this

      let O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
        bx.equiv bY (Equiv.refl (Fin n))
      have hOux : O ux = uy := by
        have : O (bx i0) = bY i0 := by
          simp [O]
        simpa [hbx0, hbY0] using this

      have hx_decomp : (‖x‖ : Real) • ux = x := by simp [ux, smul_smul, hx0]
      have hy_decomp : (‖y‖ : Real) • uy = y := by simp [uy, smul_smul, hy0]
      refine ⟨O, ?_⟩
      calc
        O x = O ((‖x‖ : Real) • ux) := by simp [hx_decomp]
        _ = (‖x‖ : Real) • O ux := by simp
        _ = (‖x‖ : Real) • uy := by simp [hOux]
        _ = (‖y‖ : Real) • uy := by simp [hxy]
        _ = y := by simp [hy_decomp]

/-- Text 12.3.5: Rotational symmetry is equivalent to depending only on the Euclidean norm. -/
theorem isRotationallySymmetric_iff_exists_norm_comp {α : Type*} (n : Nat)
    (f : (Fin n → Real) → α) :
    IsRotationallySymmetric n f ↔
      ∃ g : (Fin 1 → Real) → α, ∀ x : Fin n → Real, f x = g (fun _ : Fin 1 => euclidNorm n x) := by
  classical
  constructor
  · intro hrot
    by_cases hn : n = 0
    · subst hn
      refine ⟨fun _ => f 0, ?_⟩
      intro x
      have hx : x = (0 : Fin 0 → Real) := Subsingleton.elim x 0
      subst hx
      simp
    ·
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
      have hrot' :
          ∀ O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), ∀ x : Fin n → Real,
            f (eL (O (eL.symm x))) = f x := by
        simpa [IsRotationallySymmetric, eL] using hrot
      let i0 : Fin n := ⟨0, hn'⟩
      let u0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i0 1
      have hu0 : ‖u0‖ = 1 := by simp [u0]
      refine ⟨fun r => f (eL ((r 0) • u0)), ?_⟩
      intro x
      let ux : EuclideanSpace ℝ (Fin n) := eL.symm x
      let y : Fin n → Real := eL ((‖ux‖ : Real) • u0)
      have hxy : ‖ux‖ = ‖(‖ux‖ : Real) • u0‖ := by
        simp [hu0, norm_smul]
      rcases
        exists_linearIsometryEquiv_euclideanSpace_apply_eq_of_norm_eq (n := n) ux
          ((‖ux‖ : Real) • u0) hxy with ⟨O, hO⟩
      calc
        f x = f (eL (O ux)) := by simpa [ux] using (hrot' O x).symm
        _ = f y := by simp [y, hO]
        _ = (fun r => f (eL ((r 0) • u0))) (fun _ : Fin 1 => euclidNorm n x) := by
              simp [y, euclidNorm, ux, eL]
  · rintro ⟨g, hg⟩
    intro O x
    -- Unfold the definition and use invariance of `euclidNorm` under Euclidean isometries.
    classical
    let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
    have hnorm :
        euclidNorm n (eL (O (eL.symm x))) = euclidNorm n x := by
      simp [euclidNorm, eL, LinearIsometryEquiv.norm_map]
    rw [hg (eL (O (eL.symm x))), hg x]
    simp [hnorm]


end Section12
end Chap03
