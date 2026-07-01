/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part9

open scoped Pointwise

section Chap03
section Section13

/-- Splitting a dot product in `ℝ^{n+1}` into its head and tail parts. -/
lemma section13_dotProduct_head_succ {n : Nat} (v w : Fin (n + 1) → Real) :
    dotProduct v w =
      v 0 * w 0 +
        dotProduct (fun i : Fin n => v i.succ) (fun i : Fin n => w i.succ) := by
  classical
  simp [dotProduct, Fin.sum_univ_succ]

/-- The set `C = { (λ^*, x^*) | λ^* ≤ -f^*(x^*) } ⊆ ℝ^{n+1}` from Corollary 13.5.1. -/
def section13_supportSet {n : Nat} (f : (Fin n → Real) → EReal) : Set (Fin (n + 1) → Real) :=
  {vStar |
    ((vStar 0 : Real) : EReal) ≤ -(fenchelConjugate n f (fun i : Fin n => vStar i.succ))}

/-- For `λ > 0`, the support function of `section13_supportSet f` at `(λ,x)` is the Fenchel
conjugate of the scaled conjugate `λ • f^*`. -/
lemma section13_supportFunctionEReal_supportSet_pos {n : Nat} (f : (Fin n → Real) → EReal)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (v : Fin (n + 1) → Real) (hpos : 0 < v 0) :
    supportFunctionEReal (section13_supportSet (n := n) f) v =
      fenchelConjugate n
          (fun xStar : Fin n → Real =>
            ((v 0 : Real) : EReal) * fenchelConjugate n f xStar)
          (fun i : Fin n => v i.succ) := by
  classical
  set lam : Real := v 0
  set x : Fin n → Real := fun i : Fin n => v i.succ
  set fStar : (Fin n → Real) → EReal := fenchelConjugate n f with hfStar
  have hfStar' : fenchelConjugate n f = fStar := hfStar.symm
  have hlam0 : (0 : EReal) ≤ ((lam : Real) : EReal) := by
    exact_mod_cast (le_of_lt (by simpa [lam] using hpos))
  have hproperStar : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fStar := by
    -- `fStar` is definitionally `f^*`.
    simpa [hfStar] using (proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper)
  have hbotStar : ∀ xStar : Fin n → Real, fStar xStar ≠ (⊥ : EReal) := by
    intro xStar
    simpa using hproperStar.2.2 xStar (by simp)
  -- Rewrite the inner conjugate `f^*` to `fStar` so unfolding `fenchelConjugate` does not touch it.
  simp [section13_supportSet, hfStar']
  unfold supportFunctionEReal
  unfold fenchelConjugate
  refine le_antisymm ?_ ?_
  · -- `supportFunctionEReal ≤ fenchelConjugate` by optimizing over the `λ^*` coordinate.
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨vStar, hvStarC, rfl⟩
    set lamStar : Real := vStar 0
    set xStar : Fin n → Real := fun i : Fin n => vStar i.succ
    have hvStarC' : ((lamStar : Real) : EReal) ≤ -(fStar xStar) := by
      simpa [lamStar, xStar] using hvStarC
    have hmul :
        ((lam : Real) : EReal) * ((lamStar : Real) : EReal) ≤
          ((lam : Real) : EReal) * (-(fStar xStar)) :=
      mul_le_mul_of_nonneg_left hvStarC' hlam0
    have hmul' :
        (((lamStar * lam : Real) : EReal) : EReal) ≤ ((lam : Real) : EReal) * (-(fStar xStar)) := by
      simpa [mul_comm, lamStar, lam] using hmul
    have hdot :
        ((dotProduct vStar v : Real) : EReal) =
          ((lamStar * lam : Real) : EReal) + ((dotProduct xStar x : Real) : EReal) := by
      have := congrArg (fun r : Real => (r : EReal))
        (section13_dotProduct_head_succ (n := n) vStar v)
      simpa [lamStar, xStar, lam, x, EReal.coe_add, add_assoc, add_comm, add_left_comm] using this
    have hle_term :
        ((dotProduct vStar v : Real) : EReal) ≤
          ((dotProduct xStar x : Real) : EReal) - ((lam : Real) : EReal) * (fStar xStar) := by
      rw [hdot]
      have h1' :
          ((dotProduct xStar x : Real) : EReal) + ((lamStar * lam : Real) : EReal) ≤
            ((dotProduct xStar x : Real) : EReal) + ((lam : Real) : EReal) * (-(fStar xStar)) :=
        add_le_add_right hmul' _
      have h1 :
          ((lamStar * lam : Real) : EReal) + ((dotProduct xStar x : Real) : EReal) ≤
            ((lam : Real) : EReal) * (-(fStar xStar)) + ((dotProduct xStar x : Real) : EReal) := by
        simpa [add_assoc, add_comm, add_left_comm] using h1'
      -- Commute the sum and rewrite `lam * (-g) = -(lam*g)`.
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_neg] using h1
    have hmem_range :
        ((dotProduct xStar x : Real) : EReal) - ((lam : Real) : EReal) * (fStar xStar) ∈
          Set.range
            (fun xStar : Fin n → Real =>
              ((dotProduct xStar x : Real) : EReal) - ((lam : Real) : EReal) * fStar xStar) :=
      ⟨xStar, rfl⟩
    have hle_sSup :
        ((dotProduct xStar x : Real) : EReal) - ((lam : Real) : EReal) * (fStar xStar) ≤
          sSup
            (Set.range
              (fun xStar : Fin n → Real =>
                ((dotProduct xStar x : Real) : EReal) - ((lam : Real) : EReal) * fStar xStar)) :=
      le_sSup hmem_range
    exact le_trans hle_term hle_sSup
  · -- `fenchelConjugate ≤ supportFunctionEReal` by choosing `λ^* = -f^*(x^*)`.
    refine sSup_le ?_
    rintro z ⟨xStar, rfl⟩
    by_cases hxStar_top : fStar xStar = (⊤ : EReal)
    · -- This term is `⊥`, hence below the support function.
      have hmul_top :
          ((lam : Real) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
        simpa [lam] using (EReal.coe_mul_top_of_pos (x := lam) (by simpa [lam] using hpos))
      have :
          ((dotProduct xStar x : Real) : EReal) - ((lam : Real) : EReal) * fStar xStar =
            (⊥ : EReal) := by
        simp [hxStar_top, hmul_top, sub_eq_add_neg]
      simp [this]
    ·
      have hxStar_ne_bot : fStar xStar ≠ (⊥ : EReal) := hbotStar xStar
      lift fStar xStar to ℝ using ⟨hxStar_top, hxStar_ne_bot⟩ with r hr
      set lamStar : Real := -r
      let vStar : Fin (n + 1) → Real := Fin.cases lamStar xStar
      have hvStarC : ((lamStar : Real) : EReal) ≤ -(fStar xStar) := by
        simp [lamStar, hr]
      have hvStarC' : vStar ∈ {vStar | ((vStar 0 : Real) : EReal) ≤ -(fStar (fun i : Fin n => vStar i.succ))} := by
        simpa [vStar] using hvStarC
      have hdot_real : dotProduct vStar v = lamStar * lam + dotProduct xStar x := by
        simpa [vStar, lamStar, lam, x] using (section13_dotProduct_head_succ (n := n) vStar v)
      have hterm :
          ((dotProduct xStar x : Real) : EReal) - ((lam : Real) : EReal) * fStar xStar =
            ((dotProduct vStar v : Real) : EReal) := by
        -- Rewrite the RHS using the dot-product splitting and `fStar xStar = r`.
        have hdot' :
            (dotProduct vStar v : Real) = dotProduct xStar x - lam * r := by
          -- Expand `lamStar = -r` in `hdot_real`.
          calc
            dotProduct vStar v = lamStar * lam + dotProduct xStar x := hdot_real
            _ = dotProduct xStar x - lam * r := by
                  simp [lamStar, sub_eq_add_neg, add_comm, mul_comm]
        have : fStar xStar = (r : EReal) := by simp [hr]
        simp [this, hdot', sub_eq_add_neg, EReal.coe_mul]
      refine le_sSup ?_
      refine ⟨vStar, hvStarC', ?_⟩
      simpa [hr.symm] using hterm

/-- For `λ > 0`, `supportFunctionEReal (section13_supportSet f)` matches the `rightScalarMultiple`
branch of Corollary 13.5.1. -/
lemma section13_supportFunctionEReal_supportSet_pos_eq_rightScalarMultiple {n : Nat}
    (f : (Fin n → Real) → EReal) (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (v : Fin (n + 1) → Real) (hpos : 0 < v 0) :
    supportFunctionEReal (section13_supportSet (n := n) f) v =
      rightScalarMultiple f (v 0) (fun i : Fin n => v i.succ) := by
  classical
  have hsupp :
      supportFunctionEReal (section13_supportSet (n := n) f) v =
        fenchelConjugate n
            (fun xStar : Fin n → Real =>
              ((v 0 : Real) : EReal) * fenchelConjugate n f xStar)
            (fun i : Fin n => v i.succ) :=
    section13_supportFunctionEReal_supportSet_pos (n := n) (f := f) hf_proper v hpos
  -- Convert the scaled-conjugate expression into a right scalar multiple of the biconjugate.
  have hsmul :
      fenchelConjugate n
          (fun xStar : Fin n → Real =>
            ((v 0 : Real) : EReal) * fenchelConjugate n f xStar) =
        rightScalarMultiple (fenchelConjugate n (fenchelConjugate n f)) (v 0) := by
    simpa using
      (section13_fenchelConjugate_smul_eq_rightScalarMultiple (n := n) (f := fenchelConjugate n f)
        (lam := v 0) hpos)
  have hsmul_x :
      fenchelConjugate n
          (fun xStar : Fin n → Real =>
            ((v 0 : Real) : EReal) * fenchelConjugate n f xStar)
          (fun i : Fin n => v i.succ) =
        rightScalarMultiple (fenchelConjugate n (fenchelConjugate n f)) (v 0)
          (fun i : Fin n => v i.succ) := by
    simpa using congrArg (fun g => g (fun i : Fin n => v i.succ)) hsmul
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n f) = clConv n f := by
    simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f))
  have hcl : clConv n f = f :=
    clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hf_closed.2)
      (hf_proper := hf_proper)
  -- Put everything together.
  rw [hsupp, hsmul_x]
  simp [hbiconj, hcl]

/-- For `λ = 0`, the support function of `section13_supportSet f` reduces to the support function
of `dom f^*`, evaluated at the tail vector. -/
lemma section13_supportFunctionEReal_supportSet_zero {n : Nat} (f : (Fin n → Real) → EReal)
    (v : Fin (n + 1) → Real) (hzero : v 0 = 0) :
    supportFunctionEReal (section13_supportSet (n := n) f) v =
      supportFunctionEReal
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))
        (fun i : Fin n => v i.succ) := by
  classical
  set x : Fin n → Real := fun i : Fin n => v i.succ
  -- Unfold both support functions and compare the defining sets.
  unfold supportFunctionEReal
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro z hz
    rcases hz with ⟨vStar, hvStarC, rfl⟩
    set xStar : Fin n → Real := fun i : Fin n => vStar i.succ
    have hxStar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
      -- If `f^*(xStar) = ⊤` then the defining inequality for `C` is impossible.
      intro hx
      have : ((vStar 0 : Real) : EReal) ≤ (⊥ : EReal) := by
        have hv := hvStarC
        simp [section13_supportSet, xStar, hx] at hv
      exact (not_le_of_gt (EReal.bot_lt_coe (vStar 0))).elim this
    have hxStar_mem :
        xStar ∈
          effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) := by
      -- `xStar ∈ dom f^*` iff `f^*(xStar) < ⊤`.
      have : fenchelConjugate n f xStar < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxStar_ne_top
      have : xStar ∈ {z | z ∈ (Set.univ : Set (Fin n → Real)) ∧ fenchelConjugate n f z < (⊤ : EReal)} :=
        ⟨by simp, this⟩
      simpa [effectiveDomain_eq] using this
    -- For `v 0 = 0`, the dot product ignores the head coordinate.
    have hdot :
        (dotProduct vStar v : Real) = dotProduct xStar x := by
      have hsplit := section13_dotProduct_head_succ (n := n) vStar v
      simp [hsplit, xStar, x, hzero]
    -- The value belongs to the defining set for the RHS support function.
    refine le_sSup ?_
    refine ⟨xStar, hxStar_mem, ?_⟩
    simp [hdot]
  · refine sSup_le ?_
    intro z hz
    rcases hz with ⟨xStar, hxStar_mem, rfl⟩
    set lamStar : Real := -(fenchelConjugate n f xStar).toReal - 1
    let vStar : Fin (n + 1) → Real := Fin.cases lamStar xStar
    have hvStarC : vStar ∈ section13_supportSet (n := n) f := by
      have hxStar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real)))
          (f := fenchelConjugate n f) (by simpa using hxStar_mem)
      have hle_toReal :
          fenchelConjugate n f xStar ≤ ((fenchelConjugate n f xStar).toReal : EReal) :=
        EReal.le_coe_toReal hxStar_ne_top
      have hneg_le :
          (-(fenchelConjugate n f xStar).toReal : EReal) ≤ -(fenchelConjugate n f xStar) := by
        -- Re-express as `-a ≤ -b` and use `EReal.neg_le_neg_iff`.
        have h' :
            -((fenchelConjugate n f xStar).toReal : EReal) ≤ -(fenchelConjugate n f xStar) :=
          (EReal.neg_le_neg_iff.2 hle_toReal)
        simpa using h'
      have hlamStar_le :
          ((lamStar : Real) : EReal) ≤ (-(fenchelConjugate n f xStar).toReal : EReal) := by
        -- `-x.toReal - 1 ≤ -x.toReal`.
        exact_mod_cast (by linarith : lamStar ≤ -(fenchelConjugate n f xStar).toReal)
      have :
          ((lamStar : Real) : EReal) ≤ -(fenchelConjugate n f xStar) :=
        le_trans hlamStar_le hneg_le
      simpa [section13_supportSet, vStar, lamStar] using this
    have hdot :
        (dotProduct vStar v : Real) = dotProduct xStar x := by
      have hsplit := section13_dotProduct_head_succ (n := n) vStar v
      simp [hsplit, vStar, lamStar, x, hzero]
    refine le_sSup ?_
    refine ⟨vStar, hvStarC, ?_⟩
    simp [hdot]

/-- For `λ < 0`, the support function of `section13_supportSet f` is `⊤`. -/
lemma section13_supportFunctionEReal_supportSet_neg {n : Nat} (f : (Fin n → Real) → EReal)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (v : Fin (n + 1) → Real) (hneg : v 0 < 0) :
    supportFunctionEReal (section13_supportSet (n := n) f) v = ⊤ := by
  classical
  set lam : Real := v 0
  set x : Fin n → Real := fun i : Fin n => v i.succ
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
  rcases
      (section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f)
        hproperStar) with
    ⟨xStar, hxStar_mem⟩
  have hxStar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := fenchelConjugate n f)
      (by simpa using hxStar_mem)
  have hxBound_ne_bot : -(fenchelConjugate n f xStar) ≠ (⊥ : EReal) := by
    -- If `f^*(xStar) ≠ ⊤`, then `-f^*(xStar) ≠ ⊥`.
    intro hbot
    have : fenchelConjugate n f xStar = (⊤ : EReal) := (EReal.neg_eq_bot_iff.1 hbot)
    exact hxStar_ne_top this
  -- For any real `y`, build a witness in the support-function set whose dot product exceeds `y`.
  have hforall : ∀ y : ℝ, (y : EReal) < supportFunctionEReal (section13_supportSet (n := n) f) v := by
    intro y
    set c : Real := dotProduct xStar x
    set u : Real := (-(fenchelConjugate n f xStar)).toReal
    have hu_le :
        ((u : Real) : EReal) ≤ -(fenchelConjugate n f xStar) :=
      (EReal.coe_toReal_le (x := -(fenchelConjugate n f xStar)) hxBound_ne_bot)
    -- Choose `λ^*` below both `u` and `(y - c)/lam`.
    set lamStar : Real := min (u - 1) ((y - c) / lam - 1)
    have hlamStar_le_u : lamStar ≤ u := by
      have : lamStar ≤ u - 1 := min_le_left _ _
      linarith
    have hlamStar_lt_div : lamStar < (y - c) / lam := by
      have : lamStar ≤ (y - c) / lam - 1 := min_le_right _ _
      linarith
    have hdot_real : y < lam * lamStar + c := by
      have hlam0 : lam ≠ 0 := ne_of_lt (by simpa [lam] using hneg)
      have hmul_lt : lam * ((y - c) / lam) < lam * lamStar := by
        -- `lam < 0` reverses inequalities.
        have : lamStar < (y - c) / lam := hlamStar_lt_div
        simpa [mul_comm, lam] using (mul_lt_mul_of_neg_left this (by simpa [lam] using hneg))
      have hmul_cancel : lam * ((y - c) / lam) = y - c := by
        field_simp [hlam0]
      have : y - c < lam * lamStar := by simpa [hmul_cancel] using hmul_lt
      linarith
    -- Build the witness `vStar = (lamStar, xStar)` in `C`.
    let vStar : Fin (n + 1) → Real := Fin.cases lamStar xStar
    have hvStarC : vStar ∈ section13_supportSet (n := n) f := by
      -- From `lamStar ≤ u` and `(u : EReal) ≤ -f^*(xStar)`, get the defining inequality.
      have hlamStar_le_u' : ((lamStar : Real) : EReal) ≤ (u : EReal) := by
        exact_mod_cast hlamStar_le_u
      have : ((lamStar : Real) : EReal) ≤ -(fenchelConjugate n f xStar) :=
        le_trans hlamStar_le_u' hu_le
      simpa [section13_supportSet, vStar] using this
    have hdot :
        (dotProduct vStar v : Real) = lamStar * lam + c := by
      have hsplit := section13_dotProduct_head_succ (n := n) vStar v
      simp [hsplit, vStar, lamStar, lam, x, c]
    have hylt :
        (y : EReal) < ((dotProduct vStar v : Real) : EReal) := by
      have : (y : EReal) < ((lam * lamStar + c : Real) : EReal) :=
        (EReal.coe_lt_coe_iff.2 hdot_real)
      simpa [hdot, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this
    -- Conclude via `le_sSup` for the defining set of `supportFunctionEReal`.
    have hle :
        ((dotProduct vStar v : Real) : EReal) ≤
          supportFunctionEReal (section13_supportSet (n := n) f) v := by
      unfold supportFunctionEReal
      refine le_sSup ?_
      exact ⟨vStar, hvStarC, rfl⟩
    exact lt_of_lt_of_le hylt hle
  -- Now use `eq_top_iff_forall_lt`.
  exact (EReal.eq_top_iff_forall_lt _).2 hforall

/-- Corollary 13.5.1. Let `f` be a closed proper convex function on `ℝ^n`. Define a function
`k : ℝ^{n+1} → (-∞, +∞]` by

`k(λ, x) = (f λ)(x)` if `λ > 0`,
`k(0, x) = (f0^+)(x)` if `λ = 0`,
and `k(λ, x) = +∞` if `λ < 0`.

Then `k` is the support function of the set
`C = { (λ^*, x^*) | λ^* ≤ -f^*(x^*) } ⊆ ℝ^{n+1}`. -/
theorem supportFunctionEReal_setOf_le_neg_fenchelConjugate_eq_piecewise_rightScalarMultiple
    {n : Nat} (f : (Fin n → Real) → EReal) (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (let k : (Fin (n + 1) → Real) → EReal :=
        fun v =>
          let lam : Real := v 0
          let x : Fin n → Real := fun i => v i.succ
          if _hpos : 0 < lam then
            rightScalarMultiple f lam x
          else if _hzero : lam = 0 then
            recessionFunction f x
          else
            ⊤
      let C : Set (Fin (n + 1) → Real) :=
        {vStar |
          ((vStar 0 : Real) : EReal) ≤
            -(fenchelConjugate n f (fun i : Fin n => vStar i.succ))}
      k = supportFunctionEReal C) := by
  classical
  dsimp
  funext v
  set lam : Real := v 0
  set x : Fin n → Real := fun i : Fin n => v i.succ
  -- Identify the set `C` with our local definition.
  have hC : {vStar : Fin (n + 1) → Real |
        ((vStar 0 : Real) : EReal) ≤
          -(fenchelConjugate n f (fun i : Fin n => vStar i.succ))} =
      section13_supportSet (n := n) f := by
    rfl
  -- Case split on `lam`.
  by_cases hpos : 0 < lam
  · -- `lam > 0` branch: right scalar multiple.
    have hsupp :
        supportFunctionEReal (section13_supportSet (n := n) f) v =
          rightScalarMultiple f lam x := by
      -- Rewrite `lam`/`x` and apply the prepared lemma.
      simpa [lam, x] using
        (section13_supportFunctionEReal_supportSet_pos_eq_rightScalarMultiple (n := n) (f := f)
          (hf_closed := hf_closed) (hf_proper := hf_proper) (v := v) (hpos := by simpa [lam] using hpos))
    -- Reduce `k v` and rewrite `C`.
    simp [lam, x, hpos, hC, hsupp]
  · by_cases hzero : lam = 0
    · -- `lam = 0` branch: recession function.
      have hsupp0 :
          supportFunctionEReal (section13_supportSet (n := n) f) v =
            recessionFunction f x := by
        have hdom :
            supportFunctionEReal
                (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) =
              recessionFunction f :=
          section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n) (f := f)
            hf_closed hf_proper
        have hdom_x :
            supportFunctionEReal
                (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) x =
              recessionFunction f x := by
          simpa using congrArg (fun g => g x) hdom
        have hzero' : v 0 = 0 := by simpa [lam] using hzero
        have hz :
            supportFunctionEReal (section13_supportSet (n := n) f) v =
              supportFunctionEReal
                (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) x := by
          simpa [x] using
            (section13_supportFunctionEReal_supportSet_zero (n := n) (f := f) (v := v) hzero')
        simpa [hz] using hdom_x
      simp [lam, x, hzero, hC, hsupp0]
    · -- `lam < 0` branch: support function is `⊤`.
      have hneg : lam < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
      have hsuppneg :
          supportFunctionEReal (section13_supportSet (n := n) f) v = ⊤ := by
        simpa [lam] using
          (section13_supportFunctionEReal_supportSet_neg (n := n) (f := f) (hf_proper := hf_proper)
            (v := v) (hneg := by simpa [lam] using hneg))
      simp [lam, hpos, hzero, hC, hsuppneg]

/-- Move `mulVec` from the right argument of `dotProduct` to the left. -/
lemma section13_dotProduct_mulVec_right {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    dotProduct x (A.mulVec y) = dotProduct (A.transpose.mulVec x) y := by
  simpa [Matrix.mulVec, Matrix.mulVec_transpose] using (Matrix.dotProduct_mulVec x A y)

/-- Support function under a linear image `y ↦ A y`: `δ^*(x | A '' C) = δ^*(Aᵀ x | C)`. -/
lemma section13_deltaStar_image_mulVec {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Set (Fin n → ℝ)) (xStar : Fin n → ℝ) :
    deltaStar ((fun y => A.mulVec y) '' C) xStar = deltaStar C (A.transpose.mulVec xStar) := by
  classical
  calc
    deltaStar ((fun y => A.mulVec y) '' C) xStar =
        sSup (Set.image (fun y : Fin n → ℝ => dotProduct xStar y) ((fun y => A.mulVec y) '' C)) := by
          simp [deltaStar, supportFunction_eq_sSup_image_dotProduct]
    _ = sSup (Set.image (fun y : Fin n → ℝ => dotProduct xStar (A.mulVec y)) C) := by
          simp [Set.image_image]
    _ = sSup (Set.image (fun y : Fin n → ℝ => dotProduct (A.transpose.mulVec xStar) y) C) := by
          refine congrArg sSup (Set.image_congr' ?_)
          intro y
          simp [section13_dotProduct_mulVec_right]
    _ = deltaStar C (A.transpose.mulVec xStar) := by
          simp [deltaStar, supportFunction_eq_sSup_image_dotProduct]

/-- The support function of a singleton is just the dot product. -/
lemma section13_deltaStar_singleton {n : Nat} (a xStar : Fin n → ℝ) :
    deltaStar ({a} : Set (Fin n → ℝ)) xStar = dotProduct xStar a := by
  classical
  simp [deltaStar, supportFunction_eq_sSup_image_dotProduct]

/-- Quadratic forms from positive definite matrices are nonnegative. -/
lemma section13_posDef_dotProduct_mulVec_nonneg {n : Nat} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) (x : Fin n → ℝ) :
    0 ≤ dotProduct x (Q.mulVec x) := by
  simpa using (Matrix.PosSemidef.dotProduct_mulVec_nonneg hQ.posSemidef x)

open scoped MatrixOrder

/-- A real positive definite matrix factors as `Bᵀ * B` with `B` invertible. -/
lemma section13_posDef_exists_isUnit_transpose_mul_self {n : Nat} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, IsUnit B ∧ Q = B.transpose * B := by
  classical
  have hQsp : IsStrictlyPositive Q := (Matrix.isStrictlyPositive_iff_posDef (x := Q)).2 hQ
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self (a := Q)).1 hQsp with ⟨B, hB, hQeq⟩
  refine ⟨B, hB, ?_⟩
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hQeq

/-- Completing the square for the elliptic quadratic inequality. -/
lemma section13_ellipticSet_completeSquare_mem {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) (α : ℝ) (hQ : Q.PosDef) :
    let C : Set (Fin n → ℝ) :=
      {x | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct a x + α ≤ 0}
    let b : Fin n → ℝ := -((Q⁻¹).mulVec a)
    let β : ℝ := (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) - α
    ∀ x, x ∈ C ↔ (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) ≤ β := by
  classical
  intro C b β x
  have hQdet : IsUnit Q.det :=
    (Matrix.isUnit_iff_isUnit_det (A := Q)).1 (by simpa using hQ.isUnit)
  have hQsymm : Q.transpose = Q := by
    -- For real matrices, `IsHermitian` is `transpose` symmetry.
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (show Q.conjTranspose = Q from hQ.1)
  have hQ_mul_inv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQdet
  set d : Fin n → ℝ := (Q⁻¹).mulVec a with hd
  have hQd : Q.mulVec d = a := by
    calc
      Q.mulVec d = (Q * Q⁻¹).mulVec a := by
        simp [d, Matrix.mulVec_mulVec]
      _ = a := by simp [hQ_mul_inv]
  have hdot_dx : dotProduct d (Q.mulVec x) = dotProduct a x := by
    calc
      dotProduct d (Q.mulVec x) = dotProduct (Q.transpose.mulVec d) x := by
        simpa using (section13_dotProduct_mulVec_right (A := Q) (x := d) (y := x))
      _ = dotProduct (Q.mulVec d) x := by simp [hQsymm]
      _ = dotProduct a x := by simp [hQd]
  have hdot_xd : dotProduct x (Q.mulVec d) = dotProduct a x := by
    calc
      dotProduct x (Q.mulVec d) = dotProduct (Q.mulVec d) x := by
        simpa using (dotProduct_comm x (Q.mulVec d))
      _ = dotProduct a x := by simp [hQd]
  have hdot_dd : dotProduct d (Q.mulVec d) = dotProduct a ((Q⁻¹).mulVec a) := by
    calc
      dotProduct d (Q.mulVec d) = dotProduct d a := by simp [hQd]
      _ = dotProduct a d := by simpa using (dotProduct_comm d a)
      _ = dotProduct a ((Q⁻¹).mulVec a) := by simp [d]
  have hxb : x - b = x + d := by
    simp [b, d, sub_eq_add_neg]
  have hexpand :
      (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) =
        (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct a x +
          (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) := by
    have hquad :
        dotProduct (x + d) (Q.mulVec (x + d)) =
          dotProduct x (Q.mulVec x) + dotProduct a x + dotProduct a x +
            dotProduct a ((Q⁻¹).mulVec a) := by
      calc
        dotProduct (x + d) (Q.mulVec (x + d)) =
            dotProduct x (Q.mulVec x) + dotProduct x (Q.mulVec d) +
              dotProduct d (Q.mulVec x) + dotProduct d (Q.mulVec d) := by
              simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_assoc, add_left_comm,
                add_comm]
        _ = dotProduct x (Q.mulVec x) + dotProduct a x + dotProduct a x +
              dotProduct a ((Q⁻¹).mulVec a) := by
              simp [hdot_dx, hdot_xd, hdot_dd, add_assoc, add_comm]
    calc
      (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) =
          (1 / 2 : ℝ) * dotProduct (x + d) (Q.mulVec (x + d)) := by simp [hxb]
      _ =
          (1 / 2 : ℝ) *
            (dotProduct x (Q.mulVec x) + dotProduct a x + dotProduct a x +
              dotProduct a ((Q⁻¹).mulVec a)) := by
            simp [hquad]
      _ =
          (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct a x +
            (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) := by
            ring
  constructor
  · intro hxC
    have hxC' : (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct a x + α ≤ 0 := by
      simpa [C] using hxC
    have : (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) ≤
        (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) - α := by
      -- Rearrange using the expansion.
      have := hxC'
      linarith [hexpand]
    simpa [β] using this
  · intro hxβ
    have hxβ' :
        (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) ≤
          (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) - α := by
      simpa [β] using hxβ
    have : (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct a x + α ≤ 0 := by
      linarith [hexpand, hxβ']
    simpa [C] using this

/-- Nonemptiness of the elliptic set forces the radius parameter `β` to be nonnegative. -/
lemma section13_beta_nonneg_of_nonempty {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (α : ℝ) (hQ : Q.PosDef) :
    let C : Set (Fin n → ℝ) :=
      {x | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct a x + α ≤ 0}
    let β : ℝ := (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) - α
    Set.Nonempty C → 0 ≤ β := by
  classical
  dsimp
  intro hCne
  let b : Fin n → ℝ := -((Q⁻¹).mulVec a)
  rcases hCne with ⟨x, hxC⟩
  have hxβ :
      (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) ≤
        (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) - α :=
    by
      simpa [b] using
        (section13_ellipticSet_completeSquare_mem (Q := Q) (a := a) (α := α) hQ (x := x)).1 hxC
  have hnonneg :
      0 ≤ (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) := by
    have : 0 ≤ dotProduct (x - b) (Q.mulVec (x - b)) :=
      section13_posDef_dotProduct_mulVec_nonneg (hQ := hQ) (x := x - b)
    nlinarith
  exact le_trans hnonneg hxβ

/-- The set `{z | (1/2) * ⟪z, z⟫ ≤ β}` is a scaling of the unit Euclidean ball. -/
lemma section13_setOf_half_dotProduct_self_le_eq_smul_unitEuclideanBall {n : Nat} (β : ℝ)
    (hβ : 0 ≤ β) :
    {z : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct z z ≤ β} =
      (Real.sqrt (2 * β)) • {y : Fin n → ℝ | Real.sqrt (dotProduct y y) ≤ (1 : ℝ)} := by
  classical
  set lam : ℝ := Real.sqrt (2 * β)
  have h2β : 0 ≤ 2 * β := by nlinarith [hβ]
  have hlam_nonneg : 0 ≤ lam := by simp [lam]
  ext z
  constructor
  · intro hz
    have hz' : (1 / 2 : ℝ) * dotProduct z z ≤ β := by simpa using hz
    have hz2β : dotProduct z z ≤ 2 * β := by nlinarith [hz']
    by_cases hlam0 : lam = 0
    · have h2β0 : 2 * β = 0 := by
        have : Real.sqrt (2 * β) = 0 := by simpa [lam] using hlam0
        exact (Real.sqrt_eq_zero h2β).1 this
      have hz0 : z = 0 := by
        have hnn : 0 ≤ dotProduct z z := by simpa using (dotProduct_self_star_nonneg z)
        have hle0 : dotProduct z z ≤ 0 := by simpa [h2β0] using hz2β
        have hz00 : dotProduct z z = 0 := le_antisymm hle0 hnn
        exact dotProduct_self_eq_zero.1 hz00
      refine (Set.mem_smul_set).2 ⟨0, by simp, ?_⟩
      simp [hz0, lam, hlam0]
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam_nonneg (Ne.symm hlam0)
      let y : Fin n → ℝ := (1 / lam) • z
      have hy_le : dotProduct y y ≤ (1 : ℝ) := by
        have hy :
            dotProduct y y = (1 / lam) ^ 2 * dotProduct z z := by
          simp [y, smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two, mul_left_comm,
            mul_comm]
        have hmul : (1 / lam) ^ 2 * dotProduct z z ≤ (1 / lam) ^ 2 * (2 * β) := by
          have hnonneg : 0 ≤ (1 / lam) ^ 2 := by nlinarith [hlam_pos.le]
          exact mul_le_mul_of_nonneg_left hz2β hnonneg
        have hscale : (1 / lam) ^ 2 * (2 * β) = 1 := by
          have hlam_sq : lam ^ 2 = 2 * β := by simpa [lam] using (Real.sq_sqrt h2β)
          calc
            (1 / lam) ^ 2 * (2 * β) = (1 / lam) ^ 2 * (lam ^ 2) := by simp [hlam_sq]
            _ = 1 := by
              simp [pow_two, mul_assoc, mul_comm, hlam_pos.ne']
        have : dotProduct y y ≤ 1 := by
          have := le_trans hmul (le_of_eq hscale)
          simpa [hy] using this
        simpa using this
      have hyB : y ∈ {y : Fin n → ℝ | Real.sqrt (dotProduct y y) ≤ (1 : ℝ)} := by
        have : Real.sqrt (dotProduct y y) ≤ (1 : ℝ) := by
          refine (Real.sqrt_le_left (x := dotProduct y y) (y := (1 : ℝ)) (by norm_num)).2 ?_
          simpa using hy_le
        simpa using this
      refine (Set.mem_smul_set).2 ⟨y, hyB, ?_⟩
      have hne : lam ≠ 0 := hlam_pos.ne'
      simp [y, smul_smul, one_div, hne]
  · rintro hz
    rcases (Set.mem_smul_set).1 hz with ⟨y, hyB, rfl⟩
    have hy_le : dotProduct y y ≤ (1 : ℝ) := by
      have hy_sqrt : Real.sqrt (dotProduct y y) ≤ (1 : ℝ) := by simpa using hyB
      have :=
        (Real.sqrt_le_left (x := dotProduct y y) (y := (1 : ℝ)) (by norm_num)).1 hy_sqrt
      simpa [pow_two] using this
    have hsq : lam ^ 2 = 2 * β := by simpa [lam] using (Real.sq_sqrt h2β)
    have hz2β : dotProduct (lam • y) (lam • y) ≤ 2 * β := by
      have hdot :
          dotProduct (lam • y) (lam • y) = lam ^ 2 * dotProduct y y := by
        simp [smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two, mul_left_comm,
          mul_comm]
      nlinarith [hy_le, hdot, hsq]
    have : (1 / 2 : ℝ) * dotProduct (lam • y) (lam • y) ≤ β := by nlinarith [hz2β]
    simpa [lam] using this

/-- Boundedness in direction `xStar` for the centered ellipsoid `{x | (1/2) ⟪x, Qx⟫ ≤ β}`. -/
lemma section13_bddAbove_image_dotProduct_centeredSublevel_posDef {n : Nat}
    (Q : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (xStar : Fin n → ℝ) (hQ : Q.PosDef) (hβ : 0 ≤ β) :
    BddAbove (Set.image (fun x : Fin n → ℝ => dotProduct x xStar)
      {x : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) ≤ β}) := by
  classical
  rcases section13_posDef_exists_isUnit_transpose_mul_self (Q := Q) hQ with ⟨M, hM, hQeq⟩
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det (A := M)).1 hM
  have hMinvMul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMdet
  have hMmulInv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMdet
  set D : Set (Fin n → ℝ) := {x : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) ≤ β}
  set Ball : Set (Fin n → ℝ) := {y : Fin n → ℝ | Real.sqrt (dotProduct y y) ≤ (1 : ℝ)}
  set lam : ℝ := Real.sqrt (2 * β)
  set w : Fin n → ℝ := (M⁻¹).transpose.mulVec xStar
  refine ⟨lam * Real.sqrt (dotProduct w w), ?_⟩
  intro r hr
  rcases hr with ⟨x, hxD, rfl⟩
  -- Let `z = M x`, so `x = M⁻¹ z` and `z` lies in the scaled unit ball.
  set z : Fin n → ℝ := M.mulVec x
  have hxpre : x = (M⁻¹).mulVec z := by
    have : (M⁻¹).mulVec z = x := by
      calc
        (M⁻¹).mulVec z = (M⁻¹).mulVec (M.mulVec x) := by simp [z]
        _ = (M⁻¹ * M).mulVec x := by simp [Matrix.mulVec_mulVec]
        _ = x := by simp [hMinvMul]
    simpa using this.symm
  have hz_mem : z ∈ lam • Ball := by
    -- Transfer the quadratic inequality to `z`.
    have hquad :
        dotProduct x (Q.mulVec x) = dotProduct z z := by
      calc
        dotProduct x (Q.mulVec x) = dotProduct x ((M.transpose * M).mulVec x) := by simp [hQeq]
        _ = dotProduct x (M.transpose.mulVec (M.mulVec x)) := by simp [Matrix.mulVec_mulVec]
        _ = dotProduct z z := by
          have :=
            (section13_dotProduct_mulVec_right (A := M.transpose) (x := x) (y := M.mulVec x))
          simpa [z] using this
    have hz' : z ∈ {z : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct z z ≤ β} := by
      have hx' : (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) ≤ β := by simpa [D] using hxD
      -- membership in `{z | ...}` is the defining inequality
      simpa [hquad] using hx'
    -- Use the ball characterization lemma.
    have hball :
        {z : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct z z ≤ β} = lam • Ball := by
      simpa [lam, Ball] using
        (section13_setOf_half_dotProduct_self_le_eq_smul_unitEuclideanBall (n := n) (β := β) hβ)
    -- rewrite the defining set as a scaled ball
    rw [← hball]
    exact hz'
  -- Bound the dot product via the unit-ball bound.
  have hzmem : z ∈ ({(0 : Fin n → ℝ)} : Set (Fin n → ℝ)) + (lam • Ball) := by
    simpa using
      (Set.add_mem_add (show (0 : Fin n → ℝ) ∈ ({(0 : Fin n → ℝ)} : Set (Fin n → ℝ)) by simp)
        hz_mem)
  have hbound :=
    section13_dotProduct_le_dotProduct_add_mul_sqrt_of_mem_singleton_add_smul_unitEuclideanBall
      (n := n) (a := (0 : Fin n → ℝ)) (x := w) (z := z) (lam := lam) (hlam := by simp [lam])
      (by simpa [Ball] using hzmem)
  have hdot : dotProduct x xStar = dotProduct w z := by
    -- `xStar ⋅ (M⁻¹ z) = (M⁻¹ᵀ xStar) ⋅ z`
    calc
      dotProduct x xStar = dotProduct ((M⁻¹).mulVec z) xStar := by simp [hxpre]
      _ = dotProduct xStar ((M⁻¹).mulVec z) := by simp [dotProduct_comm]
      _ = dotProduct w z := by
        simpa [w] using (section13_dotProduct_mulVec_right (A := M⁻¹) (x := xStar) (y := z))
  -- Conclude.
  simpa [hdot, dotProduct_comm, w, lam, z] using hbound

/-- Support function of the centered ellipsoid `{x | (1/2) ⟪x, Qx⟫ ≤ β}` for positive definite `Q`. -/
lemma section13_deltaStar_centeredSublevel_posDef {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ) (β : ℝ)
    (xStar : Fin n → ℝ) (hQ : Q.PosDef) (hβ : 0 ≤ β) :
    deltaStar {x : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) ≤ β} xStar =
      Real.sqrt (2 * β * dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
  classical
  rcases section13_posDef_exists_isUnit_transpose_mul_self (Q := Q) hQ with ⟨M, hM, hQeq⟩
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det (A := M)).1 hM
  have hMinvMul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMdet
  have hMmulInv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMdet
  set Ball : Set (Fin n → ℝ) := {y : Fin n → ℝ | Real.sqrt (dotProduct y y) ≤ (1 : ℝ)}
  set lam : ℝ := Real.sqrt (2 * β)
  have hlam : 0 ≤ lam := by simp [lam]
  -- Express the ellipsoid as a linear image of `lam • Ball`.
  have hball :
      {z : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct z z ≤ β} = lam • Ball := by
    simpa [lam, Ball] using
      (section13_setOf_half_dotProduct_self_le_eq_smul_unitEuclideanBall (n := n) (β := β) hβ)
  have hD :
      {x : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) ≤ β} =
        (fun z => (M⁻¹).mulVec z) '' (lam • Ball) := by
    ext x
    constructor
    · intro hx
      set z : Fin n → ℝ := M.mulVec x
      have hxpre : x = (M⁻¹).mulVec z := by
        have : (M⁻¹).mulVec z = x := by
          calc
            (M⁻¹).mulVec z = (M⁻¹).mulVec (M.mulVec x) := by simp [z]
            _ = (M⁻¹ * M).mulVec x := by simp [Matrix.mulVec_mulVec]
            _ = x := by simp [hMinvMul]
        simpa using this.symm
      have hquad :
          dotProduct x (Q.mulVec x) = dotProduct z z := by
        calc
          dotProduct x (Q.mulVec x) = dotProduct x ((M.transpose * M).mulVec x) := by
            simp [hQeq]
          _ = dotProduct x (M.transpose.mulVec (M.mulVec x)) := by simp [Matrix.mulVec_mulVec]
          _ = dotProduct z z := by
            have :=
              (section13_dotProduct_mulVec_right (A := M.transpose) (x := x) (y := M.mulVec x))
            simpa [z] using this
      have hz : (1 / 2 : ℝ) * dotProduct z z ≤ β := by
        simpa [hquad] using hx
      have hzmem : z ∈ lam • Ball := by
        rw [← hball]
        exact hz
      exact ⟨z, hzmem, hxpre.symm⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : (1 / 2 : ℝ) * dotProduct z z ≤ β := by
        have hzset : z ∈ {z : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct z z ≤ β} := by
          -- Rewrite the goal to match `hz : z ∈ lam • Ball`.
          rw [hball]
          exact hz
        simpa using hzset
      have hMz : M.mulVec ((M⁻¹).mulVec z) = z := by
        calc
          M.mulVec ((M⁻¹).mulVec z) = (M * M⁻¹).mulVec z := by simp [Matrix.mulVec_mulVec]
          _ = z := by simp [hMmulInv]
      have hquad :
          dotProduct ((M⁻¹).mulVec z) (Q.mulVec ((M⁻¹).mulVec z)) = dotProduct z z := by
        have hQmul :
            Q.mulVec ((M⁻¹).mulVec z) = M.transpose.mulVec z := by
          calc
            Q.mulVec ((M⁻¹).mulVec z) = (M.transpose * M).mulVec ((M⁻¹).mulVec z) := by
              simp [hQeq]
            _ = M.transpose.mulVec (M.mulVec ((M⁻¹).mulVec z)) := by
              simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
            _ = M.transpose.mulVec z := by simp [hMz]
        calc
          dotProduct ((M⁻¹).mulVec z) (Q.mulVec ((M⁻¹).mulVec z)) =
              dotProduct ((M⁻¹).mulVec z) (M.transpose.mulVec z) := by simp [hQmul]
          _ = dotProduct (M.mulVec ((M⁻¹).mulVec z)) z := by
              simpa using
                (section13_dotProduct_mulVec_right (A := M.transpose) (x := (M⁻¹).mulVec z) (y := z))
          _ = dotProduct z z := by simp [hMz]
      have : (1 / 2 : ℝ) * dotProduct ((M⁻¹).mulVec z) (Q.mulVec ((M⁻¹).mulVec z)) ≤ β := by
        simpa [hquad.symm] using hz'
      simpa using this
  -- Reduce via the linear-image lemma and the unit-ball formula.
  calc
    deltaStar {x : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) ≤ β} xStar =
        deltaStar ((fun z => (M⁻¹).mulVec z) '' (lam • Ball)) xStar := by
          simpa using
            congrArg (fun S : Set (Fin n → ℝ) => deltaStar S xStar) hD
    _ = deltaStar (lam • Ball) ((M⁻¹).transpose.mulVec xStar) := by
          simpa using
            (section13_deltaStar_image_mulVec (A := M⁻¹) (C := lam • Ball) (xStar := xStar))
    _ = Real.sqrt (2 * β * dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
          -- Use the unit-ball support function and rewrite the induced quadratic form.
          have hBallSupp :
              deltaStar (lam • Ball) ((M⁻¹).transpose.mulVec xStar) =
                lam * Real.sqrt (dotProduct ((M⁻¹).transpose.mulVec xStar) ((M⁻¹).transpose.mulVec xStar)) := by
            have h0 :
                deltaStar (({(0 : Fin n → ℝ)} : Set (Fin n → ℝ)) + (lam • Ball))
                    ((M⁻¹).transpose.mulVec xStar) =
                  dotProduct ((M⁻¹).transpose.mulVec xStar) (0 : Fin n → ℝ) +
                    lam * Real.sqrt (dotProduct ((M⁻¹).transpose.mulVec xStar) ((M⁻¹).transpose.mulVec xStar)) := by
              simpa [Ball] using
                (deltaStar_singleton_add_smul_unitEuclideanBall (n := n) (a := (0 : Fin n → ℝ))
                  (x := (M⁻¹).transpose.mulVec xStar) (lam := lam) hlam)
            simpa [zero_add, add_zero] using h0
          -- Identify `Q⁻¹` with `M⁻¹ * (M⁻¹)ᵀ`.
          have hMinv : (M.transpose * M)⁻¹ = M⁻¹ * (M.transpose)⁻¹ := by
            apply Matrix.inv_eq_right_inv
            have hMTdet : IsUnit M.transpose.det := Matrix.isUnit_det_transpose (A := M) hMdet
            have hMmulInv' : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMdet
            have hMTmulInv : M.transpose * (M.transpose)⁻¹ = 1 :=
              Matrix.mul_nonsing_inv M.transpose hMTdet
            calc
              (M.transpose * M) * (M⁻¹ * (M.transpose)⁻¹) =
                  M.transpose * (M * M⁻¹) * (M.transpose)⁻¹ := by
                simp [Matrix.mul_assoc]
              _ = 1 := by simp [hMmulInv', hMTmulInv]
          have hQinv : Q⁻¹ = M⁻¹ * (M⁻¹).transpose := by
            have hMTinv : (M.transpose)⁻¹ = (M⁻¹).transpose := by
              -- `transpose` commutes with nonsingular inverse.
              simpa using (Matrix.transpose_nonsing_inv (A := M)).symm
            calc
              Q⁻¹ = (M.transpose * M)⁻¹ := by simp [hQeq]
              _ = M⁻¹ * (M.transpose)⁻¹ := hMinv
              _ = M⁻¹ * (M⁻¹).transpose := by simp [hMTinv]
          have h2β : 0 ≤ 2 * β := by nlinarith [hβ]
          have hdot :
              dotProduct ((M⁻¹).transpose.mulVec xStar) ((M⁻¹).transpose.mulVec xStar) =
                dotProduct xStar ((Q⁻¹).mulVec xStar) := by
            have htmp :
                dotProduct xStar ((M⁻¹ * (M⁻¹).transpose).mulVec xStar) =
                  dotProduct ((M⁻¹).transpose.mulVec xStar) ((M⁻¹).transpose.mulVec xStar) := by
              simpa [Matrix.mulVec_mulVec] using
                (section13_dotProduct_mulVec_right (A := M⁻¹) (x := xStar)
                  (y := (M⁻¹).transpose.mulVec xStar))
            calc
              dotProduct ((M⁻¹).transpose.mulVec xStar) ((M⁻¹).transpose.mulVec xStar) =
                  dotProduct xStar ((M⁻¹ * (M⁻¹).transpose).mulVec xStar) := by
                    simpa using htmp.symm
              _ = dotProduct xStar ((Q⁻¹).mulVec xStar) := by simp [hQinv]
          have hsqrt :
              lam * Real.sqrt (dotProduct xStar ((Q⁻¹).mulVec xStar)) =
                Real.sqrt (2 * β * dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
            have := (Real.sqrt_mul h2β (dotProduct xStar ((Q⁻¹).mulVec xStar))).symm
            simpa [lam, mul_assoc] using this
          -- Finish.
          have : deltaStar (lam • Ball) ((M⁻¹).transpose.mulVec xStar) =
              Real.sqrt (2 * β * dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
            -- Start from the unit-ball formula.
            have : deltaStar (lam • Ball) ((M⁻¹).transpose.mulVec xStar) =
                lam * Real.sqrt (dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
              simpa [hdot, hQinv] using hBallSupp
            simpa [hsqrt] using this
          simpa using this

/-- Text 13.5.2: For the “elliptic” convex set

`C = {x | (1/2) ⟪x, Qx⟫ + ⟪a, x⟫ + α ≤ 0}`,

where `Q` is a positive definite symmetric matrix, one has (assuming `C ≠ ∅`)

`δ^*(xStar | C) = ⟪b, xStar⟫ + (2β ⟪xStar, Q⁻¹ xStar⟫)^{1/2}`,

where `b = -Q⁻¹ a` and `β = (1/2) ⟪a, Q⁻¹ a⟫ - α`. -/
theorem deltaStar_ellipticSet_eq {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (α : ℝ) (xStar : Fin n → ℝ) (hQ : Q.PosDef) :
    let C : Set (Fin n → ℝ) :=
      {x |
        (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct a x + α ≤ 0}
    let b : Fin n → ℝ := -((Q⁻¹).mulVec a)
    let β : ℝ := (1 / 2 : ℝ) * dotProduct a ((Q⁻¹).mulVec a) - α
    Set.Nonempty C →
      deltaStar C xStar =
        dotProduct xStar b + Real.sqrt (2 * β * dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
  classical
  intro C b β hCne
  have hβnonneg : 0 ≤ β := by
    simpa [C, b, β] using
      (section13_beta_nonneg_of_nonempty (Q := Q) (a := a) (α := α) hQ (by simpa [C] using hCne))
  let D : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) ≤ β}
  have hcomp :
      ∀ x, x ∈ C ↔ (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) ≤ β := by
    simpa [C, b, β] using
      (section13_ellipticSet_completeSquare_mem (Q := Q) (a := a) (α := α) hQ)
  have hCeq : C = ({b} : Set (Fin n → ℝ)) + D := by
    ext x
    constructor
    · intro hxC
      have hxD : x - b ∈ D := by
        have hxβ : (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) ≤ β := (hcomp x).1 hxC
        simpa [D] using hxβ
      refine ⟨b, by simp, x - b, hxD, ?_⟩
      abel_nf
    · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
      have hx₁' : x₁ = b := by simpa using hx₁
      subst hx₁'
      have hx₂ineq : (1 / 2 : ℝ) * dotProduct x₂ (Q.mulVec x₂) ≤ β := by
        simpa [D] using hx₂
      have hxβ :
          (1 / 2 : ℝ) * dotProduct ((b + x₂) - b) (Q.mulVec ((b + x₂) - b)) ≤ β := by
        simpa [add_sub_cancel_left] using hx₂ineq
      exact (hcomp (b + x₂)).2 hxβ
  have hDne : Set.Nonempty D := by
    rcases hCne with ⟨x, hxC⟩
    have hxβ : (1 / 2 : ℝ) * dotProduct (x - b) (Q.mulVec (x - b)) ≤ β := (hcomp x).1 hxC
    exact ⟨x - b, by simpa [D] using hxβ⟩
  have hbdd₁ :
      BddAbove (Set.image (fun x : Fin n → ℝ => dotProduct x xStar) ({b} : Set (Fin n → ℝ))) := by
    classical
    simp [Set.image_singleton]
  have hbdd₂ :
      BddAbove (Set.image (fun x : Fin n → ℝ => dotProduct x xStar) D) := by
    simpa [D] using
      (section13_bddAbove_image_dotProduct_centeredSublevel_posDef (Q := Q) (β := β) (xStar := xStar)
        hQ hβnonneg)
  have hdelta_add :
      deltaStar (({b} : Set (Fin n → ℝ)) + D) xStar =
        deltaStar ({b} : Set (Fin n → ℝ)) xStar + deltaStar D xStar := by
    simpa using
      (section13_deltaStar_add_of_bddAbove (C₁ := ({b} : Set (Fin n → ℝ))) (C₂ := D)
        (xStar := xStar) (hC₁ne := by simp) (hC₂ne := hDne) hbdd₁ hbdd₂)
  have hδD :
      deltaStar D xStar = Real.sqrt (2 * β * dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
    simpa [D] using
      (section13_deltaStar_centeredSublevel_posDef (Q := Q) (β := β) (xStar := xStar) hQ hβnonneg)
  calc
    deltaStar C xStar = deltaStar (({b} : Set (Fin n → ℝ)) + D) xStar := by simp [hCeq]
    _ = deltaStar ({b} : Set (Fin n → ℝ)) xStar + deltaStar D xStar := hdelta_add
    _ = dotProduct xStar b + Real.sqrt (2 * β * dotProduct xStar ((Q⁻¹).mulVec xStar)) := by
      simp [section13_deltaStar_singleton, hδD]

end Section13
end Chap03
