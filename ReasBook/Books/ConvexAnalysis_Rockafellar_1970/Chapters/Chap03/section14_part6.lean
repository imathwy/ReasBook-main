/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part5
section Chap03
section Section14

open scoped Pointwise
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- (Theorem 14.3, auxiliary) If `f* φ` is strictly positive, then `(posHomHull f)* φ = ⊤`.

This is the scaling argument used to identify the effective domain of the conjugate of the
positively-homogeneous hull. -/
lemma section14_fenchelConjugate_posHomHull_eq_top_of_fenchelConjugate_pos {f : E → EReal}
    (φ : Module.Dual ℝ E)
    (hpos :
      (0 : EReal) <
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ) :
    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
        (section14_posHomHull (E := E) f) φ = ⊤ := by
  classical
  -- Extract a witness `x0` with a strictly positive conjugate term.
  have hx0 : ∃ x0 : E, (0 : EReal) < (φ x0 : EReal) - f x0 := by
    by_contra hno
    have hall : ∀ x : E, (φ x : EReal) - f x ≤ (0 : EReal) := by
      intro x
      by_contra hx
      have hxpos : (0 : EReal) < (φ x : EReal) - f x := lt_of_not_ge hx
      exact hno ⟨x, hxpos⟩
    have hle : fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal) := by
      unfold fenchelConjugateBilin
      refine sSup_le ?_
      rintro _ ⟨x, rfl⟩
      exact hall x
    exact (not_lt_of_ge hle) hpos
  rcases hx0 with ⟨x0, hx0pos⟩
  -- If `f x0 = ⊥`, then already a single term of the `sSup` is `⊤`.
  by_cases hfbot : f x0 = ⊥
  · have hkbot : section14_posHomHull (E := E) f x0 = ⊥ := by
      have hxmem :
          (⊥ : EReal) ∈
            {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (t⁻¹ • x0)} := by
        refine ⟨(1 : ℝ), by norm_num, ?_⟩
        simp [hfbot]
      have hle : section14_posHomHull (E := E) f x0 ≤ ⊥ := by
        simpa [section14_posHomHull] using (sInf_le hxmem)
      exact le_antisymm hle bot_le
    -- The conjugate is `⊤` since the `x0`-term equals `⊤`.
    unfold fenchelConjugateBilin
    apply (EReal.eq_top_iff_forall_lt _).2
    intro y
    have htermTop :
        ((φ x0 : EReal) - section14_posHomHull (E := E) f x0) = ⊤ := by
      simp [hkbot]
    have htop_le :
        (⊤ : EReal) ≤ sSup (Set.range fun x : E => (φ x : EReal) - section14_posHomHull (E := E) f x) := by
      exact le_sSup ⟨x0, by simp [htermTop]⟩
    exact lt_of_lt_of_le (EReal.coe_lt_top y) htop_le
  · -- Otherwise, the positive witness `d` is a (finite) positive real.
    set d : EReal := (φ x0 : EReal) - f x0
    have hdpos : (0 : EReal) < d := by simpa [d] using hx0pos
    -- Show `f x0` is a real number.
    have hfTop : f x0 ≠ ⊤ := by
      intro hTop
      have : d = ⊥ := by simp [d, hTop]
      simp [this] at hdpos
    rcases
        section14_eq_coe_of_lt_top (z := f x0) (lt_top_iff_ne_top.2 hfTop) hfbot with
      ⟨fr, hfr⟩
    have hdcoe : d = ((φ x0 - fr : ℝ) : EReal) := by
      simp [d, hfr, EReal.coe_sub]
    have hdrpos : (0 : ℝ) < φ x0 - fr := by
      have : (0 : EReal) < ((φ x0 - fr : ℝ) : EReal) := by simpa [hdcoe] using hdpos
      simpa using (EReal.coe_lt_coe_iff.1 this)
    -- The conjugate is above every real.
    unfold fenchelConjugateBilin
    apply (EReal.eq_top_iff_forall_lt _).2
    intro y
    -- Choose `n` so that `y < n * (φ x0 - fr)`.
    obtain ⟨n0 : ℕ, hn0 : y / (φ x0 - fr) < n0⟩ := exists_nat_gt (y / (φ x0 - fr))
    let n : ℕ := n0 + 1
    have hn : y / (φ x0 - fr) < (n : ℝ) := by
      have hnlt : (n0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (Nat.lt_succ_self n0)
      exact lt_trans hn0 hnlt
    have hmul : y < (n : ℝ) * (φ x0 - fr) := (div_lt_iff₀ hdrpos).1 hn
    have hylt : (y : EReal) < ((n : ℝ) * (φ x0 - fr) : ℝ) := by exact_mod_cast hmul
    -- Compare with the term at `x = n • x0`.
    have htpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := Nat.succ_pos n0
      exact_mod_cast this
    have hk_le :
        section14_posHomHull (E := E) f ((n : ℝ) • x0) ≤ ((n : ℝ) : EReal) * f x0 :=
      section14_posHomHull_smul_le (E := E) (f := f) (t := (n : ℝ)) htpos x0
    have hsub :
        (φ ((n : ℝ) • x0) : EReal) - (((n : ℝ) : EReal) * f x0) ≤
          (φ ((n : ℝ) • x0) : EReal) - section14_posHomHull (E := E) f ((n : ℝ) • x0) := by
      simpa using
        (EReal.sub_le_sub (x := (φ ((n : ℝ) • x0) : EReal)) (y := (φ ((n : ℝ) • x0) : EReal))
              (z := ((n : ℝ) : EReal) * f x0)
              (t := section14_posHomHull (E := E) f ((n : ℝ) • x0))
              le_rfl hk_le)
    have hterm_eq :
        (φ ((n : ℝ) • x0) : EReal) - (((n : ℝ) : EReal) * f x0) =
          (((n : ℝ) * (φ x0 - fr) : ℝ) : EReal) := by
      -- Everything is a real coercion.
      have hφn : (φ ((n : ℝ) • x0) : EReal) = (((n : ℝ) * φ x0 : ℝ) : EReal) := by
        simp [map_smul, smul_eq_mul, EReal.coe_mul]
      have hfn : (((n : ℝ) : EReal) * f x0) = (((n : ℝ) * fr : ℝ) : EReal) := by
        simp [hfr, EReal.coe_mul]
      -- Compute in `ℝ` and cast back.
      have hreal :
          (n : ℝ) * φ x0 - (n : ℝ) * fr = (n : ℝ) * (φ x0 - fr) := by ring
      -- Rewrite the subtraction in `EReal` as a real subtraction.
      calc
        (φ ((n : ℝ) • x0) : EReal) - (((n : ℝ) : EReal) * f x0) =
            (((n : ℝ) * φ x0 : ℝ) : EReal) - (((n : ℝ) * fr : ℝ) : EReal) := by
              -- Rewrite both sides as real coercions.
              rw [hφn, hfr]
              simp [EReal.coe_mul]
        _ = (((((n : ℝ) * φ x0) - ((n : ℝ) * fr)) : ℝ) : EReal) := by
              simp [EReal.coe_sub]
        _ = (((((n : ℝ) * (φ x0 - fr)) : ℝ)) : EReal) := by
              simp [hreal]
    have hylt_term :
        (y : EReal) < (φ ((n : ℝ) • x0) : EReal) - (((n : ℝ) : EReal) * f x0) := by
      -- Use the explicit computation of the term.
      -- `rw` is more reliable than `simp` here, since `simp` may rewrite the left-hand side first.
      rw [hterm_eq]
      exact hylt
    have hylt_term' :
        (y : EReal) < (φ ((n : ℝ) • x0) : EReal) - section14_posHomHull (E := E) f ((n : ℝ) • x0) :=
      lt_of_lt_of_le hylt_term hsub
    have hleSup :
        (φ ((n : ℝ) • x0) : EReal) - section14_posHomHull (E := E) f ((n : ℝ) • x0) ≤
          sSup (Set.range fun x : E => (φ x : EReal) - section14_posHomHull (E := E) f x) :=
      le_sSup ⟨(n : ℝ) • x0, rfl⟩
    exact lt_of_lt_of_le hylt_term' hleSup

/-- (Theorem 14.3, auxiliary) The effective domain of the conjugate of the positively homogeneous
hull is exactly the `0`-sublevel set of the original conjugate. -/
lemma section14_erealDom_fenchelConjugate_posHomHull_eq_sublevelZero {f : E → EReal} :
    erealDom
        (fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
          (section14_posHomHull (E := E) f)) =
      {φ : Module.Dual ℝ E |
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)} := by
  classical
  ext φ
  constructor
  · intro hφ
    -- If `f* φ > 0`, then `k* φ = ⊤`, contradicting `hφ : k* φ < ⊤`.
    by_contra hne
    have hpos : (0 : EReal) < fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ := by
      exact lt_of_not_ge hne
    have htop :
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
            (section14_posHomHull (E := E) f) φ = ⊤ :=
      section14_fenchelConjugate_posHomHull_eq_top_of_fenchelConjugate_pos (E := E) (f := f) (φ := φ) hpos
    have hφ' := hφ
    simp [erealDom, htop] at hφ'
  · intro hφ
    -- Use the already-proved equality of `0`-sublevel sets under `posHomHull`.
    have hkφ : fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
        (section14_posHomHull (E := E) f) φ ≤ (0 : EReal) := by
      have : φ ∈ {ψ : Module.Dual ℝ E |
          fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
            (section14_posHomHull (E := E) f) ψ ≤ (0 : EReal)} := by
        -- Rewrite membership using `section14_sublevelZero_fenchelConjugate_posHomHull_eq`.
        have : φ ∈ {ψ : Module.Dual ℝ E |
            fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f ψ ≤ (0 : EReal)} := by
          exact hφ
        simpa [section14_sublevelZero_fenchelConjugate_posHomHull_eq (E := E) (f := f)] using this
      simpa using this
    -- `k* φ ≤ 0` implies `k* φ < ⊤`.
    have : fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
        (section14_posHomHull (E := E) f) φ < ⊤ :=
      lt_of_le_of_lt hkφ (by simp)
    simpa [erealDom] using this

/-- The positively-homogeneous hull takes value `0` at the origin, provided `f 0` is finite and
strictly positive. -/
lemma section14_posHomHull_zero {f : E → EReal} (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤)
    (hf0_ne_bot : f 0 ≠ ⊥) :
    section14_posHomHull (E := E) f 0 = 0 := by
  classical
  -- Write `f 0` as a real number.
  rcases section14_eq_coe_of_lt_top (z := f 0) hf0_ltTop hf0_ne_bot with ⟨a, ha⟩
  have ha_pos : (0 : ℝ) < a := by
    have : (0 : EReal) < (a : EReal) := by simpa [ha] using hf0
    simpa using (EReal.coe_lt_coe_iff.1 this)
  -- Unfold the definition of `k` at `0`.
  have hk0 :
      section14_posHomHull (E := E) f (0 : E) =
        sInf {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (0 : E)} := by
    simp [section14_posHomHull]
  -- Work with the simplified infimum set.
  set S0 : Set EReal := {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (0 : E)} with hS0
  have hk0' : section14_posHomHull (E := E) f (0 : E) = sInf S0 := by simpa [hS0] using hk0
  -- `0` is a lower bound, hence `0 ≤ sInf S0`.
  have h0_le : (0 : EReal) ≤ sInf S0 := by
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    have ht0 : (0 : EReal) ≤ (t : EReal) := by
      simpa [EReal.coe_nonneg] using (show (0 : ℝ) ≤ t from le_of_lt ht)
    have hf0_0 : (0 : EReal) ≤ f (0 : E) := le_of_lt hf0
    exact mul_nonneg ht0 hf0_0
  -- `sInf S0` cannot be strictly positive: otherwise choose a small scaling parameter.
  have hsInf_le0 : sInf S0 ≤ (0 : EReal) := by
    by_contra hgt
    have hsInf_pos : (0 : EReal) < sInf S0 := lt_of_not_ge hgt
    -- `sInf S0` is finite since it is bounded above by the `t = 1` element.
    have hsInf_ltTop : sInf S0 < ⊤ := by
      have hmem : (f (0 : E)) ∈ S0 := by
        refine ⟨(1 : ℝ), by norm_num, ?_⟩
        simp
      exact lt_of_le_of_lt (sInf_le hmem) hf0_ltTop
    have hsInf_ne_bot : sInf S0 ≠ ⊥ := by
      have : (⊥ : EReal) < sInf S0 :=
        lt_of_lt_of_le (by simp) h0_le
      exact ne_of_gt this
    rcases section14_eq_coe_of_lt_top (z := sInf S0) hsInf_ltTop hsInf_ne_bot with ⟨b, hb⟩
    have hb_pos : (0 : ℝ) < b := by
      have : (0 : EReal) < (b : EReal) := by simpa [hb] using hsInf_pos
      simpa using (EReal.coe_lt_coe_iff.1 this)
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    let t : ℝ := b / (2 * a)
    have ht_pos : 0 < t := by
      have : 0 < 2 * a := by nlinarith [ha_pos]
      exact div_pos hb_pos this
    have ht0 : t ≠ 0 := ne_of_gt ht_pos
    have hmem : ((t : EReal) * f (0 : E)) ∈ S0 := ⟨t, ht_pos, rfl⟩
    have hle : sInf S0 ≤ (t : EReal) * f (0 : E) := sInf_le hmem
    have hlt : (t : EReal) * f (0 : E) < sInf S0 := by
      -- Compute in `ℝ`: `t * a = b/2 < b`.
      have hta : t * a = b / 2 := by
        dsimp [t]
        field_simp [ha_ne]
      have : (t : EReal) * f (0 : E) = ((b / 2 : ℝ) : EReal) := by
        -- Expand using `ha` and the computation of `t * a`.
        calc
          (t : EReal) * f (0 : E) = (t : EReal) * (a : EReal) := by simp [ha]
          _ = ((t * a : ℝ) : EReal) := by simp
          _ = ((b / 2 : ℝ) : EReal) := by simp [hta]
      have hb2 : (b / 2 : ℝ) < b := by nlinarith
      have hb2' : ((b / 2 : ℝ) : EReal) < (b : EReal) := by
        simpa using (EReal.coe_lt_coe_iff.2 hb2)
      -- Rewrite `sInf S0` as `b` using `hb`.
      simpa [this] using hb2'.trans_eq hb.symm
    exact (hlt.not_ge hle)
  have : sInf S0 = (0 : EReal) := le_antisymm hsInf_le0 h0_le
  simp [hk0', this]

/-- Strict negativity for the positively-homogeneous hull forces membership in the conic hull of
the `0`-sublevel set of `f`. -/
lemma section14_strictSublevel_posHomHull_subset_coneHull_sublevelZero
    {f : E → EReal} (hf : ProperConvexERealFunction (F := E) f) :
    {x : E | section14_posHomHull (E := E) f x < (0 : EReal)} ⊆
      ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
  classical
  intro x hx
  have hx0 : section14_posHomHull (E := E) f x < (0 : EReal) := by simpa using hx
  -- Unfold the infimum defining `k` and extract a witness strictly below `0`.
  have hx' :
      ∃ r ∈ {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (t⁻¹ • x)}, r < (0 : EReal) := by
    simpa [section14_posHomHull] using (sInf_lt_iff).1 hx0
  rcases hx' with ⟨_, ⟨t, ht, rfl⟩, htlt⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht
  -- The inequality `t * f(t⁻¹ • x) < 0` forces `f(t⁻¹ • x)` to be finite.
  have hfx_ltTop : f (t⁻¹ • x) < ⊤ := by
    by_contra hTop
    have : f (t⁻¹ • x) = ⊤ := top_le_iff.1 (le_of_not_gt hTop)
    have : (t : EReal) * f (t⁻¹ • x) = ⊤ := by
      simpa [this] using (EReal.coe_mul_top_of_pos ht)
    have htlt' := htlt
    simp [this] at htlt'
  rcases section14_eq_coe_of_lt_top (z := f (t⁻¹ • x)) hfx_ltTop (hf.1.1 (t⁻¹ • x)) with ⟨a, ha⟩
  have ha_lt0 : a < 0 := by
    -- Compare in `ℝ` after rewriting `f (t⁻¹ • x)`.
    have : ((t : EReal) * f (t⁻¹ • x)) < (0 : EReal) := by simpa using htlt
    have : ((t * a : ℝ) : EReal) < (0 : EReal) := by simpa [ha, EReal.coe_mul] using this
    have hta : t * a < 0 := by simpa using (EReal.coe_lt_coe_iff.1 this)
    have hcases : (0 < t ∧ a < 0) ∨ (t < 0 ∧ 0 < a) := (mul_neg_iff).1 hta
    rcases hcases with ⟨_, ha_neg⟩ | ⟨htneg, _⟩
    · exact ha_neg
    · exact (False.elim ((not_lt_of_ge (le_of_lt ht) htneg)))
  have hxS : f (t⁻¹ • x) ≤ (0 : EReal) := by
    have : (a : EReal) ≤ (0 : EReal) := by
      simpa using (EReal.coe_le_coe_iff.2 (le_of_lt ha_lt0))
    simpa [ha] using this
  have hxHull :
      t⁻¹ • x ∈ (ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) :=
    ConvexCone.subset_hull (R := ℝ) (s := {x : E | f x ≤ (0 : EReal)}) hxS
  -- Scale back by `t` to recover `x`.
  have : t • (t⁻¹ • x) ∈ (ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) :=
    ConvexCone.smul_mem (C := ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)}) ht hxHull
  simpa [smul_inv_smul₀ ht_ne] using this

/-- (Theorem 14.3, auxiliary) Under the hypotheses ensuring nonemptiness of the dual `0`-sublevel
set, the positively homogeneous hull never takes the value `⊥`. -/
lemma section14_posHomHull_ne_bot
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) :
    ∀ x : E, section14_posHomHull (E := E) f x ≠ ⊥ := by
  classical
  obtain ⟨ψ, hψ⟩ :=
    section14_sublevelZero_fenchelConjugate_nonempty (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hψ_le : ∀ x : E, (ψ x : EReal) ≤ f x :=
    (section14_fenchelConjugate_le_zero_iff (E := E) (f := f) ψ).1 (by simpa using hψ)
  have hψ_le_k :
      ∀ x : E, (ψ x : EReal) ≤ section14_posHomHull (E := E) f x :=
    section14_le_posHomHull_of_le (E := E) (f := f) (φ := ψ) hψ_le
  intro x hx
  have : (ψ x : EReal) ≤ (⊥ : EReal) := by simpa [hx] using hψ_le_k x
  exact (not_le_of_gt (EReal.bot_lt_coe (ψ x))) this

/-- (Theorem 14.3, auxiliary) Subadditivity of the positively homogeneous hull. -/
lemma section14_posHomHull_subadd
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) :
    ∀ x y : E,
      section14_posHomHull (E := E) f (x + y) ≤
        section14_posHomHull (E := E) f x + section14_posHomHull (E := E) f y := by
  classical
  intro x y
  let k : E → EReal := section14_posHomHull (E := E) f
  change k (x + y) ≤ k x + k y

  have hk_ne_bot : ∀ z : E, k z ≠ ⊥ :=
    section14_posHomHull_ne_bot (E := E) (f := f) hf hf_closed hf0 hf0_ltTop

  -- Trivial cases where the right-hand side is `⊤`.
  by_cases hkx_top : k x = ⊤
  · have hky_ne_bot : k y ≠ ⊥ := hk_ne_bot y
    have hsum : k x + k y = ⊤ := by simpa [hkx_top] using (EReal.top_add_of_ne_bot hky_ne_bot)
    rw [hsum]
    exact le_top
  by_cases hky_top : k y = ⊤
  · have hkx_ne_bot : k x ≠ ⊥ := hk_ne_bot x
    have hsum : k x + k y = ⊤ := by simpa [hky_top] using (EReal.add_top_of_ne_bot hkx_ne_bot)
    rw [hsum]
    exact le_top

  have hkx_ltTop : k x < ⊤ := lt_of_le_of_ne le_top hkx_top
  have hky_ltTop : k y < ⊤ := lt_of_le_of_ne le_top hky_top
  rcases section14_eq_coe_of_lt_top (z := k x) hkx_ltTop (hk_ne_bot x) with ⟨a, ha⟩
  rcases section14_eq_coe_of_lt_top (z := k y) hky_ltTop (hk_ne_bot y) with ⟨b, hb⟩

  -- Epsilon argument in `ℝ`.
  have hlt :
      ∀ ε : ℝ, 0 < ε → k (x + y) < ((a + b + ε : ℝ) : EReal) := by
    intro ε hε
    -- Choose a small error term `δ`.
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith

    -- Extract witnesses from the infimum definitions of `k x` and `k y`.
    have hxlt : k x < ((a + δ : ℝ) : EReal) := by
      have : ((a : ℝ) : EReal) < ((a + δ : ℝ) : EReal) := by
        exact_mod_cast (lt_add_of_pos_right a hδ)
      simpa [k, ha] using this
    have hylt : k y < ((b + δ : ℝ) : EReal) := by
      have : ((b : ℝ) : EReal) < ((b + δ : ℝ) : EReal) := by
        exact_mod_cast (lt_add_of_pos_right b hδ)
      simpa [k, hb] using this

    have hx' :
        ∃ r ∈ {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (t⁻¹ • x)},
          r < ((a + δ : ℝ) : EReal) := by
      simpa [k, section14_posHomHull, ha] using (sInf_lt_iff).1 hxlt
    have hy' :
        ∃ r ∈ {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (t⁻¹ • y)},
          r < ((b + δ : ℝ) : EReal) := by
      simpa [k, section14_posHomHull, hb] using (sInf_lt_iff).1 hylt

    rcases hx' with ⟨_, ⟨t1, ht1, rfl⟩, ht1lt⟩
    rcases hy' with ⟨_, ⟨t2, ht2, rfl⟩, ht2lt⟩

    -- Use the scaling `t = t1 + t2` for the sum.
    set t : ℝ := t1 + t2 with ht_def
    have ht : 0 < t := add_pos ht1 ht2
    have ht_ne : t ≠ 0 := ne_of_gt ht

    have hkxy_le :
        k (x + y) ≤ (t : EReal) * f (t⁻¹ • (x + y)) := by
      have hxmem :
          (t : EReal) * f (t⁻¹ • (x + y)) ∈
            {r : EReal | ∃ t' : ℝ, 0 < t' ∧ r = (t' : EReal) * f (t'⁻¹ • (x + y))} := by
        refine ⟨t, ht, rfl⟩
      simpa [k, section14_posHomHull] using (sInf_le hxmem)

    -- Convexity estimate:
    -- `(t1+t2) * f((t1+t2)⁻¹ • (x+y)) ≤ t1 * f(t1⁻¹•x) + t2 * f(t2⁻¹•y)`.
    have hconvineq :
        (t : EReal) * f (t⁻¹ • (x + y)) ≤
          (t1 : EReal) * f (t1⁻¹ • x) + (t2 : EReal) * f (t2⁻¹ • y) := by
      have hfconv : ConvexERealFunction (F := E) f := hf.2
      let aCoeff : ℝ := t1 / t
      let bCoeff : ℝ := t2 / t
      have haCoeff : 0 ≤ aCoeff := div_nonneg (le_of_lt ht1) (le_of_lt ht)
      have hbCoeff : 0 ≤ bCoeff := div_nonneg (le_of_lt ht2) (le_of_lt ht)
      have habCoeff : aCoeff + bCoeff = 1 := by
        -- `(t1/t) + (t2/t) = (t1+t2)/t = 1`.
        dsimp [aCoeff, bCoeff]
        field_simp [ht_ne]
        simp [ht_def]
      have harg :
          aCoeff • (t1⁻¹ • x) + bCoeff • (t2⁻¹ • y) = (t⁻¹ : ℝ) • (x + y) := by
        have ht1_ne : t1 ≠ 0 := ne_of_gt ht1
        have ht2_ne : t2 ≠ 0 := ne_of_gt ht2
        calc
          aCoeff • (t1⁻¹ • x) + bCoeff • (t2⁻¹ • y)
              = ((t⁻¹ : ℝ) • x) + ((t⁻¹ : ℝ) • y) := by
                  simp [aCoeff, bCoeff, div_eq_mul_inv, smul_smul, mul_comm, ht1_ne, ht2_ne]
          _ = (t⁻¹ : ℝ) • (x + y) := by
                  simp
      have hconv :=
        hfconv (x := (t1⁻¹ : ℝ) • x) (y := (t2⁻¹ : ℝ) • y) (a := aCoeff) (b := bCoeff) haCoeff
          hbCoeff habCoeff
      have hconv' :
          f ((t⁻¹ : ℝ) • (x + y)) ≤
            (aCoeff : EReal) * f ((t1⁻¹ : ℝ) • x) + (bCoeff : EReal) * f ((t2⁻¹ : ℝ) • y) := by
        simpa [harg] using hconv
      have htE : (0 : EReal) ≤ (t : EReal) := by
        simpa [EReal.coe_nonneg] using (show (0 : ℝ) ≤ t from le_of_lt ht)
      have hmul := mul_le_mul_of_nonneg_left hconv' htE
      -- Distribute and simplify the coefficients.
      have hta : (t : EReal) * (aCoeff : EReal) = (t1 : EReal) := by
        have hreal : t * aCoeff = t1 := by
          dsimp [aCoeff]
          field_simp [ht_ne]
        calc
          (t : EReal) * (aCoeff : EReal) = ((t * aCoeff : ℝ) : EReal) := by
            simp
          _ = (t1 : EReal) := by simp [hreal]
      have htb : (t : EReal) * (bCoeff : EReal) = (t2 : EReal) := by
        have hreal : t * bCoeff = t2 := by
          dsimp [bCoeff]
          field_simp [ht_ne]
        calc
          (t : EReal) * (bCoeff : EReal) = ((t * bCoeff : ℝ) : EReal) := by
            simp
          _ = (t2 : EReal) := by simp [hreal]
      -- Finish the inequality (distribute and simplify coefficients).
      calc
        (t : EReal) * f ((t⁻¹ : ℝ) • (x + y)) ≤
            (t : EReal) * ((aCoeff : EReal) * f ((t1⁻¹ : ℝ) • x) +
              (bCoeff : EReal) * f ((t2⁻¹ : ℝ) • y)) := hmul
        _ = (t : EReal) * ((aCoeff : EReal) * f ((t1⁻¹ : ℝ) • x)) +
              (t : EReal) * ((bCoeff : EReal) * f ((t2⁻¹ : ℝ) • y) ) := by
            -- Distribute since the multiplier is finite and nonnegative.
            simpa using
              (EReal.left_distrib_of_nonneg_of_ne_top (x := (t : EReal)) htE (by simp)
                ((aCoeff : EReal) * f ((t1⁻¹ : ℝ) • x)) ((bCoeff : EReal) * f ((t2⁻¹ : ℝ) • y)))
        _ =
            ((t : EReal) * (aCoeff : EReal)) * f ((t1⁻¹ : ℝ) • x) +
              ((t : EReal) * (bCoeff : EReal)) * f ((t2⁻¹ : ℝ) • y) := by
            simp [mul_assoc]
        _ = (t1 : EReal) * f ((t1⁻¹ : ℝ) • x) + (t2 : EReal) * f ((t2⁻¹ : ℝ) • y) := by
            simp [hta, htb]

    have hsum_lt :
        (t1 : EReal) * f (t1⁻¹ • x) + (t2 : EReal) * f (t2⁻¹ • y) <
          ((a + δ : ℝ) : EReal) + ((b + δ : ℝ) : EReal) :=
      EReal.add_lt_add ht1lt ht2lt
    have habδ :
        ((a + δ : ℝ) : EReal) + ((b + δ : ℝ) : EReal) = ((a + b + ε : ℝ) : EReal) := by
      calc
        ((a + δ : ℝ) : EReal) + ((b + δ : ℝ) : EReal) =
            ((a + δ + (b + δ) : ℝ) : EReal) := by
              simp
        _ = ((a + b + ε : ℝ) : EReal) := by
              congr 1
              dsimp [δ]
              ring
    have hkxy_lt :
        k (x + y) < ((a + b + ε : ℝ) : EReal) := by
      have hsum_lt' :
          (t1 : EReal) * f (t1⁻¹ • x) + (t2 : EReal) * f (t2⁻¹ • y) <
            ((a + b + ε : ℝ) : EReal) :=
        lt_of_lt_of_le hsum_lt (le_of_eq habδ)
      exact lt_of_le_of_lt (hkxy_le.trans hconvineq) hsum_lt'
    simpa [k] using hkxy_lt

  have hkxy_ltTop : k (x + y) < ⊤ := by
    have : k (x + y) < ((a + b + (1 : ℝ) : ℝ) : EReal) := hlt 1 (by norm_num)
    exact lt_of_lt_of_le this (le_of_lt (EReal.coe_lt_top (a + b + (1 : ℝ))))
  rcases section14_eq_coe_of_lt_top (z := k (x + y)) hkxy_ltTop (hk_ne_bot (x + y)) with ⟨c, hc⟩

  have hc_le : c ≤ a + b := by
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    have hε' : k (x + y) < ((a + b + ε : ℝ) : EReal) := hlt ε hε
    have : ((c : ℝ) : EReal) < ((a + b + ε : ℝ) : EReal) := by simpa [hc] using hε'
    exact (EReal.coe_lt_coe_iff.1 this)

  have hkxy_le : k (x + y) ≤ ((a + b : ℝ) : EReal) := by
    have : ((c : ℝ) : EReal) ≤ ((a + b : ℝ) : EReal) := (EReal.coe_le_coe_iff.2 hc_le)
    simpa [hc] using this

  -- Translate back to `k x + k y`.
  have : k (x + y) ≤ k x + k y := by
    simpa [k, ha, hb, EReal.coe_add, add_assoc, add_left_comm, add_comm] using hkxy_le
  simpa [k] using this

/-- (Theorem 14.3, auxiliary) The positively homogeneous hull is a proper convex function. -/
lemma section14_properConvex_posHomHull
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) :
    ProperConvexERealFunction (F := E) (section14_posHomHull (E := E) f) := by
  classical
  let k : E → EReal := section14_posHomHull (E := E) f
  have hk_ne_bot : ∀ x : E, k x ≠ ⊥ :=
    section14_posHomHull_ne_bot (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hk0 : k 0 = 0 :=
    section14_posHomHull_zero (E := E) (f := f) (hf0 := hf0) (hf0_ltTop := hf0_ltTop)
      (hf0_ne_bot := hf.1.1 0)

  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      simpa [k] using hk_ne_bot x
    · refine ⟨0, ?_⟩
      -- `k 0 = 0` is finite.
      simp [k, hk0]
  · -- Convexity from subadditivity + positive homogeneity.
    intro x y a b ha hb hab
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simp
    by_cases hb0 : b = 0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simp
    have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)

    have hsub :=
      section14_posHomHull_subadd (E := E) (f := f) hf hf_closed hf0 hf0_ltTop (a • x) (b • y)
    have hhom_a : k (a • x) = (a : EReal) * k x :=
      section14_posHomHull_smul (E := E) (f := f) ha_pos x
    have hhom_b : k (b • y) = (b : EReal) * k y :=
      section14_posHomHull_smul (E := E) (f := f) hb_pos y
    -- Combine.
    simpa [k, hhom_a, hhom_b, add_assoc, add_left_comm, add_comm] using hsub

/-- In the weak topology on the algebraic dual induced by evaluation, every evaluation map
`φ ↦ φ x` is continuous. -/
noncomputable local instance section14_instTopologicalSpace_dualWeak_part6 :
    TopologicalSpace (Module.Dual ℝ E) :=
  section14_instTopologicalSpace_dualWeak (E := E)

lemma section14_continuous_dual_apply (x : E) :
    Continuous fun φ : Module.Dual ℝ E => φ x := by
  let B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip
  have hcont : Continuous fun φ : Module.Dual ℝ E => fun y : E => B φ y := by
    simpa [section14_instTopologicalSpace_dualWeak, WeakBilin.instTopologicalSpace, B] using
      (continuous_induced_dom :
        Continuous fun φ : Module.Dual ℝ E => fun y : E => B φ y)
  have hx : Continuous fun φ : Module.Dual ℝ E => B φ x := by
    simpa using (continuous_pi_iff.1 hcont x)
  simpa [B, LinearMap.applyₗ] using hx

/-- The Fenchel conjugate (with respect to the evaluation pairing) is lower semicontinuous in the
weak topology on `Module.Dual ℝ E`. -/
lemma section14_lowerSemicontinuous_fenchelConjugate_dual (f : E → EReal) :
    LowerSemicontinuous
      (fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f) := by
  classical
  -- Rewrite `sSup (range ...)` as an `iSup`.
  have hrepr :
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f =
        fun φ : Module.Dual ℝ E => ⨆ x : E, ((φ x : EReal) - f x) := by
    funext φ
    simp [fenchelConjugateBilin, sSup_range, LinearMap.applyₗ]
  have hterm :
      ∀ x : E, LowerSemicontinuous fun φ : Module.Dual ℝ E => (φ x : EReal) - f x := by
    intro x
    have hcontReal : Continuous fun φ : Module.Dual ℝ E => φ x :=
      section14_continuous_dual_apply (E := E) x
    have hcont : Continuous fun φ : Module.Dual ℝ E => (φ x : EReal) :=
      continuous_coe_real_ereal.comp hcontReal
    have hpair : Continuous fun φ : Module.Dual ℝ E => ((φ x : EReal), -(f x)) :=
      hcont.prodMk continuous_const
    have hlsc : LowerSemicontinuous fun φ : Module.Dual ℝ E => (φ x : EReal) + (-(f x)) :=
      (EReal.lowerSemicontinuous_add.comp hpair)
    simpa [sub_eq_add_neg] using hlsc
  have : LowerSemicontinuous fun φ : Module.Dual ℝ E => ⨆ x : E, ((φ x : EReal) - f x) :=
    lowerSemicontinuous_iSup hterm
  simpa [hrepr] using this

/-- The Fenchel conjugate with respect to the flipped evaluation pairing is lower semicontinuous
as a function of the primal variable (in finite dimensions, where all linear functionals are
continuous). -/
lemma section14_lowerSemicontinuous_fenchelConjugate_flip
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    (g : Module.Dual ℝ E → EReal) :
    LowerSemicontinuous
      (fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip g) := by
  classical
  have hrepr :
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip g =
        fun x : E => ⨆ φ : Module.Dual ℝ E, ((φ x : EReal) - g φ) := by
    funext x
    simp [fenchelConjugateBilin, sSup_range, LinearMap.applyₗ]
  have hterm :
      ∀ φ : Module.Dual ℝ E, LowerSemicontinuous fun x : E => (φ x : EReal) - g φ := by
    intro φ
    have hcontReal : Continuous fun x : E => φ x := by
      simpa using (LinearMap.continuous_of_finiteDimensional (f := (φ : E →ₗ[ℝ] ℝ)))
    have hcont : Continuous fun x : E => (φ x : EReal) :=
      continuous_coe_real_ereal.comp hcontReal
    have hpair : Continuous fun x : E => ((φ x : EReal), -(g φ)) :=
      hcont.prodMk continuous_const
    have hlsc : LowerSemicontinuous fun x : E => (φ x : EReal) + (-(g φ)) :=
      (EReal.lowerSemicontinuous_add.comp hpair)
    simpa [sub_eq_add_neg] using hlsc
  have : LowerSemicontinuous fun x : E => ⨆ φ : Module.Dual ℝ E, ((φ x : EReal) - g φ) :=
    lowerSemicontinuous_iSup hterm
  simpa [hrepr] using this

/-- (Theorem 14.3, auxiliary) The *closed hull* `cl k` of the positively homogeneous hull is
modeled as the Fenchel biconjugate `(k*)*`, and is lower semicontinuous. -/
lemma section14_lowerSemicontinuous_posHomHull
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {f : E → EReal} (_hf_closed : LowerSemicontinuous f) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    LowerSemicontinuous
      (fenchelConjugateBilin p.flip (fenchelConjugateBilin p (section14_posHomHull (E := E) f))) := by
  intro p
  -- The conjugate is always lower semicontinuous; no semicontinuity assumption on the inner
  -- function is needed here.
  simpa using
    (section14_lowerSemicontinuous_fenchelConjugate_flip (E := E)
      (g := fenchelConjugateBilin p (section14_posHomHull (E := E) f)))

/-- (Theorem 14.3, auxiliary) The Fenchel conjugate of a proper `EReal` function (with respect to
any real bilinear pairing) never takes the value `⊥`. -/
lemma section14_fenchelConjugate_ne_bot_of_proper {E₁ F₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [AddCommGroup F₁] [Module ℝ F₁] (p : E₁ →ₗ[ℝ] F₁ →ₗ[ℝ] ℝ) {f : E₁ → EReal}
    (hf : ProperERealFunction f) :
    ∀ y : F₁, fenchelConjugateBilin (E := E₁) p f y ≠ ⊥ := by
  classical
  intro y
  rcases hf.2 with ⟨x0, hx0neTop⟩
  have hx0lt : f x0 < ⊤ := lt_top_iff_ne_top.2 hx0neTop
  rcases section14_eq_coe_of_lt_top (z := f x0) hx0lt (hf.1 x0) with ⟨r0, hr0⟩
  have hle :
      ((p x0 y : EReal) - f x0) ≤ fenchelConjugateBilin (E := E₁) p f y := by
    unfold fenchelConjugateBilin
    exact le_sSup ⟨x0, rfl⟩
  intro hbot
  have hle' : ((p x0 y - r0 : ℝ) : EReal) ≤ (⊥ : EReal) := by
    have hle' := hle
    simp [hbot, hr0, sub_eq_add_neg] at hle'
  exact (not_le_of_gt (EReal.bot_lt_coe (p x0 y - r0))) hle'

/-- (Theorem 14.3, auxiliary) Antitonicity of the Fenchel conjugate in the primal function. -/
lemma section14_fenchelConjugate_anti {E₁ F₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [AddCommGroup F₁] [Module ℝ F₁] (p : E₁ →ₗ[ℝ] F₁ →ₗ[ℝ] ℝ) {f g : E₁ → EReal}
    (hfg : ∀ x, f x ≤ g x) :
    ∀ y : F₁, fenchelConjugateBilin (E := E₁) p g y ≤ fenchelConjugateBilin (E := E₁) p f y := by
  classical
  intro y
  unfold fenchelConjugateBilin
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  -- `p x y - g x ≤ p x y - f x` since `f x ≤ g x` and subtraction is antitone on the right.
  have hterm :
      (p x y : EReal) - g x ≤ (p x y : EReal) - f x := by
    simpa using
      (EReal.sub_le_sub (x := (p x y : EReal)) (y := (p x y : EReal)) (z := g x) (t := f x)
            le_rfl (hfg x))
  have hsup : (p x y : EReal) - f x ≤ sSup (Set.range fun x : E₁ => (p x y : EReal) - f x) :=
    le_sSup ⟨x, rfl⟩
  exact hterm.trans hsup

/-- (Theorem 14.3, auxiliary) Fenchel biconjugate inequality: if `f` is proper, then `(f*)* ≤ f`. -/
lemma section14_fenchelBiconjugate_le_of_proper {E₁ F₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [AddCommGroup F₁] [Module ℝ F₁] (p : E₁ →ₗ[ℝ] F₁ →ₗ[ℝ] ℝ) {f : E₁ → EReal}
    (hf : ProperERealFunction f) :
    ∀ x : E₁, fenchelConjugateBilin (E := F₁) p.flip (fenchelConjugateBilin (E := E₁) p f) x ≤ f x := by
  classical
  intro x
  -- Expand the biconjugate as a supremum over `y : F₁`.
  unfold fenchelConjugateBilin
  refine sSup_le ?_
  rintro _ ⟨y, rfl⟩
  -- Start from the defining inequality for the conjugate at the point `x`.
  have hle0 :
      ((p x y : EReal) - f x) ≤ fenchelConjugateBilin (E := E₁) p f y := by
    unfold fenchelConjugateBilin
    exact le_sSup ⟨x, rfl⟩
  have hneBot_conj :
      fenchelConjugateBilin (E := E₁) p f y ≠ ⊥ :=
    section14_fenchelConjugate_ne_bot_of_proper (p := p) hf y
  -- Rewrite `p x y - f x ≤ f* y` as `p x y ≤ f* y + f x`.
  have hle1 : (p x y : EReal) ≤ fenchelConjugateBilin (E := E₁) p f y + f x := by
    have h :=
      (EReal.sub_le_iff_le_add (a := (p x y : EReal)) (b := f x)
            (c := fenchelConjugateBilin (E := E₁) p f y) (.inl (hf.1 x)) (.inr hneBot_conj)).1 hle0
    simpa [add_comm, add_left_comm, add_assoc] using h
  -- Convert back to `p x y - f* y ≤ f x`.
  exact
    (EReal.sub_le_iff_le_add (a := (p x y : EReal)) (b := fenchelConjugateBilin (E := E₁) p f y)
          (c := f x) (.inl hneBot_conj) (.inr (hf.1 x))).2
      (by simpa [add_comm, add_left_comm, add_assoc] using hle1)

/-- (Theorem 14.3, auxiliary) The Fenchel triconjugate with respect to evaluation satisfies
`((f*)*)* = f*` for a proper function `f`. -/
lemma section14_fenchelConjugate_triconjugate_eq_of_proper {E₁ F₁ : Type*} [AddCommGroup E₁]
    [Module ℝ E₁] [AddCommGroup F₁] [Module ℝ F₁] (p : E₁ →ₗ[ℝ] F₁ →ₗ[ℝ] ℝ) {f : E₁ → EReal}
    (hf : ProperERealFunction f)
    (hdom : ∃ y0 : F₁, fenchelConjugateBilin (E := E₁) p f y0 < ⊤) :
    fenchelConjugateBilin (E := E₁) p (fenchelConjugateBilin (E := F₁) p.flip (fenchelConjugateBilin (E := E₁) p f)) =
      fenchelConjugateBilin (E := E₁) p f := by
  classical
  -- Write `f*` and `f***` and use the order-reversing property of `*` together with the
  -- biconjugate inequality.
  apply funext
  intro y
  apply le_antisymm
  · -- `f*** ≤ f*` is the biconjugate inequality applied to `f*`.
    have hfstar_ne_bot : ∀ y : F₁, fenchelConjugateBilin (E := E₁) p f y ≠ ⊥ :=
      section14_fenchelConjugate_ne_bot_of_proper (p := p) hf
    have hfstar : ProperERealFunction (fenchelConjugateBilin (E := E₁) p f) := by
      refine ⟨hfstar_ne_bot, ?_⟩
      rcases hdom with ⟨y0, hy0⟩
      exact ⟨y0, ne_of_lt hy0⟩
    -- Apply `(f*)** ≤ f*` with pairing `p.flip`.
    simpa [fenchelConjugateBilin] using
      section14_fenchelBiconjugate_le_of_proper (p := p.flip) (f := fenchelConjugateBilin (E := E₁) p f)
        hfstar y
  · -- `f* ≤ f***` by antitonicity and the biconjugate inequality `(f*)* ≤ f`.
    have hbi :
        ∀ x : E₁,
          fenchelConjugateBilin (E := F₁) p.flip (fenchelConjugateBilin (E := E₁) p f) x ≤ f x :=
      section14_fenchelBiconjugate_le_of_proper (p := p) (f := f) hf
    -- Antitonicity gives `f* ≤ (f**)* = f***`.
    exact
      (section14_fenchelConjugate_anti (p := p) (f := fenchelConjugateBilin (E := F₁) p.flip (fenchelConjugateBilin (E := E₁) p f))
            (g := f) hbi y)

/-- (Theorem 14.3, auxiliary) The Fenchel biconjugate of the positively homogeneous hull is a
proper convex function. -/
lemma section14_properConvex_fenchelBiconjugate_posHomHull
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let k : E → EReal := section14_posHomHull (E := E) f
    ProperConvexERealFunction (F := E) (fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)) := by
  classical
  intro p k
  set kstar : Module.Dual ℝ E → EReal := fenchelConjugateBilin p k
  set kcl : E → EReal := fenchelConjugateBilin p.flip kstar
  have hk : ProperConvexERealFunction (F := E) k :=
    section14_properConvex_posHomHull (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hk_proper : ProperERealFunction k := hk.1

  -- A witness that `k*` is finite at some point, using the `0`-sublevel nonemptiness of `f*`.
  have hdom_kstar : erealDom kstar =
        {φ : Module.Dual ℝ E | fenchelConjugateBilin p f φ ≤ (0 : EReal)} := by
    simpa [kstar, k] using
      (section14_erealDom_fenchelConjugate_posHomHull_eq_sublevelZero (E := E) (f := f))
  obtain ⟨ψ, hψ⟩ :=
    section14_sublevelZero_fenchelConjugate_nonempty (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hψdom : ψ ∈ erealDom kstar := by
    simpa [hdom_kstar] using hψ
  have hkstar_ne_bot : ∀ φ : Module.Dual ℝ E, kstar φ ≠ ⊥ :=
    section14_fenchelConjugate_ne_bot (E := E) (f := k) hk_proper
  have hkstar_proper : ProperERealFunction kstar := by
    refine ⟨hkstar_ne_bot, ?_⟩
    refine ⟨ψ, ?_⟩
    exact ne_of_lt (hψdom : kstar ψ < ⊤)

  -- Properness of `kcl`.
  have hkcl_ne_bot : ∀ x : E, kcl x ≠ ⊥ := by
    intro x
    -- Use the witness `ψ` with `k* ψ < ⊤` and bound `kcl x` below by the corresponding term.
    have hψlt : kstar ψ < ⊤ := hψdom
    rcases section14_eq_coe_of_lt_top (z := kstar ψ) hψlt (hkstar_ne_bot ψ) with ⟨r0, hr0⟩
    have hle :
        ((p x ψ : EReal) - kstar ψ) ≤ kcl x := by
      unfold kcl kstar
      -- `p.flip ψ x = p x ψ`.
      have : ((p x ψ : EReal) - fenchelConjugateBilin p k ψ) ≤
          fenchelConjugateBilin p.flip (fenchelConjugateBilin p k) x := by
        unfold fenchelConjugateBilin
        exact le_sSup ⟨ψ, rfl⟩
      simpa using this
    intro hxbot
    have hle' : ((p x ψ - r0 : ℝ) : EReal) ≤ (⊥ : EReal) := by
      have hle' := hle
      simp [hxbot, hr0, sub_eq_add_neg] at hle'
    exact (not_le_of_gt (EReal.bot_lt_coe (p x ψ - r0))) hle'

  have hk0 : k 0 = 0 :=
    section14_posHomHull_zero (E := E) (f := f) (hf0 := hf0) (hf0_ltTop := hf0_ltTop)
      (hf0_ne_bot := hf.1.1 0)
  have hkcl_le_k : ∀ x : E, kcl x ≤ k x :=
    section14_fenchelBiconjugate_le_of_proper (p := p) (f := k) hk_proper

  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      simpa [kcl] using hkcl_ne_bot x
    · refine ⟨0, ?_⟩
      -- `kcl 0 ≤ k 0 = 0` implies `kcl 0` is finite.
      have hkcl0_le : kcl 0 ≤ k 0 := hkcl_le_k 0
      have : kcl 0 < ⊤ := lt_of_le_of_lt (hkcl0_le.trans_eq hk0) (EReal.coe_lt_top 0)
      exact ne_of_lt this
  · -- Convexity of `kcl` as a supremum of affine functions.
    intro x y a b ha hb hab
    have haE : (0 : EReal) ≤ (a : EReal) := by simpa [EReal.coe_nonneg] using ha
    have hbE : (0 : EReal) ≤ (b : EReal) := by simpa [EReal.coe_nonneg] using hb
    have habE : (a : EReal) + (b : EReal) = (1 : EReal) := by
      simpa [EReal.coe_add] using congrArg (fun r : ℝ => (r : EReal)) hab
    -- Rewrite `kcl` as an indexed supremum.
    have hkcl_repr :
        kcl = fun x : E => ⨆ φ : Module.Dual ℝ E, ((p x φ : EReal) - kstar φ) := by
      funext x
      classical
      simp [kcl, kstar, fenchelConjugateBilin, sSup_range]
    have hkcl_app (z : E) :
        kcl z = ⨆ φ : Module.Dual ℝ E, ((p z φ : EReal) - kstar φ) := by
      simpa using congrArg (fun g : E → EReal => g z) hkcl_repr
    -- Reduce to bounding each term in the `iSup`.
    rw [hkcl_app (a • x + b • y)]
    refine iSup_le ?_
    intro φ
    have hx_le : ((p x φ : EReal) - kstar φ) ≤ kcl x := by
      -- Evaluate one term in the supremum defining `kcl x`.
      have := le_iSup (fun ψ : Module.Dual ℝ E => (p x ψ : EReal) - kstar ψ) φ
      simpa [hkcl_app x] using this
    have hy_le : ((p y φ : EReal) - kstar φ) ≤ kcl y := by
      have := le_iSup (fun ψ : Module.Dual ℝ E => (p y ψ : EReal) - kstar ψ) φ
      simpa [hkcl_app y] using this
    have hterm :
        ((p (a • x + b • y) φ : EReal) - kstar φ) =
          (a : EReal) * ((p x φ : EReal) - kstar φ) + (b : EReal) * ((p y φ : EReal) - kstar φ) := by
      -- Use linearity of `φ` and distribute the scalars across the subtraction term-by-term.
      have hlin :
          (p (a • x + b • y) φ : EReal) =
            (a : EReal) * (p x φ : EReal) + (b : EReal) * (p y φ : EReal) := by
        -- `p z φ = φ z`.
        have hlinℝ : (p (a • x + b • y) φ : ℝ) = a * (p x φ : ℝ) + b * (p y φ : ℝ) := by
          simp [p, LinearMap.applyₗ, map_add, map_smul, smul_eq_mul]
        -- Cast to `EReal`.
        simp [EReal.coe_add, EReal.coe_mul]
      -- Prove the identity by rewriting the right-hand side.
      have ha_ne_top : (a : EReal) ≠ ⊤ := by simp
      have hb_ne_top : (b : EReal) ≠ ⊤ := by simp
      symm
      calc
        (a : EReal) * ((p x φ : EReal) - kstar φ) + (b : EReal) * ((p y φ : EReal) - kstar φ)
            =
            (a : EReal) * ((p x φ : EReal) + (-kstar φ)) +
              (b : EReal) * ((p y φ : EReal) + (-kstar φ)) := by
                simp [sub_eq_add_neg]
        _ =
            ((a : EReal) * (p x φ : EReal) + (a : EReal) * (-kstar φ)) +
              ((b : EReal) * (p y φ : EReal) + (b : EReal) * (-kstar φ)) := by
                rw [EReal.left_distrib_of_nonneg_of_ne_top haE ha_ne_top (p x φ : EReal) (-kstar φ)]
                rw [EReal.left_distrib_of_nonneg_of_ne_top hbE hb_ne_top (p y φ : EReal) (-kstar φ)]
        _ =
            ((a : EReal) * (p x φ : EReal) + (b : EReal) * (p y φ : EReal)) +
              ((a : EReal) * (-kstar φ) + (b : EReal) * (-kstar φ)) := by
                simp [add_assoc, add_left_comm, add_comm]
        _ =
            ((a : EReal) * (p x φ : EReal) + (b : EReal) * (p y φ : EReal)) +
              (((a : EReal) + (b : EReal)) * (-kstar φ)) := by
                congr 1
                simpa [add_comm, add_left_comm, add_assoc] using
                  (EReal.right_distrib_of_nonneg (ha := haE) (hb := hbE) (c := -kstar φ)).symm
        _ =
            ((a : EReal) * (p x φ : EReal) + (b : EReal) * (p y φ : EReal)) + (-kstar φ) := by
                simp [habE]
        _ = ((a : EReal) * (p x φ : EReal) + (b : EReal) * (p y φ : EReal)) - kstar φ := by
                simp [sub_eq_add_neg]
        _ = (p (a • x + b • y) φ : EReal) - kstar φ := by
                simp
    -- Apply monotonicity after rewriting the term.
    have hax :
        (a : EReal) * ((p x φ : EReal) - kstar φ) ≤ (a : EReal) * kcl x :=
      mul_le_mul_of_nonneg_left hx_le haE
    have hby :
        (b : EReal) * ((p y φ : EReal) - kstar φ) ≤ (b : EReal) * kcl y :=
      mul_le_mul_of_nonneg_left hy_le hbE
    -- Combine.
    -- (Use `hterm` to rewrite the left-hand side.)
    have haux :
        (a : EReal) * ((p x φ : EReal) - kstar φ) + (b : EReal) * ((p y φ : EReal) - kstar φ) ≤
          (a : EReal) * kcl x + (b : EReal) * kcl y :=
      add_le_add hax hby
    exact
      (calc
        ((p (a • x + b • y) φ : EReal) - kstar φ)
            =
            (a : EReal) * ((p x φ : EReal) - kstar φ) + (b : EReal) * ((p y φ : EReal) - kstar φ) := hterm
        _ ≤ (a : EReal) * kcl x + (b : EReal) * kcl y := haux)


end Section14
end Chap03
