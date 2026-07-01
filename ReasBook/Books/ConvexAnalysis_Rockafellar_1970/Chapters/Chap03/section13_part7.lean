/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part8

open scoped Pointwise

section Chap03
section Section13

/-- Auxiliary definition: the global Lipschitz condition
`|f(z) - f(x)| ≤ α * ‖z - x‖`, expressed via `toReal` for an `EReal`-valued function. -/
def LipschitzCondition {n : Nat} (f : (Fin n → Real) → EReal) (α : ℝ) : Prop :=
  ∀ z x : Fin n → Real, |(f z).toReal - (f x).toReal| ≤ α * ‖z - x‖

/-- Auxiliary definition: the `ℓ¹`-norm on `ℝ^n` (with `ℝ^n` represented as `Fin n → ℝ`). -/
noncomputable def l1Norm {n : Nat} (x : Fin n → Real) : ℝ :=
  Finset.univ.sum fun i : Fin n => ‖x i‖

/-- Auxiliary definition: the quantity `sup { ‖xStar‖₁ | xStar ∈ dom f^* }`, where `dom f^*` is the
effective domain of the Fenchel conjugate `f^*`. -/
noncomputable def conjugateDomainRadius {n : Nat} (f : (Fin n → Real) → EReal) : ℝ :=
  sSup
    (Set.image (fun xStar : Fin n → Real => l1Norm xStar)
      (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)))

/-- If `f` is finite everywhere and satisfies `LipschitzCondition f α`, then its recession function
is bounded above by `α‖y‖`. -/
lemma section13_recessionFunction_le_mul_norm_of_LipschitzCondition {n : Nat}
    {f : (Fin n → Real) → EReal} {α : ℝ}
    (hfinite : ∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥) (hLip : LipschitzCondition f α) :
    ∀ y : Fin n → Real, recessionFunction f y ≤ ((α * ‖y‖ : Real) : EReal) := by
  classical
  intro y
  unfold recessionFunction
  refine sSup_le ?_
  rintro r ⟨x, _hxdom, rfl⟩
  have hx_ne_top : f x ≠ (⊤ : EReal) := (hfinite x).1
  have hx_ne_bot : f x ≠ (⊥ : EReal) := (hfinite x).2
  have hxy_ne_top : f (x + y) ≠ (⊤ : EReal) := (hfinite (x + y)).1
  have hxy_ne_bot : f (x + y) ≠ (⊥ : EReal) := (hfinite (x + y)).2
  have hx_coe : ((f x).toReal : EReal) = f x := EReal.coe_toReal hx_ne_top hx_ne_bot
  have hxy_coe : ((f (x + y)).toReal : EReal) = f (x + y) := EReal.coe_toReal hxy_ne_top hxy_ne_bot
  have hrewrite :
      f (x + y) - f x = (((f (x + y)).toReal - (f x).toReal : Real) : EReal) := by
    calc
      f (x + y) - f x =
          ((f (x + y)).toReal : EReal) - ((f x).toReal : EReal) := by
            simp [hxy_coe, hx_coe]
      _ = (((f (x + y)).toReal - (f x).toReal : Real) : EReal) := by
            simp [sub_eq_add_neg]
  have hLip' :
      |(f (x + y)).toReal - (f x).toReal| ≤ α * ‖y‖ := by
    simpa [add_sub_cancel_left] using (hLip (x + y) x)
  have hdiff : (f (x + y)).toReal - (f x).toReal ≤ α * ‖y‖ :=
    le_trans (le_abs_self ((f (x + y)).toReal - (f x).toReal)) hLip'
  have hdiffE :
      (((f (x + y)).toReal - (f x).toReal : Real) : EReal) ≤ ((α * ‖y‖ : Real) : EReal) :=
    (EReal.coe_le_coe_iff.2 hdiff)
  simpa [hrewrite] using hdiffE

/-- If a nonempty convex set has support function `⊤` in every nonzero direction, then the set
is all of `ℝ^n`. -/
lemma section13_set_eq_univ_of_supportFunctionEReal_eq_top {n : Nat} (C : Set (Fin n → Real))
    (hconv : Convex ℝ C) (hne : Set.Nonempty C)
    (htop : ∀ y : Fin n → Real, y ≠ (0 : Fin n → Real) → supportFunctionEReal C y = (⊤ : EReal)) :
    C = Set.univ := by
  classical
  by_cases hn : 0 < n
  · by_contra hCne
    rcases
        exists_closedHalfspace_superset_of_convex_ne_univ (n := n) C hn hconv
          (by simpa using hCne) with
      ⟨b, β, hb0, hCb⟩
    have hle : supportFunctionEReal C b ≤ (β : EReal) := by
      refine (section13_supportFunctionEReal_le_coe_iff (C := C) (y := b) (μ := β)).2 ?_
      intro x hx
      have : x ∈ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := hCb hx
      simpa using this
    have htopb : supportFunctionEReal C b = (⊤ : EReal) := htop b hb0
    have : (⊤ : EReal) ≤ (β : EReal) := by
      exact (htopb ▸ hle)
    exact (not_top_le_coe β) this
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    rcases hne with ⟨x0, hx0⟩
    ext x
    have hx : x = x0 := Subsingleton.elim x x0
    simpa [hx] using hx0

/-- If `f` is proper convex and `dom f*` is bounded, then `f` is finite everywhere. -/
lemma section13_finite_everywhere_of_isBounded_effectiveDomain_fenchelConjugate {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hbounded :
      Bornology.IsBounded
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))) :
    ∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥ := by
  classical
  let fStar : (Fin n → Real) → EReal := fenchelConjugate n f
  have hclosedStar : ClosedConvexFunction fStar := by
    refine ⟨(fenchelConjugate_closedConvex (n := n) (f := f)).2, ?_⟩
    exact (fenchelConjugate_closedConvex (n := n) (f := f)).1
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hcoFiniteStar : CoFiniteConvexFunction fStar :=
    coFiniteConvexFunction_of_isBounded_effectiveDomain (n := n) (f := fStar) hclosedStar
      hproperStar hbounded

  have hsupp :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) =
        recessionFunction fStar := by
    simpa [fStar] using
      supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate (n := n) (f := f)
        (hf := hf) (fStar0_plus := recessionFunction fStar) (hfStar0_plus := by intro y; rfl)
  have htop_dom :
      ∀ y : Fin n → Real,
        y ≠ (0 : Fin n → Real) →
          supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) y = (⊤ : EReal) := by
    intro y hy
    have hrec :
        recessionFunction fStar y = (⊤ : EReal) := by
      simpa [fStar, recessionFunction] using hcoFiniteStar.2.2 y hy
    have hsupp_y :
        supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) y =
          recessionFunction fStar y := by
      simpa using congrArg (fun g => g y) hsupp
    simpa [hsupp_y] using hrec

  have hdom_univ :
      effectiveDomain (Set.univ : Set (Fin n → Real)) f = Set.univ := by
    have hCconv :
        Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
    have hCne :
        Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hf
    exact
      section13_set_eq_univ_of_supportFunctionEReal_eq_top
        (C := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hCconv hCne htop_dom
  intro z
  have hzdom : z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simp [hdom_univ]
  refine ⟨?_, ?_⟩
  · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hzdom
  · exact hf.2.2 z (by simp)

/-- If `C` is bounded, then its support function is dominated by `R‖y‖` for some `R ≥ 0`
with respect to the sup norm on `ℝ^n`. -/
lemma section13_supportFunctionEReal_le_mul_norm_of_isBounded {n : Nat} (C : Set (Fin n → Real))
    (hbounded : Bornology.IsBounded C) :
    ∃ R ≥ 0,
      ∀ y : Fin n → Real, supportFunctionEReal C y ≤ ((R * ‖y‖ : Real) : EReal) := by
  classical
  obtain ⟨R0, hCsub⟩ := hbounded.subset_closedBall (0 : Fin n → Real)
  let R : Real := (Fintype.card (Fin n) : Real) * max R0 0
  have hR_nonneg : 0 ≤ R := by
    have hcard : 0 ≤ (Fintype.card (Fin n) : Real) := by
      exact_mod_cast (Nat.zero_le (Fintype.card (Fin n)))
    have hmax : 0 ≤ max R0 0 := le_max_right _ _
    nlinarith
  refine ⟨R, hR_nonneg, ?_⟩
  intro y
  refine (section13_supportFunctionEReal_le_coe_iff (C := C) (y := y) (μ := R * ‖y‖)).2 ?_
  intro x hx
  have hxball : x ∈ Metric.closedBall (0 : Fin n → Real) R0 := hCsub hx
  have hxnorm0 : ‖x‖ ≤ max R0 0 := by
    have hxnormR0 : ‖x‖ ≤ R0 := by
      have : dist x 0 ≤ R0 := (Metric.mem_closedBall).1 hxball
      simpa [dist_eq_norm] using this
    exact le_trans hxnormR0 (le_max_left _ _)
  have hy_sum :
      (Finset.univ.sum fun i : Fin n => ‖y i‖) ≤ (Fintype.card (Fin n)) • ‖y‖ := by
    simpa using (Pi.sum_norm_apply_le_norm (f := y))
  have hy_sum' :
      (Finset.univ.sum fun i : Fin n => ‖y i‖) ≤ (Fintype.card (Fin n) : Real) * ‖y‖ := by
    simpa [nsmul_eq_mul] using hy_sum
  have hsum_nonneg : 0 ≤ Finset.univ.sum fun i : Fin n => ‖y i‖ :=
    Finset.sum_nonneg (fun i _hi => norm_nonneg (y i))

  have hdot_le_sum :
      dotProduct x y ≤ ‖x‖ * (Finset.univ.sum fun i : Fin n => ‖y i‖) := by
    -- Bound each term of `∑ i, x i * y i` by `‖x‖ * ‖y i‖`.
    have hterm :
        ∀ i : Fin n, x i * y i ≤ ‖x‖ * ‖y i‖ := by
      intro i
      have hmul_abs : x i * y i ≤ ‖x i‖ * ‖y i‖ := by
        calc
          x i * y i ≤ |x i * y i| := le_abs_self _
          _ = |x i| * |y i| := by simp [abs_mul]
          _ = ‖x i‖ * ‖y i‖ := by simp [Real.norm_eq_abs]
      have hxle : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm (f := x) i
      have : ‖x i‖ * ‖y i‖ ≤ ‖x‖ * ‖y i‖ :=
        mul_le_mul_of_nonneg_right hxle (norm_nonneg (y i))
      exact le_trans hmul_abs this
    have hsum :
        dotProduct x y ≤ Finset.univ.sum fun i : Fin n => ‖x‖ * ‖y i‖ := by
      -- termwise comparison inside the sum
      unfold dotProduct
      exact Finset.sum_le_sum (fun i _hi => hterm i)
    -- pull out the constant `‖x‖`.
    simpa [Finset.mul_sum] using hsum
  have hdot_le :
      dotProduct x y ≤ (max R0 0) * ((Fintype.card (Fin n) : Real) * ‖y‖) := by
    have hdot_le' :
        dotProduct x y ≤ (max R0 0) * (Finset.univ.sum fun i : Fin n => ‖y i‖) := by
      have :
          ‖x‖ * (Finset.univ.sum fun i : Fin n => ‖y i‖) ≤
            (max R0 0) * (Finset.univ.sum fun i : Fin n => ‖y i‖) :=
        mul_le_mul_of_nonneg_right hxnorm0 hsum_nonneg
      exact le_trans hdot_le_sum this
    have hmax_nonneg : 0 ≤ max R0 0 := le_max_right _ _
    have :
        (max R0 0) * (Finset.univ.sum fun i : Fin n => ‖y i‖) ≤
          (max R0 0) * ((Fintype.card (Fin n) : Real) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hy_sum' hmax_nonneg
    exact le_trans hdot_le' this
  -- Put the pieces together.
  simpa [R, mul_assoc, mul_left_comm, mul_comm] using hdot_le

/-- If `f` is finite everywhere and `f₀⁺(y) ≤ α‖y‖` for all `y`, then `f` satisfies the global
Lipschitz condition with constant `α`. -/
lemma section13_lipschitzCondition_of_recessionFunction_le_mul_norm {n : Nat}
    {f : (Fin n → Real) → EReal} {α : ℝ}
    (hfinite : ∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥)
    (hrec : ∀ y : Fin n → Real, recessionFunction f y ≤ ((α * ‖y‖ : Real) : EReal)) :
    LipschitzCondition f α := by
  classical
  intro z x
  have hx_ne_top : f x ≠ (⊤ : EReal) := (hfinite x).1
  have hx_ne_bot : f x ≠ (⊥ : EReal) := (hfinite x).2
  have hz_ne_top : f z ≠ (⊤ : EReal) := (hfinite z).1
  have hz_ne_bot : f z ≠ (⊥ : EReal) := (hfinite z).2

  have hzx : (f z).toReal - (f x).toReal ≤ α * ‖z - x‖ := by
    have hxlt : f x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx_ne_top
    have hxdom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      have : x ∈ {u : Fin n → Real | u ∈ (Set.univ : Set (Fin n → Real)) ∧ f u < (⊤ : EReal)} :=
        ⟨by simp, hxlt⟩
      simpa [effectiveDomain_eq] using this
    have hxz_eq : x + (z - x) = z := by
      funext i
      simp
    have hdiff_le_rec : f z - f x ≤ recessionFunction f (z - x) := by
      unfold recessionFunction
      refine le_sSup ?_
      exact ⟨x, hxdom, by simp [hxz_eq]⟩
    have hdiff_le :
        f z - f x ≤ ((α * ‖z - x‖ : Real) : EReal) :=
      le_trans hdiff_le_rec (hrec (z - x))
    have hx_coe : ((f x).toReal : EReal) = f x := EReal.coe_toReal hx_ne_top hx_ne_bot
    have hz_coe : ((f z).toReal : EReal) = f z := EReal.coe_toReal hz_ne_top hz_ne_bot
    have hrewrite :
        f z - f x = (((f z).toReal - (f x).toReal : Real) : EReal) := by
      calc
        f z - f x = ((f z).toReal : EReal) - ((f x).toReal : EReal) := by
          simp [hz_coe, hx_coe]
        _ = (((f z).toReal - (f x).toReal : Real) : EReal) := by
          simp [sub_eq_add_neg]
    have hdiff_le' :
        (((f z).toReal - (f x).toReal : Real) : EReal) ≤ ((α * ‖z - x‖ : Real) : EReal) := by
      simpa [hrewrite] using hdiff_le
    exact (EReal.coe_le_coe_iff.1 hdiff_le')

  have hxz : (f x).toReal - (f z).toReal ≤ α * ‖z - x‖ := by
    have hzlt : f z < (⊤ : EReal) := (lt_top_iff_ne_top).2 hz_ne_top
    have hzdom : z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      have : z ∈ {u : Fin n → Real | u ∈ (Set.univ : Set (Fin n → Real)) ∧ f u < (⊤ : EReal)} :=
        ⟨by simp, hzlt⟩
      simpa [effectiveDomain_eq] using this
    have hzx_eq : z + (x - z) = x := by
      funext i
      simp
    have hdiff_le_rec : f x - f z ≤ recessionFunction f (x - z) := by
      unfold recessionFunction
      refine le_sSup ?_
      exact ⟨z, hzdom, by simp [hzx_eq]⟩
    have hdiff_le :
        f x - f z ≤ ((α * ‖x - z‖ : Real) : EReal) :=
      le_trans hdiff_le_rec (hrec (x - z))
    have hx_coe : ((f x).toReal : EReal) = f x := EReal.coe_toReal hx_ne_top hx_ne_bot
    have hz_coe : ((f z).toReal : EReal) = f z := EReal.coe_toReal hz_ne_top hz_ne_bot
    have hrewrite :
        f x - f z = (((f x).toReal - (f z).toReal : Real) : EReal) := by
      calc
        f x - f z = ((f x).toReal : EReal) - ((f z).toReal : EReal) := by
          simp [hx_coe, hz_coe]
        _ = (((f x).toReal - (f z).toReal : Real) : EReal) := by
          simp [sub_eq_add_neg]
    have hdiff_le' :
        (((f x).toReal - (f z).toReal : Real) : EReal) ≤ ((α * ‖x - z‖ : Real) : EReal) := by
      simpa [hrewrite] using hdiff_le
    have :
        (f x).toReal - (f z).toReal ≤ α * ‖x - z‖ :=
      (EReal.coe_le_coe_iff.1 hdiff_le')
    simpa [norm_sub_rev] using this

  have hneg : -(α * ‖z - x‖) ≤ (f z).toReal - (f x).toReal := by
    linarith
  exact (abs_le.2 ⟨hneg, hzx⟩)

/-- If `f` is proper convex and `dom f*` is bounded, then `f` satisfies a global Lipschitz
condition for some `α ≥ 0`. -/
lemma section13_lipschitzCondition_of_isBounded_effectiveDomain_fenchelConjugate {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hbounded :
      Bornology.IsBounded
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)))
    (hfinite : ∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥) :
    ∃ α : ℝ, 0 ≤ α ∧ LipschitzCondition f α := by
  classical
  -- `f` is closed and proper because it is convex and finite everywhere.
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have hclosed : ClosedConvexFunction f :=
    (section13_closedProper_of_convex_finite (f := f) (hf := hconv) hfinite).1
  set C : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  obtain ⟨R, hR0, hsupp_le⟩ :=
    section13_supportFunctionEReal_le_mul_norm_of_isBounded (n := n) (C := C) hbounded
  have hsupp_eq :
      supportFunctionEReal C = recessionFunction f := by
    simpa [C] using
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n) (f := f)
        hclosed hf
  have hrec_le :
      ∀ y : Fin n → Real, recessionFunction f y ≤ ((R * ‖y‖ : Real) : EReal) := by
    intro y
    have : supportFunctionEReal C y ≤ ((R * ‖y‖ : Real) : EReal) := hsupp_le y
    simpa [hsupp_eq] using this
  refine ⟨R, hR0, ?_⟩
  exact section13_lipschitzCondition_of_recessionFunction_le_mul_norm (n := n) (f := f)
    (hfinite := hfinite) hrec_le

/-- Corollary 13.3.3. Let `f` be a proper convex function. The effective domain `dom f^*` is
bounded if and only if `f` is finite everywhere and there exists `α ≥ 0` such that
`|f(z) - f(x)| ≤ α * ‖z - x‖` for all `z` and `x` (a global Lipschitz condition). -/
theorem isBounded_effectiveDomain_fenchelConjugate_iff_finite_and_exists_lipschitz {n : Nat}
    (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    Bornology.IsBounded
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) ↔
      (∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥) ∧ ∃ α : ℝ, 0 ≤ α ∧ LipschitzCondition f α := by
  constructor
  · intro hbounded
    have hfinite :
        ∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥ :=
      section13_finite_everywhere_of_isBounded_effectiveDomain_fenchelConjugate (n := n) (f := f)
        hf hbounded
    have hLip :
        ∃ α : ℝ, 0 ≤ α ∧ LipschitzCondition f α :=
      section13_lipschitzCondition_of_isBounded_effectiveDomain_fenchelConjugate (n := n) (f := f)
        hf hbounded hfinite
    exact ⟨hfinite, hLip⟩
  · rintro ⟨hfinite, α, hα0, hLip⟩
    classical
    -- `f` is closed and proper when it is convex and finite everywhere.
    have hconv : ConvexFunction f := by
      simpa [ConvexFunction] using hf.1
    have hclosed : ClosedConvexFunction f :=
      (section13_closedProper_of_convex_finite (f := f) (hf := hconv) hfinite).1
    set C : Set (Fin n → Real) :=
      effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
    have hproperStar :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
      proper_fenchelConjugate_of_proper (n := n) (f := f) hf
    have hCne : Set.Nonempty C :=
      section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
    have hsupp_eq :
        supportFunctionEReal C = recessionFunction f := by
      simpa [C] using
        section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n) (f := f)
          hclosed hf
    have hsupp_le : ∀ y : Fin n → Real, supportFunctionEReal C y ≤ ((α * ‖y‖ : Real) : EReal) := by
      intro y
      have hrec :
          recessionFunction f y ≤ ((α * ‖y‖ : Real) : EReal) :=
        section13_recessionFunction_le_mul_norm_of_LipschitzCondition (n := n) (f := f)
          (hfinite := hfinite) (hLip := hLip) y
      simpa [hsupp_eq] using hrec
    -- The support function is never `⊥` because `C` is nonempty, and never `⊤` thanks to `hsupp_le`.
    have hsupp_finite :
        ∀ y : Fin n → Real,
          supportFunctionEReal C y ≠ (⊤ : EReal) ∧ supportFunctionEReal C y ≠ (⊥ : EReal) := by
      intro y
      refine ⟨?_, ?_⟩
      · intro htop
        have hle_top :
            (⊤ : EReal) ≤ ((α * ‖y‖ : Real) : EReal) := by
          simpa [htop] using hsupp_le y
        exact (not_top_le_coe (α * ‖y‖)) hle_top
      · exact section13_supportFunctionEReal_ne_bot_of_nonempty (n := n) (C := C) hCne y
    have hCbd : Bornology.IsBounded C :=
      section13_isBounded_of_supportFunctionEReal_finite (C := C) hsupp_finite
    exact hCbd

/-- Hölder-style estimate for the `sup`-norm: `⟪x,y⟫ ≤ ‖x‖₁‖y‖`. -/
lemma section13_dotProduct_le_l1Norm_mul_norm {n : Nat} (x y : Fin n → Real) :
    dotProduct x y ≤ l1Norm x * ‖y‖ := by
  classical
  unfold l1Norm
  have hterm : ∀ i : Fin n, x i * y i ≤ ‖x i‖ * ‖y‖ := by
    intro i
    have hyi : ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm (f := y) i
    have hxabs : x i * y i ≤ ‖x i‖ * ‖y i‖ := by
      calc
        x i * y i ≤ |x i * y i| := le_abs_self _
        _ = |x i| * |y i| := by simp [abs_mul]
        _ = ‖x i‖ * ‖y i‖ := by simp [Real.norm_eq_abs]
    have : ‖x i‖ * ‖y i‖ ≤ ‖x i‖ * ‖y‖ :=
      mul_le_mul_of_nonneg_left hyi (norm_nonneg (x i))
    exact le_trans hxabs this
  have hsum :
      dotProduct x y ≤ Finset.univ.sum fun i : Fin n => ‖x i‖ * ‖y‖ := by
    unfold dotProduct
    exact Finset.sum_le_sum (fun i _hi => hterm i)
  simpa [Finset.sum_mul] using hsum

/-- `l1Norm` is bounded above on a bounded set. -/
lemma section13_bddAbove_image_l1Norm_of_isBounded {n : Nat} (C : Set (Fin n → Real))
    (hbounded : Bornology.IsBounded C) :
    BddAbove (Set.image (fun x : Fin n → Real => l1Norm x) C) := by
  classical
  obtain ⟨R0, hCsub⟩ := hbounded.subset_closedBall (0 : Fin n → Real)
  refine ⟨(Fintype.card (Fin n) : Real) * max R0 0, ?_⟩
  rintro r ⟨x, hxC, rfl⟩
  have hxball : x ∈ Metric.closedBall (0 : Fin n → Real) R0 := hCsub hxC
  have hxnorm0 : ‖x‖ ≤ max R0 0 := by
    have hxnormR0 : ‖x‖ ≤ R0 := by
      have : dist x 0 ≤ R0 := (Metric.mem_closedBall).1 hxball
      simpa [dist_eq_norm] using this
    exact le_trans hxnormR0 (le_max_left _ _)
  have hl1_le : l1Norm x ≤ (Fintype.card (Fin n) : Real) * ‖x‖ := by
    unfold l1Norm
    have hterm : ∀ i : Fin n, ‖x i‖ ≤ ‖x‖ := by
      intro i
      simpa using (norm_le_pi_norm (f := x) i)
    have :
        (Finset.univ.sum fun i : Fin n => ‖x i‖) ≤
          Finset.univ.sum fun _i : Fin n => ‖x‖ :=
      Finset.sum_le_sum (fun i _hi => hterm i)
    simpa [Finset.sum_const_nat, nsmul_eq_mul] using this
  have hcard : 0 ≤ (Fintype.card (Fin n) : Real) := by
    exact_mod_cast (Nat.zero_le (Fintype.card (Fin n)))
  have : (Fintype.card (Fin n) : Real) * ‖x‖ ≤ (Fintype.card (Fin n) : Real) * max R0 0 :=
    mul_le_mul_of_nonneg_left hxnorm0 hcard
  exact le_trans hl1_le this

/-- If `xStar ∈ dom f*`, then `‖xStar‖₁ ≤ conjugateDomainRadius f`. -/
lemma section13_l1Norm_le_conjugateDomainRadius_of_mem_dom {n : Nat} (f : (Fin n → Real) → EReal)
    (hbounded :
      Bornology.IsBounded
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))) :
    ∀ xStar : Fin n → Real,
      xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) →
        l1Norm xStar ≤ conjugateDomainRadius f := by
  classical
  set C : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  have hbdd :
      BddAbove (Set.image (fun x : Fin n → Real => l1Norm x) C) :=
    section13_bddAbove_image_l1Norm_of_isBounded (n := n) (C := C) hbounded
  intro xStar hxStar
  unfold conjugateDomainRadius
  refine le_csSup hbdd ?_
  exact ⟨xStar, hxStar, rfl⟩

/-- The support function of `dom f*` is bounded by `conjugateDomainRadius f * ‖y‖`. -/
lemma section13_supportFunctionEReal_le_mul_norm_conjugateDomainRadius {n : Nat}
    (f : (Fin n → Real) → EReal)
    (hbounded :
      Bornology.IsBounded
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))) :
    ∀ y : Fin n → Real,
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) y ≤
        ((conjugateDomainRadius f * ‖y‖ : Real) : EReal) := by
  classical
  set C : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  intro y
  refine
    (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := y)
        (μ := conjugateDomainRadius f * ‖y‖)).2 ?_
  intro xStar hxStar
  have hxStar_le : l1Norm xStar ≤ conjugateDomainRadius f :=
    section13_l1Norm_le_conjugateDomainRadius_of_mem_dom (n := n) (f := f) (hbounded := hbounded)
      xStar hxStar
  have hdot : dotProduct xStar y ≤ l1Norm xStar * ‖y‖ :=
    section13_dotProduct_le_l1Norm_mul_norm (n := n) xStar y
  have hmul :
      l1Norm xStar * ‖y‖ ≤ conjugateDomainRadius f * ‖y‖ :=
    mul_le_mul_of_nonneg_right hxStar_le (norm_nonneg y)
  exact le_trans hdot hmul

/-- If `f` is finite everywhere and satisfies a global Lipschitz condition with constant `α`,
then any `xStar` with `α < ‖xStar‖₁` lies outside `dom f*` (equivalently, `f* xStar = ⊤`). -/
lemma section13_fenchelConjugate_eq_top_of_LipschitzCondition_lt_l1Norm {n : Nat}
    {f : (Fin n → Real) → EReal} {α : ℝ}
    (hfinite : ∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥) (hα0 : 0 ≤ α)
    (hLip : LipschitzCondition f α) :
    ∀ xStar : Fin n → Real, α < l1Norm xStar → fenchelConjugate n f xStar = ⊤ := by
  classical
  intro xStar hlt
  -- Build a sign vector `s` with `⟪s, xStar⟫ = ‖xStar‖₁`.
  let s : Fin n → Real := fun i => if 0 ≤ xStar i then (1 : Real) else (-1 : Real)
  have hs_dot : dotProduct s xStar = l1Norm xStar := by
    unfold dotProduct l1Norm
    refine Finset.sum_congr rfl ?_
    intro i _hi
    by_cases hxi : 0 ≤ xStar i
    · simp [s, hxi, Real.norm_eq_abs, abs_of_nonneg hxi]
    · have hxi' : xStar i < 0 := lt_of_not_ge hxi
      simp [s, hxi, Real.norm_eq_abs, abs_of_neg hxi']
  have hs_norm : ‖s‖ ≤ (1 : Real) := by
    refine (pi_norm_le_iff_of_nonneg (x := s) (r := (1 : Real)) (by norm_num)).2 ?_
    intro i
    by_cases hxi : 0 ≤ xStar i <;> simp [s, hxi]
  have hδpos : 0 < l1Norm xStar - α := sub_pos.2 hlt
  refine (EReal.eq_top_iff_forall_lt (fenchelConjugate n f xStar)).2 ?_
  intro y
  by_cases hN : y + (f 0).toReal + 1 ≤ 0
  · have hy : y < - (f 0).toReal := by linarith
    have h0_ne_top : f 0 ≠ (⊤ : EReal) := (hfinite 0).1
    have h0_ne_bot : f 0 ≠ (⊥ : EReal) := (hfinite 0).2
    have h0_coe : ((f 0).toReal : EReal) = f 0 := EReal.coe_toReal h0_ne_top h0_ne_bot
    have hyE : (y : EReal) < ((- (f 0).toReal : Real) : EReal) :=
      (EReal.coe_lt_coe_iff.2 hy)
    have hval : ((- (f 0).toReal : Real) : EReal) = ((0 ⬝ᵥ xStar : Real) : EReal) - f 0 := by
      simp [h0_coe, sub_eq_add_neg]
    have hle : ((0 ⬝ᵥ xStar : Real) : EReal) - f 0 ≤ fenchelConjugate n f xStar := by
      unfold fenchelConjugate
      exact le_sSup ⟨0, rfl⟩
    exact lt_of_lt_of_le (hyE.trans_eq hval) hle
  · have hNpos : 0 < y + (f 0).toReal + 1 := lt_of_not_ge hN
    let t : Real := (y + (f 0).toReal + 1) / (l1Norm xStar - α)
    have htpos : 0 < t := div_pos hNpos hδpos
    have ht0 : 0 ≤ t := le_of_lt htpos
    let x : Fin n → Real := t • s
    have hx_ne_top : f x ≠ (⊤ : EReal) := (hfinite x).1
    have hx_ne_bot : f x ≠ (⊥ : EReal) := (hfinite x).2
    have hx_coe : ((f x).toReal : EReal) = f x := EReal.coe_toReal hx_ne_top hx_ne_bot
    have hxnorm : ‖x‖ ≤ t := by
      have hx_eq : ‖x‖ = |t| * ‖s‖ := by simp [x, norm_smul]
      have hx_eq' : ‖x‖ = t * ‖s‖ := by simp [hx_eq, abs_of_pos htpos]
      calc
        ‖x‖ = t * ‖s‖ := hx_eq'
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left hs_norm ht0
        _ = t := by simp
    have hfx_le : (f x).toReal ≤ (f 0).toReal + α * t := by
      have hLip0 : |(f x).toReal - (f 0).toReal| ≤ α * ‖x - 0‖ := by
        simpa using (hLip x 0)
      have hle : (f x).toReal - (f 0).toReal ≤ α * ‖x‖ := by
        have : (f x).toReal - (f 0).toReal ≤ |(f x).toReal - (f 0).toReal| :=
          le_abs_self _
        exact le_trans this (by simpa [sub_eq_add_neg] using hLip0)
      have : (f x).toReal ≤ (f 0).toReal + α * ‖x‖ := by linarith
      have hαt : α * ‖x‖ ≤ α * t := mul_le_mul_of_nonneg_left hxnorm hα0
      exact le_trans this (by linarith)
    have hdotx : dotProduct x xStar = t * l1Norm xStar := by
      have : dotProduct x xStar = t * dotProduct s xStar := by
        simp [x]
      simp [this, hs_dot]
    have hreal_gt : y < dotProduct x xStar - (f x).toReal := by
      have h1 : dotProduct x xStar - (f x).toReal ≥ (t * l1Norm xStar) - ((f 0).toReal + α * t) := by
        have hfx : (f x).toReal ≤ (f 0).toReal + α * t := hfx_le
        have : - (f x).toReal ≥ - ((f 0).toReal + α * t) := by linarith
        nlinarith [hdotx, this]
      have htdef : t * (l1Norm xStar - α) = y + (f 0).toReal + 1 := by
        have hδne : (l1Norm xStar - α) ≠ 0 := ne_of_gt hδpos
        simp [t, div_eq_mul_inv, hδne]
      have h2 : (t * l1Norm xStar) - ((f 0).toReal + α * t) = (y + 1) := by
        have : (t * l1Norm xStar) - ((f 0).toReal + α * t) =
            t * (l1Norm xStar - α) - (f 0).toReal := by ring
        nlinarith [this, htdef]
      have hge : dotProduct x xStar - (f x).toReal ≥ y + 1 := by
        nlinarith [h1, h2]
      have : y < y + 1 := by linarith
      exact lt_of_lt_of_le this hge
    have hyE :
        (y : EReal) < ((dotProduct x xStar - (f x).toReal : Real) : EReal) :=
      (EReal.coe_lt_coe_iff.2 hreal_gt)
    have hval :
        ((dotProduct x xStar - (f x).toReal : Real) : EReal) =
          ((dotProduct x xStar : Real) : EReal) - f x := by
      simp [hx_coe, sub_eq_add_neg, add_comm]
    have hle : ((dotProduct x xStar : Real) : EReal) - f x ≤ fenchelConjugate n f xStar := by
      unfold fenchelConjugate
      exact le_sSup ⟨x, rfl⟩
    exact lt_of_lt_of_le (hyE.trans_eq hval) hle

/-- Corollary 13.3.3 (optimal Lipschitz constant): assuming `f` is finite everywhere and
`dom f^*` is bounded, the smallest `α` for which the global Lipschitz condition holds is
`α = sup { ‖xStar‖ | xStar ∈ dom f^* }` (here `conjugateDomainRadius f`). -/
theorem lipschitzCondition_conjugateDomainRadius_and_minimal {n : Nat}
    (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hbounded :
      Bornology.IsBounded
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)))
    (hfinite : ∀ z : Fin n → Real, f z ≠ ⊤ ∧ f z ≠ ⊥) :
    LipschitzCondition f (conjugateDomainRadius f) ∧
      ∀ α : ℝ, 0 ≤ α → LipschitzCondition f α → conjugateDomainRadius f ≤ α := by
  classical
  set C : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have hclosed : ClosedConvexFunction f :=
    (section13_closedProper_of_convex_finite (f := f) (hf := hconv) hfinite).1
  have hsupp_eq :
      supportFunctionEReal C = recessionFunction f := by
    simpa [C] using
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n) (f := f)
        hclosed hf
  have hrec_le :
      ∀ y : Fin n → Real,
        recessionFunction f y ≤ ((conjugateDomainRadius f * ‖y‖ : Real) : EReal) := by
    intro y
    have : supportFunctionEReal C y ≤ ((conjugateDomainRadius f * ‖y‖ : Real) : EReal) := by
      simpa [C] using
        section13_supportFunctionEReal_le_mul_norm_conjugateDomainRadius (n := n) (f := f)
          (hbounded := hbounded) y
    simpa [hsupp_eq] using this
  have hLip_radius : LipschitzCondition f (conjugateDomainRadius f) :=
    section13_lipschitzCondition_of_recessionFunction_le_mul_norm (n := n) (f := f)
      (hfinite := hfinite) hrec_le
  refine ⟨hLip_radius, ?_⟩
  intro α hα0 hLip
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hCne : Set.Nonempty C :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
  have hdom_le : ∀ xStar : Fin n → Real, xStar ∈ C → l1Norm xStar ≤ α := by
    intro xStar hxStar
    by_contra hnot
    have hlt : α < l1Norm xStar := lt_of_not_ge hnot
    have htop : fenchelConjugate n f xStar = ⊤ :=
      section13_fenchelConjugate_eq_top_of_LipschitzCondition_lt_l1Norm (n := n) (f := f)
        (hfinite := hfinite) (hα0 := hα0) (hLip := hLip) xStar hlt
    have hxStar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real)))
        (f := fenchelConjugate n f) hxStar
    exact hxStar_ne_top htop
  unfold conjugateDomainRadius
  refine csSup_le ?_ ?_
  · rcases hCne with ⟨x0, hx0⟩
    exact ⟨l1Norm x0, ⟨x0, hx0, rfl⟩⟩
  · rintro r ⟨xStar, hxStar, rfl⟩
    exact hdom_le xStar hxStar

/-- The `EReal`-valued affine functional `x ↦ ⟪x, a⟫` is proper convex on `univ`. -/
lemma section13_properConvexFunctionOn_dotProduct {n : Nat} (a : Fin n → Real) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x : Fin n → Real => ((dotProduct x a : Real) : EReal)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- Convexity comes from the fact that this is an affine function.
    have haff :
        AffineFunctionOn (Set.univ : Set (Fin n → Real))
          (fun x : Fin n → Real => ((Finset.univ.sum (fun i : Fin n => x i * a i) + (0 : Real) : Real) : EReal)) := by
      simpa [dotProduct] using
        (affineFunctionOn_univ_inner_add_const (n := n) (a := a) (α := (0 : Real)))
    -- Extract the convexity component.
    simpa [AffineFunctionOn] using haff.2.1
  · -- The epigraph is nonempty: take `(0, 0)`.
    refine ⟨((0 : Fin n → Real), (0 : Real)), ?_⟩
    refine And.intro (by trivial) ?_
    simp [dotProduct]
  · -- This function is never `⊥`.
    intro x _hx
    exact (EReal.coe_ne_bot (dotProduct x a : Real))

/-- Theorem 12.3 specialization: conjugating `x ↦ f x - ⟪x, xStar⟫` translates the conjugate. -/
lemma section13_fenchelConjugate_sub_dotProduct {n : Nat}
    (f : (Fin n → Real) → EReal) (xStar : Fin n → Real) :
    let g : (Fin n → Real) → EReal := fun x => f x - ((dotProduct x xStar : Real) : EReal)
    fenchelConjugate n g = fun yStar => fenchelConjugate n f (yStar + xStar) := by
  classical
  -- Apply `fenchelConjugate_affineTransform` with `A = id`, `a = 0`, `aStar = -xStar`, `α = 0`.
  have h :=
    (fenchelConjugate_affineTransform (n := n) (h := f)
      (A := LinearEquiv.refl ℝ (Fin n → Real))
      (AStar := LinearEquiv.refl ℝ (Fin n → Real))
      (hAStar := by intro x y; simp)
      (a := 0) (aStar := -xStar) (α := 0)
    )
  -- Unfold the `let` and simplify.
  simpa [sub_eq_add_neg, dotProduct_neg, add_assoc, add_left_comm, add_comm] using h

/-- The effective domain of `(f - ⟪·, xStar⟫)^*` is the translate `dom f^* - xStar`. -/
lemma section13_effectiveDomain_fenchelConjugate_sub_dotProduct {n : Nat}
    (f : (Fin n → Real) → EReal) (xStar : Fin n → Real) :
    let domFstar : Set (Fin n → Real) :=
      effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
    let g : (Fin n → Real) → EReal := fun x => f x - ((dotProduct x xStar : Real) : EReal)
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n g) =
      domFstar - ({xStar} : Set (Fin n → Real)) := by
  classical
  intro domFstar g
  have hfench :
      fenchelConjugate n g = fun yStar => fenchelConjugate n f (yStar + xStar) := by
    simpa [g] using
      (section13_fenchelConjugate_sub_dotProduct (n := n) (f := f) (xStar := xStar))
  ext y
  constructor
  · intro hy
    have hy' : fenchelConjugate n f (y + xStar) < (⊤ : EReal) := by
      have hy' : fenchelConjugate n g y < (⊤ : EReal) := by
        simpa [effectiveDomain_eq, and_left_comm, and_assoc, and_comm] using hy
      simpa [hfench] using hy'
    have hy_dom : y + xStar ∈ domFstar := by
      simpa [domFstar, effectiveDomain_eq] using hy'
    -- `y = (y + xStar) - xStar`, so `y` belongs to the translate `domFstar - {xStar}`.
    simpa [Set.sub_singleton] using ⟨y + xStar, hy_dom, by simp⟩
  · intro hy
    -- Unpack membership in the translated set `domFstar - {xStar}`.
    have hy' : y ∈ (fun z : Fin n → Real => z - xStar) '' domFstar := by
      simpa [Set.sub_singleton] using hy
    rcases hy' with ⟨z, hz, rfl⟩
    have hz' : fenchelConjugate n f z < (⊤ : EReal) := by
      simpa [domFstar, effectiveDomain_eq] using hz
    -- Rewrite back using the conjugate translation formula.
    have : fenchelConjugate n g (z - xStar) < (⊤ : EReal) := by
      have : fenchelConjugate n f ((z - xStar) + xStar) < (⊤ : EReal) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz'
      simpa [hfench] using this
    simpa [effectiveDomain_eq, and_left_comm, and_assoc, and_comm] using this

/-- Translating a set preserves membership in `closure` (specialized to translation by `-a`). -/
lemma section13_translate_mem_closure_iff {n : Nat} (S : Set (Fin n → Real)) (a : Fin n → Real) :
    (a ∈ closure S ↔ (0 : Fin n → Real) ∈ closure (S - ({a} : Set (Fin n → Real)))) := by
  classical
  -- Translate by `-a`.
  let h : (Fin n → Real) ≃ₜ (Fin n → Real) := Homeomorph.subRight a
  constructor
  · intro ha
    have : h a ∈ h '' closure S := ⟨a, ha, rfl⟩
    have : h a ∈ closure (h '' S) := by simpa [h.image_closure] using this
    simpa [h, Set.sub_singleton, sub_eq_add_neg] using this
  · intro h0
    have h0' : (0 : Fin n → Real) ∈ closure (h '' S) := by
      simpa [h, Set.sub_singleton, sub_eq_add_neg] using h0
    -- Pull back the closure statement along the inverse translation.
    have : h.symm 0 ∈ h ⁻¹' closure (h '' S) := by
      change h (h.symm 0) ∈ closure (h '' S)
      simpa using h0'
    have : h.symm 0 ∈ closure (h ⁻¹' (h '' S)) := by
      simpa [h.preimage_closure] using this
    have : h.symm 0 ∈ closure S := by
      simpa [Homeomorph.preimage_image] using this
    have hsymm0 : h.symm (0 : Fin n → Real) = a := by
      simp [h, Homeomorph.subRight]
    simpa [hsymm0] using this

/-- Translating a set preserves membership in `interior` (specialized to translation by `-a`). -/
lemma section13_translate_mem_interior_iff {n : Nat} (S : Set (Fin n → Real)) (a : Fin n → Real) :
    (a ∈ interior S ↔ (0 : Fin n → Real) ∈ interior (S - ({a} : Set (Fin n → Real)))) := by
  classical
  let h : (Fin n → Real) ≃ₜ (Fin n → Real) := Homeomorph.subRight a
  constructor
  · intro ha
    have : h a ∈ h '' interior S := ⟨a, ha, rfl⟩
    have : h a ∈ interior (h '' S) := by simpa [h.image_interior] using this
    simpa [h, Set.sub_singleton, sub_eq_add_neg] using this
  · intro h0
    have h0' : (0 : Fin n → Real) ∈ interior (h '' S) := by
      simpa [h, Set.sub_singleton, sub_eq_add_neg] using h0
    have : h.symm 0 ∈ h ⁻¹' interior (h '' S) := by
      change h (h.symm 0) ∈ interior (h '' S)
      simpa using h0'
    have : h.symm 0 ∈ interior (h ⁻¹' (h '' S)) := by
      simpa [h.preimage_interior] using this
    have : h.symm 0 ∈ interior S := by
      simpa [Homeomorph.preimage_image] using this
    have hsymm0 : h.symm (0 : Fin n → Real) = a := by
      simp [h, Homeomorph.subRight]
    simpa [hsymm0] using this

/-- Translating a set preserves membership in `intrinsicInterior`. -/
lemma section13_translate_mem_intrinsicInterior_iff {n : Nat} (S : Set (Fin n → Real))
    (a : Fin n → Real) :
    (a ∈ intrinsicInterior ℝ S ↔
        (0 : Fin n → Real) ∈ intrinsicInterior ℝ (S - ({a} : Set (Fin n → Real)))) := by
  classical
  -- Use the affine isometry `x ↦ x - a`.
  let e : (Fin n → Real) ≃ᵃⁱ[ℝ] (Fin n → Real) := AffineIsometryEquiv.vaddConst ℝ (-a)
  have himage :
      intrinsicInterior ℝ ((fun x : Fin n → Real => x - a) '' S) =
        (fun x : Fin n → Real => x - a) '' intrinsicInterior ℝ S := by
    simpa [e, sub_eq_add_neg] using
      (AffineIsometry.image_intrinsicInterior (φ := e.toAffineIsometry) (s := S))
  constructor
  · intro ha
    have h0image : (0 : Fin n → Real) ∈ (fun x : Fin n → Real => x - a) '' intrinsicInterior ℝ S :=
      ⟨a, ha, by simp⟩
    have h0ii : (0 : Fin n → Real) ∈ intrinsicInterior ℝ ((fun x : Fin n → Real => x - a) '' S) := by
      rw [himage]
      exact h0image
    -- Rewrite the target set as a translate image.
    -- Avoid `simp` to prevent typeclass inference timeouts on `affineSpan`.
    -- `S - {a} = (fun x => x - a) '' S`.
    rw [Set.sub_singleton]
    exact h0ii
  · intro h0
    have h0ii : (0 : Fin n → Real) ∈ intrinsicInterior ℝ ((fun x : Fin n → Real => x - a) '' S) := by
      -- `S - {a} = (fun x => x - a) '' S`.
      have h0' := h0
      rw [Set.sub_singleton] at h0'
      exact h0'
    have h0image : (0 : Fin n → Real) ∈ (fun x : Fin n → Real => x - a) '' intrinsicInterior ℝ S := by
      have h0ii' := h0ii
      rw [himage] at h0ii'
      exact h0ii'
    rcases h0image with ⟨x, hx, hx0⟩
    have : x = a := by simpa using sub_eq_zero.1 hx0
    exact this ▸ hx

/-- Translating a set preserves membership in its `affineSpan`. -/
lemma section13_translate_mem_affineSpan_iff {n : Nat} (S : Set (Fin n → Real)) (a : Fin n → Real) :
    (a ∈ (affineSpan ℝ S : Set (Fin n → Real)) ↔
        (0 : Fin n → Real) ∈
          (affineSpan ℝ (S - ({a} : Set (Fin n → Real))) : Set (Fin n → Real))) := by
  classical
  let e : (Fin n → Real) ≃ᵃ[ℝ] (Fin n → Real) := AffineEquiv.vaddConst ℝ (-a)
  let f : (Fin n → Real) →ᵃ[ℝ] (Fin n → Real) := (↑e : (Fin n → Real) →ᵃ[ℝ] (Fin n → Real))
  -- Map `affineSpan` across the translation affine equivalence.
  have hmap :
      AffineSubspace.map f (affineSpan ℝ S) = affineSpan ℝ (f '' S) := by
    simpa using (AffineSubspace.map_span (f := f) S)
  constructor
  · intro ha
    have : (0 : Fin n → Real) ∈ AffineSubspace.map f (affineSpan ℝ S) := by
      refine (AffineSubspace.mem_map).2 ?_
      refine ⟨a, ha, ?_⟩
      simp [f, e]
    have : (0 : Fin n → Real) ∈ (affineSpan ℝ (f '' S) : Set (Fin n → Real)) := by
      simpa [hmap] using this
    simpa [f, e, Set.sub_singleton, sub_eq_add_neg] using this
  · intro h0
    have : (0 : Fin n → Real) ∈ (affineSpan ℝ (f '' S) : Set (Fin n → Real)) := by
      simpa [f, e, Set.sub_singleton, sub_eq_add_neg] using h0
    have : (0 : Fin n → Real) ∈ AffineSubspace.map f (affineSpan ℝ S) := by
      simpa [hmap] using this
    rcases (AffineSubspace.mem_map).1 this with ⟨x, hx, hx0⟩
    have : x = a := by
      have : x + (-a) = 0 := by simpa [f, e] using hx0
      simpa [sub_eq_add_neg] using (eq_neg_of_add_eq_zero_left this)
    simpa [this] using hx

/-- Translation invariance of closure, intrinsic interior, interior and affine span at the origin. -/
lemma section13_translate_mem_closure_ri_interior_affineSpan_iff_zero {n : Nat}
    (S : Set (Fin n → Real)) (a : Fin n → Real) :
    (a ∈ closure S ↔ (0 : Fin n → Real) ∈ closure (S - ({a} : Set (Fin n → Real)))) ∧
      (a ∈ intrinsicInterior ℝ S ↔
          (0 : Fin n → Real) ∈ intrinsicInterior ℝ (S - ({a} : Set (Fin n → Real)))) ∧
        (a ∈ interior S ↔ (0 : Fin n → Real) ∈ interior (S - ({a} : Set (Fin n → Real)))) ∧
          (a ∈ (affineSpan ℝ S : Set (Fin n → Real)) ↔
              (0 : Fin n → Real) ∈
                (affineSpan ℝ (S - ({a} : Set (Fin n → Real))) : Set (Fin n → Real))) := by
  classical
  refine ⟨section13_translate_mem_closure_iff (n := n) S a, ?_, ?_, ?_⟩
  · exact section13_translate_mem_intrinsicInterior_iff (n := n) S a
  · exact section13_translate_mem_interior_iff (n := n) S a
  · exact section13_translate_mem_affineSpan_iff (n := n) S a

/-- Support-function characterization of `(0 : ℝ^n) ∈ cl C` for convex nonempty `C`. -/
lemma section13_zero_mem_closure_iff_forall_zero_le_supportFunctionEReal {n : Nat}
    (C : Set (Fin n → Real)) (hCconv : Convex ℝ C) (hCne : C.Nonempty) :
    (0 : Fin n → Real) ∈ closure C ↔ ∀ y : Fin n → Real, (0 : EReal) ≤ supportFunctionEReal C y := by
  classical
  constructor
  · intro h0 y
    by_contra hneg
    have hlt : supportFunctionEReal C y < (0 : EReal) := lt_of_not_ge hneg
    have hne_top : supportFunctionEReal C y ≠ ⊤ := by
      intro htop
      have hlt' := hlt
      simp [htop] at hlt'
    set μ : Real := (supportFunctionEReal C y).toReal
    have hμlt : μ < 0 := by
      have : (μ : EReal) = supportFunctionEReal C y := by
        simpa [μ] using
          (section13_supportFunctionEReal_coe_toReal (n := n) (C := C) hCne (y := y) hne_top)
      have : (μ : EReal) < (0 : EReal) := by simpa [this] using hlt
      exact (EReal.coe_lt_coe_iff.1 this)
    have hsupp_leμ : supportFunctionEReal C y ≤ (μ : EReal) := by
      simpa [μ] using (EReal.le_coe_toReal (x := supportFunctionEReal C y) hne_top)
    have hCsub : C ⊆ {x : Fin n → Real | dotProduct x y ≤ μ} := by
      intro x hx
      exact (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := y) (μ := μ)).1
        hsupp_leμ x hx
    have hclosed : IsClosed ({x : Fin n → Real | dotProduct x y ≤ μ} : Set (Fin n → Real)) := by
      simpa using (isClosed_setOf_dotProduct_le (n := n) (b := y) (β := μ))
    have hclsub : closure C ⊆ {x : Fin n → Real | dotProduct x y ≤ μ} :=
      (IsClosed.closure_subset_iff hclosed).2 hCsub
    have : (0 : Fin n → Real) ∈ {x : Fin n → Real | dotProduct x y ≤ μ} := hclsub h0
    have : (0 : Real) ≤ μ := by simpa [dotProduct] using this
    exact (not_lt_of_ge this) hμlt
  · intro hnonneg
    by_contra h0
    -- Strongly separate `0` and `C`, then contradict nonnegativity for the separating normal.
    have hdisj : Disjoint (closure ({0} : Set (Fin n → Real))) (closure C) := by
      have : Disjoint ({0} : Set (Fin n → Real)) (closure C) :=
        Set.disjoint_singleton_left.2 h0
      simpa [closure_singleton] using this
    rcases
        exists_hyperplaneSeparatesStrongly_of_disjoint_closure_convex_of_bounded (n := n)
          ({0} : Set (Fin n → Real)) C (Set.singleton_nonempty 0) hCne
          (convex_singleton (𝕜 := Real) (c := (0 : Fin n → Real))) hCconv hdisj
          (Or.inl Bornology.isBounded_singleton) with
      ⟨H, hH⟩
    rcases hH with ⟨_h₁ne, _h₂ne, b, β, hb0, _hHdef, ε, _hεpos, hcases⟩
    let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
    have hB0 : (0 : Fin n → Real) ∈ (ε • B) := by
      refine ⟨0, ?_, by simp⟩
      simp [B]
    cases hcases with
    | inl h =>
        -- `{0}` is on the `< β` side, hence `β > 0`, and `C` on the `β <` side.
        rcases h with ⟨h0β, hCβ⟩
        have hβpos : 0 < β := by
          have : (0 : Fin n → Real) ∈ ({0} : Set (Fin n → Real)) + (ε • B) := by
            refine ⟨0, by simp, 0, hB0, by simp⟩
          have : dotProduct (0 : Fin n → Real) b < β := h0β this
          simpa [dotProduct] using this
        have hC_ge : ∀ x ∈ C, β < dotProduct x b := by
          intro x hxC
          have : x ∈ C + (ε • B) := by
            refine ⟨x, hxC, 0, hB0, by simp⟩
          exact hCβ this
        -- Apply nonnegativity to `-b`.
        have hneg : (0 : EReal) ≤ supportFunctionEReal C (-b) := hnonneg (-b)
        have hsupp_le : supportFunctionEReal C (-b) ≤ ((-β : Real) : EReal) := by
          refine (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := -b) (μ := -β)).2 ?_
          intro x hxC
          have : β < dotProduct x b := hC_ge x hxC
          have : dotProduct x (-b) < -β := by simpa [dotProduct_neg] using (neg_lt_neg this)
          exact le_of_lt this
        have : (0 : EReal) ≤ ((-β : Real) : EReal) := le_trans hneg hsupp_le
        have : (0 : Real) ≤ -β := (EReal.coe_le_coe_iff.1 this)
        linarith
    | inr h =>
        -- `C` is on the `< β` side, and `{0}` on the `β <` side, hence `β < 0`.
        rcases h with ⟨hCβ, h0β⟩
        have hβneg : β < 0 := by
          have : (0 : Fin n → Real) ∈ ({0} : Set (Fin n → Real)) + (ε • B) := by
            refine ⟨0, by simp, 0, hB0, by simp⟩
          have : β < dotProduct (0 : Fin n → Real) b := h0β this
          simpa [dotProduct] using this
        have hsupp_le : supportFunctionEReal C b ≤ (β : EReal) := by
          refine (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := b) (μ := β)).2 ?_
          intro x hxC
          have : x ∈ C + (ε • B) := by
            refine ⟨x, hxC, 0, hB0, by simp⟩
          exact le_of_lt (hCβ this)
        have hnonneg_b : (0 : EReal) ≤ supportFunctionEReal C b := hnonneg b
        have : (0 : EReal) ≤ (β : EReal) := le_trans hnonneg_b hsupp_le
        have : (0 : Real) ≤ β := (EReal.coe_le_coe_iff.1 this)
        linarith

/-- Support-function characterization of `(0 : ℝ^n) ∈ int C` for convex nonempty `C`. -/
lemma section13_zero_mem_interior_iff_forall_supportFunctionEReal_pos {n : Nat}
    (C : Set (Fin n → Real)) (hCconv : Convex ℝ C) (hCne : C.Nonempty) :
    (0 : Fin n → Real) ∈ interior C ↔
      ∀ y : Fin n → Real, y ≠ 0 → supportFunctionEReal C y > (0 : EReal) := by
  classical
  cases n with
  | zero =>
      -- In dimension `0`, there are no nonzero directions, and every nonempty set contains `0`.
      have h0C : (0 : Fin 0 → Real) ∈ C := by
        rcases hCne with ⟨x, hx⟩
        have hx0 : x = 0 := Subsingleton.elim x 0
        simpa [hx0] using hx
      have hinter : (0 : Fin 0 → Real) ∈ interior C := by
        -- `Fin 0 → ℝ` is a subsingleton, so `C` is `univ` once nonempty.
        have : C = (Set.univ : Set (Fin 0 → Real)) := by
          ext x
          constructor
          · intro hx; trivial
          · intro _hx
            have hx0 : x = 0 := Subsingleton.elim x 0
            simpa [hx0] using h0C
        simp [this]
      refine ⟨fun _ => ?_, fun _ => hinter⟩
      · intro y hy0
        exact (hy0 (Subsingleton.elim y 0)).elim
  | succ n =>
      constructor
      · intro h0int y hy0
        -- Get a ball around `0` contained in `C`.
        have hnhds : C ∈ nhds (0 : Fin (Nat.succ n) → Real) :=
          (mem_interior_iff_mem_nhds).1 h0int
        rcases (Metric.mem_nhds_iff.1 hnhds) with ⟨ε, hεpos, hball⟩
        have hnormpos : 0 < ‖y‖ := (norm_pos_iff.2 hy0)
        set t : Real := ε / (2 * ‖y‖)
        have htpos : 0 < t := by
          have hdenpos : 0 < (2 * ‖y‖) := mul_pos (by norm_num) hnormpos
          exact div_pos hεpos hdenpos
        have htlt : t * ‖y‖ < ε := by
          -- `t * ‖y‖ = ε / 2`.
          have hyne : (‖y‖ : Real) ≠ 0 := ne_of_gt hnormpos
          have ht_mul : t * ‖y‖ = ε / 2 := by
            -- Cancel `‖y‖` from the denominator.
            calc
              t * ‖y‖ = (ε / (2 * ‖y‖)) * ‖y‖ := by rfl
              _ = (ε * ‖y‖) / (2 * ‖y‖) := by
                    simp [div_mul_eq_mul_div]
              _ = ε / 2 := by
                    simpa [mul_assoc] using (mul_div_mul_right ε (2 : Real) hyne)
          have hhalf : (ε / 2) < ε := by nlinarith [hεpos]
          simpa [ht_mul] using hhalf
        have htball : t • y ∈ Metric.ball (0 : Fin (Nat.succ n) → Real) ε := by
          -- `‖t • y‖ = t * ‖y‖ < ε`.
          have : ‖t • y‖ < ε := by
            simpa [norm_smul, Real.norm_eq_abs, abs_of_pos htpos] using htlt
          simpa [Metric.mem_ball, dist_eq_norm] using this
        have htyC : t • y ∈ C := hball htball
        have hdotpos : (0 : Real) < dotProduct (t • y) y := by
          have hyypos : (0 : Real) < dotProduct y y := by
            have hnonneg : (0 : Real) ≤ dotProduct y y := by
              unfold dotProduct
              exact Finset.sum_nonneg (fun i _hi => mul_self_nonneg (y i))
            have hne : dotProduct y y ≠ 0 := by
              intro hEq
              exact hy0 ((dotProduct_self_eq_zero (v := y)).1 hEq)
            exact lt_of_le_of_ne hnonneg hne.symm
          -- `⟪t•y, y⟫ = t * ⟪y, y⟫`.
          have hdot : dotProduct (t • y) y = t * dotProduct y y :=
            smul_dotProduct t y y
          simpa [hdot] using (mul_pos htpos hyypos)
        -- Now bound the support function from below by `⟪t•y, y⟫`.
        have hle : ((dotProduct (t • y) y : Real) : EReal) ≤ supportFunctionEReal C y := by
          unfold supportFunctionEReal
          refine le_sSup ?_
          exact ⟨t • y, htyC, rfl⟩
        have : (0 : EReal) < ((dotProduct (t • y) y : Real) : EReal) :=
          (EReal.coe_lt_coe_iff.2 hdotpos)
        exact lt_of_lt_of_le this hle
      · intro hpos
        -- Prove by contradiction that `0 ∈ interior C`.
        by_contra h0int
        by_cases h0C : (0 : Fin (Nat.succ n) → Real) ∈ C
        · -- Split into the full-dimensional and lower-dimensional cases.
          by_cases hspan : affineSpan ℝ C = (⊤ : AffineSubspace ℝ (Fin (Nat.succ n) → Real))
          · -- If the affine span is `⊤`, then `ri C = int C`, so `0 ∉ ri C`.
            have hri_eq : intrinsicInterior ℝ C = interior C :=
              cor11_6_1_intrinsicInterior_eq_interior_of_affineSpan_eq_top (n := Nat.succ n) C hspan
            have h0not_ri : (0 : Fin (Nat.succ n) → Real) ∉ intrinsicInterior ℝ C := by
              simpa [hri_eq] using h0int
            have hdisj :
                Disjoint ({0} : Set (Fin (Nat.succ n) → Real)) (intrinsicInterior ℝ C) := by
              exact Set.disjoint_singleton_left.2 h0not_ri
            have hsubset : ({0} : Set (Fin (Nat.succ n) → Real)) ⊆ C := by
              intro x hx
              have : x = 0 := by simpa [Set.mem_singleton_iff] using hx
              simpa [this] using h0C
            have hiff :=
              exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n := Nat.succ n)
                (C := C) (D := ({0} : Set (Fin (Nat.succ n) → Real))) hCconv
                (Set.singleton_nonempty (0 : Fin (Nat.succ n) → Real)) (convex_singleton 0) hsubset
            rcases (hiff.2 hdisj) with ⟨H, hHnontriv, hDH⟩
            rcases hHnontriv with ⟨hHsupport, hCnotH⟩
            rcases hHsupport with ⟨b, β, hb0, hHdef, hC_le, _hx_touch⟩
            have h0H : (0 : Fin (Nat.succ n) → Real) ∈ H := hDH (by simp)
            have hβ : β = 0 := by
              have : dotProduct (0 : Fin (Nat.succ n) → Real) b = β := by simpa [hHdef] using h0H
              simpa [dotProduct] using this.symm
            -- `supportFunctionEReal C b = 0`, contradicting strict positivity for `b ≠ 0`.
            have hsupp_le : supportFunctionEReal C b ≤ (0 : EReal) := by
              refine (section13_supportFunctionEReal_le_coe_iff (n := Nat.succ n) (C := C) (y := b)
                (μ := 0)).2 ?_
              intro x hxC
              have : dotProduct x b ≤ β := hC_le x hxC
              simpa [hβ] using this
            have hsupp_ge : (0 : EReal) ≤ supportFunctionEReal C b := by
              unfold supportFunctionEReal
              refine le_sSup ?_
              exact ⟨0, h0C, by simp⟩
            have hsupp0 : supportFunctionEReal C b = 0 := le_antisymm hsupp_le hsupp_ge
            have : ¬ supportFunctionEReal C b > (0 : EReal) := by
              simp [hsupp0]
            exact this (hpos b hb0)
          · -- If `affineSpan C ≠ ⊤`, then `C` lies in a hyperplane, yielding a nonzero direction
            -- with support function value `0`.
            rcases
                exists_hyperplane_superset_affineSpan_of_affineSpan_ne_top (n := Nat.succ n)
                  (hn := Nat.succ_pos n) C hspan with
              ⟨b, β, hb0, hCsub, _hAsub⟩
            have hβ : β = 0 := by
              have : dotProduct (0 : Fin (Nat.succ n) → Real) b = β := by simpa using hCsub h0C
              simpa [dotProduct] using this.symm
            have hsupp_eq : supportFunctionEReal C b = 0 := by
              unfold supportFunctionEReal
              refine le_antisymm ?_ ?_
              · refine sSup_le ?_
                rintro _ ⟨x, hxC, rfl⟩
                have : dotProduct x b = β := hCsub hxC
                simp [this, hβ]
              · refine le_sSup ?_
                exact ⟨0, h0C, by simp⟩
            have : ¬ supportFunctionEReal C b > (0 : EReal) := by
              simp [hsupp_eq]
            exact this (hpos b hb0)
        · -- If `0 ∉ C`, separate `{0}` from `C` and obtain `b ≠ 0` with `σ_C(b) ≤ 0`.
          have hsep :
              ∃ H, HyperplaneSeparatesProperly (Nat.succ n) H ({0} : Set (Fin (Nat.succ n) → Real)) C := by
            refine cor11_5_2_exists_hyperplaneSeparatesProperly_point (n := Nat.succ n) (C := C)
              (a := (0 : Fin (Nat.succ n) → Real)) hCne hCconv ?_
            exact h0C
          rcases hsep with ⟨H, hsep⟩
          rcases hyperplaneSeparatesProperly_oriented (Nat.succ n) H ({0} : Set (Fin (Nat.succ n) → Real)) C hsep with
            ⟨b, β, hb0, _hHdef, h0_ge, hC_le, _hnot⟩
          have hβle : β ≤ 0 := by
            have := h0_ge (0 : Fin (Nat.succ n) → Real) (by simp)
            simpa [dotProduct] using this
          have hsupp_le : supportFunctionEReal C b ≤ (0 : EReal) := by
            have : supportFunctionEReal C b ≤ (β : EReal) := by
              refine (section13_supportFunctionEReal_le_coe_iff (n := Nat.succ n) (C := C) (y := b)
                (μ := β)).2 ?_
              intro x hxC
              exact hC_le x hxC
            exact this.trans (by simpa using (EReal.coe_le_coe_iff.2 hβle))
          have : ¬ supportFunctionEReal C b > (0 : EReal) := by
            exact not_lt_of_ge hsupp_le
          exact this (hpos b hb0)

end Section13
end Chap03
