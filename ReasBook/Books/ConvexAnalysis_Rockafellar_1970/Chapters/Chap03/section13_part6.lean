/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part5

open scoped Pointwise

section Chap03
section Section13

/-- Text 13.3.1: A convex function `f` is called co-finite if `f` is closed and proper and
`epi f` contains no non-vertical half-lines; equivalently, its recession function `f₀⁺` satisfies
`f₀⁺(y) = +∞` for all `y ≠ 0`. -/
def CoFiniteConvexFunction {n : Nat} (f : (Fin n → Real) → EReal) : Prop :=
  ClosedConvexFunction f ∧
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f ∧
      ∀ y : Fin n → Real,
        y ≠ (0 : Fin n → Real) →
          sSup
              {r : EReal |
                ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f,
                  r = f (x + y) - f x} =
            (⊤ : EReal)

/-- If `f` is proper on `univ`, then its effective domain is nonempty. -/
lemma section13_effectiveDomain_nonempty_of_proper {n : Nat} {f : (Fin n → Real) → EReal} :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f →
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  intro hproper
  have hne_epi : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f) := hproper.2.1
  exact (nonempty_epigraph_iff_nonempty_effectiveDomain (Set.univ : Set (Fin n → Real)) f).1 hne_epi

/-- A bounded set cannot contain all iterates `x + n • y` for a nonzero vector `y`. -/
lemma section13_exists_mem_add_not_mem_effectiveDomain_of_isBounded {n : Nat}
    {D : Set (Fin n → Real)} (hbounded : Bornology.IsBounded D) (hne : Set.Nonempty D)
    {y : Fin n → Real} (hy : y ≠ (0 : Fin n → Real)) :
    ∃ x ∈ D, x + y ∉ D := by
  classical
  by_contra hxy
  push_neg at hxy
  rcases hne with ⟨x0, hx0⟩
  have hx0_iter : ∀ m : ℕ, x0 + m • y ∈ D := by
    intro m
    induction m with
    | zero =>
        simpa using hx0
    | succ m ih =>
        have h' : x0 + m • y + y ∈ D := by
          simpa [add_assoc] using hxy (x0 + m • y) ih
        -- Avoid simp rewriting `m • y` into `↑m * y` (pointwise multiplication).
        convert h' using 1
        calc
          x0 + (m + 1) • y = x0 + (m • y + y) := by rw [succ_nsmul]
          _ = x0 + m • y + y := (add_assoc x0 (m • y) y).symm
  have hy_exists : ∃ i : Fin n, y i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    funext i
    exact h i
  rcases hy_exists with ⟨i0, hy0⟩
  have hcoord_all :
      ∀ i : Fin n, Bornology.IsBounded (Function.eval i '' D) :=
    (Bornology.forall_isBounded_image_eval_iff (s := D)).2 hbounded
  have hcoord : Bornology.IsBounded (Function.eval i0 '' D) := hcoord_all i0
  obtain ⟨C, hCsub⟩ := hcoord.subset_closedBall (0 : Real)
  have hC : ∀ z ∈ Function.eval i0 '' D, ‖z‖ ≤ C := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : Real) C := hCsub hz
    have : dist z 0 ≤ C := (Metric.mem_closedBall).1 hz'
    simpa [Real.norm_eq_abs, Real.dist_eq] using this
  have hle : ∀ m : ℕ, (m : Real) * ‖y i0‖ ≤ C + ‖x0 i0‖ := by
    intro m
    have hnorm : ‖(x0 + m • y) i0‖ ≤ C := by
      have hmem : (x0 + m • y) i0 ∈ Function.eval i0 '' D :=
        ⟨x0 + m • y, hx0_iter m, rfl⟩
      exact hC _ hmem
    have hnorm' : ‖m • y i0‖ ≤ C + ‖x0 i0‖ := by
      have htmp : ‖m • y i0‖ ≤ ‖x0 i0 + m • y i0‖ + ‖x0 i0‖ := by
        simpa using (norm_sub_le (x0 i0 + m • y i0) (x0 i0))
      have htmp2 : ‖x0 i0 + m • y i0‖ + ‖x0 i0‖ ≤ C + ‖x0 i0‖ := by
        have hnorm' : ‖x0 i0 + m • y i0‖ ≤ C := by
          simpa [Pi.add_apply] using hnorm
        exact add_le_add hnorm' le_rfl
      exact le_trans htmp htmp2
    have hnsmul : ‖m • y i0‖ = (m : Real) * ‖y i0‖ := by
      calc
        ‖m • y i0‖ = ‖(m : Real) * y i0‖ := by simp [nsmul_eq_mul]
        _ = ‖(m : Real)‖ * ‖y i0‖ := by simp
        _ = (m : Real) * ‖y i0‖ := by simp
    simpa [hnsmul] using hnorm'
  have hypos : 0 < ‖y i0‖ := norm_pos_iff.2 hy0
  obtain ⟨m, hm⟩ := exists_nat_gt ((C + ‖x0 i0‖) / ‖y i0‖)
  have hm' : C + ‖x0 i0‖ < (m : Real) * ‖y i0‖ := (div_lt_iff₀ hypos).1 hm
  have hle_m : (m : Real) * ‖y i0‖ ≤ C + ‖x0 i0‖ := hle m
  exact (not_lt_of_ge hle_m) hm'

/-- If `x ∈ dom f` but `x+y ∉ dom f`, then the recession `sSup` in direction `y` is `⊤`. -/
lemma section13_sSup_recession_eq_top_of_exists_not_mem {n : Nat} {f : (Fin n → Real) → EReal}
    {y : Fin n → Real} :
    (∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f,
        x + y ∉ effectiveDomain (Set.univ : Set (Fin n → Real)) f) →
      sSup
          {r : EReal |
            ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, r = f (x + y) - f x} =
        (⊤ : EReal) := by
  classical
  rintro ⟨x, hx, hxy⟩
  have hx_ne_top :
      f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
  have hxy_top : f (x + y) = (⊤ : EReal) := by
    have hnot_lt : ¬ f (x + y) < (⊤ : EReal) := by
      intro hlt
      have hmem : x + y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
        have : x + y ∈ {z | z ∈ (Set.univ : Set (Fin n → Real)) ∧ f z < (⊤ : EReal)} :=
          ⟨by simp, hlt⟩
        simpa [effectiveDomain_eq] using this
      exact hxy hmem
    exact (top_le_iff).1 ((not_lt).1 hnot_lt)
  have hdiff : f (x + y) - f x = (⊤ : EReal) := by
    calc
      f (x + y) - f x = (⊤ : EReal) - f x := by simp [hxy_top]
      _ = (⊤ : EReal) := EReal.top_sub hx_ne_top
  have htop_le :
      (⊤ : EReal) ≤
        sSup
            {r : EReal |
              ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, r = f (x + y) - f x} := by
    exact le_sSup ⟨x, hx, hdiff.symm⟩
  exact le_antisymm le_top htop_le

/-- Text 13.3.2: Let `f : ℝ^n → (-∞, +∞]` be closed, proper, and convex. If `dom f` is bounded,
then `f` is co-finite. -/
theorem coFiniteConvexFunction_of_isBounded_effectiveDomain {n : Nat}
    (f : (Fin n → Real) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hbounded : Bornology.IsBounded (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    CoFiniteConvexFunction f := by
  refine ⟨hclosed, hproper, ?_⟩
  intro y hy
  have hne_dom :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hproper
  have hex :
      ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f,
        x + y ∉ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    section13_exists_mem_add_not_mem_effectiveDomain_of_isBounded (n := n)
      (D := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hbounded hne_dom hy
  exact section13_sSup_recession_eq_top_of_exists_not_mem (n := n) (f := f) (y := y) hex

/-- The support function of `Set.univ` is `⊤` in any nonzero direction. -/
lemma section13_supportFunctionEReal_univ_eq_top_of_ne_zero {n : Nat} {y : Fin n → Real}
    (hy : y ≠ (0 : Fin n → Real)) :
    supportFunctionEReal (Set.univ : Set (Fin n → Real)) y = (⊤ : EReal) := by
  classical
  -- If the support function were not `⊤`, it would be bounded above by a real number; but
  -- the dot product `⟪t • y, y⟫` grows without bound for `t → ∞` when `y ≠ 0`.
  by_contra hne_top
  set μ : Real := (supportFunctionEReal (Set.univ : Set (Fin n → Real)) y).toReal
  have hleμ :
      supportFunctionEReal (Set.univ : Set (Fin n → Real)) y ≤ (μ : EReal) := by
    simpa [μ] using
      (EReal.le_coe_toReal (x := supportFunctionEReal (Set.univ : Set (Fin n → Real)) y) hne_top)
  have hyy_pos : 0 < dotProduct y y := by
    have hyy_nonneg : 0 ≤ dotProduct y y := by
      classical
      -- `dotProduct y y = ∑ i, (y i)^2 ≥ 0`.
      simpa [dotProduct] using
        (Finset.sum_nonneg (s := Finset.univ) (fun i _hi => mul_self_nonneg (y i)))
    have hyy_ne : dotProduct y y ≠ 0 := by
      intro hzero
      apply hy
      -- `dotProduct y y = 0 ↔ y = 0`.
      exact (dotProduct_self_eq_zero (v := y)).1 hzero
    exact lt_of_le_of_ne hyy_nonneg (Ne.symm hyy_ne)
  set M : Real := μ + 1
  obtain ⟨m, hm⟩ := exists_nat_gt (M / dotProduct y y)
  have hm' : M < (m : Real) * dotProduct y y := (div_lt_iff₀ hyy_pos).1 hm
  set x : Fin n → Real := (m : Real) • y
  have hx_dot : dotProduct x y = (m : Real) * dotProduct y y := by
    simp [x, smul_dotProduct]
  have hx_le_sup :
      ((dotProduct x y : Real) : EReal) ≤ supportFunctionEReal (Set.univ : Set (Fin n → Real)) y := by
    -- `x ∈ univ`, so `⟪x,y⟫` is one of the candidates defining the supremum.
    unfold supportFunctionEReal
    refine le_sSup ?_
    exact ⟨x, by simp, rfl⟩
  have hx_le_μ : (dotProduct x y : Real) ≤ μ := by
    have : ((dotProduct x y : Real) : EReal) ≤ (μ : EReal) := le_trans hx_le_sup hleμ
    exact (EReal.coe_le_coe_iff.1 this)
  have hx_gt_μ : μ < dotProduct x y := by
    have : μ < M := by simp [M]
    exact lt_trans this (by simpa [hx_dot] using hm')
  exact (not_lt_of_ge hx_le_μ) hx_gt_μ

/-- If `f*` is finite everywhere (no `⊥` and `dom f* = univ`), then `f` is proper. -/
lemma section13_proper_of_conjugate_finite_everywhere {n : Nat} {f : (Fin n → Real) → EReal}
    (hclosed : ClosedConvexFunction f)
    (hfiniteStar :
      effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) = Set.univ ∧
        ∀ xStar : Fin n → Real, fenchelConjugate n f xStar ≠ (⊥ : EReal)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
  classical
  -- First show `f*` is proper; then use `fenchelConjugate_proper_iff`.
  have hconvStar : ConvexFunction (fenchelConjugate n f) :=
    (fenchelConjugate_closedConvex (n := n) (f := f)).2
  have hconvOnStar : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) := by
    simpa [ConvexFunction] using hconvStar
  have hne_dom :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) := by
    refine ⟨0, ?_⟩
    simp [hfiniteStar.1]
  have hne_epi :
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain (Set.univ : Set (Fin n → Real))
          (fenchelConjugate n f)).2 hne_dom
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) := by
    refine ⟨hconvOnStar, hne_epi, ?_⟩
    intro xStar _hxStar
    exact hfiniteStar.2 xStar
  -- Properness is preserved by Fenchel conjugation (for convex functions).
  exact (fenchelConjugate_proper_iff (n := n) (f := f) hclosed.1).1 hproperStar

/-- Corollary 13.3.1. Let `f` be a closed convex function on `ℝ^n`. Then `f^*` is finite
everywhere (equivalently `dom f^* = ℝ^n`) if and only if `f` is co-finite. -/
theorem effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite {n : Nat}
    (f : (Fin n → Real) → EReal) (hclosed : ClosedConvexFunction f) :
    (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) = Set.univ ∧
        ∀ xStar : Fin n → Real, fenchelConjugate n f xStar ≠ (⊥ : EReal)) ↔
      CoFiniteConvexFunction f := by
  classical
  let fStar : (Fin n → Real) → EReal := fenchelConjugate n f
  let f0_plus : (Fin n → Real) → EReal :=
    fun y =>
      sSup
        {r : EReal |
          ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, r = f (x + y) - f x}
  have hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup
            {r : EReal |
              ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, r = f (x + y) - f x} := by
    intro y; rfl

  constructor
  · rintro ⟨hdomStar, hnotbotStar⟩
    have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
      section13_proper_of_conjugate_finite_everywhere (n := n) (f := f) hclosed ⟨hdomStar, hnotbotStar⟩
    have hsupp :
        supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) = f0_plus :=
      supportFunctionEReal_effectiveDomain_fenchelConjugate_eq_recession (n := n) (f := f)
        (hf := hproper) (hclosed := hclosed) (f0_plus := f0_plus) hf0_plus
    refine ⟨hclosed, hproper, ?_⟩
    intro y hy
    have hsupp_y :
        supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) y =
          f0_plus y := by
      simpa using congrArg (fun g => g y) hsupp
    have huniv_top : supportFunctionEReal (Set.univ : Set (Fin n → Real)) y = (⊤ : EReal) :=
      section13_supportFunctionEReal_univ_eq_top_of_ne_zero (n := n) (y := y) hy
    -- Rewrite `dom f* = univ` and identify the recession `sSup`.
    have : f0_plus y = (⊤ : EReal) := by
      have : supportFunctionEReal (Set.univ : Set (Fin n → Real)) y = f0_plus y := by
        simpa [hdomStar] using hsupp_y
      -- Combine with the explicit `supportFunctionEReal univ` computation.
      simpa [this] using huniv_top
    simpa [f0_plus] using this
  · intro hco
    have hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := hco.2.1
    have hnotbotStar : ∀ xStar : Fin n → Real, fenchelConjugate n f xStar ≠ (⊥ : EReal) := by
      have hfStar_proper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
        proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
      intro xStar
      exact hfStar_proper.2.2 xStar (by simp)
    have hsupp :
        supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) = f0_plus :=
      supportFunctionEReal_effectiveDomain_fenchelConjugate_eq_recession (n := n) (f := f)
        (hf := hf_proper) (hclosed := hco.1) (f0_plus := f0_plus) hf0_plus
    have htop_domStar :
        ∀ y : Fin n → Real,
          y ≠ (0 : Fin n → Real) →
            supportFunctionEReal
                (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) y =
              (⊤ : EReal) := by
      intro y hy
      have hsupp_y :
          supportFunctionEReal
              (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) y =
            f0_plus y := by
        simpa using congrArg (fun g => g y) hsupp
      calc
        supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) y =
            f0_plus y := hsupp_y
        _ = (⊤ : EReal) := by
            simpa [f0_plus] using (hco.2.2 y hy)
    -- Use Corollary 11.5.2 (half-space containment) to show `dom f*` cannot be a proper convex set.
    have hdomStar :
        effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) = Set.univ := by
      classical
      by_cases hn : 0 < n
      · -- Positive-dimensional case: apply the half-space separation corollary.
        set C : Set (Fin n → Real) :=
          effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
        have hconvStar : ConvexFunction (fenchelConjugate n f) :=
          (fenchelConjugate_closedConvex (n := n) (f := f)).2
        have hCconv : Convex ℝ C := by
          simpa [C] using
            (effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real)))
              (f := fenchelConjugate n f) (hf := (by simpa [ConvexFunction] using hconvStar)))
        by_contra hCne
        rcases
            exists_closedHalfspace_superset_of_convex_ne_univ (n := n) C hn hCconv
              (by simpa [C] using hCne) with
          ⟨b, β, hb0, hCb⟩
        have hle :
            supportFunctionEReal C b ≤ (β : EReal) := by
          have hforall :
              ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f),
                (dotProduct x b : Real) ≤ β := by
            intro x hx
            have : x ∈ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := hCb (by simpa [C] using hx)
            simpa using this
          -- Use the general support-function bound lemma with `f := f*`.
          have :=
            (section13_supportFunctionEReal_effectiveDomain_le_coe_iff (f := fStar) (y := b)
                  (μ := β)).2 hforall
          simpa [fStar, C] using this
        have htopb : supportFunctionEReal C b = (⊤ : EReal) := by
          -- `b ≠ 0` implies the support function must be `⊤` at `b`.
          simpa [C] using htop_domStar b hb0
        have : (⊤ : EReal) ≤ (β : EReal) := by
          rw [← htopb]
          exact hle
        exact (not_top_le_coe β) this
      · -- `n = 0`: the ambient space is subsingleton, so any nonempty domain is `univ`.
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst hn0
        have hfStar_proper :
            ProperConvexFunctionOn (Set.univ : Set (Fin 0 → Real)) (fenchelConjugate 0 f) :=
          proper_fenchelConjugate_of_proper (n := 0) (f := f) hf_proper
        have hne_dom :
            Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin 0 → Real)) (fenchelConjugate 0 f)) :=
          (nonempty_epigraph_iff_nonempty_effectiveDomain (Set.univ : Set (Fin 0 → Real))
                (fenchelConjugate 0 f)).1 hfStar_proper.2.1
        rcases hne_dom with ⟨x0, hx0⟩
        ext x
        have hx : x = x0 := Subsingleton.elim x x0
        simpa [hx] using hx0
    exact ⟨hdomStar, hnotbotStar⟩

/-- Auxiliary definition: the recession function `f₀⁺` of an `EReal`-valued function `f` on `ℝ^n`,
given by `f₀⁺(y) = sup { f(x+y) - f(x) | x ∈ dom f }`. -/
noncomputable def recessionFunction {n : Nat} (f : (Fin n → Real) → EReal) :
    (Fin n → Real) → EReal :=
  fun y =>
    sSup
      {r : EReal |
        ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, r = f (x + y) - f x}

/-- For the `EReal`-valued support function, an upper bound by a real `μ` is equivalent to a
pointwise upper bound on all dot products defining the supremum. -/
lemma section13_supportFunctionEReal_le_coe_iff {n : Nat} (C : Set (Fin n → Real))
    (y : Fin n → Real) (μ : Real) :
    supportFunctionEReal C y ≤ (μ : EReal) ↔ ∀ x ∈ C, (dotProduct x y : Real) ≤ μ := by
  classical
  constructor
  · intro hle x hx
    have hxle :
        ((dotProduct x y : Real) : EReal) ≤
          sSup {z : EReal | ∃ x ∈ C, z = ((dotProduct x y : Real) : EReal)} :=
      le_sSup ⟨x, hx, rfl⟩
    have : ((dotProduct x y : Real) : EReal) ≤ (μ : EReal) := le_trans hxle hle
    exact (EReal.coe_le_coe_iff.1 this)
  · intro hle
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact (EReal.coe_le_coe_iff.2 (hle x hx))

/-- If `C` is nonempty and `supportFunctionEReal C y ≠ ⊤`, then `supportFunctionEReal C y` is the
coercion of its `toReal`. -/
lemma section13_supportFunctionEReal_coe_toReal {n : Nat} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) {y : Fin n → Real} (hy : supportFunctionEReal C y ≠ ⊤) :
    ((supportFunctionEReal C y).toReal : EReal) = supportFunctionEReal C y := by
  exact
    EReal.coe_toReal hy
      (section13_supportFunctionEReal_ne_bot_of_nonempty (n := n) (C := C) hCne y)

/-- On an affine subspace, if the support function is finite at `y`, then it is symmetric. -/
lemma section13_supportFunctionEReal_affineSubspace_symmetry {n : Nat}
    (A : AffineSubspace ℝ (Fin n → Real)) (hAne : (A : Set (Fin n → Real)).Nonempty)
    {y : Fin n → Real} (hy : supportFunctionEReal (A : Set (Fin n → Real)) y ≠ ⊤) :
    -supportFunctionEReal (A : Set (Fin n → Real)) (-y) =
      supportFunctionEReal (A : Set (Fin n → Real)) y := by
  classical
  rcases hAne with ⟨x0, hx0A⟩
  set μ : Real := (supportFunctionEReal (A : Set (Fin n → Real)) y).toReal
  have hsup_le :
      supportFunctionEReal (A : Set (Fin n → Real)) y ≤ (μ : EReal) := by
    simpa [μ] using
      (EReal.le_coe_toReal
        (x := supportFunctionEReal (A : Set (Fin n → Real)) y) hy)
  have hdot_le : ∀ x ∈ (A : Set (Fin n → Real)), (dotProduct x y : Real) ≤ μ :=
    (section13_supportFunctionEReal_le_coe_iff (n := n) (C := (A : Set (Fin n → Real))) (y := y)
          (μ := μ)).1 hsup_le

  have hdir0 : ∀ v ∈ A.direction, dotProduct v y = 0 := by
    intro v hv
    by_contra hv0
    have hlt_or_gt : dotProduct v y < 0 ∨ 0 < dotProduct v y := lt_or_gt_of_ne hv0
    have hw :
        ∃ w ∈ A.direction, 0 < dotProduct w y := by
      cases hlt_or_gt with
      | inl hvneg =>
          refine ⟨-v, ?_, ?_⟩
          · simpa using A.direction.neg_mem hv
          · have : dotProduct (-v) y = -(dotProduct v y) := by
              calc
                dotProduct (-v) y = dotProduct y (-v) := by simp [dotProduct_comm]
                _ = -(dotProduct y v) := by simp [dotProduct_neg]
                _ = -(dotProduct v y) := by simp [dotProduct_comm]
            simpa [this] using (neg_pos.2 hvneg)
      | inr hvpos =>
          exact ⟨v, hv, hvpos⟩
    rcases hw with ⟨w, hwdir, hwpos⟩
    -- Translate along `w` to contradict the upper bound on `⟪x, y⟫`.
    set M : Real := (μ - dotProduct x0 y) + 1
    obtain ⟨m, hm⟩ := exists_nat_gt (M / dotProduct w y)
    have hm' : M < (m : Real) * dotProduct w y := (div_lt_iff₀ hwpos).1 hm
    have hwA : (m : Real) • w ∈ A.direction := A.direction.smul_mem (m : Real) hwdir
    have hxA : (m : Real) • w +ᵥ x0 ∈ A := AffineSubspace.vadd_mem_of_mem_direction (s := A) hwA hx0A
    have hx_le : (dotProduct ((m : Real) • w +ᵥ x0) y : Real) ≤ μ := hdot_le _ hxA
    have hx_gt : μ < dotProduct ((m : Real) • w +ᵥ x0) y := by
      have hdot :
          dotProduct ((m : Real) • w +ᵥ x0) y =
          (m : Real) * dotProduct w y + dotProduct x0 y := by
        -- `v +ᵥ p` is `v + p` in this model.
        simp [vadd_eq_add, smul_dotProduct]
      have hμ_lt : μ < M + dotProduct x0 y := by
        -- `M + ⟪x0,y⟫ = μ + 1`.
        dsimp [M]
        linarith
      have hM_lt :
          M + dotProduct x0 y < (m : Real) * dotProduct w y + dotProduct x0 y := by
        -- `hm' : M < m * ⟪w,y⟫`; add `⟪x0,y⟫` to both sides and normalize.
        have := add_lt_add_left hm' (dotProduct x0 y)
        simpa [add_assoc, add_left_comm, add_comm] using this
      have hlt : μ < (m : Real) * dotProduct w y + dotProduct x0 y := lt_trans hμ_lt hM_lt
      simpa [hdot] using hlt
    exact (not_lt_of_ge hx_le) hx_gt

  have hdot_eq : ∀ x ∈ (A : Set (Fin n → Real)), dotProduct x y = dotProduct x0 y := by
    intro x hxA
    have hx_dir : x - x0 ∈ A.direction := by
      have : x -ᵥ x0 ∈ A.direction := AffineSubspace.vsub_mem_direction hxA hx0A
      simpa [vsub_eq_sub] using this
    have hx0 : dotProduct (x - x0) y = 0 := hdir0 (x - x0) hx_dir
    -- Expand `dotProduct (x - x0) y = dotProduct x y - dotProduct x0 y`.
    have hsub : dotProduct (x - x0) y = dotProduct x y - dotProduct x0 y := by
      have hneg : dotProduct (-x0) y = -dotProduct x0 y := by
        calc
          dotProduct (-x0) y = dotProduct y (-x0) := by simp [dotProduct_comm]
          _ = -(dotProduct y x0) := by simp [dotProduct_neg]
          _ = -(dotProduct x0 y) := by simp [dotProduct_comm]
      calc
        dotProduct (x - x0) y = dotProduct (x + (-x0)) y := by simp [sub_eq_add_neg]
        _ = dotProduct x y + dotProduct (-x0) y := by simp
        _ = dotProduct x y - dotProduct x0 y := by simp [hneg, sub_eq_add_neg]
    have : dotProduct x y - dotProduct x0 y = 0 := by simpa [hsub] using hx0
    linarith

  have hsupp_y :
      supportFunctionEReal (A : Set (Fin n → Real)) y = ((dotProduct x0 y : Real) : EReal) := by
    unfold supportFunctionEReal
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have : dotProduct x y = dotProduct x0 y := hdot_eq x hx
      simp [this]
    · exact le_sSup ⟨x0, hx0A, rfl⟩

  have hsupp_neg_y :
      supportFunctionEReal (A : Set (Fin n → Real)) (-y) = ((dotProduct x0 (-y) : Real) : EReal) := by
    have hdot_eq_neg : ∀ x ∈ (A : Set (Fin n → Real)), dotProduct x (-y) = dotProduct x0 (-y) := by
      intro x hx
      have hxy : dotProduct x y = dotProduct x0 y := hdot_eq x hx
      have : -dotProduct x y = -dotProduct x0 y := congrArg Neg.neg hxy
      simpa [dotProduct_neg] using this
    unfold supportFunctionEReal
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have : dotProduct x (-y) = dotProduct x0 (-y) := hdot_eq_neg x hx
      simp [this]
    · exact le_sSup ⟨x0, hx0A, rfl⟩

  -- Conclude by evaluating the constant dot products.
  simp [hsupp_y, hsupp_neg_y, dotProduct_neg]

/-- A convex set is affine iff its `EReal` support function is symmetric on the directions where it
is finite. -/
lemma section13_isAffineSet_iff_supportFunction_symmetry {n : Nat} {C : Set (Fin n → Real)}
    (hCconv : Convex ℝ C) (hCne : C.Nonempty) :
    (∃ A : AffineSubspace ℝ (Fin n → Real), (A : Set (Fin n → Real)) = C) ↔
      ∀ y : Fin n → Real,
        supportFunctionEReal C y ≠ ⊤ →
          -supportFunctionEReal C (-y) = supportFunctionEReal C y := by
  classical
  constructor
  · rintro ⟨A, rfl⟩
    intro y hy
    have hAne : (A : Set (Fin n → Real)).Nonempty := hCne
    exact section13_supportFunctionEReal_affineSubspace_symmetry (n := n) (A := A) hAne hy
  · intro hsym
    refine ⟨affineSpan ℝ C, ?_⟩
    refine le_antisymm ?_ (subset_affineSpan (k := ℝ) (s := C))
    · intro z hz_span
      by_contra hzC
      have hzC' : z ∉ C := hzC
      rcases cor11_5_2_exists_hyperplaneSeparatesProperly_point (n := n) (C := C) (a := z) hCne
            hCconv hzC' with
        ⟨H, hsep⟩
      rcases hyperplaneSeparatesProperly_oriented n H ({z} : Set (Fin n → Real)) C hsep with
        ⟨b, β, hb0, hHdef, hz_ge, hC_le, hnot⟩
      have hsupp_le : supportFunctionEReal C b ≤ (β : EReal) := by
        exact
          (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := b) (μ := β)).2 hC_le
      have hsupp_ne_top : supportFunctionEReal C b ≠ ⊤ := by
        intro htop
        simp [htop] at hsupp_le
      have hsymb :
          -supportFunctionEReal C (-b) = supportFunctionEReal C b := hsym b hsupp_ne_top
      have hsupp_neg : supportFunctionEReal C (-b) = -supportFunctionEReal C b := by
        have := congrArg (fun z : EReal => -z) hsymb
        simpa [neg_neg] using this
      set μ : Real := (supportFunctionEReal C b).toReal
      have hsupp_leμ : supportFunctionEReal C b ≤ (μ : EReal) := by
        simpa [μ] using (EReal.le_coe_toReal (x := supportFunctionEReal C b) hsupp_ne_top)
      have hdot_le : ∀ x ∈ C, (dotProduct x b : Real) ≤ μ :=
        (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := b) (μ := μ)).1 hsupp_leμ
      have hsupp_eq : (μ : EReal) = supportFunctionEReal C b := by
        simpa [μ] using
          section13_supportFunctionEReal_coe_toReal (n := n) (C := C) hCne (y := b) hsupp_ne_top
      have hsupp_neg_eq : supportFunctionEReal C (-b) = ((-μ : Real) : EReal) := by
        simp [hsupp_neg, hsupp_eq.symm]
      have hsupp_neg_le : supportFunctionEReal C (-b) ≤ ((-μ : Real) : EReal) := by
        simp [hsupp_neg_eq]
      have hdot_neg_le : ∀ x ∈ C, (dotProduct x (-b) : Real) ≤ (-μ : Real) :=
        (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := -b) (μ := (-μ))).1
          hsupp_neg_le
      have hdot_ge : ∀ x ∈ C, (μ : Real) ≤ dotProduct x b := by
        intro x hx
        have hle' : (dotProduct x (-b) : Real) ≤ (-μ : Real) := hdot_neg_le x hx
        have : -dotProduct x b ≤ -μ := by
          simpa [dotProduct_neg] using hle'
        exact (neg_le_neg_iff).1 this
      have hdot_eq : ∀ x ∈ C, dotProduct x b = μ := by
        intro x hx
        exact le_antisymm (hdot_le x hx) (hdot_ge x hx)
      -- Package the constant level-set as an affine subspace.
      let Hμ : AffineSubspace ℝ (Fin n → Real) :=
        { carrier := {x : Fin n → Real | dotProduct x b = μ}
          smul_vsub_vadd_mem := by
            intro c p1 p2 p3 hp1 hp2 hp3
            have hp1' : dotProduct p1 b = μ := by simpa using hp1
            have hp2' : dotProduct p2 b = μ := by simpa using hp2
            have hp3' : dotProduct p3 b = μ := by simpa using hp3
            have hp12 : dotProduct (p1 - p2) b = 0 := by
              have hsub : dotProduct (p1 - p2) b = dotProduct p1 b - dotProduct p2 b := by
                calc
                  dotProduct (p1 - p2) b = dotProduct b (p1 - p2) := by simp [dotProduct_comm]
                  _ = dotProduct b p1 - dotProduct b p2 := by
                    exact dotProduct_sub (u := b) (v := p1) (w := p2)
                  _ = dotProduct p1 b - dotProduct p2 b := by simp [dotProduct_comm]
              calc
                dotProduct (p1 - p2) b = dotProduct p1 b - dotProduct p2 b := hsub
                _ = μ - μ := by simp [hp1', hp2']
                _ = 0 := by simp
            have : dotProduct (c • (p1 - p2) + p3) b = μ := by
              simp [add_dotProduct, smul_dotProduct, hp12, hp3']
            simpa [vsub_eq_sub, vadd_eq_add] using this }
      have hC_Hμ : C ⊆ (Hμ : Set (Fin n → Real)) := by
        intro x hx
        exact hdot_eq x hx
      have hz_Hμ : z ∈ (Hμ : Set (Fin n → Real)) := by
        have hspan_le : affineSpan ℝ C ≤ Hμ :=
          (affineSpan_le (k := ℝ) (s := C) (Q := Hμ)).2 hC_Hμ
        exact hspan_le hz_span
      have hz_eq : dotProduct z b = μ := hz_Hμ
      have hβ_le : β ≤ dotProduct z b := by
        have : β ≤ (z ⬝ᵥ b) := by simpa using (hz_ge z (by simp))
        simpa using this
      have hμ_le_β : μ ≤ β := by
        have : (μ : EReal) ≤ (β : EReal) := by
          -- `supportFunctionEReal C b ≤ β` and `supportFunctionEReal C b = μ`.
          simpa [hsupp_eq.symm] using hsupp_le
        exact (EReal.coe_le_coe_iff.1 this)
      have hβ_eq_μ : β = μ := le_antisymm (by simpa [hz_eq] using hβ_le) hμ_le_β
      have hC_H : C ⊆ H := by
        intro u hu
        have huμ : dotProduct u b = μ := hdot_eq u hu
        have : dotProduct u b = β := by simpa [hβ_eq_μ] using huμ
        simp [hHdef, this]
      have hz_H : ({z} : Set (Fin n → Real)) ⊆ H := by
        intro u hu
        have hu_eq : u = z := by simpa using hu
        have hz_in : z ∈ H := by
          have : dotProduct z b = β := by simpa [hβ_eq_μ] using hz_eq
          simp [hHdef, this]
        simpa [hu_eq] using hz_in
      exact hnot ⟨hz_H, hC_H⟩

/-- The support function of `dom f*` is the recession function `recessionFunction f`. -/
lemma section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction {n : Nat}
    (f : (Fin n → Real) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    supportFunctionEReal
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) =
      recessionFunction f := by
  classical
  simpa [recessionFunction] using
    (supportFunctionEReal_effectiveDomain_fenchelConjugate_eq_recession (n := n) (f := f)
      (hf := hproper) (hclosed := hclosed) (f0_plus := recessionFunction f) (by intro y; rfl))

/-- Auxiliary definition: the linearity space of a function `f`, defined as the set of directions
`y` for which the recession function is finite and symmetric:
`-(f₀⁺)(-y) = (f₀⁺)(y)` whenever `(f₀⁺)(y) < +∞`. -/
def linearitySpace {n : Nat} (f : (Fin n → Real) → EReal) : Set (Fin n → Real) :=
  {y | recessionFunction f y ≠ (⊤ : EReal) ∧ -(recessionFunction f (-y)) = recessionFunction f y}

/-- Corollary 13.3.2. Let `f` be a closed proper convex function. In order that `dom f*` be an
affine set, it is necessary and sufficient that `(f0+)(y) = +∞` for every `y` which is not
actually in the linearity space of `f`. -/
theorem effectiveDomain_fenchelConjugate_isAffine_iff_forall_recessionFunction_eq_top_of_not_mem
    {n : Nat} (f : (Fin n → Real) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (∃ A : AffineSubspace ℝ (Fin n → Real),
        (A : Set (Fin n → Real)) =
          effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) ↔
      ∀ y : Fin n → Real, y ∉ linearitySpace f → recessionFunction f y = (⊤ : EReal) := by
  classical
  set C : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hCne : C.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
  have hCconv : Convex ℝ C := by
    have hconvStar : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    simpa [C] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := fenchelConjugate n f)
        (hf := (by simpa [ConvexFunction] using hconvStar)))
  have hsupp :
      supportFunctionEReal C = recessionFunction f := by
    simpa [C] using
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n) (f := f)
        hclosed hproper
  have hsupp_y : ∀ y : Fin n → Real, supportFunctionEReal C y = recessionFunction f y := by
    intro y
    simpa using congrArg (fun g => g y) hsupp

  -- Replace `dom f*`-affineness with symmetry of the support/recession function.
  have haff_symm :
      (∃ A : AffineSubspace ℝ (Fin n → Real), (A : Set (Fin n → Real)) = C) ↔
        ∀ y : Fin n → Real,
          recessionFunction f y ≠ ⊤ → -(recessionFunction f (-y)) = recessionFunction f y := by
    -- Apply the general lemma to `C`, then rewrite the support function using `hsupp_y`.
    have haff_support :=
      section13_isAffineSet_iff_supportFunction_symmetry (n := n) (C := C) hCconv hCne
    constructor
    · intro haff
      have hsymm := haff_support.1 haff
      intro y hy
      have hy' : supportFunctionEReal C y ≠ ⊤ := by
        simpa [(hsupp_y y).symm] using hy
      have h := hsymm y hy'
      simpa [hsupp_y y, hsupp_y (-y)] using h
    · intro hsymm
      refine haff_support.2 ?_
      intro y hy
      have hy' : recessionFunction f y ≠ ⊤ := by
        simpa [hsupp_y y] using hy
      have h := hsymm y hy'
      simpa [hsupp_y y, hsupp_y (-y)] using h

  -- Convert symmetry-on-finite-directions into the formulation using `linearitySpace`.
  constructor
  · intro haff
    have hsymm : ∀ y : Fin n → Real,
        recessionFunction f y ≠ ⊤ → -(recessionFunction f (-y)) = recessionFunction f y :=
      (haff_symm.1 (by simpa [C] using haff))
    intro y hy_not
    by_contra hy_top
    have hy_mem : y ∈ linearitySpace f := by
      refine ⟨hy_top, ?_⟩
      exact hsymm y hy_top
    exact hy_not hy_mem
  · intro htop
    have hsymm : ∀ y : Fin n → Real,
        recessionFunction f y ≠ ⊤ → -(recessionFunction f (-y)) = recessionFunction f y := by
      intro y hy
      have hy_mem : y ∈ linearitySpace f := by
        by_contra hy_not
        have : recessionFunction f y = ⊤ := htop y hy_not
        exact hy this
      exact hy_mem.2
    have haff : (∃ A : AffineSubspace ℝ (Fin n → Real), (A : Set (Fin n → Real)) = C) :=
      haff_symm.2 hsymm
    simpa [C] using haff

end Section13
end Chap03
