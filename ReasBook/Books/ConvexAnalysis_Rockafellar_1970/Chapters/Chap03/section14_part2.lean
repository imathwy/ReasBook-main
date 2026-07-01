/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part1

section Chap03
section Section14

open scoped Pointwise
open scoped Topology
open scoped RealInnerProductSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The effective domain `dom f` of an `EReal`-valued function, as the set where `f` is finite
(i.e. strictly below `⊤`). -/
def erealDom {F : Type*} (f : F → EReal) : Set F :=
  {x | f x < ⊤}

/-- A basic notion of properness for an `EReal`-valued function: it never takes the value `⊥`
and is finite at some point. -/
def ProperERealFunction {F : Type*} (f : F → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤

/-- A Jensen-style convexity condition for an `EReal`-valued function on a real vector space. -/
def ConvexERealFunction {F : Type*} [AddCommGroup F] [Module ℝ F] (f : F → EReal) : Prop :=
  ∀ ⦃x y : F⦄ ⦃a b : ℝ⦄,
    0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

/-- A "proper convex function" (proper + Jensen convex) for `EReal`-valued functions. -/
def ProperConvexERealFunction {F : Type*} [AddCommGroup F] [Module ℝ F] (f : F → EReal) : Prop :=
  ProperERealFunction f ∧ ConvexERealFunction f

/-- The recession function `f₀⁺(y) = sup { f(x+y) - f(x) | x ∈ dom f }` for an `EReal`-valued
function. -/
noncomputable def recessionFunctionEReal {F : Type*} [AddCommGroup F] (f : F → EReal) :
    F → EReal :=
  fun y => sSup {r : EReal | ∃ x ∈ erealDom f, r = f (x + y) - f x}

/-- The recession cone `{y | f₀⁺(y) ≤ 0}` associated to `recessionFunctionEReal`. -/
def recessionConeEReal {F : Type*} [AddCommGroup F] (f : F → EReal) : Set F :=
  {y | recessionFunctionEReal f y ≤ (0 : EReal)}

/-- Membership in `recessionConeEReal` is equivalent to a pointwise nonpositivity condition on
increment differences over the effective domain. -/
lemma section14_mem_recessionConeEReal_iff {F : Type*} [AddCommGroup F] (g : F → EReal) (y : F) :
    y ∈ recessionConeEReal (F := F) g ↔
      ∀ x, x ∈ erealDom g → g (x + y) - g x ≤ (0 : EReal) := by
  classical
  constructor
  · intro hy x hx
    have hy' :
        sSup {r : EReal | ∃ x ∈ erealDom g, r = g (x + y) - g x} ≤ (0 : EReal) := by
      simpa [recessionConeEReal, recessionFunctionEReal] using hy
    have hy'' := (sSup_le_iff).1 hy'
    exact hy'' (g (x + y) - g x) ⟨x, hx, rfl⟩
  · intro hy
    have : sSup {r : EReal | ∃ x ∈ erealDom g, r = g (x + y) - g x} ≤ (0 : EReal) := by
      refine (sSup_le_iff).2 ?_
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact hy x hx
    simpa [recessionConeEReal, recessionFunctionEReal] using this

/-- For `f : E → EReal`, membership in the polar cone of the cone hull of `erealDom f` is
equivalent to being nonpositive on `erealDom f`. -/
lemma section14_mem_polarCone_hull_erealDom_iff {f : E → EReal} (φ : Module.Dual ℝ E) :
    φ ∈ polarCone (E := E) ((ConvexCone.hull ℝ (erealDom f) : ConvexCone ℝ E) : Set E) ↔
      ∀ x, x ∈ erealDom f → φ x ≤ 0 := by
  constructor
  · intro hφ x hx
    have hxHull :
        x ∈ ((ConvexCone.hull ℝ (erealDom f) : ConvexCone ℝ E) : Set E) :=
      (ConvexCone.subset_hull (s := erealDom f)) hx
    exact (mem_polarCone_iff (E := E)
          (K := ((ConvexCone.hull ℝ (erealDom f) : ConvexCone ℝ E) : Set E)) (φ := φ)).1 hφ x
      hxHull
  · intro hφ
    refine (mem_polarCone_iff (E := E)
          (K := ((ConvexCone.hull ℝ (erealDom f) : ConvexCone ℝ E) : Set E)) (φ := φ)).2 ?_
    intro x hx
    have hx' : x ∈ (nonposCone (E := E) φ : Set E) := by
      have hle :
          ConvexCone.hull ℝ (erealDom f) ≤ nonposCone (E := E) φ := by
        refine (ConvexCone.hull_le_iff (C := nonposCone (E := E) φ) (s := erealDom f)).2 ?_
        intro z hz
        exact hφ z hz
      exact hle hx
    simpa [mem_nonposCone_iff] using hx'

/-- If `y★` is nonpositive on `erealDom f`, then the Fenchel conjugate of `f` is nonincreasing
under translation by `y★`. -/
lemma section14_fenchelConjugate_add_le_of_le_zero_on_dom {f : E → EReal}
    (yStar : Module.Dual ℝ E) (hy : ∀ x, x ∈ erealDom f → yStar x ≤ 0) :
    ∀ xStar : Module.Dual ℝ E,
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f (xStar + yStar) ≤
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f xStar := by
  classical
  intro xStar
  unfold fenchelConjugateBilin
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ erealDom f
  · have hyx : yStar x ≤ 0 := hy x hx
    have hle_real : xStar x + yStar x ≤ xStar x := add_le_of_nonpos_right hyx
    have hle_eval :
        ((xStar + yStar) x : EReal) ≤ (xStar x : EReal) := by
      simpa [LinearMap.add_apply] using (EReal.coe_le_coe hle_real)
    have hterm :
        ((xStar + yStar) x : EReal) - f x ≤ (xStar x : EReal) - f x := by
      -- `a - c ≤ b - c` from `a ≤ b`.
      simpa using (EReal.sub_le_sub hle_eval le_rfl)
    have : (xStar x : EReal) - f x ≤ sSup (Set.range fun x : E => (xStar x : EReal) - f x) :=
      le_sSup ⟨x, rfl⟩
    exact hterm.trans this
  · have hxTop : f x = ⊤ := by
      by_contra hne
      exact hx (lt_top_iff_ne_top.2 hne)
    simp [hxTop]

/-- A finite, non-`⊥` `EReal` value is a real coercion. -/
lemma section14_eq_coe_of_lt_top {z : EReal} (hzTop : z < ⊤) (hzBot : z ≠ ⊥) :
    ∃ r : ℝ, z = (r : EReal) := by
  induction z using EReal.rec with
  | bot => cases hzBot rfl
  | coe r => exact ⟨r, rfl⟩
  | top => cases (not_lt_of_ge le_rfl hzTop)

/-- The Fenchel conjugate of a proper function never takes the value `⊥`. -/
lemma section14_fenchelConjugate_ne_bot {f : E → EReal} (hf : ProperERealFunction f) :
    ∀ xStar : Module.Dual ℝ E,
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f xStar ≠ ⊥ := by
  classical
  intro xStar
  rcases hf.2 with ⟨x0, hx0neTop⟩
  have hx0lt : f x0 < ⊤ := lt_top_iff_ne_top.2 hx0neTop
  rcases section14_eq_coe_of_lt_top (z := f x0) hx0lt (hf.1 x0) with ⟨r0, hr0⟩
  have hle :
      ((xStar x0 : EReal) - f x0) ≤
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f xStar := by
    unfold fenchelConjugateBilin
    exact le_sSup ⟨x0, rfl⟩
  intro hbot
  have hle' : ((xStar x0 - r0 : ℝ) : EReal) ≤ (⊥ : EReal) := by
    have hle' := hle
    simp [hbot, hr0, sub_eq_add_neg] at hle'
  exact (not_le_of_gt (EReal.bot_lt_coe (xStar x0 - r0))) hle'

/-- If `y ∈ recessionConeEReal g` and `x ∈ erealDom g`, then translating by `y` does not increase
`g`, and the translate remains in the effective domain. -/
lemma section14_step_le_of_mem_recessionCone {F : Type*} [AddCommGroup F] (g : F → EReal) {x y : F}
    (hy : y ∈ recessionConeEReal (F := F) g) (hx : x ∈ erealDom g) :
    g (x + y) ≤ g x ∧ x + y ∈ erealDom g := by
  have hdiff : g (x + y) - g x ≤ (0 : EReal) :=
    (section14_mem_recessionConeEReal_iff (g := g) (y := y)).1 hy x hx
  have hle : g (x + y) ≤ g x := (EReal.sub_nonpos).1 hdiff
  have hlt : g (x + y) < ⊤ := lt_of_le_of_lt hle hx
  exact ⟨hle, hlt⟩

/-- If `n * r` is uniformly bounded above for all natural `n`, then `r ≤ 0`. -/
lemma section14_real_nonpos_of_nat_mul_le (r C : ℝ) (h : ∀ n : ℕ, (n : ℝ) * r ≤ C) : r ≤ 0 := by
  by_contra hr
  have hr' : 0 < r := lt_of_not_ge hr
  obtain ⟨n : ℕ, hn⟩ : ∃ n : ℕ, C / r < n := exists_nat_gt (C / r)
  have hC : C < (n : ℝ) * r := by
    have : C / r < (n : ℝ) := by exact_mod_cast hn
    exact (div_lt_iff₀ hr').1 this
  exact (not_lt_of_ge (h n)) hC

/-- Text 14.0.13 (Example). Define
`C₂ = {x = (ξ₁, …, ξₙ) | ξⱼ ≥ 0, ξ₁ + ⋯ + ξₙ ≤ 1}`.
Then its polar is
`C₂^∘ = {x★ = (ξ₁★, …, ξₙ★) | ξⱼ★ ≤ 1 for j = 1, …, n}`.

In this file, `C^∘` is modeled as `polar (E := EuclideanSpace ℝ (Fin n)) C :
Set (Module.Dual ℝ _)`, and we express the coordinate inequalities as
`φ (EuclideanSpace.single j 1) ≤ 1`. -/
theorem polar_sum_le_one_eq (n : ℕ) :
    let C₂ : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | (∀ j, 0 ≤ x j) ∧ (Finset.univ.sum (fun j => x j)) ≤ (1 : ℝ)}
    polar (E := EuclideanSpace ℝ (Fin n)) C₂ =
      {φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin n)) |
        ∀ j, φ (EuclideanSpace.single j (1 : ℝ)) ≤ 1} := by
  simpa using (polar_subprobabilitySimplex_eq (n := n))

/-- The coefficient vector of a linear functional on `ℝ^2` with respect to the standard basis. -/
noncomputable def section14_coeffVec (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) :=
  Finset.univ.sum fun i : Fin 2 =>
    (φ (EuclideanSpace.single i (1 : ℝ))) • EuclideanSpace.single i (1 : ℝ)

/-- The center `(1,0)` of the shifted unit disk `C₃`. -/
noncomputable def section14_C3_center : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (1 : ℝ)

/-- Expanding the squared distance from the center `(1,0)` gives the defining quadratic
inequality for `C₃`. -/
lemma section14_norm_sq_sub_C3_center (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x - section14_C3_center‖ ^ 2 = (x 0 - 1) ^ 2 + (x 1) ^ 2 := by
  classical
  -- Expand the `ℓ2` norm in coordinates.
  simp [section14_C3_center, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, Fin.sum_univ_two]

/-- Membership in `C₃` is equivalent to being within distance `1` from the center `(1,0)`. -/
lemma section14_mem_C3_iff_norm_sub_le (x : EuclideanSpace ℝ (Fin 2)) :
    ((x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)) ↔ ‖x - section14_C3_center‖ ≤ 1 := by
  constructor
  · intro hx
    have hx' : ‖x - section14_C3_center‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
      -- Rewrite the defining inequality as a squared norm inequality.
      simpa [section14_norm_sq_sub_C3_center (x := x)] using hx
    have hx'' : |‖x - section14_C3_center‖| ≤ |(1 : ℝ)| := (sq_le_sq).1 hx'
    simpa [abs_of_nonneg (norm_nonneg _)] using hx''
  · intro hx
    have hx' : ‖x - section14_C3_center‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
      -- Square both sides, using that `‖x - c‖ ≥ 0`.
      simpa [pow_two] using
        (mul_le_mul hx hx (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ (1 : ℝ)))
    -- Rewrite back to the defining inequality.
    simpa [section14_norm_sq_sub_C3_center (x := x)] using hx'

/-- A linear functional on `ℝ^2` acts as an inner product with its coefficient vector. -/
lemma section14_dual_apply_eq_inner_coeffVec (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    φ x = inner ℝ x (section14_coeffVec φ) := by
  classical
  -- Expand `φ x` in coordinates.
  have hsum :
      φ x =
        Finset.univ.sum (fun i : Fin 2 => x i * φ (EuclideanSpace.single i (1 : ℝ))) := by
    simpa using section14_dual_apply_eq_sum_mul_single (φ := φ) (x := x)
  -- Expand the inner product against the coefficient vector (only two coordinates).
  have hinner :
      inner ℝ x (section14_coeffVec φ) =
        (φ (EuclideanSpace.single 0 (1 : ℝ))) * x 0 +
          (φ (EuclideanSpace.single 1 (1 : ℝ))) * x 1 := by
    simp [section14_coeffVec, Fin.sum_univ_two, inner_add_right, inner_smul_right,
      EuclideanSpace.inner_single_right]
  -- Reconcile the two expansions.
  -- The coordinate sum over `Fin 2` is just the two-term sum.
  simpa [Fin.sum_univ_two, hinner, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using hsum

/-- If `φ` satisfies the support-function bound for the shifted unit disk, then `φ` belongs to
its polar. -/
lemma section14_mem_polar_C3_of_le_support_bound
    (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)))
    (hφ : φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖section14_coeffVec φ‖ ≤ 1) :
    φ ∈ polar (E := EuclideanSpace ℝ (Fin 2))
      ({x : EuclideanSpace ℝ (Fin 2) | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)} : Set _) := by
  refine (mem_polar_iff (E := EuclideanSpace ℝ (Fin 2))
        (C := {x : EuclideanSpace ℝ (Fin 2) | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)})
        (φ := φ)).2 ?_
  intro x hx
  have hxnorm : ‖x - section14_C3_center‖ ≤ 1 :=
    (section14_mem_C3_iff_norm_sub_le (x := x)).1 hx
  have hx_eq : section14_C3_center + (x - section14_C3_center) = x := by
    abel
  calc
    φ x = φ (section14_C3_center + (x - section14_C3_center)) := by
          simp [hx_eq]
    _ = φ section14_C3_center + φ (x - section14_C3_center) := by simp
    _ = φ (EuclideanSpace.single 0 (1 : ℝ)) +
          inner ℝ (x - section14_C3_center) (section14_coeffVec φ) := by
          simp [section14_C3_center, section14_dual_apply_eq_inner_coeffVec]
    _ ≤ φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖x - section14_C3_center‖ * ‖section14_coeffVec φ‖ := by
          gcongr
          exact real_inner_le_norm _ _
    _ ≤ φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖section14_coeffVec φ‖ := by
          have hmul : ‖x - section14_C3_center‖ * ‖section14_coeffVec φ‖ ≤ ‖section14_coeffVec φ‖ := by
            calc
              ‖x - section14_C3_center‖ * ‖section14_coeffVec φ‖ ≤
                  (1 : ℝ) * ‖section14_coeffVec φ‖ :=
                mul_le_mul_of_nonneg_right hxnorm (norm_nonneg _)
              _ = ‖section14_coeffVec φ‖ := by simp
          have hadded :=
            add_le_add_right hmul (φ (EuclideanSpace.single 0 (1 : ℝ)))
          simpa [add_comm, add_left_comm, add_assoc] using hadded
    _ ≤ 1 := hφ

/-- If `φ` belongs to the polar of the shifted unit disk, then it satisfies the support-function
bound `φ(1,0) + ‖vφ‖ ≤ 1`. -/
lemma section14_support_bound_of_mem_polar_C3
    (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)))
    (hφ : φ ∈ polar (E := EuclideanSpace ℝ (Fin 2))
      ({x : EuclideanSpace ℝ (Fin 2) | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)} : Set _)) :
    φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖section14_coeffVec φ‖ ≤ 1 := by
  classical
  have hle :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ ({x : EuclideanSpace ℝ (Fin 2) | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)} : Set _) →
          φ x ≤ 1 :=
    (mem_polar_iff (E := EuclideanSpace ℝ (Fin 2))
        (C := {x : EuclideanSpace ℝ (Fin 2) | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)})
        (φ := φ)).1 hφ
  set c : EuclideanSpace ℝ (Fin 2) := section14_C3_center
  set v : EuclideanSpace ℝ (Fin 2) := section14_coeffVec φ
  by_cases hv : v = 0
  · have hc_mem :
        c ∈ ({x : EuclideanSpace ℝ (Fin 2) | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)} : Set _) := by
      simp [c, section14_C3_center]
    have hc_le : φ c ≤ 1 := hle c hc_mem
    -- `‖v‖ = 0` in this case.
    simpa [c, v, section14_C3_center, hv] using hc_le
  · have hvnorm : ‖v‖ ≠ 0 := by
      simpa [v, norm_eq_zero] using hv
    set u : EuclideanSpace ℝ (Fin 2) := (‖v‖)⁻¹ • v
    have hu_norm : ‖u‖ ≤ 1 := by
      have : ‖u‖ = 1 := by
        calc
          ‖u‖ = ‖(‖v‖)⁻¹‖ * ‖v‖ := by simp [u, norm_smul]
          _ = |(‖v‖)⁻¹| * ‖v‖ := by simp
          _ = (‖v‖)⁻¹ * ‖v‖ := by
                have : 0 ≤ (‖v‖)⁻¹ := inv_nonneg.2 (norm_nonneg v)
                simp [abs_of_nonneg this]
          _ = 1 := by simp [hvnorm]
      simp [this]
    set x : EuclideanSpace ℝ (Fin 2) := c + u
    have hx_mem :
        x ∈ ({x : EuclideanSpace ℝ (Fin 2) | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)} : Set _) := by
      -- Use the norm characterization of `C₃`.
      have hx_sub : x - section14_C3_center = u := by
        simp [x, c, section14_C3_center, sub_eq_add_neg, add_assoc]
      have hxnorm : ‖x - section14_C3_center‖ ≤ 1 := by
        simpa [hx_sub] using hu_norm
      exact (section14_mem_C3_iff_norm_sub_le (x := x)).2 hxnorm
    have hx_le : φ x ≤ 1 := hle x hx_mem
    have hx_eq :
        φ x = φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖v‖ := by
      have hinter : inner ℝ u v = ‖v‖ := by
        calc
          inner ℝ u v = inner ℝ ((‖v‖)⁻¹ • v) v := by simp [u]
          _ = (‖v‖)⁻¹ * inner ℝ v v := by simp [inner_smul_left]
          _ = (‖v‖)⁻¹ * (‖v‖ ^ 2) := by simp
          _ = (‖v‖)⁻¹ * (‖v‖ * ‖v‖) := by simp [pow_two]
          _ = ((‖v‖)⁻¹ * ‖v‖) * ‖v‖ := by simp [mul_assoc]
          _ = ‖v‖ := by simp [hvnorm]
      calc
        φ x = φ (c + u) := by simp [x]
        _ = φ c + φ u := by simp [map_add]
        _ = φ (EuclideanSpace.single 0 (1 : ℝ)) + inner ℝ u v := by
              simp [c, section14_C3_center, v, section14_dual_apply_eq_inner_coeffVec]
        _ = φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖v‖ := by simp [hinter]
    -- Conclude the support-function bound.
    simpa [v] using (show φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖v‖ ≤ 1 by
      simpa [hx_eq] using hx_le)

/-- Text 14.0.14 (Example). Define
`C₃ = {x = (ξ₁, ξ₂) | (ξ₁ - 1)^2 + ξ₂^2 ≤ 1}`.
Then its polar can be described as
`C₃^∘ = {x★ = (ξ₁★, ξ₂★) | ξ₁★ + ‖(ξ₁★, ξ₂★)‖ ≤ 1}`.

In this file, `C^∘` is modeled as `polar (E := EuclideanSpace ℝ (Fin 2)) C :
Set (Module.Dual ℝ _)`, and we interpret the coordinates `ξ₁★, ξ₂★` of a functional `φ` as the
values `φ (EuclideanSpace.single 0 1)` and `φ (EuclideanSpace.single 1 1)`. -/
theorem polar_shiftedUnitDisk_eq :
    let C₃ : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | (x 0 - 1) ^ 2 + (x 1) ^ 2 ≤ (1 : ℝ)}
    polar (E := EuclideanSpace ℝ (Fin 2)) C₃ =
      {φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)) |
        φ (EuclideanSpace.single 0 (1 : ℝ)) + ‖section14_coeffVec φ‖ ≤ 1} := by
  classical
  -- Unfold the `let` and prove set equality by extensionality.
  ext φ
  constructor
  · intro hφ
    exact section14_support_bound_of_mem_polar_C3 (φ := φ) (by simpa using hφ)
  · intro hφ
    exact section14_mem_polar_C3_of_le_support_bound (φ := φ) hφ

/-- A concrete counterexample showing that, for the current definition of `C₄` and `P`,
the set `P` is not a subset of the polar `C₄^∘`. This indicates that `polar_C4_eq_convexHull`
cannot be proven as stated. -/
lemma section14_counterexample_P_not_subset_polar_C4 :
    let C₄ : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | x 0 ≤ 1 - Real.sqrt (1 + (x 1) ^ 2)}
    let P : Set (Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) :=
      {φ |
        Real.sqrt (1 + (φ (EuclideanSpace.single 1 (1 : ℝ))) ^ 2) ≤
          φ (EuclideanSpace.single 0 (1 : ℝ))}
    ¬ P ⊆ polar (E := EuclideanSpace ℝ (Fin 2)) C₄ := by
  classical
  intro C₄ P hP
  -- Take `t = 2`, the point `x = (1 - √(1+t^2), t) ∈ C₄`, and the functional with coordinates
  -- `(√(1+t^2), t) ∈ P`.
  let t : ℝ := 2
  let x : EuclideanSpace ℝ (Fin 2) :=
    EuclideanSpace.single 0 (1 - Real.sqrt (1 + t ^ 2)) + EuclideanSpace.single 1 t
  let φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)) :=
    (Real.sqrt (1 + t ^ 2)) •
        (PiLp.proj (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).toLinearMap +
      t • (PiLp.proj (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)).toLinearMap
  have hφP : φ ∈ P := by
    -- Unfold `P` and compute the two "coordinates" of `φ`.
    have hφ1 : φ (EuclideanSpace.single 1 (1 : ℝ)) = t := by
      simp [φ]
    have hφ0 : φ (EuclideanSpace.single 0 (1 : ℝ)) = Real.sqrt (1 + t ^ 2) := by
      simp [φ]
    -- The defining inequality is an equality for this `φ`.
    simp [P, hφ0, hφ1]
  have hxC : x ∈ C₄ := by
    -- Here we use the upper boundary of the hypograph, so the inequality holds by reflexivity.
    simp [C₄, x]
  have hφx_val : φ x = Real.sqrt (1 + t ^ 2) - 1 := by
    have hsqrt : 0 ≤ (1 + t ^ 2 : ℝ) := by nlinarith
    -- Expand the linear functional evaluation and simplify.
    simp [φ, x, sub_eq_add_neg]
    ring_nf
    simp [Real.sq_sqrt hsqrt]
    ring_nf
  have hφx_gt : (1 : ℝ) < φ x := by
    -- For `t = 2`, we have `φ x = √5 - 1 > 1`.
    have hsqrt5_gt2 : (2 : ℝ) < Real.sqrt 5 := by
      have h4lt5 : (4 : ℝ) < 5 := by norm_num
      have hsqrt : Real.sqrt (4 : ℝ) < Real.sqrt (5 : ℝ) := by
        exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) h4lt5
      have hsqrt4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by norm_num
      simpa [hsqrt4] using hsqrt
    have hEq : (1 + t ^ 2 : ℝ) = 5 := by norm_num [t]
    have hsqrt5_gt2' : (2 : ℝ) < Real.sqrt (1 + t ^ 2) := by
      simpa [hEq] using hsqrt5_gt2
    have hgt : (1 : ℝ) < Real.sqrt (1 + t ^ 2) - 1 := by linarith
    simpa [hφx_val] using hgt
  have hφpolar : φ ∈ polar (E := EuclideanSpace ℝ (Fin 2)) C₄ := hP hφP
  have hle : φ x ≤ 1 :=
    (mem_polar_iff (E := EuclideanSpace ℝ (Fin 2)) (C := C₄) (φ := φ)).1 hφpolar x hxC
  exact (not_lt_of_ge hle) hφx_gt

/-- The standard basis vector `e₀` in `ℝ²`. -/
noncomputable abbrev section14_e0 : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (1 : ℝ)

/-- The standard basis vector `e₁` in `ℝ²`. -/
noncomputable abbrev section14_e1 : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 1 (1 : ℝ)

/-- The set `C₄ = {(ξ₁, ξ₂) | ξ₁ ≤ 1 - √(1+ξ₂^2)}` from Text 14.0.15. -/
noncomputable def section14_C4 : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x 0 ≤ 1 - Real.sqrt (1 + (x 1) ^ 2)}

/-- The parabola region `P₄ = {(a,b) | b^2 + 1 ≤ 2a}` in the dual space. -/
noncomputable def section14_P4 : Set (Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {φ | (φ section14_e1) ^ 2 + 1 ≤ 2 * φ section14_e0}

/-- Coordinate expansion of a linear functional on `ℝ²`. -/
lemma section14_dual_apply_eq_two_coords
    (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) :
    φ x = x 0 * φ section14_e0 + x 1 * φ section14_e1 := by
  classical
  simpa [section14_e0, section14_e1, Fin.sum_univ_two, add_assoc, add_comm, add_left_comm] using
    (section14_dual_apply_eq_sum_mul_single (φ := φ) (x := x))

/-- The basic inequality `|t| ≤ √(1+t^2)`. -/
lemma section14_abs_le_sqrt_one_add_sq (t : ℝ) : |t| ≤ Real.sqrt (1 + t ^ 2) := by
  have hy : 0 ≤ (1 + t ^ 2 : ℝ) := by nlinarith
  have hsq : (|t|) ^ 2 ≤ (1 + t ^ 2 : ℝ) := by
    -- `|t|^2 = t^2 ≤ 1+t^2`.
    simp [sq_abs]
  exact (Real.le_sqrt (abs_nonneg t) hy).2 hsq

/-- A squaring identity gives the key inequality used in the `C₄` polar computation. -/
lemma section14_sqrt_mul_sub_ge_sqrt_sub {a b t : ℝ} (hb : |b| ≤ a) :
    Real.sqrt (a ^ 2 - b ^ 2) ≤ a * Real.sqrt (1 + t ^ 2) - b * t := by
  have ha : 0 ≤ a := le_trans (abs_nonneg b) hb
  have hb' : b * t ≤ a * Real.sqrt (1 + t ^ 2) := by
    calc
      b * t ≤ |b * t| := le_abs_self _
      _ = |b| * |t| := by simp [abs_mul]
      _ ≤ a * |t| := by gcongr
      _ ≤ a * Real.sqrt (1 + t ^ 2) := by
            gcongr
            exact section14_abs_le_sqrt_one_add_sq t
  have hy_nonneg : 0 ≤ a * Real.sqrt (1 + t ^ 2) - b * t := sub_nonneg.2 hb'
  have hs : 0 ≤ (1 + t ^ 2 : ℝ) := by nlinarith
  have hs_sq : (Real.sqrt (1 + t ^ 2)) ^ 2 = (1 + t ^ 2 : ℝ) := by
    simpa using Real.sq_sqrt hs
  have hidentity :
      (a * Real.sqrt (1 + t ^ 2) - b * t) ^ 2 =
        (a ^ 2 - b ^ 2) + (a * t - b * Real.sqrt (1 + t ^ 2)) ^ 2 := by
    ring_nf
    simp [hs_sq]
    ring_nf
  have hsq : a ^ 2 - b ^ 2 ≤ (a * Real.sqrt (1 + t ^ 2) - b * t) ^ 2 := by
    calc
      a ^ 2 - b ^ 2 ≤ (a ^ 2 - b ^ 2) + (a * t - b * Real.sqrt (1 + t ^ 2)) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = (a * Real.sqrt (1 + t ^ 2) - b * t) ^ 2 := by simpa using hidentity.symm
  exact (Real.sqrt_le_iff).2 ⟨hy_nonneg, hsq⟩

/-- The polar of any set is convex (as a subset of the dual). -/
lemma section14_convex_polar (C : Set E) : Convex ℝ (polar (E := E) C) := by
  intro φ₁ hφ₁ φ₂ hφ₂ a b ha hb hab
  refine (mem_polar_iff (E := E) (C := C) (φ := a • φ₁ + b • φ₂)).2 ?_
  intro x hx
  have h₁ := (mem_polar_iff (E := E) (C := C) (φ := φ₁)).1 hφ₁ x hx
  have h₂ := (mem_polar_iff (E := E) (C := C) (φ := φ₂)).1 hφ₂ x hx
  have h₁' : a * φ₁ x ≤ a * (1 : ℝ) := by
    simpa [mul_one] using (mul_le_mul_of_nonneg_left h₁ ha)
  have h₂' : b * φ₂ x ≤ b * (1 : ℝ) := by
    simpa [mul_one] using (mul_le_mul_of_nonneg_left h₂ hb)
  have hadd : a * φ₁ x + b * φ₂ x ≤ a + b := by
    simpa [mul_one, add_mul, mul_add, add_assoc, add_comm, add_left_comm] using add_le_add h₁' h₂'
  simpa [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab, add_assoc, add_comm,
    add_left_comm] using hadd.trans_eq (by simp [hab])

/-- The parabola region `P₄` is contained in the polar of `C₄`. -/
lemma section14_P4_subset_polar_C4 :
    section14_P4 ⊆ polar (E := EuclideanSpace ℝ (Fin 2)) section14_C4 := by
  classical
  intro φ hφ
  set a : ℝ := φ section14_e0
  set b : ℝ := φ section14_e1
  have ha : 0 ≤ a := by
    have : (b ^ 2 + 1 : ℝ) ≤ 2 * a := by simpa [section14_P4, a, b] using hφ
    nlinarith
  have hab : |b| ≤ a := by
    have hba : (b ^ 2 + 1 : ℝ) ≤ 2 * a := by simpa [section14_P4, a, b] using hφ
    have h2abs : (2 : ℝ) * |b| ≤ b ^ 2 + 1 := by
      have : 0 ≤ (|b| - 1) ^ 2 := sq_nonneg (|b| - 1)
      nlinarith [this, sq_abs b]
    linarith
  refine (mem_polar_iff (E := EuclideanSpace ℝ (Fin 2)) (C := section14_C4) (φ := φ)).2 ?_
  intro x hx
  have hx0 : x 0 ≤ 1 - Real.sqrt (1 + (x 1) ^ 2) := by simpa [section14_C4] using hx
  have hx0mul :
      x 0 * a ≤ (1 - Real.sqrt (1 + (x 1) ^ 2)) * a := by
    exact mul_le_mul_of_nonneg_right hx0 ha
  have hφx : φ x = x 0 * a + x 1 * b := by
    simpa [a, b] using (section14_dual_apply_eq_two_coords (φ := φ) (x := x))
  have hkey : a - Real.sqrt (a ^ 2 - b ^ 2) ≤ 1 := by
    have hba : (b ^ 2 + 1 : ℝ) ≤ 2 * a := by simpa [section14_P4, a, b] using hφ
    by_cases ha1 : a ≤ 1
    · have : a - Real.sqrt (a ^ 2 - b ^ 2) ≤ a := sub_le_self _ (Real.sqrt_nonneg _)
      exact this.trans ha1
    · have ha1' : 1 ≤ a := le_of_not_ge ha1
      have hsq : (a - 1) ^ 2 ≤ a ^ 2 - b ^ 2 := by nlinarith [hba]
      have hnonneg : 0 ≤ a ^ 2 - b ^ 2 := by
        have hb2 : b ^ 2 ≤ a ^ 2 := by
          have hab2 : |b| ^ 2 ≤ a ^ 2 := by
            have : |b| * |b| ≤ a * a := mul_le_mul hab hab (abs_nonneg b) ha
            simpa [pow_two] using this
          simpa [sq_abs] using hab2
        nlinarith
      have hle : a - 1 ≤ Real.sqrt (a ^ 2 - b ^ 2) := by
        have ha1nonneg : 0 ≤ a - 1 := sub_nonneg.2 ha1'
        exact (Real.le_sqrt ha1nonneg hnonneg).2 hsq
      linarith
  have hbound :
      (1 - Real.sqrt (1 + (x 1) ^ 2)) * a + x 1 * b ≤ 1 := by
    have hsqrt_le :
        Real.sqrt (a ^ 2 - b ^ 2) ≤ a * Real.sqrt (1 + (x 1) ^ 2) - b * (x 1) :=
      section14_sqrt_mul_sub_ge_sqrt_sub (a := a) (b := b) (t := x 1) hab
    have :
        (1 - Real.sqrt (1 + (x 1) ^ 2)) * a + x 1 * b ≤ a - Real.sqrt (a ^ 2 - b ^ 2) := by
      have hlin := sub_le_sub_left hsqrt_le a
      -- `ring` rewrites `a - (a*√(1+t^2) - b*t)` into `(1-√(1+t^2))*a + t*b`.
      -- (We keep it as `simp` + `ring` to avoid extra rewriting lemmas.)
      have :
          (1 - Real.sqrt (1 + (x 1) ^ 2)) * a + x 1 * b =
            a - (a * Real.sqrt (1 + (x 1) ^ 2) - b * (x 1)) := by
        ring
      -- Use the rewritten form of `hlin`.
      simpa [this] using hlin
    exact this.trans hkey
  calc
    φ x = x 0 * a + x 1 * b := hφx
    _ ≤ (1 - Real.sqrt (1 + (x 1) ^ 2)) * a + x 1 * b := by gcongr
    _ ≤ 1 := hbound

/-- The easy inclusion `conv(P₄ ∪ {0}) ⊆ C₄^∘`. -/
lemma section14_convexHull_P4_union_zero_subset_polar_C4 :
    convexHull ℝ (section14_P4 ∪ {0}) ⊆
      polar (E := EuclideanSpace ℝ (Fin 2)) section14_C4 := by
  have h0polar :
      (0 : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) ∈
        polar (E := EuclideanSpace ℝ (Fin 2)) section14_C4 := by
    refine (mem_polar_iff (E := EuclideanSpace ℝ (Fin 2)) (C := section14_C4) (φ := 0)).2 ?_
    intro x hx
    simp
  refine convexHull_min ?_ (section14_convex_polar (E := EuclideanSpace ℝ (Fin 2)) section14_C4)
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact section14_P4_subset_polar_C4 hφ
  · have : φ = (0 : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) := by simpa using hφ
    subst this
    simpa using h0polar

/-- A linear functional on `ℝ²` is determined by its values on the standard basis. -/
lemma section14_dual_eq_zero_of_apply_e0_e1_eq_zero
    (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)))
    (h0 : φ section14_e0 = 0) (h1 : φ section14_e1 = 0) :
    φ = 0 := by
  ext x
  have hx := section14_dual_apply_eq_two_coords (φ := φ) (x := x)
  simpa [h0, h1] using hx

/-- A convenient estimate: for `n ≥ 1`, `√(1+n^2) - n ≤ 1/n`. -/
lemma section14_sqrt_one_add_sq_sub_nat_le_inv_nat (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have hn' : (0 : ℕ) < n := lt_of_lt_of_le Nat.zero_lt_one hn
    exact_mod_cast hn'
  have hden_pos : 0 < Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ) := by
    have : 0 ≤ Real.sqrt (1 + (n : ℝ) ^ 2) := Real.sqrt_nonneg _
    linarith
  have hrat :
      Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ) =
        1 / (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) := by
    have hx0 : 0 ≤ (1 + (n : ℝ) ^ 2 : ℝ) := by nlinarith
    have hmul :
        (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) *
            (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) = 1 := by
      -- Rationalization: `(√u - n)(√u + n) = u - n^2 = 1`.
      have hsq :
          Real.sqrt (1 + (n : ℝ) ^ 2) * Real.sqrt (1 + (n : ℝ) ^ 2) =
            (1 + (n : ℝ) ^ 2 : ℝ) := by
        simpa using (Real.mul_self_sqrt hx0)
      calc
        (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) *
              (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ))
            = Real.sqrt (1 + (n : ℝ) ^ 2) * Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ) ^ 2 := by
                ring
        _ = (1 + (n : ℝ) ^ 2 : ℝ) - (n : ℝ) ^ 2 := by simp [hsq]
        _ = 1 := by ring
    calc
      Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)
          = ((Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) *
              (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ))) /
              (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) := by
              field_simp [ne_of_gt hden_pos]
      _ = 1 / (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) := by simp [hmul]
  have hn_le_den : (n : ℝ) ≤ Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ) :=
    le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hden_inv_le : (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ))⁻¹ ≤ (n : ℝ)⁻¹ :=
    inv_anti₀ hn0 hn_le_den
  -- Convert `inv`-bounds back to `/`.
  simpa [one_div, hrat] using hden_inv_le

/-- For `0 ≤ a` and `b^2 < a^2`, the choice `t = b / √(a^2-b^2)` attains the minimum in the
expression `a * √(1+t^2) - b * t`. -/
lemma section14_eval_opt_t {a b : ℝ} (ha : 0 ≤ a) (hba : b ^ 2 < a ^ 2) :
    let t : ℝ := b / Real.sqrt (a ^ 2 - b ^ 2)
    a * Real.sqrt (1 + t ^ 2) - b * t = Real.sqrt (a ^ 2 - b ^ 2) := by
  classical
  dsimp
  set D : ℝ := a ^ 2 - b ^ 2
  have hDpos : 0 < D := by
    have : b ^ 2 < a ^ 2 := hba
    simpa [D] using sub_pos.2 this
  have hD0 : 0 ≤ D := le_of_lt hDpos
  set s : ℝ := Real.sqrt D with hs
  have hspos : 0 < s := by simpa [hs] using (Real.sqrt_pos.2 hDpos)
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs_sq : s ^ 2 = D := by simpa [hs] using (Real.sq_sqrt hD0)
  have hsD : Real.sqrt (a ^ 2 - b ^ 2) = s := by simpa [D] using hs.symm
  set t : ℝ := b / s
  have ht : b / Real.sqrt (a ^ 2 - b ^ 2) = t := by
    calc
      b / Real.sqrt (a ^ 2 - b ^ 2) = b / s := by simp [hsD]
      _ = t := by simp [t]
  have hsqrt :
      Real.sqrt (1 + t ^ 2) = a / s := by
    have hx : 0 ≤ (1 + t ^ 2 : ℝ) := by nlinarith
    have hy : 0 ≤ a / s := div_nonneg ha (le_of_lt hspos)
    refine (Real.sqrt_eq_iff_mul_self_eq hx hy).2 ?_
    -- Clear denominators; this reduces to `s^2 + b^2 = a^2`.
    have : (1 + t ^ 2 : ℝ) = (a / s) * (a / s) := by
      simp [t]
      field_simp [hsne]
      -- After clearing denominators, use `s^2 = a^2 - b^2`.
      nlinarith [hs_sq]
    simpa using this
  have hcalc : a * Real.sqrt (1 + t ^ 2) - b * t = s := by
    calc
      a * Real.sqrt (1 + t ^ 2) - b * t
          = a * (a / s) - b * (b / s) := by simp [t, hsqrt]
      _ = (a ^ 2 - b ^ 2) / s := by
            field_simp [hsne]
      _ = D / s := by simp [D]
      _ = s := by
            have : D = s ^ 2 := hs_sq.symm
            simp [this, pow_two, hsne]
  simpa [ht, hsD] using hcalc

/-- Membership in the polar of `C₄` forces the coordinate constraints needed for the description
via `P₄`. -/
lemma section14_mem_polar_C4_coord_consequences
    {φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))}
    (hφ : φ ∈ polar (E := EuclideanSpace ℝ (Fin 2)) section14_C4) :
    0 ≤ φ section14_e0 ∧
      |φ section14_e1| ≤ φ section14_e0 ∧
        (1 ≤ φ section14_e0 → (φ section14_e1) ^ 2 + 1 ≤ 2 * φ section14_e0) := by
  set a : ℝ := φ section14_e0
  set b : ℝ := φ section14_e1
  have hle : ∀ x, x ∈ section14_C4 → φ x ≤ 1 :=
    (mem_polar_iff (E := EuclideanSpace ℝ (Fin 2)) (C := section14_C4) (φ := φ)).1 hφ
  have ha : 0 ≤ a := by
    -- Test points `(-n,0) ∈ C₄` to force `a ≥ 0`.
    have hbound : ∀ n : ℕ, (n : ℝ) * (-a) ≤ 1 := by
      intro n
      let x : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (-(n : ℝ))
      have hx : x ∈ section14_C4 := by
        -- `x 0 = -n ≤ 0 = 1 - √(1+0)`.
        simp [section14_C4, x]
      have hxle : φ x ≤ 1 := hle x hx
      have hxval : φ x = (n : ℝ) * (-a) := by
        -- Expand `φ x` in coordinates (avoid `simp` loops on coordinate expansions).
        have hxval' := section14_dual_apply_eq_two_coords (φ := φ) (x := x)
        simpa [x, a, section14_e0, section14_e1, mul_assoc, mul_left_comm, mul_comm] using hxval'
      simpa [hxval] using hxle
    have : (-a) ≤ 0 := section14_real_nonpos_of_nat_mul_le (-a) 1 hbound
    linarith
  have hb_le_a : b ≤ a := by
    -- Use points `(1-√(1+n^2), n) ∈ C₄`.
    have hbound : ∀ n : ℕ, (n : ℝ) * (b - a) ≤ 1 := by
      intro n
      let t : ℝ := (n : ℝ)
      let x : EuclideanSpace ℝ (Fin 2) :=
        EuclideanSpace.single 0 (1 - Real.sqrt (1 + t ^ 2)) + EuclideanSpace.single 1 t
      have hx : x ∈ section14_C4 := by simp [section14_C4, x]
      have hxle : φ x ≤ 1 := hle x hx
      have hxval : φ x = (1 - Real.sqrt (1 + t ^ 2)) * a + t * b := by
        simpa [a, b, x] using (section14_dual_apply_eq_two_coords (φ := φ) (x := x))
      -- Use `1 - √(1+t^2) ≥ -t` (since `√(1+t^2) ≤ t+1`) to lower-bound `φ x`.
      have ht0 : 0 ≤ t := by simp [t]
      have hsqrt_le : Real.sqrt (1 + t ^ 2) ≤ t + 1 := by
        have hpos : 0 ≤ t + 1 := by linarith
        have hsq : (1 + t ^ 2 : ℝ) ≤ (t + 1) ^ 2 := by nlinarith
        exact (Real.sqrt_le_iff).2 ⟨hpos, hsq⟩
      have h1 : (-t) ≤ 1 - Real.sqrt (1 + t ^ 2) := by linarith
      have hmul : (-t) * a ≤ (1 - Real.sqrt (1 + t ^ 2)) * a :=
        mul_le_mul_of_nonneg_right h1 ha
      have hlin : t * (b - a) ≤ (1 - Real.sqrt (1 + t ^ 2)) * a + t * b := by
        calc
          t * (b - a) = (-t) * a + t * b := by ring
          _ ≤ (1 - Real.sqrt (1 + t ^ 2)) * a + t * b := by
                have h := add_le_add_right hmul (t * b)
                simpa [add_assoc, add_left_comm, add_comm] using h
      have hxle' : (1 - Real.sqrt (1 + t ^ 2)) * a + t * b ≤ 1 := by
        simpa [hxval] using hxle
      simpa [t] using (hlin.trans hxle')
    have : b - a ≤ 0 := section14_real_nonpos_of_nat_mul_le (b - a) 1 hbound
    linarith
  have hb_ge_neg_a : -a ≤ b := by
    -- Use points `(1-√(1+n^2), -n) ∈ C₄`.
    have hbound : ∀ n : ℕ, (n : ℝ) * (-b - a) ≤ 1 := by
      intro n
      let t : ℝ := (n : ℝ)
      let x : EuclideanSpace ℝ (Fin 2) :=
        EuclideanSpace.single 0 (1 - Real.sqrt (1 + t ^ 2)) + EuclideanSpace.single 1 (-t)
      have hx : x ∈ section14_C4 := by simp [section14_C4, x]
      have hxle : φ x ≤ 1 := hle x hx
      have hxval : φ x = (1 - Real.sqrt (1 + t ^ 2)) * a + (-t) * b := by
        simpa [a, b, x] using (section14_dual_apply_eq_two_coords (φ := φ) (x := x))
      have ht0 : 0 ≤ t := by simp [t]
      have hsqrt_le : Real.sqrt (1 + t ^ 2) ≤ t + 1 := by
        have hpos : 0 ≤ t + 1 := by linarith
        have hsq : (1 + t ^ 2 : ℝ) ≤ (t + 1) ^ 2 := by nlinarith
        exact (Real.sqrt_le_iff).2 ⟨hpos, hsq⟩
      have h1 : (-t) ≤ 1 - Real.sqrt (1 + t ^ 2) := by linarith
      have hmul : (-t) * a ≤ (1 - Real.sqrt (1 + t ^ 2)) * a :=
        mul_le_mul_of_nonneg_right h1 ha
      have hlin : t * (-b - a) ≤ (1 - Real.sqrt (1 + t ^ 2)) * a + (-t) * b := by
        calc
          t * (-b - a) = (-t) * a + (-t) * b := by ring
          _ ≤ (1 - Real.sqrt (1 + t ^ 2)) * a + (-t) * b := by
                have h := add_le_add_right hmul ((-t) * b)
                simpa [add_assoc, add_left_comm, add_comm] using h
      have hxle' : (1 - Real.sqrt (1 + t ^ 2)) * a + (-t) * b ≤ 1 := by
        simpa [hxval] using hxle
      simpa [t] using (hlin.trans hxle')
    have : -b - a ≤ 0 := section14_real_nonpos_of_nat_mul_le (-b - a) 1 hbound
    linarith
  have habs : |b| ≤ a := abs_le.2 ⟨hb_ge_neg_a, hb_le_a⟩
  refine ⟨by simpa [a] using ha, by simpa [a, b] using habs, ?_⟩
  intro ha1
  have hb2le : b ^ 2 ≤ a ^ 2 := by
    have habs_mul : |b| * |b| ≤ a * a := mul_le_mul habs habs (abs_nonneg _) ha
    simpa [pow_two, sq_abs] using habs_mul
  by_cases hEq : b ^ 2 = a ^ 2
  · -- Degenerate case `|b| = a`: use a discrete approximation to force `a = 1`.
    have hbpm : b = a ∨ b = -a := by
      have := sq_eq_sq_iff_eq_or_eq_neg.1 (by simpa [pow_two] using hEq)
      simpa [pow_two] using this
    have hbound : ∀ n : ℕ, (n : ℝ) * (a - 1) ≤ a := by
      intro n
      cases n with
      | zero =>
          simpa using (show (0 : ℝ) ≤ a from ha)
      | succ n =>
          have hn' : (1 : ℕ) ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
          have hn0 : (0 : ℝ) < (Nat.succ n : ℝ) := by
            exact_mod_cast (Nat.succ_pos n)
          -- Use the polar inequality on the boundary point with `t = n` or `t = -n`.
          have hstep :
              a - 1 ≤ a * (Real.sqrt (1 + (Nat.succ n : ℝ) ^ 2) - (Nat.succ n : ℝ)) := by
            rcases hbpm with hb | hb
            · -- `b = a`, take `t = n`.
              let t : ℝ := (Nat.succ n : ℝ)
              let x : EuclideanSpace ℝ (Fin 2) :=
                EuclideanSpace.single 0 (1 - Real.sqrt (1 + t ^ 2)) + EuclideanSpace.single 1 t
              have hx : x ∈ section14_C4 := by simp [section14_C4, x]
              have hxle : φ x ≤ 1 := hle x hx
              have hxval : φ x = (1 - Real.sqrt (1 + t ^ 2)) * a + t * b := by
                simpa [a, b, x] using (section14_dual_apply_eq_two_coords (φ := φ) (x := x))
              have hxle' : (1 - Real.sqrt (1 + t ^ 2)) * a + t * b ≤ 1 := by
                simpa [hxval] using hxle
              have : a - 1 ≤ a * Real.sqrt (1 + t ^ 2) - b * t := by linarith
              simpa [hb, t, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using this
            · -- `b = -a`, take `t = -n`.
              let t : ℝ := (Nat.succ n : ℝ)
              let x : EuclideanSpace ℝ (Fin 2) :=
                EuclideanSpace.single 0 (1 - Real.sqrt (1 + t ^ 2)) + EuclideanSpace.single 1 (-t)
              have hx : x ∈ section14_C4 := by simp [section14_C4, x]
              have hxle : φ x ≤ 1 := hle x hx
              have hxval : φ x = (1 - Real.sqrt (1 + t ^ 2)) * a + (-t) * b := by
                simpa [a, b, x] using (section14_dual_apply_eq_two_coords (φ := φ) (x := x))
              have hxle' : (1 - Real.sqrt (1 + t ^ 2)) * a + (-t) * b ≤ 1 := by
                simpa [hxval] using hxle
              have : a - 1 ≤ a * Real.sqrt (1 + t ^ 2) - b * (-t) := by linarith
              simpa [hb, t, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using this
          have hsqrt_sub_le :
              Real.sqrt (1 + (Nat.succ n : ℝ) ^ 2) - (Nat.succ n : ℝ) ≤
                1 / (Nat.succ n : ℝ) :=
            section14_sqrt_one_add_sq_sub_nat_le_inv_nat (n := Nat.succ n) hn'
          have hmul_le_one :
              (Nat.succ n : ℝ) *
                  (Real.sqrt (1 + (Nat.succ n : ℝ) ^ 2) - (Nat.succ n : ℝ)) ≤ 1 := by
            have hn0' : (0 : ℝ) < (n : ℝ) + 1 := by simpa [Nat.cast_succ] using hn0
            have hn0ne' : (n : ℝ) + 1 ≠ 0 := ne_of_gt hn0'
            have := mul_le_mul_of_nonneg_left hsqrt_sub_le (le_of_lt hn0)
            simpa [one_div, Nat.cast_succ, hn0ne'] using this
          have hmul :
              (Nat.succ n : ℝ) * (a - 1) ≤ a * ((Nat.succ n : ℝ) *
                (Real.sqrt (1 + (Nat.succ n : ℝ) ^ 2) - (Nat.succ n : ℝ))) := by
            have hmul' := mul_le_mul_of_nonneg_left hstep (le_of_lt hn0)
            -- Reassociate to match `a * (n * ...)`.
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
          have : (Nat.succ n : ℝ) * (a - 1) ≤ a := by
            have := (mul_le_mul_of_nonneg_left hmul_le_one ha)
            -- `a * (n*(...)) ≤ a`.
            have hA : a * ((Nat.succ n : ℝ) *
                (Real.sqrt (1 + (Nat.succ n : ℝ) ^ 2) - (Nat.succ n : ℝ))) ≤ a := by
              simpa [mul_one] using this
            exact hmul.trans hA
          simpa using this
    have ha_le_one : a ≤ 1 := by
      have : a - 1 ≤ 0 := section14_real_nonpos_of_nat_mul_le (a - 1) a hbound
      linarith
    have ha_eq_one : a = 1 := le_antisymm ha_le_one ha1
    -- Conclude `b^2 + 1 ≤ 2a` from `a=1` and `b^2=a^2`.
    have hb2 : b ^ 2 = 1 := by simpa [ha_eq_one] using hEq
    nlinarith [ha_eq_one, hb2]
  · -- Strict case: choose `t = b / √(a^2-b^2)` and compute the sharp bound.
    have hlt : b ^ 2 < a ^ 2 := lt_of_le_of_ne hb2le hEq
    have hDpos : 0 < a ^ 2 - b ^ 2 := sub_pos.2 hlt
    let t : ℝ := b / Real.sqrt (a ^ 2 - b ^ 2)
    let x : EuclideanSpace ℝ (Fin 2) :=
      EuclideanSpace.single 0 (1 - Real.sqrt (1 + t ^ 2)) + EuclideanSpace.single 1 t
    have hx : x ∈ section14_C4 := by simp [section14_C4, x]
    have hxle : φ x ≤ 1 := hle x hx
    have hxval : φ x = (1 - Real.sqrt (1 + t ^ 2)) * a + t * b := by
      simpa [a, b, x] using (section14_dual_apply_eq_two_coords (φ := φ) (x := x))
    have hxle' : (1 - Real.sqrt (1 + t ^ 2)) * a + t * b ≤ 1 := by
      simpa [hxval] using hxle
    have hmain : a - 1 ≤ Real.sqrt (a ^ 2 - b ^ 2) := by
      have : a - 1 ≤ a * Real.sqrt (1 + t ^ 2) - b * t := by linarith
      have htval :
          a * Real.sqrt (1 + t ^ 2) - b * t = Real.sqrt (a ^ 2 - b ^ 2) := by
        simpa [t] using (section14_eval_opt_t (a := a) (b := b) ha hlt)
      simpa [htval] using this
    have hsq : (a - 1) ^ 2 ≤ a ^ 2 - b ^ 2 := by
      have hnonneg : 0 ≤ a ^ 2 - b ^ 2 := le_of_lt hDpos
      have ha1nonneg : 0 ≤ a - 1 := sub_nonneg.2 ha1
      exact (Real.le_sqrt ha1nonneg hnonneg).1 hmain
    nlinarith

/-- The hard inclusion `C₄^∘ ⊆ conv(P₄ ∪ {0})` (to be proven). -/
lemma section14_polar_C4_subset_convexHull_P4_union_zero :
    polar (E := EuclideanSpace ℝ (Fin 2)) section14_C4 ⊆ convexHull ℝ (section14_P4 ∪ {0}) := by
  intro φ hφ
  have hcoord := section14_mem_polar_C4_coord_consequences (φ := φ) hφ
  have ha0 : 0 ≤ φ section14_e0 := hcoord.1
  have habs : |φ section14_e1| ≤ φ section14_e0 := hcoord.2.1
  by_cases ha : φ section14_e0 = 0
  · have hb0 : φ section14_e1 = 0 := by
      have : |φ section14_e1| ≤ 0 := by simpa [ha] using habs
      exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))
    have hφ0 : φ = 0 :=
      section14_dual_eq_zero_of_apply_e0_e1_eq_zero (φ := φ) ha hb0
    subst hφ0
    exact (subset_convexHull ℝ (section14_P4 ∪ {0})) (by simp)
  · have ha_pos : 0 < φ section14_e0 := lt_of_le_of_ne ha0 (Ne.symm ha)
    by_cases ha1 : φ section14_e0 ≤ 1
    · -- Rescale to land in `P₄`, then use convexity of the convex hull.
      let s : ℝ := φ section14_e0
      let ψ : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)) := (1 / s) • φ
      have hs0 : 0 ≤ s := ha0
      have hs1 : s ≤ 1 := ha1
      have hsne : s ≠ 0 := by simpa [s] using ha
      have hψ0 : ψ section14_e0 = 1 := by
        simp [ψ, s, section14_e0, LinearMap.smul_apply, smul_eq_mul, hsne]
      have hψ1_abs : |ψ section14_e1| ≤ 1 := by
        have hspos : 0 < s := by simpa [s] using ha_pos
        have hs0 : 0 ≤ s := le_of_lt hspos
        have hinv_nonneg : 0 ≤ (1 / s) := one_div_nonneg.2 hs0
        have habs_s : |φ section14_e1| ≤ s := by simpa [s] using habs
        have hmul := mul_le_mul_of_nonneg_left habs_s hinv_nonneg
        have hmul' : (1 / s) * |φ section14_e1| ≤ 1 := by
          simpa [one_div, hspos.ne', mul_assoc] using hmul
        have habsψ : |ψ section14_e1| = (1 / s) * |φ section14_e1| := by
          have hψ :
              ψ section14_e1 = (1 / s) * φ section14_e1 := by
            simp [ψ, LinearMap.smul_apply, smul_eq_mul]
          calc
            |ψ section14_e1| = |(1 / s) * φ section14_e1| := by simp [hψ]
            _ = |(1 / s)| * |φ section14_e1| := by simp [abs_mul]
            _ = (1 / s) * |φ section14_e1| := by
                  have habs_inv : |(1 / s)| = (1 / s) := abs_of_nonneg hinv_nonneg
                  rw [habs_inv]
        simpa [habsψ] using hmul'
      have hψP : ψ ∈ section14_P4 := by
        have hsq : (ψ section14_e1) ^ 2 ≤ 1 := by
          have habs' : |ψ section14_e1| ≤ |(1 : ℝ)| := by simpa using hψ1_abs
          have := (sq_le_sq).2 habs'
          simpa [pow_two] using this
        have : (ψ section14_e1) ^ 2 + 1 ≤ 2 * ψ section14_e0 := by
          -- Here `ψ e0 = 1`.
          nlinarith [hsq, hψ0]
        simpa [section14_P4] using this
      have h0mem :
          (0 : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) ∈
            convexHull ℝ (section14_P4 ∪ {0}) :=
        (subset_convexHull ℝ (section14_P4 ∪ {0})) (by simp)
      have hψmem : ψ ∈ convexHull ℝ (section14_P4 ∪ {0}) :=
        (subset_convexHull ℝ (section14_P4 ∪ {0})) (by
          left; exact hψP)
      have hconv :
          Convex ℝ (convexHull ℝ (section14_P4 ∪ {0})) :=
        convex_convexHull ℝ (section14_P4 ∪ {0})
      have hcomb :
          s • ψ + (1 - s) • (0 : Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) ∈
            convexHull ℝ (section14_P4 ∪ {0}) :=
        hconv hψmem h0mem hs0 (by nlinarith) (by nlinarith)
      have hφ_eq : s • ψ = φ := by
        simp [ψ, s, hsne, smul_smul]
      have hcomb' : s • ψ ∈ convexHull ℝ (section14_P4 ∪ {0}) := by
        simpa using hcomb
      simpa [hφ_eq] using hcomb'
    · -- If `1 ≤ a`, then `φ ∈ P₄`.
      have ha1' : 1 ≤ φ section14_e0 := le_of_not_ge ha1
      have hP : (φ section14_e1) ^ 2 + 1 ≤ 2 * φ section14_e0 := hcoord.2.2 ha1'
      have : φ ∈ section14_P4 := by simpa [section14_P4] using hP
      exact (subset_convexHull ℝ (section14_P4 ∪ {0})) (by left; exact this)

/-- Text 14.0.15 (Example). Define
`C₄ = {x = (ξ₁, ξ₂) | ξ₁ ≤ 1 - (1 + ξ₂^2)^{1/2}}`.
Then its polar can be written as
`C₄^∘ = conv(P ∪ {0})`, where
`P = {x★ = (ξ₁★, ξ₂★) | ξ₁★ ≥ (1 + (ξ₂★)^2)^{1/2}}`.

Note: the set `P` above (a "sqrt cone") is not contained in the polar for the current definition
of `polar` (via Fenchel conjugates), as shown by `section14_counterexample_P_not_subset_polar_C4`.
The correct description of `C₄^∘` in this formalization uses instead the parabola region
`P₄ = {x★ = (a,b) | b^2 + 1 ≤ 2a}`, which is the closed convex hull of all supporting halfspaces
through the origin.

In this file, `C^∘` is modeled as `polar (E := EuclideanSpace ℝ (Fin 2)) C :
Set (Module.Dual ℝ _)`, and we interpret the coordinates `ξ₁★, ξ₂★` of a functional `φ` as the
values `φ (EuclideanSpace.single 0 1)` and `φ (EuclideanSpace.single 1 1)`. -/
theorem polar_C4_eq_convexHull :
    let C₄ : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | x 0 ≤ 1 - Real.sqrt (1 + (x 1) ^ 2)}
    let P₄ : Set (Module.Dual ℝ (EuclideanSpace ℝ (Fin 2))) :=
      {φ |
        (φ (EuclideanSpace.single 1 (1 : ℝ))) ^ 2 + 1 ≤
          2 * φ (EuclideanSpace.single 0 (1 : ℝ))}
    polar (E := EuclideanSpace ℝ (Fin 2)) C₄ = convexHull ℝ (P₄ ∪ {0}) := by
  classical
  have h :
      polar (E := EuclideanSpace ℝ (Fin 2)) section14_C4 =
        convexHull ℝ (section14_P4 ∪ {0}) := by
    exact Set.Subset.antisymm
      section14_polar_C4_subset_convexHull_P4_union_zero
      section14_convexHull_P4_union_zero_subset_polar_C4
  simpa [section14_C4, section14_P4, section14_e0, section14_e1] using h
  /-
  (Proof sketch omitted.)
  -/

end Section14
end Chap03
