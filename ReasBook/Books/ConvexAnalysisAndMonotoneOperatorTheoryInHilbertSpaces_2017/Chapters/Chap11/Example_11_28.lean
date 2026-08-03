import Mathlib
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

namespace ERealFunction

/-- The `Γ₀`-valued representative of the alternating-minimization counterexample. -/
noncomputable def example11_28Function : (ℝ × ℝ) → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if h : 0 ≤ x.1 ∧ 0 ≤ x.2 then
      ⟨((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal), EReal.bot_lt_coe _⟩
    else
      ⟨⊤, by simp⟩

/-- Coercing the `Γ₀`-valued representative back to `EReal` recovers the explicit formula. -/
@[simp] theorem example11_28Function_apply (x : ℝ × ℝ) :
    (example11_28Function x : EReal) =
      if 0 ≤ x.1 ∧ 0 ≤ x.2 then
        ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal)
      else
        ⊤ := by
  by_cases h : 0 ≤ x.1 ∧ 0 ≤ x.2 <;> simp [example11_28Function, h]

/-- The first coordinate update in Example 11.28: minimize the slice `ξ₁ ↦ f (ξ₁, ξ₂)` while
keeping the second coordinate fixed. -/
def example11_28MinimizeFirst (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, x.2)

/-- The second coordinate update in Example 11.28: minimize the slice `ξ₂ ↦ f (ξ₁, ξ₂)` while
keeping the first coordinate fixed. -/
def example11_28MinimizeSecond (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1, x.1)

/-- One alternating-minimization cycle in Example 11.28 consists of the first-coordinate update
followed by the second-coordinate update. -/
def example11_28AlternatingMinimizationStep (x : ℝ × ℝ) : ℝ × ℝ :=
  example11_28MinimizeSecond (example11_28MinimizeFirst x)

/-- Iterating the alternating-minimization cycle from the initial point `x0`. -/
def example11_28Recurrence (x0 : ℝ × ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (example11_28AlternatingMinimizationStep^[n]) x0

local notation "f" => example11_28Function.asEReal

/-- Helper for Example 11 28: every affine function on `ℝ × ℝ`, viewed in `EReal`, belongs to
`Γ(ℝ × ℝ)`. -/
theorem affine_pair_mem_gamma (a b c : ℝ) :
    (fun x : ℝ × ℝ ↦ ((a * x.1 + b * x.2 + c : ℝ) : EReal)) ∈ Γ(ℝ × ℝ) := by
  rw [mem_gamma_iff]
  constructor
  · intro x y α _hα0 _hα1
    -- Affine functions satisfy Jensen's inequality with equality.
    have hformula :
        a * (α * x.1 + (1 - α) * y.1) + b * (α * x.2 + (1 - α) * y.2) + c =
          α * (a * x.1 + b * x.2 + c) + (1 - α) * (a * y.1 + b * y.2 + c) := by
      ring
    have hformulaE :
        (((a * (α * x.1 + (1 - α) * y.1) + b * (α * x.2 + (1 - α) * y.2) + c : ℝ) : EReal)) =
          (α : EReal) * (((a * x.1 + b * x.2 + c : ℝ) : EReal)) +
            (1 - α : EReal) * (((a * y.1 + b * y.2 + c : ℝ) : EReal)) := by
      rw [show (1 - (α : EReal)) = (((1 - α : ℝ) : EReal)) by norm_num,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hformula
    -- Rewrite both sides to the same finite real expression.
    simpa [smul_eq_mul] using le_of_eq hformulaE
  · -- The affine map is continuous, hence lower semicontinuous after coercion to `EReal`.
    have hcont1 : Continuous fun x : ℝ × ℝ ↦ a * x.1 := by
      simpa using (continuous_const.mul continuous_fst)
    have hcont2 : Continuous fun x : ℝ × ℝ ↦ b * x.2 := by
      simpa using (continuous_const.mul continuous_snd)
    have hcont : Continuous fun x : ℝ × ℝ ↦ a * x.1 + b * x.2 + c := by
      simpa [add_assoc] using hcont1.add (hcont2.add continuous_const)
    simpa [Function.comp] using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-- Helper for Example 11 28: the maximum of the two affine branches is a member of
`Γ₀(ℝ × ℝ)`. -/
theorem example11_28_max_affine_mem_gammaZero :
    (fun x : ℝ × ℝ ↦ max (2 * x.1 - x.2) (2 * x.2 - x.1)).toEReal ∈ Γ₀(ℝ × ℝ) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  let g : Bool → (ℝ × ℝ) → EReal :=
    fun i x ↦ if i then ((2 * x.1 - x.2 : ℝ) : EReal) else ((2 * x.2 - x.1 : ℝ) : EReal)
  have hg : ∀ i, g i ∈ Γ(ℝ × ℝ) := by
    intro i
    by_cases hi : i
    · subst hi
      simpa [g] using affine_pair_mem_gamma 2 (-1) 0
    · simpa [g, hi, sub_eq_add_neg, add_comm] using affine_pair_mem_gamma (-1) 2 0
  have hs : (fun x : ℝ × ℝ ↦ ⨆ i, g i x) ∈ Γ(ℝ × ℝ) :=
    iSup_mem_gamma g hg
  -- The supremum over the two affine branches is the pointwise maximum.
  convert hs using 1
  ext x
  have hbool : (⨆ i : Bool, g i x) = g true x ⊔ g false x := iSup_bool_eq
  have hg_true : g true x = (((2 * x.1 - x.2 : ℝ) : EReal)) := by
    simp [g]
  have hg_false : g false x = (((2 * x.2 - x.1 : ℝ) : EReal)) := by
    simp [g]
  rw [hbool, hg_true, hg_false]
  by_cases h12 : 2 * x.1 - x.2 ≤ 2 * x.2 - x.1
  · have h12E :
        (((2 * x.1 - x.2 : ℝ) : EReal)) ≤ (((2 * x.2 - x.1 : ℝ) : EReal)) := by
      exact_mod_cast h12
    rw [max_eq_right h12, sup_eq_right.mpr h12E]
  · have h21 : 2 * x.2 - x.1 ≤ 2 * x.1 - x.2 := le_of_not_ge h12
    have h21E :
        (((2 * x.2 - x.1 : ℝ) : EReal)) ≤ (((2 * x.1 - x.2 : ℝ) : EReal)) := by
      exact_mod_cast h21
    rw [max_eq_left h21, sup_eq_left.mpr h21E]

/-- Helper for Example 11 28: the effective domain is exactly the positive orthant. -/
theorem example11_28_effectiveDomain :
    effectiveDomain example11_28Function = Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases h : 0 ≤ x.1 ∧ 0 ≤ x.2
    · simpa [Set.mem_prod] using h
    · simp [effectiveDomain, example11_28Function_apply, h] at hx
  · intro hx
    have h : 0 ≤ x.1 ∧ 0 ≤ x.2 := by
      simpa [Set.mem_prod] using hx
    simp [effectiveDomain, example11_28Function_apply, h]

/-- Helper for Example 11 28: each coordinate is bounded above by the function value. -/
theorem example11_28_coordinate_lower_bounds (x : ℝ × ℝ) :
    ((x.1 : ℝ) : EReal) ≤ f x ∧ ((x.2 : ℝ) : EReal) ≤ f x := by
  by_cases h : 0 ≤ x.1 ∧ 0 ≤ x.2
  · -- Inside the orthant, compare each coordinate to one branch of the maximum.
    constructor
    · by_cases h12 : x.1 ≤ x.2
      · have hx1 : x.1 ≤ 2 * x.2 - x.1 := by
          linarith
        have hx1E : ((x.1 : ℝ) : EReal) ≤ ((2 * x.2 - x.1 : ℝ) : EReal) := by
          exact_mod_cast hx1
        have hmaxE :
            ((2 * x.2 - x.1 : ℝ) : EReal) ≤
              ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) := by
          exact_mod_cast (le_max_right (2 * x.1 - x.2) (2 * x.2 - x.1))
        have hmax : ((x.1 : ℝ) : EReal) ≤ ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) :=
          le_trans hx1E hmaxE
        simpa [example11_28Function_apply, h] using hmax
      · have h21 : x.2 ≤ x.1 := le_of_not_ge h12
        have hx1 : x.1 ≤ 2 * x.1 - x.2 := by
          linarith
        have hx1E : ((x.1 : ℝ) : EReal) ≤ ((2 * x.1 - x.2 : ℝ) : EReal) := by
          exact_mod_cast hx1
        have hmaxE :
            ((2 * x.1 - x.2 : ℝ) : EReal) ≤
              ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) := by
          exact_mod_cast (le_max_left (2 * x.1 - x.2) (2 * x.2 - x.1))
        have hmax : ((x.1 : ℝ) : EReal) ≤ ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) :=
          le_trans hx1E hmaxE
        simpa [example11_28Function_apply, h] using hmax
    · by_cases h21 : x.2 ≤ x.1
      · have hx2 : x.2 ≤ 2 * x.1 - x.2 := by
          linarith
        have hx2E : ((x.2 : ℝ) : EReal) ≤ ((2 * x.1 - x.2 : ℝ) : EReal) := by
          exact_mod_cast hx2
        have hmaxE :
            ((2 * x.1 - x.2 : ℝ) : EReal) ≤
              ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) := by
          exact_mod_cast (le_max_left (2 * x.1 - x.2) (2 * x.2 - x.1))
        have hmax : ((x.2 : ℝ) : EReal) ≤ ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) :=
          le_trans hx2E hmaxE
        simpa [example11_28Function_apply, h] using hmax
      · have h12 : x.1 ≤ x.2 := le_of_not_ge h21
        have hx2 : x.2 ≤ 2 * x.2 - x.1 := by
          linarith
        have hx2E : ((x.2 : ℝ) : EReal) ≤ ((2 * x.2 - x.1 : ℝ) : EReal) := by
          exact_mod_cast hx2
        have hmaxE :
            ((2 * x.2 - x.1 : ℝ) : EReal) ≤
              ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) := by
          exact_mod_cast (le_max_right (2 * x.1 - x.2) (2 * x.2 - x.1))
        have hmax : ((x.2 : ℝ) : EReal) ≤ ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal) :=
          le_trans hx2E hmaxE
        simpa [example11_28Function_apply, h] using hmax
  · -- Outside the orthant, the value is `⊤`, so both inequalities are automatic.
    constructor <;> simp [example11_28Function_apply, h]

/-- Helper for Example 11 28: the explicit formula is globally nonnegative. -/
theorem example11_28_nonneg (x : ℝ × ℝ) :
    (0 : EReal) ≤ f x := by
  by_cases h : 0 ≤ x.1 ∧ 0 ≤ x.2
  · -- On the orthant, one coordinate lower bound already yields nonnegativity.
    exact le_trans (by exact_mod_cast h.1) (example11_28_coordinate_lower_bounds x).1
  · -- Outside the orthant, the function takes the value `⊤`.
    simp [example11_28Function_apply, h]

/-- Helper for Example 11 28: every finite lower level set is contained in the coordinate box
`[0, ξ] × [0, ξ]`. -/
theorem example11_28_mem_lowerLevelSet_implies_box_bounds {ξ : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ lowerLevelSet f ξ) :
    0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 ≤ ξ ∧ x.2 ≤ ξ := by
  have hfx_le : f x ≤ ξ := by
    simpa [lowerLevelSet] using hx
  by_cases horth : 0 ≤ x.1 ∧ 0 ≤ x.2
  · -- Finite lower-level membership forces orthant membership and then bounds each coordinate.
    have hx1_le : x.1 ≤ ξ := by
      have hle : ((x.1 : ℝ) : EReal) ≤ (ξ : EReal) :=
        (example11_28_coordinate_lower_bounds x).1.trans hfx_le
      exact_mod_cast hle
    have hx2_le : x.2 ≤ ξ := by
      have hle : ((x.2 : ℝ) : EReal) ≤ (ξ : EReal) :=
        (example11_28_coordinate_lower_bounds x).2.trans hfx_le
      exact_mod_cast hle
    exact ⟨horth.1, horth.2, hx1_le, hx2_le⟩
  · -- Outside the orthant the value is `⊤`, so no real lower-level inequality can hold.
    have : False := by
      simp [example11_28Function_apply, horth] at hfx_le
    exact this.elim

/-- Helper for Example 11 28: the function value is zero exactly at the origin. -/
theorem example11_28_value_eq_zero_iff_origin (x : ℝ × ℝ) :
    f x = 0 ↔ x = ((0 : ℝ), (0 : ℝ)) := by
  constructor
  · intro hx
    -- Zero value forces orthant membership and then both coordinates vanish.
    have horth : 0 ≤ x.1 ∧ 0 ≤ x.2 := by
      by_cases horth : 0 ≤ x.1 ∧ 0 ≤ x.2
      · exact horth
      · have : False := by
          simp [example11_28Function_apply, horth] at hx
        exact this.elim
    have hx1_le_zero : x.1 ≤ 0 := by
      have hle : ((x.1 : ℝ) : EReal) ≤ 0 := by
        calc
          ((x.1 : ℝ) : EReal) ≤ f x := (example11_28_coordinate_lower_bounds x).1
          _ = 0 := hx
      exact_mod_cast hle
    have hx2_le_zero : x.2 ≤ 0 := by
      have hle : ((x.2 : ℝ) : EReal) ≤ 0 := by
        calc
          ((x.2 : ℝ) : EReal) ≤ f x := (example11_28_coordinate_lower_bounds x).2
          _ = 0 := hx
      exact_mod_cast hle
    ext <;> linarith
  · intro hx
    -- The explicit formula at the origin is `0`.
    simp [hx]

-- Proof sketch: write the function as the sum of the positive-orthant indicator and the maximum
-- of two affine forms. Lower semicontinuity and convexity come from these two pieces, while the
-- explicit formula shows the function is proper.
/-- The explicit function from the counterexample belongs to `Γ₀(ℝ × ℝ)`. -/
theorem example11_28Function_mem_gammaZero :
    example11_28Function ∈ Γ₀(ℝ × ℝ) := by
  let C : Set (ℝ × ℝ) := Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)
  let g : (ℝ × ℝ) → Set.Ioi (⊥ : EReal) :=
    (fun x : ℝ × ℝ ↦ max (2 * x.1 - x.2) (2 * x.2 - x.1)).toEReal
  have hg_conv : ConvexOn g Set.univ := by
    simpa [g, Function.effectiveDomain_toEReal] using example11_28_max_affine_mem_gammaZero.2
  have hcont_branch1 : Continuous fun x : ℝ × ℝ ↦ 2 * x.1 - x.2 := by
    have h1 : Continuous fun x : ℝ × ℝ ↦ 2 * x.1 := by
      simpa using (continuous_const.mul continuous_fst)
    have h2 : Continuous fun x : ℝ × ℝ ↦ x.2 := continuous_snd
    simpa [sub_eq_add_neg] using h1.add h2.neg
  have hcont_branch2 : Continuous fun x : ℝ × ℝ ↦ 2 * x.2 - x.1 := by
    have h1 : Continuous fun x : ℝ × ℝ ↦ 2 * x.2 := by
      simpa using (continuous_const.mul continuous_snd)
    have h2 : Continuous fun x : ℝ × ℝ ↦ x.1 := continuous_fst
    simpa [sub_eq_add_neg] using h1.add h2.neg
  have hcont_max : Continuous fun x : ℝ × ℝ ↦ max (2 * x.1 - x.2) (2 * x.2 - x.1) :=
    hcont_branch1.max hcont_branch2
  rw [mem_gammaZero_iff]
  constructor
  · -- Write the function as the sum of the finite max-affine part and the orthant indicator.
    have hg_lsc : LowerSemicontinuous (fun x : ℝ × ℝ ↦ (g x : EReal)) := by
      simpa [g, Function.toEReal_apply] using
        (continuous_coe_real_ereal.comp hcont_max).lowerSemicontinuous
    have hC_closed : IsClosed C := by
      simpa [C] using
        (isClosed_Ici.prod isClosed_Ici :
          IsClosed (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    have hindicator : LowerSemicontinuous (fun x : ℝ × ℝ ↦ ((ι[C]) x : EReal)) := by
      simpa [ERealFunction.indicator_apply] using
        hC_closed.isOpen_compl.lowerSemicontinuous_indicator (show (0 : EReal) ≤ ⊤ by simp)
    have hsum_lsc :
        LowerSemicontinuous (fun x : ℝ × ℝ ↦ (g x : EReal) + (ι[C] x : EReal)) := by
      -- The finite branch never hits `-∞`, so adding the closed-set indicator is well behaved.
      refine hg_lsc.add' hindicator ?_
      intro x
      by_cases hxC : x ∈ C
      · have hix : ((ι[C]) x : EReal) = 0 := by
          simp [ERealFunction.indicator_apply, hxC]
        rw [hix]
        refine EReal.continuousAt_add ?_ ?_
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
      · have hix : ((ι[C]) x : EReal) = ⊤ := by
          simp [ERealFunction.indicator_apply, hxC]
        rw [hix]
        have hgx_ne_bot : (g x : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
        refine EReal.continuousAt_add ?_ ?_
        · exact Or.inr (by simp)
        · exact Or.inl hgx_ne_bot
    have hsum_eq :
        (fun x : ℝ × ℝ ↦ (example11_28Function x : EReal)) =
          fun x : ℝ × ℝ ↦ (g x : EReal) + (ι[C] x : EReal) := by
      ext x
      by_cases hxC : x ∈ C
      · have horth : 0 ≤ x.1 ∧ 0 ≤ x.2 := by
          simpa [C, Set.mem_prod] using hxC
        have hix : ((ι[C]) x : EReal) = 0 := by
          simp [ERealFunction.indicator_apply, hxC]
        -- On the orthant the indicator vanishes, so the formula reduces
        -- to the max-affine branch.
        rw [example11_28Function_apply, if_pos horth, hix]
        simp [g]
      · have horth : ¬ (0 ≤ x.1 ∧ 0 ≤ x.2) := by
          intro horth
          exact hxC (by simpa [C, Set.mem_prod] using horth)
        have hix : ((ι[C]) x : EReal) = ⊤ := by
          simp [ERealFunction.indicator_apply, hxC]
        have hgx_ne_bot : (g x : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
        -- Outside the orthant the indicator contributes `⊤`, which matches the textbook formula.
        rw [example11_28Function_apply, if_neg horth, hix, EReal.add_top_of_ne_bot hgx_ne_bot]
    exact hsum_eq.symm ▸ hsum_lsc
  · rw [example11_28_effectiveDomain]
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨(0, 0), by simp⟩
    · intro x hx
      simpa [example11_28_effectiveDomain] using hx
    · intro x hx y hy a ha0 ha1
      have hxy :
          a • x + (1 - a) • y ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) :=
        ((convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ))) hx hy ha0.le
          (sub_nonneg.mpr ha1.le) (by ring)
      have hxorth : 0 ≤ x.1 ∧ 0 ≤ x.2 := by
        simpa [Set.mem_prod] using hx
      have hyorth : 0 ≤ y.1 ∧ 0 ≤ y.2 := by
        simpa [Set.mem_prod] using hy
      have hxyorth :
          0 ≤ (a • x + (1 - a) • y).1 ∧ 0 ≤ (a • x + (1 - a) • y).2 := by
        simpa [Set.mem_prod] using hxy
      have hgineq :
          (g (a • x + (1 - a) • y) : EReal) ≤
            (a : EReal) * (g x : EReal) + (1 - a : EReal) * (g y : EReal) :=
        hg_conv.ineq (x := x) (by simp) (y := y) (by simp) ha0 ha1
      -- Restrict the max-affine convexity from `univ` to the orthant effective domain.
      calc
        f (a • x + (1 - a) • y) = (g (a • x + (1 - a) • y) : EReal) := by
          simpa [g, example11_28Function_apply, hxyorth]
        _ ≤ (a : EReal) * (g x : EReal) + (1 - a : EReal) * (g y : EReal) := hgineq
        _ = (a : EReal) * f x + (1 - a : EReal) * f y := by
          simp [g, example11_28Function_apply, hxorth, hyorth]

-- Proof sketch: outside the positive orthant the function is `+∞`, while on the orthant the
-- maximum of `2 ξ₁ - ξ₂` and `2 ξ₂ - ξ₁` dominates `(ξ₁ + ξ₂) / 2`; since
-- `(ξ₁ + ξ₂) / 2 → +∞` whenever `‖(ξ₁, ξ₂)‖ → +∞` inside the orthant, the whole function is
-- coercive.
/-- The Example 11.28 function is coercive. -/
theorem example11_28Function_coercive :
    Coercive f := by
  rw [coercive_iff_bounded_lowerLevelSet]
  intro ξ
  refine isBounded_iff_forall_norm_le.2 ?_
  refine ⟨max ξ 0, ?_⟩
  intro x hx
  rcases example11_28_mem_lowerLevelSet_implies_box_bounds hx with
    ⟨hx1_nonneg, hx2_nonneg, hx1_le, hx2_le⟩
  have hx1_bound : ‖x.1‖ ≤ max ξ 0 := by
    rw [Real.norm_of_nonneg hx1_nonneg]
    exact hx1_le.trans (le_max_left ξ 0)
  have hx2_bound : ‖x.2‖ ≤ max ξ 0 := by
    rw [Real.norm_of_nonneg hx2_nonneg]
    exact hx2_le.trans (le_max_left ξ 0)
  -- The product norm is the maximum of the coordinate norms.
  simpa [Prod.norm_def] using max_le hx1_bound hx2_bound

-- Proof sketch: on the positive orthant the formula is nonnegative and vanishes only at the
-- origin, while outside the orthant the value is `+∞`. This identifies the unique global
-- minimizer.
/-- The minimizer set of the counterexample is the singleton `{(0, 0)}`. -/
theorem example11_28Argmin_eq :
    Argmin f =
      ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := by
  ext x
  constructor
  · intro hx
    have hxmin : IsMinOn f Set.univ x := (mem_argmin_iff).1 hx
    have hle : f x ≤ 0 := by
      simpa using (isMinOn_univ_iff.mp hxmin) ((0 : ℝ), (0 : ℝ))
    have hzero : f x = 0 := le_antisymm hle (example11_28_nonneg x)
    simpa [Set.mem_singleton_iff] using
      (example11_28_value_eq_zero_iff_origin x).1 hzero
  · intro hx
    rcases Set.mem_singleton_iff.1 hx with rfl
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    -- The origin has value `0`, and every value is bounded below by `0`.
    simpa using example11_28_nonneg y

-- Proof sketch: evaluate the function at the origin to get the upper bound `0`, and use the
-- explicit positive-orthant formula to show every value is at least `0`.
/-- The infimum of the function values in the counterexample is `0`. -/
theorem example11_28Function_sInf_eq_zero :
    sInf (Set.range f) = 0 := by
  have horigin : ((0 : ℝ), (0 : ℝ)) ∈ Argmin f := by
    rw [example11_28Argmin_eq]
    simp
  -- Membership in `Argmin` identifies the value with the infimum of the range.
  have hsInf : f ((0 : ℝ), (0 : ℝ)) = sInf (Set.range f) := by
    rwa [mem_argmin_iff_eq_sInf] at horigin
  simpa using hsInf.symm

-- Proof sketch: when `t ≥ 0`, the point `(t, t)` lies in the positive orthant and both affine
-- branches take the common value `t`.
/-- On the nonnegative diagonal, the counterexample function takes the value `t`. -/
theorem example11_28Function_value_on_diagonal {t : ℝ} (ht : 0 ≤ t) :
    f (t, t) = t := by
  -- On the diagonal, the two affine branches collapse to the common value `t`.
  have hdiag : (2 * t - t : ℝ) = t := by ring
  simp [example11_28Function_apply, ht, hdiag]

-- Proof sketch: if `ξ₂ < 0`, every slice value is `+∞`, so `x.2` is still a minimizer. If
-- `ξ₂ ≥ 0`, the slice is the maximum of the decreasing affine map `ξ₁ ↦ 2 ξ₂ - ξ₁` and the
-- increasing affine map `ξ₁ ↦ 2 ξ₁ - ξ₂`, whose common minimizer is `ξ₁ = ξ₂`.
/-- The first coordinate update realizes the minimum of the first-coordinate slice. -/
theorem example11_28MinimizeFirst_isMinOn (x : ℝ × ℝ) :
    IsMinOn (fun ξ₁ : ℝ ↦ f (ξ₁, x.2)) Set.univ (example11_28MinimizeFirst x).1 := by
  rw [isMinOn_univ_iff]
  by_cases hx2 : 0 ≤ x.2
  · intro ξ₁
    -- In the nonnegative slice, the diagonal point has value `x.2`.
    have hdiag : f (x.2, x.2) = x.2 :=
      example11_28Function_value_on_diagonal hx2
    have hbound : ((x.2 : ℝ) : EReal) ≤ f (ξ₁, x.2) :=
      (example11_28_coordinate_lower_bounds (ξ₁, x.2)).2
    calc
      f ((example11_28MinimizeFirst x).1, x.2) = f (x.2, x.2) := by
        rfl
      _ = ((x.2 : ℝ) : EReal) := by
        simpa using hdiag
      _ ≤ f (ξ₁, x.2) := hbound
  · intro ξ₁
    -- If the fixed second coordinate is negative, the whole slice is constantly `⊤`.
    simp [example11_28MinimizeFirst, example11_28Function_apply, hx2]

-- Proof sketch: if `ξ₁ < 0`, the whole slice is `+∞`, so every point is a minimizer. If
-- `ξ₁ ≥ 0`, the same affine-maximum argument shows that the unique finite minimizer of
-- `ξ₂ ↦ f (ξ₁, ξ₂)` is `ξ₂ = ξ₁`.
/-- The second coordinate update realizes the minimum of the second-coordinate slice. -/
theorem example11_28MinimizeSecond_isMinOn (x : ℝ × ℝ) :
    IsMinOn (fun ξ₂ : ℝ ↦ f (x.1, ξ₂)) Set.univ (example11_28MinimizeSecond x).2 := by
  rw [isMinOn_univ_iff]
  by_cases hx1 : 0 ≤ x.1
  · intro ξ₂
    -- In the nonnegative slice, the diagonal point has value `x.1`.
    have hdiag : f (x.1, x.1) = x.1 :=
      example11_28Function_value_on_diagonal hx1
    have hbound : ((x.1 : ℝ) : EReal) ≤ f (x.1, ξ₂) :=
      (example11_28_coordinate_lower_bounds (x.1, ξ₂)).1
    calc
      f (x.1, (example11_28MinimizeSecond x).2) = f (x.1, x.1) := by
        rfl
      _ = ((x.1 : ℝ) : EReal) := by
        simpa using hdiag
      _ ≤ f (x.1, ξ₂) := hbound
  · intro ξ₂
    -- If the fixed first coordinate is negative, the whole slice is constantly `⊤`.
    simp [example11_28MinimizeSecond, example11_28Function_apply, hx1]

-- Proof sketch: unfold the two coordinate updates and simplify the resulting diagonal point.
/-- One alternating-minimization cycle sends `(ξ₁, ξ₂)` to the diagonal point `(ξ₂, ξ₂)`. -/
@[simp] theorem example11_28AlternatingMinimizationStep_eq_diagonal (x : ℝ × ℝ) :
    example11_28AlternatingMinimizationStep x = (x.2, x.2) := by
  rfl

/-- Helper for Example 11 28: every diagonal point is fixed by one alternating-minimization
cycle. -/
@[simp] theorem example11_28AlternatingMinimizationStep_diagonal (t : ℝ) :
    example11_28AlternatingMinimizationStep (t, t) = (t, t) := by
  rfl

/-- Helper for Example 11 28: iterating the alternating-minimization step on a diagonal point
leaves that point unchanged. -/
theorem example11_28AlternatingMinimizationStep_iterate_diagonal (t : ℝ) (n : ℕ) :
    (example11_28AlternatingMinimizationStep^[n]) (t, t) = (t, t) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [Function.iterate_succ_apply', ih]

-- Proof sketch: `example11_28MinimizeFirst_isMinOn` identifies the first coordinate update as the
-- relevant slice minimization, and `example11_28MinimizeSecond_isMinOn` does the same for the
-- second coordinate update. After one full cycle the orbit reaches `(ξ₂, ξ₂)`, which is fixed by
-- the same cycle. Induct on `n` through the iterate description.
/-- Every alternating-minimization iterate after the initial one is the diagonal point determined
by the second initial coordinate. -/
theorem example11_28Recurrence_eq_diagonal (x0 : ℝ × ℝ) {n : ℕ} (hn : 1 ≤ n) :
    example11_28Recurrence x0 n = (x0.2, x0.2) := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  -- After one step the orbit reaches a diagonal fixed point, so all later iterates agree.
  calc
    example11_28Recurrence x0 (1 + k) =
        (example11_28AlternatingMinimizationStep^[k + 1]) x0 := by
          simp [example11_28Recurrence, Nat.add_comm]
    _ = (example11_28AlternatingMinimizationStep^[k])
          (example11_28AlternatingMinimizationStep x0) := by
            rw [Function.iterate_add_apply, Function.iterate_one]
    _ = (example11_28AlternatingMinimizationStep^[k]) (x0.2, x0.2) := by
          simp
    _ = (x0.2, x0.2) := example11_28AlternatingMinimizationStep_iterate_diagonal x0.2 k

-- Proof sketch: combine `example11_28Recurrence_eq_diagonal` with
-- `example11_28Function_value_on_diagonal`, using `0 < x0.2` to place the diagonal point inside
-- the positive orthant.
/-- Example 11 28: for every iterate after the initial one, alternating minimization produces the
diagonal point `(ξ₂,₀, ξ₂,₀)` and the function value there is exactly `ξ₂,₀`. -/
theorem alternatingMinimization_eq_diagonal_and_value (x0 : ℝ × ℝ) (hx0_2 : 0 < x0.2)
    {n : ℕ} (hn : 1 ≤ n) :
    example11_28Recurrence x0 n = (x0.2, x0.2) ∧
      f (example11_28Recurrence x0 n) = x0.2 := by
  constructor
  · exact example11_28Recurrence_eq_diagonal x0 hn
  · rw [example11_28Recurrence_eq_diagonal x0 hn]
    exact example11_28Function_value_on_diagonal hx0_2.le

-- Proof sketch: use `example11_28Recurrence_eq_diagonal` to show the recurrence is eventually
-- constant with value `(x0.2, x0.2)`, then apply the standard criterion for convergence of
-- eventually constant sequences.
/-- The explicit Example 11.28 recurrence converges to the diagonal point fixed after the first
step. -/
theorem example11_28Recurrence_tendsto (x0 : ℝ × ℝ) :
    Tendsto (example11_28Recurrence x0) atTop (nhds (x0.2, x0.2)) := by
  have hevent :
      ∀ᶠ n in atTop, example11_28Recurrence x0 n = (x0.2, x0.2) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact example11_28Recurrence_eq_diagonal x0 hn
  -- Eventual constancy reduces the limit to the constant-sequence limit.
  have hEq : example11_28Recurrence x0 =ᶠ[atTop] fun _ : ℕ ↦ (x0.2, x0.2) := by
    simpa [Filter.EventuallyEq, Filter.Eventually] using hevent
  exact (tendsto_congr' hEq).2 <|
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (x0.2, x0.2)) atTop (nhds (x0.2, x0.2)))

/-- Helper for Example 11 28: once the second initial coordinate is positive, the composed value
sequence is eventually constant with value `x0.2`. -/
theorem example11_28_eventually_value_eq (x0 : ℝ × ℝ) (hx0_2 : 0 < x0.2) :
    ∀ᶠ n in atTop, (f ∘ example11_28Recurrence x0) n = ((x0.2 : ℝ) : EReal) := by
  -- After the first iterate, the recurrence is frozen on the diagonal and the function value is
  -- the diagonal coordinate.
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact (alternatingMinimization_eq_diagonal_and_value x0 hx0_2 hn).2

-- Proof sketch: the labeled theorem shows that every tail value of the sequence is the positive
-- constant `x0.2`, whereas `example11_28Function_sInf_eq_zero` identifies the infimum with `0`.
-- Hence the function values do not converge to the infimum.
/-- If the second initial coordinate is positive, the Example 11.28 recurrence is not a minimizing
sequence for the counterexample function. -/
theorem example11_28Recurrence_not_isMinimizing (x0 : ℝ × ℝ) (hx0_2 : 0 < x0.2) :
    ¬ IsMinimizingSequence f (example11_28Recurrence x0) := by
  intro hmin
  -- Reuse the explicit diagonal-value description to freeze the tail of the value sequence.
  have hevent :
      ∀ᶠ n in atTop, (f ∘ example11_28Recurrence x0) n = ((x0.2 : ℝ) : EReal) :=
    example11_28_eventually_value_eq x0 hx0_2
  have hconst :
      Tendsto (f ∘ example11_28Recurrence x0) atTop (nhds (((x0.2 : ℝ) : EReal))) := by
    -- The value sequence is eventually constant with value `x0.2`.
    have hEq : (f ∘ example11_28Recurrence x0) =ᶠ[atTop] fun _ : ℕ ↦ (((x0.2 : ℝ) : EReal)) := by
      simpa [Filter.EventuallyEq, Filter.Eventually, Function.comp] using hevent
    exact (tendsto_congr' hEq).2 <|
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (((x0.2 : ℝ) : EReal))) atTop
          (nhds (((x0.2 : ℝ) : EReal))))
  have hsInf :
      Tendsto (f ∘ example11_28Recurrence x0) atTop (nhds (0 : EReal)) := by
    simpa [example11_28Function_sInf_eq_zero] using hmin.tendsto
  have hzero : (((x0.2 : ℝ) : EReal)) = 0 :=
    tendsto_nhds_unique hconst hsInf
  have hreal : x0.2 = 0 := by
    exact_mod_cast hzero
  exact hx0_2.ne' hreal

-- Proof sketch: `example11_28Argmin_eq` identifies the unique minimizer with the origin, while
-- `0 < x0.2` shows the limit point `(x0.2, x0.2)` is not the origin.
/-- If the second initial coordinate is positive, the limit of the Example 11.28 recurrence is not
a minimizer of the counterexample function. -/
theorem example11_28Recurrence_limit_not_mem_argmin (x0 : ℝ × ℝ) (hx0_2 : 0 < x0.2) :
    (x0.2, x0.2) ∉ Argmin f := by
  rw [example11_28Argmin_eq]
  simp [hx0_2.ne']

end ERealFunction
