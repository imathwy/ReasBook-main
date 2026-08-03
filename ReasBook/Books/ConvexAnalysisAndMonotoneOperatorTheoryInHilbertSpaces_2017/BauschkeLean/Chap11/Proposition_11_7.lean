import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set

namespace ERealFunction

-- Semantic search note: `lean_leansearch` timed out on the strict-ray query, so this item keeps a
-- local helper-based API; for `EReal`-valued functions, clauses (4)-(5) need an explicit
-- finiteness hypothesis on the positive ray to rule out false `⊤` plateaus.

section EvenConvexOn

variable (φ : ℝ → Set.Ioi (⊥ : EReal))

/-- Helper: the value at `0` is a global lower bound for an even convex
`]-∞,+∞]`-valued function on `ℝ`. -/
lemma zeroLeValueOfEvenConvexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (x : ℝ) :
    φ.asEReal 0 ≤ φ.asEReal x := by
  by_cases hx : x ∈ effectiveDomain φ
  · have hnegx : -x ∈ effectiveDomain φ := by
      rw [mem_effectiveDomain_iff] at hx ⊢
      simpa [heven x] using hx
    have hmid : (1 / 2 : ℝ) * x + -((((1 : ℝ) - 1 / 2) : ℝ) * x) = 0 := by
      have hmid' : (1 / 2 : ℝ) * x + -((((1 : ℝ) - 1 / 2) : ℝ) * x) = 0 := by
        ring
      exact hmid'
    have hsub_cast :
        (1 - ((1 / 2 : ℝ) : EReal)) = ((((1 : ℝ) - 1 / 2 : ℝ)) : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hmid_smul : ((1 / 2 : ℝ) • x + (((1 : ℝ) - 1 / 2) : ℝ) • (-x) : ℝ) = 0 := by
      simpa [smul_eq_mul, sub_eq_add_neg] using hmid
    have hcoeff : ((((1 : ℝ) - 1 / 2 : ℝ)) : EReal) = ((1 / 2 : ℝ) : EReal) := by
      norm_num
    have hbase :
        φ.asEReal (((1 / 2 : ℝ) • x + (((1 : ℝ) - 1 / 2) : ℝ) • (-x) : ℝ)) ≤
          ((1 / 2 : ℝ) : EReal) * φ.asEReal x +
            ((((1 : ℝ) - 1 / 2 : ℝ)) : EReal) * φ.asEReal x := by
      -- Apply midpoint Jensen and use evenness to identify the two endpoint values.
      simpa [smul_eq_mul, sub_eq_add_neg, hsub_cast, heven x] using
        hconv.ineq hx hnegx (by norm_num) (by norm_num)
    have hineq :
        φ.asEReal 0 ≤
          ((1 / 2 : ℝ) : EReal) * φ.asEReal x + ((1 / 2 : ℝ) : EReal) * φ.asEReal x := by
      rw [show (0 : ℝ) = (1 / 2 : ℝ) • x + (((1 : ℝ) - 1 / 2) : ℝ) • (-x) by
        symm
        exact hmid_smul]
      calc
        φ.asEReal (((1 / 2 : ℝ) • x + (((1 : ℝ) - 1 / 2) : ℝ) • (-x) : ℝ)) ≤
            ((1 / 2 : ℝ) : EReal) * φ.asEReal x +
              ((((1 : ℝ) - 1 / 2 : ℝ)) : EReal) * φ.asEReal x := hbase
        _ = ((1 / 2 : ℝ) : EReal) * φ.asEReal x + ((1 / 2 : ℝ) : EReal) * φ.asEReal x := by
          rw [hcoeff]
    have hx_top : φ.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : φ.asEReal x ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < φ.asEReal x from (φ x).2)
    have hhalf :
        ((1 / 2 : ℝ) : EReal) * φ.asEReal x + ((1 / 2 : ℝ) : EReal) * φ.asEReal x =
          φ.asEReal x := by
      -- The midpoint average of two equal finite endpoint values collapses back to that value.
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul, ← EReal.coe_add]
      have hhalf_real :
          (1 / 2 : ℝ) * (φ.asEReal x).toReal + (1 / 2 : ℝ) * (φ.asEReal x).toReal =
            (φ.asEReal x).toReal := by
        ring
      exact_mod_cast hhalf_real
    exact hineq.trans_eq hhalf
  · have hx_top : φ.asEReal x = ⊤ := by
      rw [mem_effectiveDomain_iff] at hx
      exact le_antisymm le_top (not_lt.mp hx)
    -- Outside the effective domain, the target value is `⊤`, so the lower bound is automatic.
    simpa [hx_top] using (le_top : φ.asEReal 0 ≤ (⊤ : EReal))

/-- Helper: an even convex `]-∞,+∞]`-valued function on `ℝ` is finite at
`0`. -/
lemma zero_mem_effectiveDomain_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal) :
    (0 : ℝ) ∈ effectiveDomain φ := by
  obtain ⟨x, hx⟩ := hconv.nonempty
  -- Compare the value at `0` with one finite domain value to force finiteness at the origin.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (zeroLeValueOfEvenConvexOn φ hconv heven x)
    (mem_effectiveDomain_iff.mp hx)

/-- Helper: once the upper endpoint is finite, the convex-combination
argument gives monotonicity on the nonnegative ray. -/
lemma nonnegativeRayMonotoneStepOfMemEffectiveDomain
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    {ξ η : ℝ} (hξ0 : 0 ≤ ξ) (hξη : ξ ≤ η) (hη : η ∈ effectiveDomain φ) :
    φ.asEReal ξ ≤ φ.asEReal η := by
  have hzero : (0 : ℝ) ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_even_convexOn φ hconv heven
  by_cases hξη_eq : ξ = η
  · simpa [hξη_eq]
  by_cases hξ_eq : ξ = 0
  · -- The endpoint case is exactly the global lower-bound statement from clause (1).
    simpa [hξ_eq] using zeroLeValueOfEvenConvexOn φ hconv heven η
  have hξη_lt : ξ < η := lt_of_le_of_ne hξη hξη_eq
  have hξ_pos : 0 < ξ := lt_of_le_of_ne hξ0 (by
    intro h
    exact hξ_eq h.symm)
  have hη_pos : 0 < η := lt_of_lt_of_le hξ_pos hξη
  let α : ℝ := ξ / η
  have hα0 : 0 < α := by
    dsimp [α]
    exact div_pos hξ_pos hη_pos
  have hα1 : α < 1 := by
    dsimp [α]
    exact (div_lt_one hη_pos).2 hξη_lt
  have hsub_cast : (1 - (α : EReal)) = (((1 - α : ℝ)) : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hαη : α * η = ξ := by
    dsimp [α]
    field_simp [hη_pos.ne']
  have hpoint : α • η + (1 - α) • (0 : ℝ) = ξ := by
    calc
      α • η + (1 - α) • (0 : ℝ) = α * η + (1 - α) * (0 : ℝ) := by
        rw [smul_eq_mul, smul_eq_mul]
      _ = ξ + (1 - α) * (0 : ℝ) := by rw [hαη]
      _ = ξ := by ring
  have hbase :
      φ.asEReal (α • η + (1 - α) • (0 : ℝ)) ≤
        (α : EReal) * φ.asEReal η + (((1 - α : ℝ) : EReal)) * φ.asEReal 0 := by
    -- Write `ξ` as a convex combination of `η` and `0`, then apply Jensen.
    have htmp :=
      hconv.ineq hη hzero hα0 hα1
    rw [hsub_cast] at htmp
    exact htmp
  have hconv_ineq :
      φ.asEReal ξ ≤
        (α : EReal) * φ.asEReal η + (((1 - α : ℝ) : EReal)) * φ.asEReal 0 := by
    rw [hpoint] at hbase
    exact hbase
  have hzero_le : φ.asEReal 0 ≤ φ.asEReal η :=
    zeroLeValueOfEvenConvexOn φ hconv heven η
  have hη_top : φ.asEReal η ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hη)
  have hη_bot : φ.asEReal η ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < φ.asEReal η from (φ η).2)
  have hzero_top : φ.asEReal 0 ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hzero)
  have hzero_bot : φ.asEReal 0 ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < φ.asEReal 0 from (φ 0).2)
  have hzero_toReal :
      (φ.asEReal 0).toReal ≤ (φ.asEReal η).toReal :=
    EReal.toReal_le_toReal hzero_le hzero_bot hη_top
  have hright_toReal :
      α * (φ.asEReal η).toReal + (1 - α) * (φ.asEReal 0).toReal ≤
        (φ.asEReal η).toReal := by
    have hα_nonneg : 0 ≤ α := hα0.le
    have hone_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
    nlinarith
  have hright :
      (α : EReal) * φ.asEReal η + (((1 - α : ℝ) : EReal)) * φ.asEReal 0 ≤ φ.asEReal η := by
    -- Convert the affine upper bound to the real-valued finite representatives.
    have hright_coe :
        (((α * (φ.asEReal η).toReal + (1 - α) * (φ.asEReal 0).toReal : ℝ) : EReal)) ≤
          (((φ.asEReal η).toReal : ℝ) : EReal) := by
      exact_mod_cast hright_toReal
    rw [← EReal.coe_toReal hη_top hη_bot, ← EReal.coe_toReal hzero_top hzero_bot,
      ← EReal.coe_toReal hη_top hη_bot]
    simpa [EReal.coe_mul, EReal.coe_add] using hright_coe
  exact hconv_ineq.trans hright

/-- Helper: evenness transports nonnegative-ray monotonicity to
nonpositive-ray antitonicity. -/
lemma antitoneOn_nonpositive_of_monotoneOn_nonnegative_of_even
    (heven : Function.Even φ.asEReal)
    (hmono : MonotoneOn φ.asEReal (Ici 0)) :
    AntitoneOn φ.asEReal (Iic 0) := by
  intro x hx y hy hxy
  have hneg_mono : φ.asEReal (-y) ≤ φ.asEReal (-x) := by
    -- Negation sends `Iic 0` to `Ici 0`, where monotonicity is already known.
    apply hmono
    · simpa using neg_nonneg.mpr (show y ≤ 0 from hy)
    · simpa using neg_nonneg.mpr (show x ≤ 0 from hx)
    · simpa using neg_le_neg hxy
  simpa [heven x, heven y] using hneg_mono

/-- Helper for clause (1): an even convex `]-∞,+∞]`-valued function on `ℝ` attains its
global minimum at `0`. -/
-- Proof sketch: apply the Jensen inequality to the midpoint decomposition
-- `0 = (1 / 2) • x + (1 / 2) • (-x)` and use evenness to identify the two endpoint values.
theorem zero_mem_argmin_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : (0 : ℝ) ∈ Argmin φ.asEReal := by
  -- Clause (1) is exactly the global lower-bound statement packaged as `Argmin`.
  rw [mem_argmin_iff, isMinOn_univ_iff]
  intro x
  exact zeroLeValueOfEvenConvexOn φ hconv heven x

/-- Proposition 11.7 (1): a proper even convex `]-∞,+∞]`-valued function on `ℝ` attains its
global minimum at `0`. -/
theorem zero_mem_argmin_of_proper_even_convexOn
    (hproper : IsProper φ.asEReal)
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : (0 : ℝ) ∈ Argmin φ.asEReal := by
  let _ : IsProper φ.asEReal := hproper
  exact zero_mem_argmin_of_even_convexOn φ hconv heven

/-- Companion bridge for clause (1) in `IsMinOn` form. -/
theorem isMinOn_zero_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : IsMinOn φ.asEReal univ 0 := by
  -- Unfold `IsMinOn` on `univ` and reuse the lower-bound lemma from clause (1).
  rw [isMinOn_univ_iff]
  intro x
  exact zeroLeValueOfEvenConvexOn φ hconv heven x

/-- Helper for clause (2): an even convex `]-∞,+∞]`-valued function on `ℝ` is
increasing on the nonnegative ray. -/
-- Proof sketch: for `0 ≤ ξ < η`, write `ξ = (ξ / η) • η + (1 - ξ / η) • 0`, apply convexity, and
-- then use clause (1) to bound the value at `0` by the value at `η`.
theorem monotoneOn_nonnegative_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : MonotoneOn φ.asEReal (Ici 0) := by
  intro ξ hξ η _hη hξη
  by_cases hη_dom : η ∈ effectiveDomain φ
  · -- In the finite branch, the source convex-combination proof applies directly.
    exact nonnegativeRayMonotoneStepOfMemEffectiveDomain φ hconv heven hξ hξη hη_dom
  · have hη_top : φ.asEReal η = ⊤ := by
      rw [mem_effectiveDomain_iff] at hη_dom
      exact le_antisymm le_top (not_lt.mp hη_dom)
    -- Outside the effective domain, the target value is `⊤`, so the comparison is immediate.
    simpa [hη_top] using (le_top : φ.asEReal ξ ≤ (⊤ : EReal))

/-- Proposition 11.7 (2): a proper even convex `]-∞,+∞]`-valued function on `ℝ` is increasing on
the nonnegative ray. -/
theorem monotoneOn_nonnegative_of_proper_even_convexOn
    (hproper : IsProper φ.asEReal)
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : MonotoneOn φ.asEReal (Ici 0) := by
  let _ : IsProper φ.asEReal := hproper
  exact monotoneOn_nonnegative_of_even_convexOn φ hconv heven

/-- Helper for clause (3): an even convex `]-∞,+∞]`-valued function on `ℝ` is decreasing on the
nonpositive ray. -/
-- Proof sketch: transport clause (2) from the nonnegative ray by the symmetry `x ↦ -x` and use
-- evenness to identify the corresponding function values.
theorem antitoneOn_nonpositive_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : AntitoneOn φ.asEReal (Iic 0) := by
  -- Transport the nonnegative-ray monotonicity through the symmetry `x ↦ -x`.
  exact antitoneOn_nonpositive_of_monotoneOn_nonnegative_of_even φ heven
    (monotoneOn_nonnegative_of_even_convexOn φ hconv heven)

/-- Proposition 11.7 (3): a proper even convex `]-∞,+∞]`-valued function on `ℝ` is decreasing on
the nonpositive ray. -/
theorem antitoneOn_nonpositive_of_proper_even_convexOn
    (hproper : IsProper φ.asEReal)
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : AntitoneOn φ.asEReal (Iic 0) := by
  let _ : IsProper φ.asEReal := hproper
  exact antitoneOn_nonpositive_of_even_convexOn φ hconv heven

/-- Helper for Proposition 11.7: every positive finite point has strictly positive value once the
function vanishes only at `0`. -/
lemma zero_lt_value_of_pos_of_even_convexOn_eq_zero_iff
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0)
    {η : ℝ} (hη0 : 0 < η) (_hη : η ∈ effectiveDomain φ) :
    (0 : EReal) < φ.asEReal η := by
  have hφ0 : φ.asEReal 0 = 0 := (hzero 0).2 rfl
  have hzero_le : φ.asEReal 0 ≤ φ.asEReal η :=
    zeroLeValueOfEvenConvexOn φ hconv heven η
  have hη_nonneg : (0 : EReal) ≤ φ.asEReal η := by
    simpa [hφ0] using hzero_le
  have hη_ne_zero : φ.asEReal η ≠ 0 := by
    -- The zero-level set hypothesis rules out equality at every positive point.
    intro hη_zero
    exact hη0.ne' ((hzero η).1 hη_zero)
  exact lt_of_le_of_ne hη_nonneg fun hzero_eta ↦ hη_ne_zero hzero_eta.symm

/-- Helper for Proposition 11.7: the convex-combination step on the positive ray is strict once
the upper endpoint has strictly positive value. -/
lemma strict_positive_ray_step_of_mem_effectiveDomain
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0)
    {ξ η : ℝ} (hξ0 : 0 < ξ) (hξη : ξ < η) (hη : η ∈ effectiveDomain φ) :
    φ.asEReal ξ < φ.asEReal η := by
  have hzero_mem : (0 : ℝ) ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_even_convexOn φ hconv heven
  have hη0 : 0 < η := lt_trans hξ0 hξη
  have hφ0 : φ.asEReal 0 = 0 := (hzero 0).2 rfl
  have hη_value_pos : (0 : EReal) < φ.asEReal η :=
    zero_lt_value_of_pos_of_even_convexOn_eq_zero_iff φ hconv heven hzero hη0 hη
  let α : ℝ := ξ / η
  have hα0 : 0 < α := by
    dsimp [α]
    exact div_pos hξ0 hη0
  have hα1 : α < 1 := by
    dsimp [α]
    exact (div_lt_one hη0).2 hξη
  have hsub_cast : (1 - (α : EReal)) = (((1 - α : ℝ)) : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hαη : α * η = ξ := by
    dsimp [α]
    field_simp [hη0.ne']
  have hpoint : α • η + (1 - α) • (0 : ℝ) = ξ := by
    calc
      α • η + (1 - α) • (0 : ℝ) = α * η + (1 - α) * (0 : ℝ) := by
        rw [smul_eq_mul, smul_eq_mul]
      _ = ξ + (1 - α) * (0 : ℝ) := by rw [hαη]
      _ = ξ := by ring
  have hbase :
      φ.asEReal (α • η + (1 - α) • (0 : ℝ)) ≤
        (α : EReal) * φ.asEReal η + (((1 - α : ℝ) : EReal)) * φ.asEReal 0 := by
    -- Apply the source convex-combination argument at the finite pair `(η, 0)`.
    have htmp := hconv.ineq hη hzero_mem hα0 hα1
    rw [hsub_cast] at htmp
    exact htmp
  have hconv_ineq : φ.asEReal ξ ≤ (α : EReal) * φ.asEReal η := by
    -- The zero-value hypothesis collapses the second affine term.
    rw [hpoint] at hbase
    simpa [hφ0] using hbase
  have hη_top : φ.asEReal η ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hη)
  have hη_bot : φ.asEReal η ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < φ.asEReal η from (φ η).2)
  have hη_toReal_pos : 0 < (φ.asEReal η).toReal :=
    EReal.toReal_pos hη_value_pos hη_top
  have hmul_real_lt :
      α * (φ.asEReal η).toReal < (φ.asEReal η).toReal := by
    nlinarith [hα0, hα1, hη_toReal_pos]
  have hmul_lt : (α : EReal) * φ.asEReal η < φ.asEReal η := by
    -- Move the strict comparison to the real representatives of the finite endpoint value.
    rw [← EReal.coe_toReal hη_top hη_bot, ← EReal.coe_toReal hη_top hη_bot, ← EReal.coe_mul]
    exact_mod_cast hmul_real_lt
  exact lt_of_le_of_lt hconv_ineq hmul_lt

/-- Helper for clause (4): if an even convex `]-∞,+∞]`-valued function on `ℝ`
vanishes only at `0` and is finite at every positive point, then it is strictly increasing on the
nonnegative ray. -/
-- Proof sketch: repeat the convex-combination argument from clause (2), but now use the
-- vanishing-only-at-zero hypothesis together with `η > 0` to get the strict inequality
-- `(φ 0 : EReal) < φ η`.
theorem strictMonoOn_nonnegative_of_even_convexOn_eq_zero_iff_of_pos_mem_effectiveDomain
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0)
    (hfin_pos : ∀ ⦃η : ℝ⦄, 0 < η → η ∈ effectiveDomain φ) :
    StrictMonoOn φ.asEReal (Ici (0 : ℝ)) := by
  intro ξ hξ η _hη hξη
  have hφ0 : φ.asEReal 0 = 0 := (hzero 0).2 rfl
  by_cases hξ_eq : ξ = 0
  · have hη0 : 0 < η := by
      simpa [hξ_eq] using hξη
    have hη_dom : η ∈ effectiveDomain φ := hfin_pos hη0
    have hη_value_pos : (0 : EReal) < φ.asEReal η :=
      zero_lt_value_of_pos_of_even_convexOn_eq_zero_iff φ hconv heven hzero hη0 hη_dom
    -- Split off the endpoint case `ξ = 0` before using the positive-positive argument.
    simpa [hξ_eq, hφ0] using hη_value_pos
  · have hξ0 : 0 < ξ := by
      exact lt_of_le_of_ne hξ fun h0 ↦ hξ_eq h0.symm
    have hη0 : 0 < η := lt_trans hξ0 hξη
    have hη_dom : η ∈ effectiveDomain φ := hfin_pos hη0
    -- On the interior of the ray, reuse the strict convex-combination step.
    exact strict_positive_ray_step_of_mem_effectiveDomain φ hconv heven hzero hξ0 hξη hη_dom

/-- Proposition 11.7 (4): in this `EReal` formalization, the source strict-increase clause on `ℝ₊`
is stated on the full nonnegative ray with the needed explicit finiteness hypothesis at positive
points. -/
theorem strictMonoOn_nonnegative_of_even_convexOn_eq_zero_iff
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0)
    (hfin_pos : ∀ ⦃η : ℝ⦄, 0 < η → η ∈ effectiveDomain φ) :
    StrictMonoOn φ.asEReal (Ici (0 : ℝ)) := by
  -- This wrapper is exactly the finite-positive-endpoint strict monotonicity theorem.
  exact strictMonoOn_nonnegative_of_even_convexOn_eq_zero_iff_of_pos_mem_effectiveDomain
    φ hconv heven hzero hfin_pos

/-- Helper for Proposition 11.7: evenness transports strict increase on the nonnegative ray to
strict decrease on the nonpositive ray. -/
lemma strictAntiOn_nonpositive_of_strictMonoOn_nonnegative_of_even
    (heven : Function.Even φ.asEReal)
    (hmono : StrictMonoOn φ.asEReal (Ici 0)) :
    StrictAntiOn φ.asEReal (Iic 0) := by
  intro x hx y hy hxy
  have hneg_mono : φ.asEReal (-y) < φ.asEReal (-x) := by
    -- Negation reverses the nonpositive order and sends it to the nonnegative ray.
    apply hmono
    · simpa using neg_nonneg.mpr (show y ≤ 0 from hy)
    · simpa using neg_nonneg.mpr (show x ≤ 0 from hx)
    · simpa using neg_lt_neg hxy
  simpa [heven x, heven y] using hneg_mono

/-- Helper for clause (5): if an even convex `]-∞,+∞]`-valued function on `ℝ`
vanishes only at `0` and is finite at every positive point, then it is strictly decreasing on the
nonpositive ray. -/
-- Proof sketch: transport clause (4) from the nonnegative ray by the symmetry `x ↦ -x` and use
-- evenness to turn strict increase on `[0,+∞)` into strict decrease on `(-∞,0]`.
theorem strictAntiOn_nonpositive_of_even_convexOn_eq_zero_iff_of_pos_mem_effectiveDomain
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0)
    (hfin_pos : ∀ ⦃η : ℝ⦄, 0 < η → η ∈ effectiveDomain φ) :
    StrictAntiOn φ.asEReal (Iic (0 : ℝ)) := by
  -- Route correction: clause (5) is a symmetry transport of clause (4), not a new convexity proof.
  exact strictAntiOn_nonpositive_of_strictMonoOn_nonnegative_of_even φ heven
    (strictMonoOn_nonnegative_of_even_convexOn_eq_zero_iff_of_pos_mem_effectiveDomain
      φ hconv heven hzero hfin_pos)

/-- Proposition 11.7 (5): in this `EReal` formalization, the source strict-decrease clause on `ℝ₋`
is stated on the full nonpositive ray with the needed explicit finiteness hypothesis at positive
points. -/
theorem strictAntiOn_nonpositive_of_even_convexOn_eq_zero_iff
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0)
    (hfin_pos : ∀ ⦃η : ℝ⦄, 0 < η → η ∈ effectiveDomain φ) :
    StrictAntiOn φ.asEReal (Iic (0 : ℝ)) := by
  -- This wrapper is exactly the strict antitonicity theorem with the explicit finiteness premise.
  exact strictAntiOn_nonpositive_of_even_convexOn_eq_zero_iff_of_pos_mem_effectiveDomain
    φ hconv heven hzero hfin_pos

end EvenConvexOn

end ERealFunction
