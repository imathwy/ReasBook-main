import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_12_2_7 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar

local instance : HasPairing ℝ ℝ ℝ where
  pairing x y := x * y

/-- Source scalar branch from Text 12.2.7: `x ↦ -√(a² - x²)`. -/
def negSqrtSqSubSq (a : ℝ≥0) (x : ℝ) : ℝ :=
  -Real.sqrt (a ^ 2 - x ^ 2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item defines the extended-real function on `ℝ` given by the lower
  semicircle graph `x ↦ -√(a² - x²)` on `[-a, a]` and `+∞` outside, and computes the scalar
  Fenchel supremum attached to that public source function.
- `core/canonical`: the ambient chapter owner abstractions are the extension-by-`+∞` owner
  `Function.toWithBotTopOn f C` from Remark 4.4.5 and the Fenchel conjugate `f⋆` on the scalar
  pairing layer over `ℝ`.
- `bridge/view`: the pointwise branch formula and scalar supremum formula are companion
  specification views of the owner-side conjugate identity.

Domain-style sampling used here:
- the Chapter 1 extension-by-`+∞` owner `Function.toWithBotTopOn f C` from Remark 4.4.5;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2, together with the
  chapter postfix notation `f⋆`;
- the owner-level neighboring pattern `abs_rpow_div_fenchelConjugate_eq` from Text 12.2.5 and
  the canonical extension pattern `neg_rpow_div_ici_fenchelConjugate_eq` from Text 12.2.6;
- `Real.sqrt` for the explicit semicircle profile;
- the `WithBotTop ℝ` conventions with `⊤` for `+∞`.

Primitive data vs derived API:
- primitive source-facing data: a nonnegative radius `a : ℝ≥0` and the scalar branch
  `x ↦ -√(a² - x²)` on `[-a, a]`;
- owner-side primitive theorem surface:
  `(Function.toWithBotTopOn (negSqrtSqSubSq a) (Set.Icc (-a) a))⋆`;
- derived API: the source pointwise branch formula and the scalar Fenchel-supremum identity.

Layer target: `source-facing`; the source scalar function already lives in the owner ambient `ℝ`,
and its extension by `+∞` outside `[-a, a]` already has the chapter owner
`Function.toWithBotTopOn f C`,
so this file states the main theorem directly through that canonical owner and the chapter
conjugate notation `f⋆`, while the pointwise branch formula and raw scalar supremum remain thin
specification views.

Abstraction boundary: this item remains over `ℝ` because its statement is intrinsically built from
`Real.sqrt` and the ordered interval owner `Set.Icc (-a) a`; the exact source formula is not
available over a weaker scalar layer in the current ecosystem.
-/

-- Proof sketch: specialize the canonical extension-by-`+∞` bridge
-- owner `Function.toWithBotTopOn` to the real branch `x ↦ -√(a² - x²)` and the interval
-- `[-a, a]`, then unfold membership in `Set.Icc (-a) a` as `|x| ≤ a`.
/-- The canonical extension-by-`+∞` owner for `x ↦ -√(a² - x²)` on `[-a, a]` reproduces the
source branch formula `-√(a² - x²)` on `|x| ≤ a` and `+∞` outside `[-a, a]`. -/
@[simp] theorem neg_sqrt_sq_sub_sq_icc_eq_piecewise (a : ℝ≥0) (x : ℝ) :
    Function.toWithBotTopOn (negSqrtSqSubSq a) (Set.Icc (-a) a) x =
      if |x| ≤ a then
        (negSqrtSqSubSq a).toWithBotTop x
      else
        ⊤ := by
  simp [Function.toWithBotTopOn, negSqrtSqSubSq, Set.piecewise, Set.mem_Icc, abs_le]

-- Proof sketch: write the Fenchel conjugate as the supremum of
-- `x * xStar + √(a² - x²)` over `|x| ≤ a`, since the function is `⊤` outside this interval. Use
-- the substitution `x = a * sin θ` with `θ ∈ [-π/2, π/2]`, which turns the objective into
-- `a * (xStar * sin θ + cos θ)`. The maximum of `A * sin θ + B * cos θ` is `√(A² + B²)`, giving
-- the value `a * √(1 + xStar²)`.
/-- Text 12.2.7: for a nonnegative radius `a`, if `f` is the function
`x ↦ -√(a² - x²)` on `[-a, a]` with value `+∞` outside, written on the canonical owner surface
`Function.toWithBotTopOn (negSqrtSqSubSq a) (Set.Icc (-a) a)`, then its Fenchel conjugate is
`xStar ↦ a * √(1 + xStar²)`. -/
theorem neg_sqrt_sq_sub_sq_icc_fenchelConjugate_eq (a : ℝ≥0) :
    (Function.toWithBotTopOn (negSqrtSqSubSq a) (Set.Icc (-a) a))⋆ =
      (fun xStar : ℝ ↦ a * Real.sqrt (1 + xStar ^ 2)).toWithBotTop := by
  sorry

-- Proof sketch: rewrite `neg_sqrt_sq_sub_sq_icc_fenchelConjugate_eq` by
-- `convexConjugate_eq_iSup_pairing_sub` on the scalar pairing layer over `ℝ` to recover the
-- textbook Fenchel supremum directly.
/-- Text 12.2.7 in textbook scalar-supremum form: the same conjugate formula as
`neg_sqrt_sq_sub_sq_icc_fenchelConjugate_eq`, written directly as the scalar Fenchel supremum on
`ℝ`. -/
theorem neg_sqrt_sq_sub_sq_icc_fenchelConjugate_eq_iSup (a : ℝ≥0) (xStar : ℝ) :
    (⨆ x : ℝ,
        (⟪x, xStar⟫ₚ -
          Function.toWithBotTopOn (negSqrtSqSubSq a) (Set.Icc (-a) a) x)) =
      (fun y : ℝ ↦ a * Real.sqrt (1 + y ^ 2)).toWithBotTop xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    congrFun (neg_sqrt_sq_sub_sq_icc_fenchelConjugate_eq a) xStar

end

/-! ### Text_12_2_8 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar

local instance : HasPairing ℝ ℝ ℝ where
  pairing x y := x * y
local instance : HasPairing ℝ ℝ (WithBotTop ℝ) := instHasPairingWithBotTop

/-- Source scalar branch from Text 12.2.8: `x ↦ -log x - 1 / 2`. -/
def negLogSubHalf (x : ℝ) : ℝ :=
  -Real.log x - (1 / 2 : ℝ)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.8 computes the Fenchel conjugate of the one-variable function
  `x ↦ -log x - 1 / 2` on `(0, ∞)`, extended by `+∞` to `(-∞, 0]`.
- `core/canonical`: the owner declarations are the chapter extension-by-`+∞` owner
  `Function.toWithBotTopOn f C` on the scalar `WithBotTop ℝ` layer and the Fenchel conjugate
  `convexConjugate`, both of which already apply canonically on `ℝ`.
- `bridge/view`: `Function.toWithBotTopOn_eq_add_indicator` identifies this owner with the
  source surface `f.toWithBotTop + δ(· | C)`, while the piecewise branch theorem and the
  scalar Fenchel-supremum formula is the direct specification view of the owner-side conjugacy
  identity on `ℝ`.

Domain-style sampling used here:
- the Chapter 1 extension-by-`+∞` owner `Function.toWithBotTopOn f C` and its bridge
  `Function.toWithBotTopOn_eq_add_indicator` from Remark 4.4.5;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2;
- the scalar-source-facing neighboring patterns from Texts 12.2.4, 12.2.6, and 12.2.7;
- `Real.log` for the primal formula and the optimizer `x = -1 / xStar`;
- the `WithBotTop ℝ` order and arithmetic conventions, with `⊤` representing `+∞`.

Primitive data vs derived API:
- primitive source-facing data: the scalar branch `x ↦ -Real.log x - 1 / 2` on `Set.Ioi 0`;
- owner-side primitive theorem surface: the conjugacy formula for the canonical extension
  `(Function.toWithBotTopOn (fun x ↦ -Real.log x - 1 / 2) (Set.Ioi (0 : ℝ)))⋆`;
- derived API: the source piecewise branch formula and
  the scalar Fenchel-supremum restatement.

Layer target: `source-facing`; the scalar source function already lives on the canonical owner
ambient `ℝ`, and its extension by `+∞` outside `(0, ∞)` already has the chapter owner
`Function.toWithBotTopOn f C`, so the main conjugacy result is stated directly through that owner
and `f⋆`, with the pointwise and scalar supremum identities retained only as companion views.
-/

-- Proof sketch: unfold `Function.toWithBotTopOn` for the real branch `x ↦ -log x - 1 / 2`
-- and the set `Set.Ioi 0`, then rewrite membership in `Set.Ioi 0` as the scalar inequality
-- `0 < x`.
/-- The canonical `WithBotTop ℝ` owner for `x ↦ -log x - 1 / 2` on `(0, ∞)` reproduces the source
piecewise formula `-log x - 1 / 2` on `x > 0` and `+∞` on `x ≤ 0`. -/
@[simp] theorem neg_log_sub_half_ioi_eq_piecewise (x : ℝ) :
    negLogSubHalf.toWithBotTopOn (Set.Ioi (0 : ℝ)) x =
      if 0 < x then
        (negLogSubHalf).toWithBotTop x
      else
        ⊤ := by
  by_cases hx : 0 < x
  · have hxmem : x ∈ Set.Ioi (0 : ℝ) := by simpa [Set.mem_Ioi] using hx
    simp [Function.toWithBotTopOn, hx, hxmem]
  · have hxmem : x ∉ Set.Ioi (0 : ℝ) := by simpa [Set.mem_Ioi] using hx
    simp [Function.toWithBotTopOn, hx, hxmem]

/-- The canonical `WithBotTop ℝ` owner for `xStar ↦ -log (-xStar) - 1 / 2` on `(-∞, 0)` reproduces
the source branch formula on `xStar < 0` and gives `+∞` on `xStar ≥ 0`. -/
@[simp] theorem neg_log_neg_sub_half_iio_eq_piecewise (xStar : ℝ) :
    (fun y : ℝ ↦ -Real.log (-y) - (1 / 2 : ℝ)).toWithBotTopOn (Set.Iio (0 : ℝ)) xStar =
      if xStar < 0 then
        (fun y : ℝ ↦ -Real.log (-y) - (1 / 2 : ℝ)).toWithBotTop xStar
      else
        ⊤ := by
  by_cases hx : xStar < 0
  · have hxmem : xStar ∈ Set.Iio (0 : ℝ) := by simpa [Set.mem_Iio] using hx
    simp [Function.toWithBotTopOn, hx, hxmem]
  · have hxmem : xStar ∉ Set.Iio (0 : ℝ) := by simpa [Set.mem_Iio] using hx
    simp [Function.toWithBotTopOn, hx, hxmem]

private lemma neg_coe_add_coe (a b : ℝ) :
    -(((a + b : ℝ) : WithBotTop ℝ)) = (((-a - b : ℝ) : WithBotTop ℝ)) := by
  have h1 : ((a : WithBotTop ℝ) ≠ ⊥) ∨ ((b : WithBotTop ℝ) ≠ ⊤) := by
    left
    exact WithBotTop.coe_ne_bot a
  have h2 : ((a : WithBotTop ℝ) ≠ ⊤) ∨ ((b : WithBotTop ℝ) ≠ ⊥) := by
    left
    exact WithBotTop.coe_ne_top a
  calc
    -(((a + b : ℝ) : WithBotTop ℝ)) = -((a : WithBotTop ℝ) + (b : WithBotTop ℝ)) := by simp
    _ = (-(a : WithBotTop ℝ) - (b : WithBotTop ℝ)) := by
      convert (WithBotTop.neg_add h1 h2) using 1
    _ = (((-a - b : ℝ) : WithBotTop ℝ)) := by rfl

private lemma neg_coe_sub_eq (a b : ℝ) :
    (-(a : WithBotTop ℝ) - (b : WithBotTop ℝ)) = (((-a - b : ℝ) : WithBotTop ℝ)) := by
  have h1 : ((a : WithBotTop ℝ) ≠ ⊥) ∨ ((b : WithBotTop ℝ) ≠ ⊤) := by
    left
    exact WithBotTop.coe_ne_bot a
  have h2 : ((a : WithBotTop ℝ) ≠ ⊤) ∨ ((b : WithBotTop ℝ) ≠ ⊥) := by
    left
    exact WithBotTop.coe_ne_top a
  calc
    (-(a : WithBotTop ℝ) - (b : WithBotTop ℝ))
        = -((a : WithBotTop ℝ) + (b : WithBotTop ℝ)) := by
            simpa using (WithBotTop.neg_add h1 h2).symm
    _ = (((-a - b : ℝ) : WithBotTop ℝ)) := by
            simpa using (neg_coe_add_coe a b)

private lemma neg_neg_log_term (x : ℝ) :
    -(-WithBotTop.coe (Real.log x) + -(WithBotTop.coe 2)⁻¹) =
      ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x) : WithBotTop ℝ) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (neg_coe_add_coe (-Real.log x) (-(1 / 2 : ℝ)))

private lemma neg_log_rhs_eq (xStar : ℝ) :
    (-WithBotTop.coe (Real.log xStar) + -(WithBotTop.coe 2)⁻¹ : WithBotTop ℝ) =
      (((-Real.log xStar - (1 / 2 : ℝ) : ℝ) : WithBotTop ℝ)) := by
  have htwo : ((2 : ℝ)⁻¹ = (1 / 2 : ℝ)) := by
    norm_num
  calc
    (-WithBotTop.coe (Real.log xStar) + -(WithBotTop.coe 2)⁻¹ : WithBotTop ℝ)
        = (-(Real.log xStar : WithBotTop ℝ) - (((2 : ℝ)⁻¹ : ℝ) : WithBotTop ℝ)) := by rfl
    _ = (((-Real.log xStar - (2 : ℝ)⁻¹ : ℝ) : WithBotTop ℝ)) :=
          neg_coe_sub_eq (Real.log xStar) ((2 : ℝ)⁻¹)
    _ = (((-Real.log xStar - (1 / 2 : ℝ) : ℝ) : WithBotTop ℝ)) := by
          exact congrArg (fun t : ℝ => ((-Real.log xStar - t : ℝ) : WithBotTop ℝ)) htwo

private lemma neg_log_sub_half_term_eq_of_pos (x xStar : ℝ) (hx : 0 < x) :
    ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
      Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x) =
      (↑↑x * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x)) : WithBotTop ℝ) := by
  calc
    ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
      Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x)
        = (↑↑x * ↑↑xStar + -(-WithBotTop.coe (Real.log x) + -(WithBotTop.coe 2)⁻¹) : WithBotTop ℝ) := by
          simp [Function.toWithBotTopOn, Function.toWithBotTop, Set.mem_Ioi, hx, negLogSubHalf,
            HasPairing.pairing, sub_eq_add_neg]
          rfl
    _ = (↑↑x * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x) : WithBotTop ℝ)) := by
          rw [neg_neg_log_term x]

-- Proof sketch: split into the cases `xStar < 0` and `0 ≤ xStar`. For `0 ≤ xStar`, letting
-- `x → +∞` makes `x * xStar + log x + 1 / 2` diverge to `+∞`. For `xStar < 0`, the objective
-- `x ↦ x * xStar + log x + 1 / 2` is strictly concave on `(0, ∞)`; its derivative vanishes at
-- `x = -1 / xStar`, and substituting this maximizer yields `-log (-xStar) - 1 / 2`.
/-- Text 12.2.8: the Fenchel conjugate of the function `x ↦ -log x - 1 / 2` on `(0, ∞)` extended
by `+∞` to `(-∞, 0]`, written directly on the canonical extension owner
`Function.toWithBotTopOn`, has conjugate equal to the canonical extension owner on `(-∞, 0)`. -/
theorem neg_log_sub_half_ioi_fenchelConjugate_eq :
    (negLogSubHalf.toWithBotTopOn (Set.Ioi (0 : ℝ)))⋆ =
      (fun xStar : ℝ ↦ -Real.log (-xStar) - (1 / 2 : ℝ)).toWithBotTopOn (Set.Iio (0 : ℝ)) := by
  funext xStar
  by_cases hneg : xStar < 0
  · have hlogneg : Real.log (-xStar) = Real.log xStar := by
      simpa using (Real.log_neg_eq_log (le_of_lt hneg))
    have hrhs :
        Function.toWithBotTopOn
          (fun xStar : ℝ ↦ -Real.log (-xStar) - (1 / 2 : ℝ)) (Set.Iio (0 : ℝ)) xStar =
          (((-Real.log (-xStar) - (1 / 2 : ℝ) : ℝ) : WithBotTop ℝ)) := by
      simp [Function.toWithBotTopOn, Set.mem_Iio, hneg]
    rw [convexConjugate_eq_iSup_pairing_sub, hrhs]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro x
      by_cases hx : 0 < x
      · have hmulpos : 0 < x * (-xStar) := mul_pos hx (neg_pos.2 hneg)
        have hx0 : x ≠ 0 := ne_of_gt hx
        have hxstar0 : -xStar ≠ 0 := by linarith
        have hlog0 : Real.log (x * (-xStar)) ≤ x * (-xStar) - 1 :=
          Real.log_le_sub_one_of_pos hmulpos
        have hlog : Real.log x + Real.log (-xStar) ≤ x * (-xStar) - 1 := by
          rw [Real.log_mul hx0 hxstar0] at hlog0
          exact hlog0
        have hreal : x * xStar + ((2 : ℝ)⁻¹ + Real.log x) ≤ -Real.log xStar + -((2 : ℝ)⁻¹) := by
          have hlog' : Real.log x + Real.log xStar ≤ x * (-xStar) - 1 := by
            simpa [hlogneg] using hlog
          nlinarith
        have hE :
            (↑↑x * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x)) : WithBotTop ℝ)
              ≤ (-WithBotTop.coe (Real.log xStar) + -(WithBotTop.coe 2)⁻¹ : WithBotTop ℝ) :=
          (WithBotTop.coe_le_coe).2 hreal
        calc
          ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
            Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x)
              = (↑↑x * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x)) : WithBotTop ℝ) :=
                neg_log_sub_half_term_eq_of_pos x xStar hx
          _ ≤ (-WithBotTop.coe (Real.log xStar) + -(WithBotTop.coe 2)⁻¹ : WithBotTop ℝ) := hE
          _ = (((-Real.log (-xStar) - (1 / 2 : ℝ) : ℝ) : WithBotTop ℝ)) := by
                rw [neg_log_rhs_eq xStar, hlogneg]
      · have hxmem : x ∉ Set.Ioi (0 : ℝ) := by simpa [Set.mem_Ioi] using hx
        have hxbot :
            ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
              Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x) = (⊥ : WithBotTop ℝ) := by
          simp [Function.toWithBotTopOn, hxmem]
        rw [hxbot]
        exact bot_le
    · let x0 : ℝ := (-xStar)⁻¹
      have hx0 : 0 < x0 := by
        dsimp [x0]
        exact inv_pos.mpr (neg_pos.2 hneg)
      have hmul0 : x0 * xStar = -1 := by
        have hmulneg : x0 * (-xStar) = 1 := by
          dsimp [x0]
          field_simp [show (-xStar) ≠ 0 by linarith, show xStar ≠ 0 by linarith]
        calc
          x0 * xStar = -(x0 * (-xStar)) := by ring
          _ = -1 := by simp [hmulneg]
      have hlogx0 : Real.log x0 = -Real.log xStar := by
        have hloginv : Real.log x0 = -Real.log (-xStar) := by
          dsimp [x0]
          simpa using (Real.log_inv (-xStar))
        simpa [hlogneg] using hloginv
      have hreal0 : x0 * xStar + ((2 : ℝ)⁻¹ + Real.log x0) = -Real.log xStar + -((2 : ℝ)⁻¹) := by
        nlinarith [hmul0, hlogx0]
      have hE0 :
          (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ)
            = (-WithBotTop.coe (Real.log xStar) + -(WithBotTop.coe 2)⁻¹ : WithBotTop ℝ) :=
        congrArg (fun t : ℝ => (t : WithBotTop ℝ)) hreal0
      have hterm0 :
          ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
            Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) =
              (((-Real.log (-xStar) - (1 / 2 : ℝ) : ℝ) : WithBotTop ℝ)) := by
        calc
          ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
            Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0)
              = (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ) :=
                neg_log_sub_half_term_eq_of_pos x0 xStar hx0
          _ = (-WithBotTop.coe (Real.log xStar) + -(WithBotTop.coe 2)⁻¹ : WithBotTop ℝ) := hE0
          _ = (((-Real.log (-xStar) - (1 / 2 : ℝ) : ℝ) : WithBotTop ℝ)) := by
                rw [neg_log_rhs_eq xStar, hlogneg]
      calc
        (((-Real.log (-xStar) - (1 / 2 : ℝ) : ℝ) : WithBotTop ℝ))
            = ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
                Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) := hterm0.symm
        _ ≤ ⨆ x : ℝ,
              ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
                Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x) :=
            le_iSup
              (fun x : ℝ =>
                ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
                  Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x))
              x0
  · have hnonneg : 0 ≤ xStar := le_of_not_gt hneg
    have hrhs :
        Function.toWithBotTopOn
          (fun xStar : ℝ ↦ -Real.log (-xStar) - (1 / 2 : ℝ)) (Set.Iio (0 : ℝ)) xStar =
          (⊤ : WithBotTop ℝ) := by
      simp [Function.toWithBotTopOn, Set.mem_Iio, hneg]
    rw [convexConjugate_eq_iSup_pairing_sub, hrhs]
    refine (WithBotTop.eq_top_iff_forall_lt _).2 ?_
    intro μ
    by_cases hzero : xStar = 0
    · let x0 : ℝ := Real.exp μ
      have hx0 : 0 < x0 := by
        dsimp [x0]
        exact Real.exp_pos μ
      have hhalf : (0 : ℝ) < (2 : ℝ)⁻¹ := by
        norm_num
      have hμreal : μ < x0 * xStar + ((2 : ℝ)⁻¹ + Real.log x0) := by
        subst hzero
        dsimp [x0]
        have hμlt : μ < μ + (2 : ℝ)⁻¹ := by
          nlinarith [hhalf]
        simpa [Real.log_exp] using hμlt
      have hμE :
          ((μ : ℝ) : WithBotTop ℝ) <
            (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ) :=
        (WithBotTop.coe_lt_coe).2 hμreal
      have hterm0 :
          ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
            Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) =
            (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ) :=
        neg_log_sub_half_term_eq_of_pos x0 xStar hx0
      have hμltterm :
          ((μ : ℝ) : WithBotTop ℝ) <
            ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
              Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) := by
        calc
          ((μ : ℝ) : WithBotTop ℝ)
              < (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ) :=
                hμE
          _ = ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
                Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) := hterm0.symm
      have hx0le :
          ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
            Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) ≤
              (⨆ x : ℝ,
                ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
                  Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x)) :=
        le_iSup
          (fun x : ℝ =>
            ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
              Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x))
          x0
      exact lt_of_lt_of_le hμltterm hx0le
    · have hpos : 0 < xStar := lt_of_le_of_ne hnonneg (Ne.symm hzero)
      let x0 : ℝ := max ((μ + 1) / xStar) 1
      have hx01 : (1 : ℝ) ≤ x0 := by
        dsimp [x0]
        exact le_max_right _ _
      have hx0 : 0 < x0 := lt_of_lt_of_le (by norm_num) hx01
      have hmul : μ + 1 ≤ x0 * xStar := by
        have hdiv : (μ + 1) / xStar ≤ x0 := by
          dsimp [x0]
          exact le_max_left _ _
        have hmul' := mul_le_mul_of_nonneg_right hdiv (le_of_lt hpos)
        have hcancel : ((μ + 1) / xStar) * xStar = μ + 1 := by
          field_simp [ne_of_gt hpos]
        simpa [hcancel] using hmul'
      have hlognonneg : 0 ≤ Real.log x0 := Real.log_nonneg hx01
      have hhalf : (0 : ℝ) < (2 : ℝ)⁻¹ := by
        norm_num
      have hμreal : μ < x0 * xStar + ((2 : ℝ)⁻¹ + Real.log x0) := by
        nlinarith [hmul, hlognonneg, hhalf]
      have hμE :
          ((μ : ℝ) : WithBotTop ℝ) <
            (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ) :=
        (WithBotTop.coe_lt_coe).2 hμreal
      have hterm0 :
          ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
            Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) =
            (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ) :=
        neg_log_sub_half_term_eq_of_pos x0 xStar hx0
      have hμltterm :
          ((μ : ℝ) : WithBotTop ℝ) <
            ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
              Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) := by
        calc
          ((μ : ℝ) : WithBotTop ℝ)
              < (↑↑x0 * ↑↑xStar + ((WithBotTop.coe 2)⁻¹ + WithBotTop.coe (Real.log x0)) : WithBotTop ℝ) :=
                hμE
          _ = ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
                Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) := hterm0.symm
      have hx0le :
          ((⟪x0, xStar⟫ₚ : WithBotTop ℝ) -
            Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x0) ≤
              (⨆ x : ℝ,
                ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
                  Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x)) :=
        le_iSup
          (fun x : ℝ =>
            ((⟪x, xStar⟫ₚ : WithBotTop ℝ) -
              Function.toWithBotTopOn negLogSubHalf (Set.Ioi (0 : ℝ)) x))
          x0
      exact lt_of_lt_of_le hμltterm hx0le

/-- Text 12.2.8 in pointwise form: evaluating
`(negLogSubHalf.toWithBotTopOn (Set.Ioi 0))⋆` recovers the owner-side branch function from
`neg_log_sub_half_ioi_fenchelConjugate_eq`. -/
theorem neg_log_sub_half_ioi_fenchelConjugate_eq_apply (xStar : ℝ) :
    (negLogSubHalf.toWithBotTopOn (Set.Ioi (0 : ℝ)))⋆ xStar =
      (fun y : ℝ ↦ -Real.log (-y) - (1 / 2 : ℝ)).toWithBotTopOn (Set.Iio (0 : ℝ)) xStar := by
  simpa using congrFun neg_log_sub_half_ioi_fenchelConjugate_eq xStar

/-- Text 12.2.8 in pointwise textbook branch form: evaluating
`(negLogSubHalf.toWithBotTopOn (Set.Ioi 0))⋆` gives the same explicit `if`-formula as
`neg_log_sub_half_ioi_fenchelConjugate_eq`. -/
theorem neg_log_sub_half_ioi_fenchelConjugate_eq_apply_piecewise (xStar : ℝ) :
    (negLogSubHalf.toWithBotTopOn (Set.Ioi (0 : ℝ)))⋆ xStar =
      if xStar < 0 then
        (fun y : ℝ ↦ -Real.log (-y) - (1 / 2 : ℝ)).toWithBotTop xStar
      else
        ⊤ := by
  simpa [neg_log_neg_sub_half_iio_eq_piecewise] using
    neg_log_sub_half_ioi_fenchelConjugate_eq_apply xStar

/-- Text 12.2.8 in textbook scalar-supremum form: the Fenchel conjugate of the function
`x ↦ -log x - 1 / 2` on `(0, ∞)` extended by `+∞` to `(-∞, 0]`, written canonically as
`negLogSubHalf.toWithBotTopOn (Set.Ioi 0)`, is the same owner-side branch function as
`neg_log_sub_half_ioi_fenchelConjugate_eq`, written directly as the scalar Fenchel supremum on
`ℝ`. -/
theorem neg_log_sub_half_ioi_fenchelConjugate_eq_iSup (xStar : ℝ) :
    (⨆ x : ℝ,
      (⟪x, xStar⟫ₚ -
        negLogSubHalf.toWithBotTopOn (Set.Ioi (0 : ℝ)) x)) =
      (fun y : ℝ ↦ -Real.log (-y) - (1 / 2 : ℝ)).toWithBotTopOn (Set.Iio (0 : ℝ)) xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    neg_log_sub_half_ioi_fenchelConjugate_eq_apply xStar

/-- Text 12.2.8 in textbook scalar-supremum branch form: the same conjugate formula as
`neg_log_sub_half_ioi_fenchelConjugate_eq_iSup`, displayed with explicit `if` branches. -/
theorem neg_log_sub_half_ioi_fenchelConjugate_eq_iSup_piecewise (xStar : ℝ) :
    (⨆ x : ℝ,
      (⟪x, xStar⟫ₚ -
        negLogSubHalf.toWithBotTopOn (Set.Ioi (0 : ℝ)) x)) =
      if xStar < 0 then
        (fun y : ℝ ↦ -Real.log (-y) - (1 / 2 : ℝ)).toWithBotTop xStar
      else
        ⊤ := by
  simpa [neg_log_neg_sub_half_iio_eq_piecewise] using
    neg_log_sub_half_ioi_fenchelConjugate_eq_iSup xStar

end

/-! ### Text_12_2_9 (from Chap03) -/
noncomputable section

universe u w

section

open LinearMap.BilinMap
open scoped Rockafellar

variable {𝕜 : Type w} [Field 𝕜] [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]
variable [SupSet (WithTopBot 𝕜)]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.9 exhibits the Euclidean quadratic
  `x ↦ (1 / 2) ⟪x, x⟫` as a Fenchel-conjugation fixed point, specialized in the source to `R^n`.
- `core/canonical`: the owner constructions already present in the chapter are
  `convexConjugate`, its postfix notation `f⋆`, the canonical quadratic-form owner
  `LinearMap.halfPairingQuadratic`, and the quadratic conjugacy theorem
  `LinearMap.convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse`.
- `bridge/view`: the textbook quadratic `x ↦ (1 / 2) ⟪x, x⟫` is the source-facing realization of
  the identity-endomorphism quadratic owner on inner-product spaces and is connected to that
  owner by the bridge `id_halfPairingQuadratic_eq_half_inner_self`; no public wrapper is
  introduced.

Domain-style sampling used here:
- `LinearMap.halfPairingQuadratic`;
- `LinearMap.convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse`;
- `LinearMap.IsRangePseudoinverse`;
- `convexConjugate` with notation `f⋆`.

Primitive data vs derived API:
- primitive owner-side quadratic datum:
  `LinearMap.halfPairingQuadratic (LinearMap.id : E →ₗ[𝕜] E)`;
- primitive positivity side condition: `∀ x : E, 0 ≤ (⟪x, x⟫ₚ : 𝕜)`;
- derived bridge API: on real inner-product spaces, identify the owner with
  `x ↦ (1 / 2) ⟪x, x⟫`.

Layer target: owner-first canonicalization. The primary declarations are stated on the
pairing-level owner `halfPairingQuadratic` at scalar-generic layer `𝕜`; the textbook Euclidean
quadratic appears only as a downstream bridge specialization.
-/

local notation "halfPairingId" =>
  LinearMap.halfPairingQuadratic (LinearMap.id : E →ₗ[𝕜] E)

/-- The identity-endomorphism quadratic owner from `Text_12_3_2`, viewed in `WithTopBot 𝕜`,
is fixed by Fenchel conjugation. -/
theorem convexConjugate_id_halfPairingQuadratic :
    (hpair_nonneg : ∀ x : E, 0 ≤ (⟪x, x⟫ₚ : 𝕜)) →
    halfPairingId⋆ = halfPairingId := by
  intro hpair_nonneg
  have hnonneg : ∀ x : E, 0 ≤ (⟪x, (LinearMap.id : E →ₗ[𝕜] E) x⟫ₚ : 𝕜) := by
    simpa using hpair_nonneg
  have hIdRangePinv :
      (LinearMap.id : E →ₗ[𝕜] E).IsRangePseudoinverse (LinearMap.id : E →ₗ[𝕜] E) :=
    LinearMap.id_isRangePseudoinverse
  simpa using
    (LinearMap.convexConjugate_halfPairingQuadratic_eq_of_isRangePseudoinverse_of_range_eq_top
      (T := (LinearMap.id : E →ₗ[𝕜] E))
      (T' := (LinearMap.id : E →ₗ[𝕜] E))
      hnonneg
      hIdRangePinv
      (by simp))

/-- Any function definitionally equal to the identity-endomorphism pairing quadratic owner is
Fenchel-self-conjugate. -/
theorem convexConjugate_eq_self_of_eq_id_halfPairingQuadratic
    (hpair_nonneg : ∀ x : E, 0 ≤ (⟪x, x⟫ₚ : 𝕜))
    {f : E → WithTopBot 𝕜}
    (hf : f = halfPairingId) :
    f⋆ = f := by
  simpa [hf] using convexConjugate_id_halfPairingQuadratic (hpair_nonneg := hpair_nonneg)

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "halfPairingId" =>
  LinearMap.halfPairingQuadratic (LinearMap.id : E →ₗ[ℝ] E)
local notation "halfInnerSelf" =>
  Function.toWithTopBot (fun x : E ↦ ((1 / 2 : ℝ) * ⟪x, x⟫ : ℝ))

/-- The identity-endomorphism pairing-quadratic owner from `Text_12_3_2`, in real inner-product
spaces, is exactly the textbook quadratic `x ↦ (1 / 2) ⟪x, x⟫`. -/
@[simp] theorem id_halfPairingQuadratic_eq_half_inner_self :
    halfPairingId = halfInnerSelf := sorry

/-- The textbook quadratic `x ↦ (1 / 2) ⟪x, x⟫`, viewed in `WithTopBot ℝ`, is fixed by Fenchel
conjugation. -/
theorem convexConjugate_half_inner_self :
    halfInnerSelf⋆ = halfInnerSelf := by
  have hpair_nonneg : ∀ x : E, 0 ≤ (⟪x, x⟫ₚ : ℝ) := by
    intro x
    change 0 ≤ inner ℝ x x
    exact real_inner_self_nonneg
  have hfixed : halfPairingId⋆ = halfPairingId :=
    convexConjugate_id_halfPairingQuadratic (E := E) (hpair_nonneg := hpair_nonneg)
  calc
    halfInnerSelf⋆ = halfPairingId⋆ := by rw [← id_halfPairingQuadratic_eq_half_inner_self]
    _ = halfPairingId := hfixed
    _ = halfInnerSelf := id_halfPairingQuadratic_eq_half_inner_self

/-- Any function definitionally equal to the textbook quadratic owner is Fenchel-self-conjugate.
-/
theorem convexConjugate_eq_self_of_eq_half_inner_self
    {f : E → WithTopBot ℝ}
    (hf : f = halfInnerSelf) :
    f⋆ = f := by
  simpa [hf] using convexConjugate_half_inner_self

end
