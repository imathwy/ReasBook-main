import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

local instance : HasPairing ℝ ℝ ℝ where
  pairing x y := x * y
local instance : HasPairing ℝ ℝ (WithBotTop ℝ) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item computes the Fenchel conjugate of the scalar exponential function
  `x ↦ exp x`.
- `core/canonical`: the owner is `convexConjugate` on the pairing-based layer from Defn 12.2,
  specialized here to `ℝ` with codomain `WithBotTop ℝ` via `Function.toWithBotTop`.
- `bridge/view`: the explicit branchwise target on `[0, ∞)` written by the canonical extension
  owner `Function.toWithBotTopOn`, together with the textbook scalar Fenchel-supremum formula.

Primitive data vs derived API:
- primitive source-facing data: `Real.exp : ℝ → ℝ`;
- owner theorem surface: `((Real.exp).toWithBotTop)⋆` on the chapter codomain `WithBotTop ℝ`,
  with explicit conjugate branch owner `Function.toWithBotTopOn`;
- derived specification view: the scalar `⨆` formula on `ℝ`.

Abstraction note:
- `ℝ` remains essential in this file because the statement and proof are built on the specific
  real-analytic primitives `Real.exp`, `Real.log`, and their order/derivative inequalities.
  The owner itself stays on the pairing-based abstraction layer (no `RealInnerProductSpace`
  scope on theorem surfaces).
-/

/-- For `a > 0`, the affine-defect function `x ↦ x * a - exp x` is bounded above by
`a * log a - a`. -/
private lemma exp_linear_sub_exp_le_conjugateValue {a x : ℝ} (ha : 0 < a) :
    x * a - Real.exp x ≤ a * Real.log a - a := by
  have h := Real.add_one_le_exp (x - Real.log a)
  have hmul :
      a * ((x - Real.log a) + 1) ≤ a * Real.exp (x - Real.log a) :=
    mul_le_mul_of_nonneg_left h (le_of_lt ha)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrewrite : a * Real.exp (x - Real.log a) = Real.exp x := by
    calc
      a * Real.exp (x - Real.log a)
          = a * (Real.exp x / Real.exp (Real.log a)) := by simp [Real.exp_sub]
      _ = a * (Real.exp x / a) := by simp [Real.exp_log ha]
      _ = Real.exp x := by
        field_simp [ha0]
  have hmul' : a * ((x - Real.log a) + 1) ≤ Real.exp x := by simpa [hrewrite] using hmul
  have hadd : a * (x - Real.log a) + a ≤ Real.exp x := by
    simpa [mul_add, add_assoc] using hmul'
  have hsub : a * (x - Real.log a) ≤ Real.exp x - a :=
    (le_sub_iff_add_le).2 hadd
  have hsub' : a * x - a * Real.log a ≤ Real.exp x - a := by
    simpa [mul_sub] using hsub
  have hxle : a * x ≤ Real.exp x - a + a * Real.log a := by
    have := add_le_add_right hsub' (a * Real.log a)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hxle' :
      a * x - Real.exp x ≤ (Real.exp x - a + a * Real.log a) - Real.exp x :=
    sub_le_sub_right hxle (Real.exp x)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_comm, mul_left_comm, mul_assoc] using hxle'

/-- If `a < 0`, the function `x ↦ x * a - exp x` is unbounded above. -/
private lemma exists_gt_linear_sub_exp_of_neg {a μ : ℝ} (ha : a < 0) :
    ∃ x : ℝ, μ < x * a - Real.exp x := by
  have hpos : 0 < -a := by linarith
  have hne : (-a) ≠ 0 := ne_of_gt hpos
  set t : ℝ := max ((μ + 1) / (-a)) 1
  have ht1 : 1 ≤ t := le_max_right _ _
  have htμ : (μ + 1) / (-a) ≤ t := le_max_left _ _
  have hneg : -t < 0 := by linarith
  have hexp : Real.exp (-t) < 1 := (Real.exp_lt_one_iff).2 hneg
  have hmul' : μ + 1 ≤ t * (-a) := by
    have := mul_le_mul_of_nonneg_right htμ (le_of_lt hpos)
    have hleft : ((μ + 1) / (-a)) * (-a) = μ + 1 := by
      calc
        (μ + 1) / (-a) * (-a) = (μ + 1) * (-a) / (-a) := by
          simpa using (div_mul_eq_mul_div (μ + 1) (-a) (-a))
        _ = μ + 1 := by
          simpa using (mul_div_cancel_right₀ (μ + 1) (b := -a) hne)
    simpa [hleft] using this
  refine ⟨-t, ?_⟩
  have hsub_le : μ + 1 - Real.exp (-t) ≤ t * (-a) - Real.exp (-t) :=
    sub_le_sub_right hmul' (Real.exp (-t))
  have hμlt : μ < μ + 1 - Real.exp (-t) := by
    have htmp : μ + 1 - 1 < μ + 1 - Real.exp (-t) := sub_lt_sub_left hexp (μ + 1)
    have hμ1 : μ + 1 - 1 = μ := by ring
    simpa [hμ1] using htmp
  have : μ < t * (-a) - Real.exp (-t) := lt_of_lt_of_le hμlt hsub_le
  have hta : (-t) * a = t * (-a) := by ring
  simpa [hta] using this

/-- For negative `μ`, one can force `-exp x` above `μ` by taking `x` sufficiently negative. -/
private lemma exists_gt_neg_exp_of_neg_mu {μ : ℝ} (hμ : μ < 0) :
    ∃ x : ℝ, μ < -Real.exp x := by
  have hpos : 0 < -μ / 2 := by linarith
  refine ⟨Real.log (-μ / 2), ?_⟩
  have : -Real.exp (Real.log (-μ / 2)) = μ / 2 := by
    simp [Real.exp_log hpos]
    ring
  nlinarith [this]

/-- The `xStar > 0` branch of the Fenchel conjugate formula for `x ↦ exp x`. -/
private lemma exp_convexConjugate_pos_case (xStar : ℝ) (hpos : 0 < xStar) :
    ((Real.exp).toWithBotTop)⋆ xStar =
      (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ)) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro x
    have hreal : x * xStar - Real.exp x ≤ xStar * Real.log xStar - xStar :=
      exp_linear_sub_exp_le_conjugateValue (a := xStar) (x := x) hpos
    have hE :
        (((x * xStar - Real.exp x : ℝ) : WithBotTop ℝ)) ≤
          (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ)) := by
      simpa using hreal
    simpa [Function.toWithBotTop, sub_eq_add_neg, HasPairing.pairing, mul_comm] using hE
  · have hpair_logE :
        (⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) =
          (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ)) := by
      change (((Real.log xStar * xStar : ℝ) : WithBotTop ℝ)) =
        (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ))
      simp [mul_comm]
    have hsup :
        ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) -
            (Real.exp).toWithBotTop (Real.log xStar)) ≤
          (⨆ x : ℝ, ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := by
      exact le_iSup (fun x : ℝ => ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x))
        (Real.log xStar)
    have hsub :
        (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ)) =
          ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) +
            -((xStar : ℝ) : WithBotTop ℝ)) := by
      have hreal :
          xStar * Real.log xStar - xStar = xStar * Real.log xStar + -xStar := by ring
      calc
        (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ))
            = (((xStar * Real.log xStar + -xStar : ℝ) : WithBotTop ℝ)) := by
                exact congrArg (fun t : ℝ => (t : WithBotTop ℝ)) hreal
        _ = (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ) + (((-xStar : ℝ) : WithBotTop ℝ))) := by
              simp
        _ = (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ) + -((xStar : ℝ) : WithBotTop ℝ)) := by
              exact congrArg
                (fun t : WithBotTop ℝ =>
                  (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ) + t))
                (WithBotTop.coe_neg xStar)
        _ = ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) + -((xStar : ℝ) : WithBotTop ℝ)) := by
              exact congrArg
                (fun t : WithBotTop ℝ => t + -((xStar : ℝ) : WithBotTop ℝ))
                hpair_logE.symm
    have hlog :
        ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) + -((xStar : ℝ) : WithBotTop ℝ)) =
          ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) -
            (Real.exp).toWithBotTop (Real.log xStar)) := by
      rw [show (Real.exp).toWithBotTop (Real.log xStar) = ((xStar : ℝ) : WithBotTop ℝ) by
        simp [Function.toWithBotTop, Real.exp_log hpos]]
      rfl
    calc
      (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ))
          = ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) -
              (Real.exp).toWithBotTop (Real.log xStar)) := by
              exact hsub.trans hlog
      _ ≤ (⨆ x : ℝ, ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := hsup

/-- The `xStar = 0` branch of the Fenchel conjugate formula for `x ↦ exp x`. -/
private lemma exp_convexConjugate_zero_case :
    ((Real.exp).toWithBotTop)⋆ (0 : ℝ) = (0 : WithBotTop ℝ) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro x
    have hpair0E : (⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) = 0 := by
      simp [HasPairing.pairing]
    have hreal : (0 : ℝ) - Real.exp x ≤ 0 := sub_nonpos.2 (le_of_lt (Real.exp_pos x))
    have hrealE :
        (((0 : ℝ) - Real.exp x : ℝ) : WithBotTop ℝ) ≤ (0 : WithBotTop ℝ) :=
      (WithBotTop.coe_le_coe).2 hreal
    have hE :
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x) ≤
          (0 : WithBotTop ℝ) := by
      calc
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)
            = (((0 : ℝ) - Real.exp x : ℝ) : WithBotTop ℝ) := by
                simp [Function.toWithBotTop, hpair0E]
        _ ≤ (0 : WithBotTop ℝ) := hrealE
    exact hE
  · refine (WithBotTop.le_of_forall_lt_iff_le (x := (0 : WithBotTop ℝ))
      (y := (⨆ x : ℝ,
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)))).2 ?_
    intro μ hμ
    have hμ' : ((μ : ℝ) : WithBotTop ℝ) < ((0 : ℝ) : WithBotTop ℝ) := by
      simpa using hμ
    have hμneg : μ < 0 := (WithBotTop.coe_lt_coe).1 hμ'
    rcases exists_gt_neg_exp_of_neg_mu (μ := μ) hμneg with ⟨x0, hx0⟩
    have hx0E :
        ((μ : ℝ) : WithBotTop ℝ) <
          ((⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x0) := by
      have hpair0E : (⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) = 0 := by
        simp [HasPairing.pairing]
      have hx0' : ((μ : ℝ) : WithBotTop ℝ) < (((-Real.exp x0 : ℝ) : WithBotTop ℝ)) :=
        (WithBotTop.coe_lt_coe).2 hx0
      calc
        ((μ : ℝ) : WithBotTop ℝ) < (((-Real.exp x0 : ℝ) : WithBotTop ℝ)) := hx0'
        _ = ((⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x0) := by
          simp [Function.toWithBotTop, hpair0E]
    have hle0 :
        ((⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x0) ≤
          (⨆ x : ℝ, ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := by
      exact le_iSup (fun x : ℝ =>
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) x0
    exact lt_of_lt_of_le hx0E hle0

/-- The `xStar < 0` branch of the Fenchel conjugate formula for `x ↦ exp x`. -/
private lemma exp_convexConjugate_neg_case (xStar : ℝ) (hneg : xStar < 0) :
    ((Real.exp).toWithBotTop)⋆ xStar = (⊤ : WithBotTop ℝ) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine (WithBotTop.eq_top_iff_forall_lt _).2 ?_
  intro μ
  rcases exists_gt_linear_sub_exp_of_neg (a := xStar) (μ := μ) hneg with ⟨x0, hx0⟩
  have hx0E : ((μ : ℝ) : WithBotTop ℝ) < (((x0 * xStar - Real.exp x0 : ℝ) : WithBotTop ℝ)) := by
    simpa using hx0
  have hle :
      (((x0 * xStar - Real.exp x0 : ℝ) : WithBotTop ℝ)) ≤
        (⨆ x : ℝ, ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := by
    have := le_iSup (fun x : ℝ =>
      ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) x0
    simpa [Function.toWithBotTop, sub_eq_add_neg, HasPairing.pairing, mul_comm] using this
  exact lt_of_lt_of_le hx0E hle

-- Proof sketch: split into the three cases `xStar < 0`, `xStar = 0`, and `0 < xStar`; then use
-- explicit branchwise computations of the scalar supremum `⨆ x, x * xStar - exp x`.
/-- Text 12.2.4: the Fenchel conjugate of the exponential function `x ↦ exp x` on `ℝ` is
`xStar * log xStar - xStar` for `xStar > 0`, equals `0` at `xStar = 0`, and is `+∞` for
`xStar < 0`. -/
theorem exp_fenchelConjugate_eq :
    ((Real.exp).toWithBotTop)⋆ =
      Function.toWithBotTopOn (fun xStar : ℝ ↦ xStar * Real.log xStar - xStar) (Set.Ici 0) := by
  funext xStar
  by_cases hnonneg : 0 ≤ xStar
  · rcases lt_or_eq_of_le hnonneg with hpos | hzero
    · simp [Function.toWithBotTopOn, Set.mem_Ici,
        hnonneg, hpos, exp_convexConjugate_pos_case]
    · subst hzero
      simp [Function.toWithBotTopOn, exp_convexConjugate_zero_case]
  · have hneg : xStar < 0 := lt_of_not_ge hnonneg
    simp [Function.toWithBotTopOn, Set.mem_Ici,
      hnonneg, hneg, exp_convexConjugate_neg_case]

/-- Pointwise form of `exp_fenchelConjugate_eq`. -/
theorem exp_fenchelConjugate_eq_apply (xStar : ℝ) :
    ((Real.exp).toWithBotTop)⋆ xStar =
      Function.toWithBotTopOn (fun y : ℝ ↦ y * Real.log y - y) (Set.Ici 0) xStar := by
  simpa using congrFun exp_fenchelConjugate_eq xStar

-- Proof sketch: rewrite the owner theorem by `convexConjugate_eq_iSup_pairing_sub`.
/-- Text 12.2.4 in owner `⨆` form: the same conjugate formula as
`exp_fenchelConjugate_eq`, written through the canonical pairing notation. -/
theorem exp_fenchelConjugate_eq_iSup (xStar : ℝ) :
    (⨆ x : ℝ, (⟪x, xStar⟫ₚ - (Real.exp).toWithBotTop x)) =
      Function.toWithBotTopOn (fun y : ℝ ↦ y * Real.log y - y) (Set.Ici 0) xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    exp_fenchelConjugate_eq_apply xStar

-- Proof sketch: specialize the pairing notation to scalar multiplication on `ℝ`.
/-- Text 12.2.4 in textbook scalar-supremum form: the same conjugate formula as
`exp_fenchelConjugate_eq`, written directly as the scalar Fenchel supremum on `ℝ`. -/
theorem exp_fenchelConjugate_eq_iSup_mul (xStar : ℝ) :
    (⨆ x : ℝ, (((x * xStar : ℝ) : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) =
      Function.toWithBotTopOn (fun y : ℝ ↦ y * Real.log y - y) (Set.Ici 0) xStar := by
  simpa [HasPairing.pairing, mul_comm] using exp_fenchelConjugate_eq_iSup xStar

end
