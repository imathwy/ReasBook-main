import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.5 computes the Fenchel conjugate of the scalar function
  `x ↦ (1 / p) * |x|^p` on `ℝ`.
- `core/canonical`: the chapter owner abstraction is `convexConjugate` on
  `WithBotTop ℝ`-valued functions at the pairing layer; this file uses the canonical real
  self-pairing owner provided by `HasLinearPairing`/`HasPairing`, together with its canonical
  codomain lift to `WithBotTop ℝ`.
- `bridge/view`: the scalar supremum formula and the Hölder-conjugate `q`-restatement are thin
  views of that owner theorem.

Domain-style sampling used here:
- `Function.toWithBotTop` from `Chap01.EOrder.Basic` as the canonical codomain-lift owner for
  real-valued primal functions;
- `instHasPairingWithBotTop` from `Chap01.HasPairing` as the canonical codomain lift of the
  underlying real pairing owner;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2;
- `Real.conjExponent` together with `Real.HolderConjugate.conjExponent_eq`;
- `Analysis.MeanInequalities.young_inequality` as the standard upper-bound mechanism for the
  Fenchel supremum.

Primitive data vs derived API:
- primitive inputs: the exponent `p : ℝ` with `1 < p`, and the source power function
  `absRpowDiv p`;
- owner-side primitive theorem surface: the conjugate identity for the canonical codomain lift
  `((absRpowDiv p).toWithBotTop)` stated directly on `ℝ`;
- derived API: the scalar `iSup` presentation and the explicit `q`-exponent restatement.

Layer target: `source-facing`; the public theorem is the scalar owner theorem on `ℝ`, stated
through the canonical codomain lift `Function.toWithBotTop` rather than a parallel local wrapper.
-/

/-- Source-facing power owner for Text 12.2.5: `x ↦ (1 / p) * |x|^p` on `ℝ`. -/
def absRpowDiv (p : ℝ) : ℝ → ℝ :=
  fun x ↦ (1 / p) * |x| ^ p

@[simp] private lemma pairing_real_eq_mul (x y : ℝ) :
    (⟪x, y⟫ₚ : ℝ) = x * y := by
  change inner ℝ x y = x * y
  calc
    inner ℝ x y = y * (starRingEnd ℝ) x := RCLike.inner_apply x y
    _ = y * x := by simp
    _ = x * y := by ring

@[simp] private lemma pairing_real_withBotTop_eq_mul (x y : ℝ) :
    (⟪x, y⟫ₚ : WithBotTop ℝ) = ((x * y : ℝ) : WithBotTop ℝ) :=
  congrArg (fun t : ℝ => (t : WithBotTop ℝ)) (pairing_real_eq_mul x y)

private lemma exists_eq_abs_rpow_div_fenchel_argmax
    {p xStar : ℝ} (hp : 1 < p) :
    ∃ x0 : ℝ,
      x0 * xStar - (1 / p) * |x0| ^ p =
        (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have hqgt1 : 1 < Real.conjExponent p := hpq.symm.lt
  have hqminus_nonneg : 0 ≤ Real.conjExponent p - 1 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hp0 : p ≠ 0 := by linarith
  have hmul : (Real.conjExponent p - 1) * p = Real.conjExponent p := by
    rw [Real.conjExponent]
    field_simp [hp1]
    ring_nf
  have hone : 1 - 1 / p = 1 / Real.conjExponent p := by
    rw [Real.conjExponent]
    field_simp [hp1, hp0]
  by_cases hxs : 0 ≤ xStar
  · refine ⟨xStar ^ (Real.conjExponent p - 1), ?_⟩
    have hx0_nonneg : 0 ≤ xStar ^ (Real.conjExponent p - 1) :=
      Real.rpow_nonneg hxs _
    have hxmul :
        (xStar ^ (Real.conjExponent p - 1)) * xStar = xStar ^ (Real.conjExponent p) := by
      calc
        (xStar ^ (Real.conjExponent p - 1)) * xStar
            = (xStar ^ (Real.conjExponent p - 1)) * xStar ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = xStar ^ ((Real.conjExponent p - 1) + 1) := by
              symm
              exact Real.rpow_add_of_nonneg hxs hqminus_nonneg zero_le_one
        _ = xStar ^ (Real.conjExponent p) := by ring_nf
    have hxabs :
        |xStar ^ (Real.conjExponent p - 1)| ^ p = xStar ^ (Real.conjExponent p) := by
      calc
        |xStar ^ (Real.conjExponent p - 1)| ^ p
            = (xStar ^ (Real.conjExponent p - 1)) ^ p := by simp [abs_of_nonneg hx0_nonneg]
        _ = xStar ^ ((Real.conjExponent p - 1) * p) := by
              rw [← Real.rpow_mul hxs (Real.conjExponent p - 1) p]
        _ = xStar ^ (Real.conjExponent p) := by rw [hmul]
    calc
      (xStar ^ (Real.conjExponent p - 1)) * xStar
          - (1 / p) * |xStar ^ (Real.conjExponent p - 1)| ^ p
          = xStar ^ (Real.conjExponent p) - (1 / p) * xStar ^ (Real.conjExponent p) := by
              rw [hxmul, hxabs]
      _ = (1 - 1 / p) * xStar ^ (Real.conjExponent p) := by ring
      _ = (1 / Real.conjExponent p) * xStar ^ (Real.conjExponent p) := by rw [hone]
      _ = (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
            simp [abs_of_nonneg hxs]
  · have hneg : xStar < 0 := lt_of_not_ge hxs
    set y : ℝ := -xStar
    have hy_nonneg : 0 ≤ y := by
      dsimp [y]
      linarith
    have hyPow_nonneg : 0 ≤ y ^ (Real.conjExponent p - 1) := Real.rpow_nonneg hy_nonneg _
    refine ⟨-(y ^ (Real.conjExponent p - 1)), ?_⟩
    have hy_mul : (y ^ (Real.conjExponent p - 1)) * y = y ^ (Real.conjExponent p) := by
      calc
        (y ^ (Real.conjExponent p - 1)) * y
            = (y ^ (Real.conjExponent p - 1)) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y ^ ((Real.conjExponent p - 1) + 1) := by
              symm
              exact Real.rpow_add_of_nonneg hy_nonneg hqminus_nonneg zero_le_one
        _ = y ^ (Real.conjExponent p) := by ring_nf
    have hxmul :
        (-(y ^ (Real.conjExponent p - 1))) * xStar = y ^ (Real.conjExponent p) := by
      calc
        (-(y ^ (Real.conjExponent p - 1))) * xStar
            = (-(y ^ (Real.conjExponent p - 1))) * (-y) := by simp [y]
        _ = (y ^ (Real.conjExponent p - 1)) * y := by ring
        _ = y ^ (Real.conjExponent p) := hy_mul
    have hxabs :
        |-(y ^ (Real.conjExponent p - 1))| ^ p = y ^ (Real.conjExponent p) := by
      calc
        |-(y ^ (Real.conjExponent p - 1))| ^ p
            = |y ^ (Real.conjExponent p - 1)| ^ p := by simp
        _ = (y ^ (Real.conjExponent p - 1)) ^ p := by
              simp [abs_of_nonneg hyPow_nonneg]
        _ = y ^ ((Real.conjExponent p - 1) * p) := by
              rw [← Real.rpow_mul hy_nonneg (Real.conjExponent p - 1) p]
        _ = y ^ (Real.conjExponent p) := by rw [hmul]
    calc
      (-(y ^ (Real.conjExponent p - 1))) * xStar - (1 / p) * |-(y ^ (Real.conjExponent p - 1))| ^ p
          = y ^ (Real.conjExponent p) - (1 / p) * |-(y ^ (Real.conjExponent p - 1))| ^ p := by
              rw [hxmul]
      _ = y ^ (Real.conjExponent p) - (1 / p) * y ^ (Real.conjExponent p) := by rw [hxabs]
      _ = (1 - 1 / p) * y ^ (Real.conjExponent p) := by ring
      _ = (1 / Real.conjExponent p) * y ^ (Real.conjExponent p) := by rw [hone]
      _ = (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
            simp [y, abs_of_neg hneg]

private lemma abs_rpow_div_fenchel_iSup_eq
    {p : ℝ} (hp : 1 < p) (xStar : ℝ) :
    (⨆ x : ℝ,
        (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) =
      (absRpowDiv (Real.conjExponent p)).toWithBotTop xStar := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro x
    have hreal :
        x * xStar - (1 / p) * |x| ^ p ≤
          (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
      have hyoung := Real.young_inequality x xStar hpq
      have hyoung' :
          x * xStar ≤
            (1 / p) * |x| ^ p + (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
        simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hyoung
      linarith
    have hE :
        (((x * xStar - (1 / p) * |x| ^ p : ℝ) : WithBotTop ℝ)) ≤
          (((1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) : ℝ) : WithBotTop ℝ) :=
      (WithBotTop.coe_le_coe).2 hreal
    simpa [absRpowDiv, Function.toWithBotTop, sub_eq_add_neg] using hE
  · rcases exists_eq_abs_rpow_div_fenchel_argmax (hp := hp) (xStar := xStar) with ⟨x0, hx0⟩
    have hx0E :
        (absRpowDiv (Real.conjExponent p)).toWithBotTop xStar ≤
          (⟪x0, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x0) := by
      have hreal :
          (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) ≤
            x0 * xStar - (1 / p) * |x0| ^ p := le_of_eq hx0.symm
      have hE :
          (((1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) : ℝ) : WithBotTop ℝ) ≤
            (((x0 * xStar - (1 / p) * |x0| ^ p : ℝ) : WithBotTop ℝ)) :=
        (WithBotTop.coe_le_coe).2 hreal
      simpa [absRpowDiv, Function.toWithBotTop, sub_eq_add_neg] using hE
    have hx0Sup :
        (⟪x0, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x0) ≤
          (⨆ x : ℝ, (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) :=
      le_iSup (fun x : ℝ ↦ (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) x0
    exact le_trans hx0E hx0Sup

-- Proof sketch: identify the conjugate with the scalar Fenchel supremum by
-- `convexConjugate_eq_iSup_pairing_sub`. Young's inequality bounds each affine defect by
-- `(1 / q) * |xStar| ^ q`, where `q = Real.conjExponent p`, and equality is attained at the
-- standard optimizer `x = sign xStar * |xStar| ^ (q - 1)`.
/-- Text 12.2.5: for `1 < p`, the Fenchel conjugate of `x ↦ (1 / p) * |x|^p` on `ℝ` is the power
law with canonical dual exponent `Real.conjExponent p`. -/
theorem abs_rpow_div_fenchelConjugate_eq
    {p : ℝ} (hp : 1 < p) :
    ((absRpowDiv p).toWithBotTop)⋆ =
      (absRpowDiv (Real.conjExponent p)).toWithBotTop := by
  funext xStar
  simpa [absRpowDiv, Function.toWithBotTop, convexConjugate_eq_iSup_pairing_sub] using
    abs_rpow_div_fenchel_iSup_eq (hp := hp) xStar

-- Proof sketch: rewrite the owner theorem by `convexConjugate_eq_iSup_pairing_sub`. On `ℝ`, the
-- canonical pairing is multiplication, so the supremum becomes the textbook scalar Fenchel
-- supremum.
/-- Text 12.2.5 in textbook scalar-supremum form: the same conjugate formula as
`abs_rpow_div_fenchelConjugate_eq`, written directly as the scalar Fenchel supremum on `ℝ`. -/
theorem abs_rpow_div_fenchelConjugate_eq_iSup
    {p : ℝ} (hp : 1 < p) (xStar : ℝ) :
    (⨆ x : ℝ,
        (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) =
      (absRpowDiv (Real.conjExponent p)).toWithBotTop xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    congrFun (abs_rpow_div_fenchelConjugate_eq (hp := hp)) xStar

-- Proof sketch: specialize the canonical dual-exponent owner theorem above to `hpq.lt : 1 < p`,
-- then rewrite `Real.conjExponent p` to `q` using the bridge `hpq.conjExponent_eq`.
/-- Source-facing restatement of Text 12.2.5: if `p` and `q` are Hölder-conjugate exponents, then
the Fenchel conjugate of `x ↦ (1 / p) * |x|^p` is `xStar ↦ (1 / q) * |xStar|^q`. -/
theorem abs_rpow_div_fenchelConjugate_eq_of_holderConjugate
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ((absRpowDiv p).toWithBotTop)⋆ =
      (absRpowDiv q).toWithBotTop := by
  simpa [absRpowDiv, hpq.conjExponent_eq] using abs_rpow_div_fenchelConjugate_eq hpq.lt

end
