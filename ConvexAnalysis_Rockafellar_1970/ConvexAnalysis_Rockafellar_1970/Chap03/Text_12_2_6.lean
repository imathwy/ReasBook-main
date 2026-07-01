import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

local instance : HasPairing ℝ ℝ ℝ where
  pairing x y := x * y
local instance : HasPairing ℝ ℝ (WithBotTop ℝ) := instHasPairingWithBotTop

variable (p : ℝ)

/-- Source scalar branch from Text 12.2.6: `x ↦ -(1 / p) * x^p`. -/
def negRpowDiv (p : ℝ) : ℝ → ℝ :=
  fun x ↦ (-(1 / p)) * x ^ p

/-- Conjugate-side scalar branch used in Text 12.2.6: `x ↦ -(1 / q) * |x|^q`. -/
def negAbsRpowDiv (q : ℝ) : ℝ → ℝ :=
  fun x ↦ (-(1 / q)) * |x| ^ q

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item defines the one-dimensional function
  `x ↦ -(1 / p) x^p` on `[0, ∞)`, extended by `+∞` to `(-∞, 0)`, for `0 < p < 1`.
- `core/canonical`: the chapter owner abstractions are the extension-by-`+∞` owner
  `Function.toWithBotTopOn f C` from Remark 4.4.5, the Fenchel conjugate `convexConjugate` on the
  scalar pairing layer over `ℝ`, and the canonical dual exponent owner `Real.conjExponent`.
- `bridge/view`: the piecewise branch formula follows by unfolding
  `Function.toWithBotTopOn`, while the scalar Fenchel-supremum formula and the textbook
  reciprocal relation `1 / p + 1 / q = 1` are companion restatement layers of the owner theorem.

Domain-style sampling used here:
- the Chapter 1 extension-by-`+∞` owner `Function.toWithBotTopOn f C` from Remark 4.4.5;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2;
- `Real.conjExponent` from mathlib as the owner dual exponent API;
- the neighboring owner-pattern `abs_rpow_div_fenchelConjugate_eq` from Text 12.2.5;
- the scalar-source-facing patterns `exp_fenchelConjugate_eq` from Text 12.2.4 and
  `neg_sqrt_sq_sub_sq_icc_fenchelConjugate_eq` from Text 12.2.7;
- `Real.rpow` for the fractional powers `x^p` and `|xStar|^q`;
- the `WithBotTop ℝ` conventions, with `⊤` standing for `+∞`.

Primitive data vs derived API:
- primitive source-facing data: the exponent `p` with `0 < p < 1` and the scalar function itself;
- owner-side primitive theorem surface: the conjugacy formula for
  `(Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0))⋆` stated directly on `ℝ`;
- derived API: the branchwise source formula for the canonical extension owner, the scalar
  Fenchel-supremum formula, and the two-branch closed form with exponent
  `Real.conjExponent p`, plus a thin `q`-based bridge restatement.

Layer target: `source-facing`; the scalar source function already lives on the canonical owner
ambient `ℝ`, and its extension by `+∞` outside `[0, ∞)` already has the chapter owner
`Function.toWithBotTopOn f C`, so the main conjugacy result is stated directly through that owner
and `f⋆`, with the raw scalar supremum retained only as a companion specification view.

Abstraction boundary: this item remains over `ℝ` because its source formula uses
`Real.rpow` with a real exponent parameter and the canonical dual-exponent API
`Real.conjExponent`; these owners are intrinsically real-valued in the current ecosystem.
-/

-- Proof sketch: unfold the canonical extension owner `Function.toWithBotTopOn` for the real
-- branch `x ↦ -(1 / p) x^p` on `[0, ∞) = Set.Ici 0`, then simplify the two piecewise branches.
/-- The canonical `WithBotTop ℝ` owner for `x ↦ -(1 / p) x^p` on `[0, ∞)` reproduces
the source branch formula `-(1 / p) x^p` on `x ≥ 0` and `+∞` on `x < 0`. -/
@[simp] theorem neg_rpow_div_ici_eq_piecewise (x : ℝ) :
    Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0) x =
      if 0 ≤ x then
        (negRpowDiv p).toWithBotTop x
      else
        ⊤ := by
  by_cases hx : 0 ≤ x
  · simp [Function.toWithBotTopOn, Set.mem_Ici, hx, negRpowDiv]
  · simp [Function.toWithBotTopOn, Set.mem_Ici, hx, negRpowDiv]

-- Proof sketch: write the Fenchel conjugate on `ℝ` as the supremum of
-- `x * xStar + (1 / p) * x^p` over `x ≥ 0`. If `xStar ≥ 0`, the affine term forces this supremum
-- to be `+∞` as `x → +∞`. If `xStar < 0`, maximize the concave one-variable function by solving
-- `xStar + x^(p - 1) = 0`, which gives the critical point `x = |xStar|^(1 / (p - 1))`; this
-- evaluates to the canonical dual-exponent formula with `Real.conjExponent p = p / (p - 1) < 0`.
/-- Text 12.2.6: if `0 < p < 1`, then the Fenchel conjugate of the function
`x ↦ -(1 / p) x^p` on `[0, ∞)` extended by `+∞` to `(-∞, 0)`, written on the canonical
`WithBotTop ℝ` owner surface as `Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0)`,
has Fenchel conjugate given
on the same owner layer by the extension-by-`+∞` operator on `Set.Iio 0` with canonical dual
exponent `Real.conjExponent p`. -/
theorem neg_rpow_div_ici_fenchelConjugate_eq
    (hp0 : 0 < p) (hp1 : p < 1) :
    (Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0))⋆ =
      Function.toWithBotTopOn (negAbsRpowDiv (Real.conjExponent p)) (Set.Iio 0) := by
  sorry

-- Proof sketch: the reciprocal relation `1 / p + 1 / q = 1` with `0 < p < 1` determines
-- `q = Real.conjExponent p`, so the source-facing `q`-formula is a direct restatement of the
-- canonical owner theorem above.
/-- Source-facing restatement of Text 12.2.6: if `0 < p < 1` and `q` satisfies
`1 / p + 1 / q = 1`, then the Fenchel conjugate formula may be written with `q` instead of the
canonical dual exponent `Real.conjExponent p`. -/
theorem neg_rpow_div_ici_fenchelConjugate_eq_of_reciprocal_relation
    (q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hpq : 1 / p + 1 / q = 1) :
    (Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0))⋆ =
      Function.toWithBotTopOn (negAbsRpowDiv q) (Set.Iio 0) := by
  sorry

-- Proof sketch: rewrite the owner theorem by `convexConjugate_eq_iSup_pairing_sub` at the pairing
-- layer. On `ℝ`, this recovers the textbook scalar Fenchel supremum.
/-- Text 12.2.6 in textbook supremum form: the same conjugate formula as
`neg_rpow_div_ici_fenchelConjugate_eq`, expressed directly by the scalar Fenchel
supremum on `ℝ`. -/
theorem neg_rpow_div_ici_fenchelConjugate_eq_iSup
    (hp0 : 0 < p) (hp1 : p < 1) (xStar : ℝ) :
    (⨆ x : ℝ,
        (⟪x, xStar⟫ₚ -
          Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0) x)) =
      Function.toWithBotTopOn (negAbsRpowDiv (Real.conjExponent p)) (Set.Iio 0) xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    congrFun (neg_rpow_div_ici_fenchelConjugate_eq p hp0 hp1) xStar

end
