import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

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
