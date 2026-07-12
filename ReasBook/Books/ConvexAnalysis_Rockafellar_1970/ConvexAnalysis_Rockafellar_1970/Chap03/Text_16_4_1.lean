import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

variable {E EStar : Type*}
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable [SeminormedAddCommGroup EStar] [NormedSpace ℝ EStar]
variable [HasPairing EStar E ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.4.1 identifies the Fenchel conjugate of the distance function
  `x ↦ d(x, C)` for a nonempty set `C`.
- `core/canonical`: the owner abstractions are mathlib's canonical point-to-set owner
  `Metric.infEDist`, the chapter Fenchel conjugate `convexConjugate`, and the support function
  `supportFunction`.
- `bridge/view`: Rockafellar's `δ*(x⋆ | C)` is `δᵛ(x⋆ | C)` on an abstract dual owner `EStar`
  paired with `E`; the condition `|x⋆| ≤ 1` is rendered by `‖xStar‖ ≤ 1` in the dual norm; the
  source notation `d(x, C)` is used directly on the theorem surface in codomain `WithBotTop ℝ`.

Domain-style sampling used here:
- `Metric.infEDist`, recalled in `Defintion_4_8_3`;
- `infimal_convolution_norm_indicator_eq_distanceToSet` from Text 5.4.1.4;
- the canonical pairing-swap indicator/support bridge
  `convexConjugate_indicatorFunction_eq_supportFunction` from Text 13.1.4;
- `convexConjugate_finiteInfimalConvolution_eq_sum` from Theorem 16.4.1, with the
  needed `⊥`-exclusion supplied at the call site.

Primitive data vs derived API:
- primitive input: only the set `C`;
- derived APIs: the owner-level conjugate decomposition and the source-facing pointwise
  `if ‖x⋆‖ ≤ 1 then ... else ...` companion (which needs nonemptiness only to eliminate
  the `⊤ + ⊥` path at points outside the unit ball).

Layer target: `core/canonical` for the main theorem (an owner-level function equality) on an
abstract paired dual owner `EStar`, with a source-facing pointwise companion theorem for the
textbook conditional form.
-/

omit [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup EStar] [NormedSpace ℝ EStar] in
private theorem bot_lt_supportFunction_of_nonempty {C : Set E} (hC_nonempty : C.Nonempty)
    (xStar : EStar) :
    (⊥ : WithBotTop ℝ) < δᵛ[WithBotTop ℝ](xStar | C) := by
  rcases hC_nonempty with ⟨y, hy⟩
  rw [supportFunction_def]
  exact lt_of_lt_of_le (WithBotTop.bot_lt_coe _)
    (le_iSup (fun z : C ↦ ((⟪xStar, (z : E)⟫ₚ : ℝ) : WithBotTop ℝ)) ⟨y, hy⟩)

-- Proof sketch: write the distance function as the infimal convolution of the norm with
-- the `0/+∞` indicator of `C` using Text 5.4.1.4. Apply Theorem 16.4.1 to that two-term infimal
-- convolution. Then rewrite the indicator conjugate as `supportFunction C` by
-- `convexConjugate_indicatorFunction_eq_supportFunction`.
variable [HasPairing E EStar ℝ] [HasPairingAddLeft E EStar ℝ] [HasPairingSwap E EStar ℝ]

/-- Text 16.4.1 at the owner layer: for any set `C`, the Fenchel conjugate of the Chapter 1
distance function (lifted from `ℝ≥0∞` to `WithBotTop ℝ` by `ENNReal.toEReal`) is the sum of the
dual unit-ball indicator and the support function of `C` on an abstract paired dual owner
`EStar`. The statement is parameterized by the norm-conjugate bridge hypothesis
`((fun x ↦ ‖x‖)⋆ = δ(· | closedBall (0 : EStar) 1))`, so the theorem surface is not tied to a
concrete dual model. -/
theorem convexConjugate_distanceToSet_eq_indicator_unitBall_add_supportFunction
    {C : Set E}
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ)) :
    ((ENNReal.toEReal ∘ (d(·, C) : E → ENNReal))⋆ : EStar → WithBotTop ℝ) =
      (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ) +
        (δᵛ[WithBotTop ℝ](· | C) : EStar → WithBotTop ℝ) := by
  sorry

-- Proof sketch: evaluate the owner-level theorem
-- `convexConjugate_distanceToSet_eq_indicator_unitBall_add_supportFunction` at `xStar`
-- and simplify the unit-ball indicator pointwise. Nonemptiness is only used outside the unit ball
-- to simplify `⊤ + δᵛ(xStar | C)` to `⊤` by excluding `δᵛ(xStar | C) = ⊥`.
/-- Source-facing pointwise companion of Text 16.4.1: if `C` is nonempty, then the conjugate of
 the distance function is `δᵛ(x⋆ | C)` on the dual closed unit ball and `+∞` outside. -/
theorem convexConjugate_distanceToSet_eq_supportFunction_if_norm_le_one_of_nonempty
    {C : Set E} (hC_nonempty : C.Nonempty)
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ))
    (xStar : EStar) :
    ((ENNReal.toEReal ∘ (d(·, C) : E → ENNReal))⋆ : EStar → WithBotTop ℝ) xStar =
      if ‖xStar‖ ≤ 1 then δᵛ[WithBotTop ℝ](xStar | C) else ⊤ := by
  sorry

end
