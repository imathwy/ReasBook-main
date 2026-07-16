import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section

variable {E : Type*} [SeminormedAddCommGroup E]
variable {ι : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.5.1 specializes Theorem 16.5.3 to the finite family
  `fᵢ(x) = ‖x - aᵢ‖`, so that the conjugate of the pointwise maximum is described by a minimum
  of weighted pairings under unit-ball constraints.
- `core/canonical`: the owner abstractions are `convexConjugate`,
  Theorem 16.5.3's finite-family `StdSimplex` interface, and the norm/pairing structure reused
  from earlier Chapter 3 items.
- `bridge/view`: the textbook coefficients `λᵢ` are represented by `w : StdSimplex ℝ ι`,
  while the constraints `|xᵢ⋆| ≤ 1` become `‖xStarFamily i‖ ≤ 1`.

Domain-style sampling used here:
- `convexConjugate`;
- `StdSimplex`;
- `convexConjugate_iSup_eq_sInf_finite_convex_combinations_`
  `convexConjugate_of_common_closure_effectiveDomain`;
- `exists_finite_convex_combination_eq_convexConjugate_iSup_of_common_closure_effectiveDomain`.

Primitive data vs derived API:
- primitive data: the family of centers `a : ι → E`, with finiteness needed only when
  specializing Theorem 16.5.3;
- derived API: the source-facing owner `maximumDistanceToFamily a`, its admissible dual-value
  set, the `sInf` formula for the conjugate, the outside-the-unit-ball emptiness companion for
  that admissible set, and the minimum statement on the unit ball as an `IsLeast` assertion.

Layer target: the owner `maximumDistanceToFamily` is kept `source-facing`, but it is defined at
the weaker seminormed-additive-group layer because it only uses translated norms. The dual-value
set is a `bridge/view` item and therefore reintroduces an abstract dual owner via pairing for
its affine objective. The ambient `R^n` model and `Fin m` indexing from the prose are nonessential
here, so finite-dimensionality and finite-family assumptions are imposed only on the two
Theorem 16.5.3 specializations that actually use them.
-/

/-- The source-facing owner for the pointwise maximum of the translated norms `x ↦ ‖x - a i‖`,
implemented canonically as their pointwise supremum. -/
def maximumDistanceToFamily (a : ι → E) : E → WithBotTop ℝ :=
  fun x ↦ ⨆ i, (‖x - a i‖ : WithBotTop ℝ)

end

namespace maximumDistanceToFamily

section

variable {E EStar : Type*}
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable [SeminormedAddCommGroup EStar] [NormedSpace ℝ EStar]
variable [HasLinearPairing E EStar ℝ]
variable {ι : Type*}

/-- The admissible weighted pairing values in the dual formula for
`(maximumDistanceToFamily a)⋆ x⋆`. -/
def dualValues (a : ι → E) (xStar : EStar) : Set (WithBotTop ℝ) :=
  {r : WithBotTop ℝ |
    ∃ w : StdSimplex ℝ ι,
      ∃ xStarFamily : ι → EStar,
        w.sum (fun i wgt ↦ wgt • xStarFamily i) = xStar ∧
        (∀ i, ‖xStarFamily i‖ ≤ 1) ∧
        r = ((w.sum (fun i wgt ↦ wgt * ⟪a i, xStarFamily i⟫ₚ) : ℝ) : WithBotTop ℝ)}

section

variable [Finite ι] [FiniteDimensional ℝ E] [Nonempty ι]

/-- The conjugate of `maximumDistanceToFamily a` at `x⋆` is the infimum of the weighted
pairing values allowed by the textbook unit-ball and simplex constraints. -/
-- Proof sketch: apply Theorem 16.5.3 (2) to the family `x ↦ ‖x - a i‖`. For each summand, the
-- conjugate of the translated norm is the indicator of the dual unit ball plus the affine pairing
-- term `⟪a i, ·⟫ₚ`, so the general finite-convex-combination formula reduces to this explicit
-- admissible-value set. The unit-ball bridge is supplied by `h_norm_conj`.
theorem conjugate_eq_sInf_dualValues
    (a : ι → E) (xStar : EStar)
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ)) :
    (maximumDistanceToFamily a)⋆ xStar = sInf (dualValues a xStar) := sorry

end

-- Proof sketch: every admissible witness expresses `x⋆` as a convex combination of points in the
-- closed unit ball. Since that ball is convex, such a witness can exist only when `‖x⋆‖ ≤ 1`.
theorem dualValues_eq_empty_of_one_lt_norm
    (a : ι → E) {xStar : EStar} (hxStar : 1 < ‖xStar‖) :
    dualValues a xStar = ∅ := sorry

section

variable [Finite ι] [FiniteDimensional ℝ E] [Nonempty ι]

/-- Text 16.5.1, minimum form on the unit ball: for `f(x) = max_i ‖x - a_i‖` and `‖x⋆‖ ≤ 1`, the
conjugate value `f⋆(x⋆)` is the minimum of `∑ i λᵢ ⟪aᵢ, xᵢ⋆⟫ₚ` over all simplex weights
`w : StdSimplex ℝ ι` and vectors `xStarFamily : ι → EStar` satisfying `∑ i λᵢ xᵢ⋆ = x⋆` and
`‖xᵢ⋆‖ ≤ 1`. Outside the unit ball, `dualValues a x⋆ = ∅`, so the source `sInf` formula above
still yields the correct `⊤` value but there is no minimizing element. -/
-- Proof sketch: under `‖x⋆‖ ≤ 1`, specialize Theorem 16.5.3 (3) to the translated-norm family
-- `x ↦ ‖x - a i‖`. The resulting attaining finite-convex-combination formula lands in
-- `dualValues a x⋆`, because each translated-norm conjugate is finite exactly on the unit ball and
-- there it equals the affine pairing term `⟪a i, ·⟫ₚ`. Together with
-- `conjugate_eq_sInf_dualValues`, this
-- gives the `IsLeast` formulation of the textbook minimum claim on the finite-valued regime.
theorem isLeast_dualValues_of_norm_le_one
    (a : ι → E) {xStar : EStar} (hxStar : ‖xStar‖ ≤ 1)
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ)) :
    IsLeast (dualValues a xStar) ((maximumDistanceToFamily a)⋆ xStar) := sorry

end

end

end maximumDistanceToFamily
