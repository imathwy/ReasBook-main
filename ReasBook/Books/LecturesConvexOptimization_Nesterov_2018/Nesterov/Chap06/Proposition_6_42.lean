import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Theorem_6_14
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open ConditionalGradientContraction

/- Proposition 6.42 lies in the Chapter 6 composite linearization-gap / Hölder lower-model domain.

Sampled owner-style declarations:
- `ConditionalGradientContraction.HolderGradientOn.upper_model` in `Proposition_6_39`, the
  gradient-side Chapter 6 owner for Hölder first-order models on a feasible set;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the auxiliary
  extended-valued chosen-dual bridge attached to a feasible base point;
- `linearModelTotalVariation` and `linearModelTotalVariationReal` in `Definition_6_59`, the
  canonical Chapter 6 `EReal` owner and its finite real-part bridge for the same composite gap
  pattern;
- `totalVariation_ge_compositeObjective_gap_and_nonneg` in
  `Text_6_4_1_Total_Variation_as_a_First_Order_Optimality_Measure`, the ambient-owner
  specialization showing that the gradient-based gap bounds the composite optimality gap;
- `initialLinearizationGap` in `Definition_6_54`, the direct downstream specialization at the
  initial point;
- mathlib `IsMinOn`, the canonical owner for minimizers on a set or, equivalently, on its subtype.

Best owner abstraction:
- source-facing: `HasHolderLowerModelOn S f x₀ g Gᵥ ν` together with the canonical gradient-owner
  surface `δ[S, f, Ψ](x₀)`;
- core/canonical: `δ[S, f, Ψ](x₀)`;
- bridge/view: `ConditionalGradientContraction.linearizedCompositeGap S Ψ g x₀`, plus the
  gradient specialization from `δ[S, f, Ψ](x₀)` to
  `g = InnerProductSpace.toDualMap ℝ E (∇ f x₀)`.

Primitive data:
- the feasible/maximization set `S`, the functions `f` and `Ψ`, the base point `x₀`, the model
  functional `g`, and the Hölder data `Gᵥ`, `ν`;
- the lower-model owner `HasHolderLowerModelOn S f x₀ g Gᵥ ν`.

Derived API:
- the reversed linearization inequality `HasHolderLowerModelOn.sub_le`;
- the supremum bound and the optimality-gap bound below.

This refinement keeps the arbitrary lower-model owner and reuses the Chapter 6 chosen-dual
bridge from `Theorem_6_14` instead of redefining it locally. The file then serves purely as a
bridge: it turns the lower-model hypothesis into supremum and optimality-gap bounds for the
chosen-dual bridge, and specializes that bridge back to the canonical Chapter 6 total variation
in the gradient case.
-/

/-- `HasHolderLowerModelOn S f x₀ g Gᵥ ν` means that `g` gives the Hölder-type affine lower
model for `f` at `x₀` on the feasible set `S`, with exponent `1 + ν` and constant `Gᵥ`. -/
def HasHolderLowerModelOn
    (S : Set E) (f : E → ℝ) (x0 : E) (g : StrongDual ℝ E) (Gv ν : ℝ) : Prop :=
  ∀ ⦃x : E⦄, x ∈ S →
    f x ≥
      f x0 + g (x - x0) -
        Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν)

namespace HasHolderLowerModelOn

-- Proof sketch: rearrange the defining lower-model inequality by moving `f x` to the right and
-- using `g (x₀ - x) = -g (x - x₀)`.
/-- A Hölder lower model yields the reversed linearization bound
`g (x₀ - x) ≤ f(x₀) - f(x) + Gᵥ ‖x - x₀‖^(1 + ν) / (1 + ν)`. -/
theorem sub_le
    {S : Set E} {f : E → ℝ} {x0 : E} {g : StrongDual ℝ E} {Gv ν : ℝ}
    (hmodel : HasHolderLowerModelOn S f x0 g Gv ν) {x : E} (hx : x ∈ S) :
    g (x0 - x) ≤
      f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) := sorry

end HasHolderLowerModelOn

open scoped Gradient TotalVariationNotation

variable {S : Set E} {f Ψ : E → ℝ} {x0 : S} {g : StrongDual ℝ E} {Gv ν : ℝ}

-- Proof sketch: the pointwise inequality from `HasHolderLowerModelOn.sub_le` gives the
-- first supremum bound after adding `Ψ x₀ - Ψ x` and taking suprema over `S`.
/-- Proposition 6.42, first clause: a Hölder affine lower model at `x₀` bounds the linearized
composite gap by the supremum of the corresponding Hölder upper-gap expression over `S`. -/
theorem linearizedCompositeGap_le_holderUpperGapSup
    (hmodel : HasHolderLowerModelOn S f x0 g Gv ν) :
    linearizedCompositeGap S Ψ g x0 ≤
      sSup
        ((fun x : E ↦
            ((f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x : ℝ) :
              EReal)) '' S) := sorry

-- Proof sketch: apply the previous supremum bound and use a minimizer `xStar` of `f + Ψ` on the
-- feasible subtype `S` to bound `f x₀ - f x + Ψ x₀ - Ψ x` by
-- `(f x₀ + Ψ x₀) - (f xStar + Ψ xStar)`. The radius condition `‖x - x₀‖ ≤ D` together with
-- `0 ≤ Gᵥ` and `0 < 1 + ν` then bounds the Hölder remainder by
-- `Gᵥ D^(1 + ν) / (1 + ν)` uniformly on `S`.
/-- Proposition 6.42, second clause: every minimizer `xStar` of `f + Ψ` on `S` bounds the
linearized composite gap by the composite optimality gap at `x₀` plus the uniform Hölder
remainder on `S`. -/
theorem linearizedCompositeGap_le_optimality_gap_add_holderError
    (hmodel : HasHolderLowerModelOn S f x0 g Gv ν)
    {xStar : S} (hxStar : IsMinOn (fun x : S ↦ f x + Ψ x) Set.univ xStar)
    {D : ℝ} (hGv : 0 ≤ Gv) (hν : 0 < 1 + ν)
    (hdiam : ∀ ⦃x : E⦄, x ∈ S → ‖x - x0‖ ≤ D) :
    linearizedCompositeGap S Ψ g x0 ≤
      (((f x0 + Ψ x0) - (f xStar + Ψ xStar) +
          Gv * Real.rpow D (1 + ν) / (1 + ν) : ℝ) : EReal) := sorry

namespace ConditionalGradientContraction

variable [CompleteSpace E]

/-- Proposition 6.42, first clause in the canonical gradient-owner form used elsewhere in
Chapter 6. -/
theorem linearModelTotalVariation_le_holderUpperGapSup
    {S : Set E} {f Ψ : E → ℝ} {x0 : S} {Gv ν : ℝ}
    (hmodel :
      HasHolderLowerModelOn S f x0 (InnerProductSpace.toDualMap ℝ E (∇ f x0)) Gv ν) :
    δ[S, f, Ψ](x0) ≤
      sSup
        ((fun x : E ↦
            ((f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x : ℝ) :
              EReal)) '' S) := by
  simpa [linearModelTotalVariation_eq_linearizedCompositeGap] using
    linearizedCompositeGap_le_holderUpperGapSup hmodel

/-- Proposition 6.42, second clause in the canonical gradient-owner form used elsewhere in
Chapter 6. -/
theorem linearModelTotalVariation_le_optimality_gap_add_holderError
    {S : Set E} {f Ψ : E → ℝ} {x0 : S} {Gv ν : ℝ}
    (hmodel :
      HasHolderLowerModelOn S f x0 (InnerProductSpace.toDualMap ℝ E (∇ f x0)) Gv ν)
    {xStar : S} (hxStar : IsMinOn (fun x : S ↦ f x + Ψ x) Set.univ xStar)
    {D : ℝ} (hGv : 0 ≤ Gv) (hν : 0 < 1 + ν)
    (hdiam : ∀ ⦃x : E⦄, x ∈ S → ‖x - x0‖ ≤ D) :
    δ[S, f, Ψ](x0) ≤
      (((f x0 + Ψ x0) - (f xStar + Ψ xStar) +
          Gv * Real.rpow D (1 + ν) / (1 + ν) : ℝ) : EReal) := by
  simpa [linearModelTotalVariation_eq_linearizedCompositeGap] using
    linearizedCompositeGap_le_optimality_gap_add_holderError hmodel hxStar hGv hν hdiam

end ConditionalGradientContraction

end
