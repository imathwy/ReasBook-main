import Nesterov.Chap06.Definition_6_52
import Nesterov.Chap06.Definition_6_53
import Nesterov.Chap06.Proposition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient WeightSequenceNotation

universe u

section InitialLinearizationGap

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : Set E}

/- Definition 6.54 lies in the Chapter 6 conditional-gradient / linearization-gap domain.

Sampled owner-style declarations:
- `linearOptimizationOracleObjective` in `Theorem_6_11`, the chapter owner of the feasible-set
  affine-plus-regularizer objective `x ↦ ⟨s, x⟩ + Ψ(x)`;
- `IsLinearOptimizationOracle` in `Definition_6_52`, the source-facing oracle-selection owner
  built on that objective;
- `LinearOracleCompositeMethod.oraclePoint_mem_argmin` in `Algorithm_6_4`, the direct downstream
  chapter surface using `gradientWithin f Q` together with
  `linearOptimizationOracleObjective`;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the ambient
  extended-valued chosen-dual gap owner obtained after extending `Ψ : Q → ℝ` to `E`.

Best owner abstraction:
- source-facing: the initial gap `V₀` for the constrained method on the feasible subtype `Q`;
- core/canonical: `linearOptimizationOracleObjective` together with the canonical constrained
  gradient `gradientWithin f Q`;
- bridge/view: `linearizedCompositeGap Q (Function.extend Subtype.val Ψ 0)
    (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x₀)) x₀`.

Primitive data:
- the feasible set `Q`, objective `f`, regularizer `Ψ : Q → ℝ`, and starting point `x₀ : Q`.

Derived API:
- the oracle-objective supremum formula;
- the displayed affine-plus-regularizer expansion;
- the bridge to `linearizedCompositeGap`;
- reuse of the canonical Chapter 6 error-term owner `linearOptimizationOracleErrorBound`.
-/

/-- Definition 6.54: the initial linearization gap `V₀` at the starting point `x₀`, relative to
the feasible set `Q`, is the supremum over feasible points `x ∈ Q` of the drop in the Chapter 6
oracle objective `x ↦ ⟪∇_Q f(x₀), x⟫ + Ψ(x)` between `x₀` and `x`. -/
def initialLinearizationGap
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) : ℝ :=
  let s := InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)
  sSup <| Set.range fun x : Q ↦
    linearOptimizationOracleObjective s Ψ x0 - linearOptimizationOracleObjective s Ψ x

/-- `initialLinearizationGap` is the supremum of the Chapter 6 oracle-objective drop at the
starting point, formed with the canonical constrained gradient `gradientWithin f Q x₀`. -/
-- Proof sketch: unfold `initialLinearizationGap` and the local `let`-bound dual vector.
theorem initialLinearizationGap_eq_oracleObjectiveGapSup
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) :
    initialLinearizationGap Q f Ψ x0 =
      sSup (Set.range fun x : Q ↦
        linearOptimizationOracleObjective
            (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x0 -
          linearOptimizationOracleObjective
            (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x) := sorry

/-- Expanding `initialLinearizationGap Q f Ψ x₀` gives the supremum of the affine-plus-regularizer
gap values `⟪∇_Q f(x₀), x₀ - x⟫ + Ψ(x₀) - Ψ(x)` over `x ∈ Q`. -/
-- Proof sketch: rewrite both oracle-objective values, simplify the dual pairing, and rearrange
-- the resulting real expression inside the supremum.
theorem initialLinearizationGap_def
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) :
    initialLinearizationGap Q f Ψ x0 =
      sSup (Set.range fun x : Q ↦
        inner ℝ (gradientWithin f Q x0) ((x0 : E) - x) + Ψ x0 - Ψ x) := sorry

/-- `initialLinearizationGap` is the subtype-regularizer specialization of the Chapter 6 ambient
gap owner `linearizedCompositeGap`, using the canonical ambient extension
`Function.extend Subtype.val Ψ 0` and the constrained gradient `gradientWithin f Q x₀`. -/
-- Proof sketch: identify the subtype-indexed oracle-objective gap with the ambient-image
-- supremum defining `linearizedCompositeGap` after extending `Ψ` off `Q`.
theorem initialLinearizationGap_eq_linearizedCompositeGap
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) :
    (initialLinearizationGap Q f Ψ x0 : EReal) =
      ConditionalGradientContraction.linearizedCompositeGap Q
        (Function.extend Subtype.val Ψ 0)
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) x0 := sorry

end InitialLinearizationGap
