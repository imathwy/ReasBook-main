import Nesterov.Chap02.Lemma_2_18
import Nesterov.Chap03.Definition_3_1_2_1
import Nesterov.Chap03.Definition_3_7
import Nesterov.Chap03.Lemma_3_1_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConvexAnalysis

universe u v

variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 6.1.1 lies in the finite max-type / simplex-duality domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `StdSimplex` and its weight coordinates in the chapter's finite convex-combination layer;
- the chapter's Fenchel-duality bridge `fenchelDual` in `Chap03/Definition_3_1_2_1`.

Best owner abstraction:
- source-facing: the finite max-absolute affine objective attached to a family `(a_j, b_j)`;
- core/canonical: `maxTypeObjective` together with `StdSimplex`;
- bridge/view: the `ℓ₁`-ball and signed-simplex multiplier representations of the same function.

Primitive data:
- a finite family `a : ι → E`;
- offsets `b : ι → ℝ`.

Derived API:
- the source-facing owner `piecewiseLinearObjective a b`;
- its direct finite-maximum formula;
- the `ℓ₁`-ball representation;
- the signed-simplex representation from the end of the example.

This file keeps the public owner at the actual source-facing absolute-value function
`x ↦ max_j |⟪a_j, x⟫ - b_j|`, and records the multiplier representations as separate theorem
statements rather than replacing that function by a surrogate package. -/

/-- The max-absolute affine objective attached to the finite family
`x ↦ ⟪a_j, x⟫ - b_j`. -/
def piecewiseLinearObjective (a : ι → E) (b : ι → ℝ) : E → ℝ :=
  maxTypeObjective fun j x ↦ |inner ℝ (a j) x - b j|

-- Proof sketch: unfold `piecewiseLinearObjective` through the owner
-- `maxTypeObjective`.
/-- Evaluating the max-absolute affine objective gives the finite maximum of the absolute affine
pieces. -/
theorem piecewiseLinearObjective_apply (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x - b j|) := sorry

-- Proof sketch: use the scalar identity
-- `|t| = sup {u * t | |u| ≤ 1}`, then combine the coordinate multipliers into a single point of
-- the `ℓ₁` ball in `ι → ℝ`.
/-- The max-absolute affine objective is the supremum of the corresponding linear functional over
the `ℓ₁` unit ball of coefficient vectors. -/
theorem piecewiseLinearObjective_eq_sSup_l1Ball
    (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      sSup
        ((fun u : ι → ℝ ↦ ∑ j, u j * (inner ℝ (a j) x - b j)) ''
          {u : ι → ℝ | ∑ j, |u j| ≤ 1}) := sorry

-- Proof sketch: split each signed coefficient `u j` as a difference of nonnegative parts
-- `u₁ j - u₂ j`, normalize them to total mass `1`, and identify those nonnegative parts with a
-- simplex point on the signed index set `ι ⊕ ι`.
/-- Example 6.1.1 [Chapter6_1.json:13]: the max-absolute affine objective admits the signed-simplex
representation
`f(x) = sup_{u ∈ Δ(ι ⊕ ι)} ∑_j (u(inl j) - u(inr j)) (⟪a_j, x⟫ - b_j)`. -/
theorem piecewiseLinearObjective_eq_simplexSup
    (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      sSup
        (Set.range fun u : StdSimplex ℝ (ι ⊕ ι) ↦
          ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) *
            (inner ℝ (a j) x - b j)) := sorry

end
