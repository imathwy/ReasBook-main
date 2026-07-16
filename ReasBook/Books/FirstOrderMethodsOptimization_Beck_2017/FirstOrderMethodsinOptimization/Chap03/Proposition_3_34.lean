import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}
variable {xStar g : Fin n → ℝ}

local notation "Δ" => stdSimplex ℝ (Fin n)

/- Proposition 3.34 is a `bridge/view` item in the simplex-constrained optimality API. The
ambient owner abstraction for feasible-displacement inequalities is the Chapter 3 normal cone
`normal_cone`, while the source-facing simplex content is the scalar multiplier condition below.
The primitive data are only the simplex point `xStar`, the coordinate vector `g`, and the scalar
`μ`; the raw inequality `∀ x ∈ Δ_n, 0 ≤ gᵀ (x - xStar)` is derived from owner
`normal_cone`-membership rather than treated as a second root notion. -/

recall normal_cone

/-- The simplex multiplier condition says that a coordinate vector `g` is constant on the positive
support of `xStar` with common value `μ`, and that the remaining coordinates are bounded below by
`μ`. -/
def IsStdSimplexMultiplier
    (xStar g : Fin n → ℝ) (μ : ℝ) : Prop :=
  (∀ i : Fin n, 0 < xStar i → g i = μ) ∧
    ∀ i : Fin n, xStar i = 0 → μ ≤ g i

-- Proof sketch: for the forward implication, test the variational inequality on simplex points
-- obtained by moving a small amount of mass from one positive coordinate of `xStar` to another
-- coordinate. This shows that all coordinates of `g` on the positive support of `xStar` are equal,
-- while every coordinate of `g` on the zero support is at least that common value. For the reverse
-- implication, expand `dotProduct g (x - xStar)` and use that both `x` and `xStar` have coordinate
-- sum `1`. This is exactly the coordinate form of
-- `-dotProductEquiv ℝ (Fin n) g ∈ normal_cone (stdSimplex ℝ (Fin n)) xStar`.
/-- Proposition 3.34 in owner form: the negative Euclidean-dual vector corresponding to `g` lies in
the normal cone of the unit simplex at `xStar` if and only if `g` satisfies the scalar simplex
multiplier condition. -/
theorem neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier
    (hxStar : xStar ∈ Δ) :
    -dotProductEquiv ℝ (Fin n) g ∈ normal_cone Δ xStar ↔
      ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ := sorry

/-- Proposition 3.34: for a point `xStar` of the unit simplex `Δ_n`, the condition
`gᵀ (x - xStar) ≥ 0` for every `x ∈ Δ_n` is equivalent to the existence of a scalar `μ` such that
`g i = μ` whenever `xStar i > 0` and `μ ≤ g i` whenever `xStar i = 0`. This is the source-facing
variational-inequality view of the normal-cone statement
`neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier`. -/
theorem dotProduct_sub_nonneg_on_stdSimplex_iff_exists_multiplier
    (hxStar : xStar ∈ Δ) :
    (∀ x ∈ Δ, 0 ≤ dotProduct g (x - xStar)) ↔
      ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ := sorry

end
