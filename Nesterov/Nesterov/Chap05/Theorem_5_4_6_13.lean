import Mathlib
import Nesterov.Chap05.Definition_5_4_6_1
import Nesterov.Chap05.Definition_5_4_6_2
import Nesterov.Chap05.Definition_5_4_6_3
import Nesterov.Chap05.Definition_5_4_6_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₁ × E₃)]
  [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)]
  [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.13 lies in the subsection's cone-composition self-concordant-barrier domain.

Sampled owner declarations:
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the source-facing feasible-set owner
  for the composed cone constraint;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier owner on
  `E₁ × E₃`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for barrier
  self-concordance on an open domain;
* `coneCompositionBarrier_slice_selfConcordant_bound` from `Theorem_5_4_6_12`, the slice-level
  self-concordance estimate feeding this global barrier statement.

Best owner abstraction:
* source-facing: the composed barrier `coneCompositionBarrier F Φ ξ β` on the composed feasible
  set `coneCompositionFeasibleSet Q K ξ Q₂`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: the pointwise formula `coneCompositionBarrier_apply` and the one-variable slice
  owner used in `Theorem_5_4_6_12`.

Primitive data:
* the cone-concavity owner `IsThreeTimesContDiffConcaveOnWith Q K ξ`;
* the compatibility owner `IsBetaCompatibleWith Q K F β ξ`;
* the barrier owners on `interior Q` and `interior Q₂`;
* convexity of `Q₂` and the recession-direction hypothesis for `K × {0}`.

Derived API:
* the final barrier owner on `interior (coneCompositionFeasibleSet Q K ξ Q₂)` with parameter
  `μ + β^3 ν`.

This theorem is therefore already at the right owner level: it should state the barrier result
directly for the existing feasible-set and composed-barrier owners, not through any extra local
wrapper or duplicated set/function definition. -/

section

variable {Q : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
  {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂}
  {β μ ν : NNReal}

-- Proof sketch: combine the cone-concavity of `ξ` and its `β`-compatibility with the
-- self-concordant barriers on `Q` and `Q₂` to verify the standard self-concordance and barrier
-- parameter inequalities for `coneCompositionBarrier F Φ ξ β`, whose pointwise formula is
-- `Φ (ξ x, z) + β^3 F x`, on the interior of `coneCompositionFeasibleSet Q K ξ Q₂`. The
-- recession-direction hypothesis for `K × {0}` is used to control the barrier part inherited
-- from `Φ`, and the resulting parameter is `μ + β^3 ν`.
/-- Theorem 5.4.6.13: if `ξ` is three-times continuously differentiable and concave with respect
to the cone `K`, if `ξ` is `β`-compatible with the barrier `F` on `Q`, if `Φ` is a
`μ`-self-concordant barrier on `interior Q₂`, if `Q₂` is convex, and if every direction
`(s, 0)` with `s ∈ K` is a recession direction of `Q₂`, then the composed function
`coneCompositionBarrier F Φ ξ β (x, z) = Φ (ξ x, z) + β^3 F x` is a `(\mu + β^3 ν)`-
self-concordant barrier on
`interior (coneCompositionFeasibleSet Q K ξ Q₂)`. -/
theorem coneCompositionBarrier_isSelfConcordantBarrierOnWith
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (hp : p ∈ Q₂) (τ : ℝ) (hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) :
    IsSelfConcordantBarrierOnWith
      (interior (coneCompositionFeasibleSet Q K ξ Q₂))
      (μ + β ^ 3 * ν)
      (coneCompositionBarrier F Φ ξ β) := sorry

end

end
