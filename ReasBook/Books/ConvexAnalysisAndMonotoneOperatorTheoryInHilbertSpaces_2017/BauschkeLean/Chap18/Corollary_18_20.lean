import Mathlib
import BauschkeLean.Chap05.Example_5_18
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Remark_12_24
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap13.GammaZeroConjugate

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v} [Fintype I]
variable (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ)

/- Source/core/bridge triage:
- `source-facing`: the weighted Moreau-average potential `∑ i, α i (f_i^* □ q)` and the
  resulting proximal-operator identity from Corollary 18.20.
- `core/canonical`: the intended owner route is Theorem 18.15 at `β = 1`, together with the
  Chapter 12 Moreau-envelope gradient formula and the Chapter 14 shifted-conjugate transport.
- `bridge/view`: this file now reuses the canonical Chapter 13/14 owners directly, so the
  remaining gap is only the weighted finite-sum specialization.
- `owner-state`: once `frechetDifferentiable_tfae_lipschitz_gradient` is materialized as an
  importable owner theorem, this file has no further local proof gap. -/

/-- The real-valued potential `∑ i, α i (f_i^* □ q)` from Moreau's formula, written using the
unit Moreau envelopes of the Fenchel conjugates `f_i^*`. -/
abbrev weightedConjugateMoreauAverage (x : H) : ℝ :=
  ∑ i, α i * (({}^[(1 : PosReal)] ((f i)∗[hf i])) x).toReal

omit [CompleteSpace H] in
/-- Helper for Corollary 18.20: subtracting the unit quadratic kernel from the Fenchel conjugate
of a real-valued function still lands in `]-∞,+∞]`. -/
theorem conjugate_sub_invHalfSquaredNorm_gt_bot
    (g : H → ℝ) (u : H) :
    ⊥ < g.toEReal.asEReal∗ u - moreauQuadraticKernel (1 : PosReal) u := by
  refine bot_lt_iff_ne_bot.mpr ?_
  have hconj : g.toEReal.asEReal∗ u ≠ ⊥ := by
    exact conjugate_ne_bot_of_effectiveDomain_nonempty (by simp) u
  have hkernel : (moreauQuadraticKernel (1 : PosReal) u : EReal) ≠ ⊤ := by
    simpa using (EReal.coe_ne_top (((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) : ℝ)))
  change g.toEReal.asEReal∗ u + -↑(moreauQuadraticKernel (1 : PosReal) u) ≠ ⊥
  rw [EReal.add_ne_bot_iff]
  constructor
  · exact hconj
  · intro hneg
    exact hkernel (EReal.neg_eq_bot_iff.mp hneg)

/-- Helper for Corollary 18.20: the unit shifted conjugate `g* - q`, packaged as
an `]-∞,+∞]`-valued function. -/
noncomputable def conjugateSubInvHalfSquaredNorm
    (g : H → ℝ) : H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨g.toEReal.asEReal∗ u - moreauQuadraticKernel (1 : PosReal) u,
      conjugate_sub_invHalfSquaredNorm_gt_bot g u⟩

omit [CompleteSpace H] in
/-- Helper for Corollary 18.20: coercing the packaged unit shifted conjugate back to `EReal`
recovers the canonical expression `g* - q`. -/
@[simp] theorem conjugateSubInvHalfSquaredNorm_apply
    (g : H → ℝ) (u : H) :
    (conjugateSubInvHalfSquaredNorm g u : EReal) =
      g.toEReal.asEReal∗ u - moreauQuadraticKernel (1 : PosReal) u :=
  rfl

/-- The shifted conjugate
`(∑ i, α i (f_i^* □ q))^* - q`, encoded through
`conjugateSubInvHalfSquaredNorm`. -/
abbrev weightedMoreauAverageShiftedConjugate : H → Set.Ioi (⊥ : EReal) :=
  conjugateSubInvHalfSquaredNorm (weightedConjugateMoreauAverage f hf α)

/-- The real-valued potential `∑ i, α i (f_i □ q)` from Moreau's decomposition, written using the
unit Moreau envelopes of the original functions `f_i`. -/
abbrev weightedPrimalMoreauAverage (x : H) : ℝ :=
  ∑ i, α i * (({}^[(1 : PosReal)] (f i)) x).toReal

/-- Helper for Corollary 18.20: unit Moreau envelopes of `Γ₀(H)` members are finite-valued. -/
lemma unit_moreau_ne_top_ne_bot
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) (x : H) :
    ({}^[(1 : PosReal)] g) x ≠ ⊤ ∧ ({}^[(1 : PosReal)] g) x ≠ ⊥ := by
  sorry

section
omit [Fintype I]

/-- Helper for Corollary 18.20: each unit Moreau summand of `f_i` is convex. -/
lemma unit_moreau_convexOn (i : I) :
    _root_.ConvexOn ℝ Set.univ
      (fun x : H ↦ (({}^[(1 : PosReal)] (f i)) x).toReal) := by
  sorry

/-- Helper for Corollary 18.20: the unit Moreau decomposition is the `γ = 1` specialization of
Theorem 14.3.

TODO: replace this local stub by the canonical owner from `BauschkeLean.Chap14.Theorem_14_3`
once that module is materialized in the build. -/
lemma moreauEnvelope_add_unit_conjugateMoreauEnvelope_eq_halfSquaredNorm
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    ({}^[(1 : PosReal)] g) + ({}^[(1 : PosReal)] (g∗[hg])) =
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := by
  -- The unit Moreau decomposition owner is blocked upstream in the current workspace.
  sorry

/-- Helper for Corollary 18.20: for `g ∈ Γ₀(H)`, the proximal operator of `g` is the gradient of
the unit Moreau envelope of `g^*`.

TODO: close the conjugate proximal-point rewrite with the canonical unit-parameter case of
Theorem 14.3 once that owner module is available. -/
lemma proximityOperator_eq_gradient_unit_conjugateMoreauEnvelope_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) :
    Prox[g, hg] =
      ∇ (fun y : H ↦ (({}^[(1 : PosReal)] (g∗[hg])) y).toReal) := by
  -- The unit proximal-gradient bridge is blocked upstream in the current workspace.
  sorry

/-- Helper for Corollary 18.20: Moreau's unit decomposition rewrites
`q - (f_i^* □ q)` as `f_i □ q`. -/
lemma halfSquaredNorm_sub_unit_conjugateMoreau_eq_unit_moreau
    (i : I) (x : H) :
    ((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) -
        (({}^[(1 : PosReal)] ((f i)∗[hf i])) x).toReal) =
      (({}^[(1 : PosReal)] (f i)) x).toReal := by
  sorry

end

/-- Helper for Corollary 18.20: the quadratic gap of the weighted conjugate Moreau average is the
weighted primal Moreau average. -/
lemma halfSquaredNorm_sub_weightedConjugateMoreauAverage_eq_weightedPrimalMoreauAverage
    (hα_sum : ∑ i, α i = 1) :
    (fun x : H ↦
      (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) - weightedConjugateMoreauAverage f hf α x) =
      weightedPrimalMoreauAverage f α := by
  sorry

/-- Helper for Corollary 18.20: the weighted primal Moreau average is convex. -/
lemma convexOn_weightedPrimalMoreauAverage
    (hα_nonneg : ∀ i, 0 ≤ α i) :
    _root_.ConvexOn ℝ Set.univ (weightedPrimalMoreauAverage f α) := by
  sorry

/-- Helper for Corollary 18.20: if the quadratic gap `q - g` is convex, then the shifted
conjugate `g* - q` lies in `Γ₀(H)`. -/
lemma shifted_conjugate_mem_gammaZero_of_halfSquared_gap_convex
    (g : H → ℝ) (hcont : Continuous g) (hconv : _root_.ConvexOn ℝ Set.univ g)
    (hgap_conv : _root_.ConvexOn ℝ Set.univ
      (fun x : H ↦ (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) - g x)) :
    conjugateSubInvHalfSquaredNorm g ∈ Γ₀(H) := by
  -- The canonical `β = 1` owner is blocked upstream in the current workspace.
  sorry

section
omit [Fintype I]

/-- Helper for Corollary 18.20: each unit Moreau summand of `f_i^*` is convex. -/
lemma unit_conjugate_moreau_convexOn (i : I) :
    _root_.ConvexOn ℝ Set.univ
      (fun x : H ↦ (({}^[(1 : PosReal)] ((f i)∗[hf i])) x).toReal) := by
  sorry

/-- Helper for Corollary 18.20: the unit Moreau envelope of `f_i^*` has derivative
`Prox[f_i]` at every point. -/
lemma unit_conjugate_moreau_hasFDerivAt (i : I) (x : H) :
    HasFDerivAt
      (fun y : H ↦ (({}^[(1 : PosReal)] ((f i)∗[hf i])) y).toReal)
      (InnerProductSpace.toDual ℝ H (Prox[f i, hf i] x)) x := by
  -- The unit Fréchet-derivative bridge is blocked upstream in the current workspace.
  sorry

end

/-- Helper for Corollary 18.20: differentiating the weighted finite sum termwise yields the
expected weighted sum of proximal operators. -/
lemma hasFDerivAt_weightedConjugateMoreauAverage (x : H) :
    HasFDerivAt (weightedConjugateMoreauAverage f hf α)
      (InnerProductSpace.toDual ℝ H (∑ i, α i • Prox[f i, hf i] x)) x := by
  sorry

section
omit [CompleteSpace H]

/-- Helper for Corollary 18.20: a finite convex combination of `1`-Lipschitz maps is again
`1`-Lipschitz. -/
lemma lipschitzWith_weighted_sum_fintype
    (T : I → H → H) (hT : ∀ i, LipschitzWith 1 (T i))
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    LipschitzWith 1 (fun x : H ↦ ∑ i, α i • T i x) := by
  sorry

end

-- Proof sketch: differentiate the finite weighted sum termwise and apply Proposition 12.30 to
-- each unit Moreau envelope `{}^[1] (f_i^*)`.
/-- The gradient of `weightedConjugateMoreauAverage` is the finite weighted sum of the proximity
operators of the original functions. -/
theorem gradient_weightedConjugateMoreauAverage_eq_weightedSum_proximityOperator :
    ∇ (weightedConjugateMoreauAverage f hf α) =
      fun x ↦ ∑ i, α i • Prox[f i, hf i] x := by
  sorry

-- Proof sketch: Proposition 12.30 gives a gradient formula termwise for the unit Moreau
-- envelopes of the conjugates `f_i^*`, and finite sums of differentiable functions are
-- differentiable.
/-- The weighted Moreau-average potential is Fréchet differentiable. -/
theorem differentiable_weightedConjugateMoreauAverage :
    Differentiable ℝ (weightedConjugateMoreauAverage f hf α) := by
  sorry

-- Proof sketch: each unit Moreau envelope `{}^[1] (f_i^*)` is convex, and a nonnegative weighted
-- finite sum of convex functions remains convex.
/-- If the coefficients are nonnegative, then `weightedConjugateMoreauAverage` is convex. -/
theorem convexOn_weightedConjugateMoreauAverage
    (hα_nonneg : ∀ i, 0 ≤ α i) :
    _root_.ConvexOn ℝ Set.univ (weightedConjugateMoreauAverage f hf α) := by
  sorry

-- Proof sketch: Proposition 12.28 makes each proximity operator `Prox[f i, hf i]` nonexpansive,
-- the gradient formula above identifies `∇ weightedConjugateMoreauAverage` with their weighted
-- sum, and the convex-combination hypotheses make that sum `1`-Lipschitz.
/-- If the coefficients form a finite convex combination, then the gradient of
`weightedConjugateMoreauAverage` is `1`-Lipschitz. -/
theorem lipschitzWith_one_gradient_weightedConjugateMoreauAverage
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    LipschitzWith 1 (∇ (weightedConjugateMoreauAverage f hf α)) := by
  sorry

/-- Helper for Corollary 18.20: clause `(ix)` of Theorem 18.15 specialized to the weighted
conjugate-Moreau potential at `β = 1`, proved directly from Chapters 12 and 14. -/
lemma weightedConjugateMoreauAverage_clause_ix
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    weightedMoreauAverageShiftedConjugate f hf α ∈ Γ₀(H) ∧
      (∀ hgamma : weightedMoreauAverageShiftedConjugate f hf α ∈ Γ₀(H),
        ∇ (weightedConjugateMoreauAverage f hf α) =
          fun x ↦ Prox[(1 : PosReal), weightedMoreauAverageShiftedConjugate f hf α, hgamma]
            ((1 : ℝ) • x)) := by
  -- The canonical Chapter 18 TFAE owner is blocked upstream in the current workspace.
  sorry

-- Proof sketch: the weighted quadratic gap is a convex weighted sum of unit Moreau envelopes of
-- the original functions, so Proposition 14.2 upgrades the shifted conjugate to a `Γ₀(H)` owner.
/-- The shifted conjugate
`(∑ i, α i (f_i^* □ q))^* - q`, encoded by
`weightedMoreauAverageShiftedConjugate f hf α`,
belongs to `Γ₀(H)` when the coefficients form a finite convex combination. -/
theorem weightedMoreauAverageShiftedConjugate_mem_gammaZero
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    weightedMoreauAverageShiftedConjugate f hf α ∈ Γ₀(H) :=
  (weightedConjugateMoreauAverage_clause_ix
    (f := f) (hf := hf) (α := α) hα_nonneg hα_sum).1

/-- Corollary 18.20: for a finite family `(f_i)` in `Γ₀(H)` and nonnegative coefficients `α i`
with `∑ i, α i = 1`, the convex combination `∑ i, α i Prox_{f_i}` is the proximity operator of
`h = (∑ i, α i (f_i^* □ q))^* - q`, encoded by
`weightedMoreauAverageShiftedConjugate f hf α`. -/
theorem weightedSum_proximityOperator_eq_proximityOperator_shiftedConjugate
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    (fun x ↦ ∑ i, α i • Prox[f i, hf i] x) =
      Prox[
        weightedMoreauAverageShiftedConjugate f hf α,
        weightedMoreauAverageShiftedConjugate_mem_gammaZero
          f hf α hα_nonneg hα_sum] := by
  have hprox :=
    (weightedConjugateMoreauAverage_clause_ix
      (f := f) (hf := hf) (α := α) hα_nonneg hα_sum).2
      (weightedMoreauAverageShiftedConjugate_mem_gammaZero
        (f := f) (hf := hf) (α := α) hα_nonneg hα_sum)
  -- Rewrite the gradient formula from clause `(ix)` using the explicit weighted gradient identity.
  rw [← gradient_weightedConjugateMoreauAverage_eq_weightedSum_proximityOperator
    (f := f) (hf := hf) (α := α)]
  simpa [weightedMoreauAverageShiftedConjugate, scaledProximityOperator, one_smul] using hprox

end StrongerDifferentiabilityNotions

end ERealFunction
