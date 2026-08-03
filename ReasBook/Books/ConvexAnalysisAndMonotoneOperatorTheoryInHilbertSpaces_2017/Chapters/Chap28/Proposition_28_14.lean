import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap26.Theorem_26_17

open Filter
open InnerProductSpace
open SetValuedOperator
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Proposition 28.14 is Tseng's projected forward-backward-forward algorithm for
  the convex minimization problem `min (f + g)`.
- `core/canonical`: the Chapter 26 owner API is the projected Tseng recursion given by
  `projectedForwardBackwardForwardIteration` and its predictor/resolvent/correction companions,
  together with the convergence target `((∂ f) + (∂ g)).zeros`.
- `bridge/view`: this file specializes that operator-level owner to the proximal-gradient surface
  `JγA = Prox[γ, f, hf]`, `Bf = gradg`, and the source-facing minimizer set
  `C ∩ Argmin (f + g).asEReal`.

Semantic recall: `lean_leansearch` returned only generic convexity hits here, so the statement
surface is taken directly from the Chapter 26 Tseng owner plus Chapter 12 proximal notation.
-/

section TsengAlgorithm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 28.14 (1): let `f ∈ Γ₀(H)` satisfy `(∂ f).dom ⊆ D`, let `g ∈ Γ₀(H)` be Gâteaux
differentiable on `D`, let `β ∈ ℝ_{++}`, and let `C` be a closed convex subset of `D` with
`(C ∩ Argmin (f + g).asEReal).Nonempty`. If `gradg` is `1 / β`-Lipschitz on
`C ∪ (∂ f).dom`, if `D ⊆ effectiveDomain g`, if the derivative of `(fun x ↦ (g x : EReal).toReal)`
on `D` is realized by `gradg`, and if `0 < γ < β`, then for the canonical Chapter 26 projected
forward-backward-forward specialization `JγA = Prox[γ, f, hf]`, `Bf = gradg`, the residual
sequence `(x_n - z_n)` converges strongly to `0`. -/
theorem tsengAlgorithm_sub_tendsto_zero
    {D C : Set H} {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hsubdiff_dom : (∂ f).dom ⊆ D) {gradg : H → H}
    (hD_dom : D ⊆ effectiveDomain g)
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (g x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradg x)) D)
    (β : Set.Ioi (0 : ℝ)) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hC_argmin : (C ∩ Argmin (f + g).asEReal).Nonempty)
    (hgrad_lipschitz :
      LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg (C ∪ (∂ f).dom))
    (γ : Set.Ioi (0 : ℝ)) (hγ_lt : (γ : ℝ) < β) (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    let x := projectedForwardBackwardForwardIteration (Prox[γ, f, hf]) gradg C hC γ x0
    let z := projectedForwardBackwardForwardResolventSequence (Prox[γ, f, hf]) gradg C hC γ x0
    Tendsto (fun n ↦ x n - z n) atTop (𝓝 (0 : H)) := sorry

/-- Proposition 28.14 (2): under the hypotheses of Proposition 28.14, the sequences `(x_n)` and
`(z_n)` of the canonical Chapter 26 projected forward-backward-forward specialization
`JγA = Prox[γ, f, hf]`, `Bf = gradg` converge weakly to a common point of
`C ∩ Argmin (f + g).asEReal`. -/
theorem tsengAlgorithm_tendsto_weakly_to_argmin
    {D C : Set H} {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hsubdiff_dom : (∂ f).dom ⊆ D) {gradg : H → H}
    (hD_dom : D ⊆ effectiveDomain g)
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (g x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradg x)) D)
    (β : Set.Ioi (0 : ℝ)) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hC_argmin : (C ∩ Argmin (f + g).asEReal).Nonempty)
    (hgrad_lipschitz :
      LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg (C ∪ (∂ f).dom))
    (γ : Set.Ioi (0 : ℝ)) (hγ_lt : (γ : ℝ) < β) (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    let x := projectedForwardBackwardForwardIteration (Prox[γ, f, hf]) gradg C hC γ x0
    let z := projectedForwardBackwardForwardResolventSequence (Prox[γ, f, hf]) gradg C hC γ x0
    ∃ p ∈ C ∩ Argmin (f + g).asEReal,
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H p)) ∧
        Tendsto (fun n ↦ toWeakSpace ℝ H (z n)) atTop (𝓝 (toWeakSpace ℝ H p)) := sorry

/-- Proposition 28.14 (3): under the hypotheses of Proposition 28.14, suppose that `f` or `g` is
uniformly convex on every nonempty bounded subset of `(∂ f).dom`. Then `(x_n)` and `(z_n)`
of the canonical Chapter 26 projected forward-backward-forward specialization
`JγA = Prox[γ, f, hf]`, `Bf = gradg` converge strongly to the unique point of
`C ∩ Argmin (f + g).asEReal`. -/
theorem tsengAlgorithm_tendsto_to_unique_argmin_of_uniformlyConvexOnEveryBoundedSubset
    {D C : Set H} {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hsubdiff_dom : (∂ f).dom ⊆ D) {gradg : H → H}
    (hD_dom : D ⊆ effectiveDomain g)
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (g x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradg x)) D)
    (β : Set.Ioi (0 : ℝ)) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hC_argmin : (C ∩ Argmin (f + g).asEReal).Nonempty)
    (hgrad_lipschitz :
      LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg (C ∪ (∂ f).dom))
    (γ : Set.Ioi (0 : ℝ)) (hγ_lt : (γ : ℝ) < β)
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
            ∃ φ : NNReal → EReal, UniformlyConvexOn g S φ)
    (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    let x := projectedForwardBackwardForwardIteration (Prox[γ, f, hf]) gradg C hC γ x0
    let z := projectedForwardBackwardForwardResolventSequence (Prox[γ, f, hf]) gradg C hC γ x0
    ∃ p ∈ C ∩ Argmin (f + g).asEReal,
      Tendsto x atTop (𝓝 p) ∧
        Tendsto z atTop (𝓝 p) ∧
        C ∩ Argmin (f + g).asEReal = ({p} : Set H) := sorry

end TsengAlgorithm

end

end ERealFunction
