import BauschkeLean.Chap28.IndicatorOptimization
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap28.Proposition_28_14

open Filter
open InnerProductSpace
open SetValuedOperator
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 28.15 is the projected-gradient specialization of Tseng's
  forward-backward-forward method on a closed convex constraint set `C`.
- `core/canonical`: Proposition 28.14 is already the Chapter 28 owner theorem for the projected
  forward-backward-forward iteration with proximal part `Prox[γ, f, hf]`.
- `bridge/view`: this file specializes `f` to the indicator `ι[C]`, so the canonical proximal
  owner becomes the projector `P[C, hC]`, and the owner solution set
  `C ∩ Argmin ((ι[C] + g).asEReal)` rewrites to `Argmin[C] g.asEReal`.

Primitive data: the constraint set `C`, the indicator owner `ι[C] ∈ Γ₀(H)`, and the Chapter 28
gradient data for `g`.
Derived API: the three convergence clauses obtained by direct specialization of
`Proposition_28_14`. -/

section TsengAlgorithm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem indicator_mem_gammaZero
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (x0 : C) :
    ι[C] ∈ Γ₀(H) :=
  indicator_mem_gammaZero_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex

omit [CompleteSpace H] in
private theorem subdifferential_indicator_dom_subset
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (x0 : C) :
    SetValuedOperator.dom (∂ ι[C]) ⊆ C := by
  simpa using
    (subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
      (indicator_mem_gammaZero hC_closed hC_convex x0))

omit [CompleteSpace H] in
private theorem lipschitzOnWith_union_subdifferential_indicator_dom
    {C : Set H} {g : H → H} {β : Set.Ioi (0 : ℝ)}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (x0 : C)
    (hgrad_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) g C) :
    LipschitzOnWith
      (Real.toNNReal ((β : ℝ)⁻¹)) g (C ∪ SetValuedOperator.dom (∂ ι[C])) := by
  simpa [Set.union_eq_left.mpr (subdifferential_indicator_dom_subset hC_closed hC_convex x0)] using
    hgrad_lipschitz

/-- Example 28.15 (1): let `C` be a nonempty closed convex subset of `H`, let `β ∈ ℝ_{++}`, let
`g ∈ Γ₀(H)` satisfy `C ⊆ effectiveDomain g` and be differentiable on `C` with a `1 / β`-Lipschitz
gradient field `gradg`, and assume `Argmin[C] g.asEReal` is nonempty. Then for the canonical
Chapter 26 projected forward-backward-forward specialization `JγA = P[C, hC]`, `Bf = gradg`,
the residual sequence `(x_n - z_n)` converges strongly to `0`. -/
theorem tsengProjectedGradient_sub_tendsto_zero
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {gradg : H → H}
    (hC_dom : C ⊆ effectiveDomain g)
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (g x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradg x)) C)
    (β : Set.Ioi (0 : ℝ))
    (hgrad_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg C)
    (hargmin : (Argmin[C] g.asEReal).Nonempty)
    (γ : Set.Ioi (0 : ℝ)) (hγ_lt : (γ : ℝ) < β) (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    let x := projectedForwardBackwardForwardIteration (P[C, hC]) gradg C hC γ x0
    let z := projectedForwardBackwardForwardResolventSequence (P[C, hC]) gradg C hC γ x0
    Tendsto (fun n ↦ x n - z n) atTop (𝓝 (0 : H)) := by
  have hprox :=
    proxIndicator_eq_projectionPoint_of_nonempty_isClosed_convex
      ⟨(x0 : H), x0.2⟩ hC_closed hC_convex γ
  simpa [indicator_mem_gammaZero, hprox] using
    tsengAlgorithm_sub_tendsto_zero
      (indicator_mem_gammaZero hC_closed hC_convex x0)
      hg
      (subdifferential_indicator_dom_subset hC_closed hC_convex x0)
      hC_dom
      hgrad
      β
      hC_closed
      hC_convex
      subset_rfl
      (by
        simpa [argminOn_asEReal_eq_inter_argmin_indicator_add g C] using
          hargmin)
      (lipschitzOnWith_union_subdifferential_indicator_dom
        hC_closed hC_convex x0 hgrad_lipschitz)
      γ
      hγ_lt
      x0

/-- Example 28.15 (2): under the hypotheses of Example 28.15, the sequences `(x_n)` and `(z_n)`
of the canonical Chapter 26 projected forward-backward-forward specialization
`JγA = P[C, hC]`, `Bf = gradg` converge weakly to a common point of `Argmin[C] g.asEReal`. -/
theorem tsengProjectedGradient_tendsto_weakly_to_argminOn
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {gradg : H → H}
    (hC_dom : C ⊆ effectiveDomain g)
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (g x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradg x)) C)
    (β : Set.Ioi (0 : ℝ))
    (hgrad_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg C)
    (hargmin : (Argmin[C] g.asEReal).Nonempty)
    (γ : Set.Ioi (0 : ℝ)) (hγ_lt : (γ : ℝ) < β) (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    let x := projectedForwardBackwardForwardIteration (P[C, hC]) gradg C hC γ x0
    let z := projectedForwardBackwardForwardResolventSequence (P[C, hC]) gradg C hC γ x0
    ∃ p ∈ Argmin[C] g.asEReal,
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H p)) ∧
        Tendsto (fun n ↦ toWeakSpace ℝ H (z n)) atTop (𝓝 (toWeakSpace ℝ H p)) := by
  have hprox :=
    proxIndicator_eq_projectionPoint_of_nonempty_isClosed_convex
      ⟨(x0 : H), x0.2⟩ hC_closed hC_convex γ
  simpa [argminOn_asEReal_eq_inter_argmin_indicator_add g C, indicator_mem_gammaZero, hprox] using
    tsengAlgorithm_tendsto_weakly_to_argmin
      (indicator_mem_gammaZero hC_closed hC_convex x0)
      hg
      (subdifferential_indicator_dom_subset hC_closed hC_convex x0)
      hC_dom
      hgrad
      β
      hC_closed
      hC_convex
      subset_rfl
      (by
        simpa [argminOn_asEReal_eq_inter_argmin_indicator_add g C] using
          hargmin)
      (lipschitzOnWith_union_subdifferential_indicator_dom
        hC_closed hC_convex x0 hgrad_lipschitz)
      γ
      hγ_lt
      x0

/-- Example 28.15 (3): under the hypotheses of Example 28.15, if `g` is uniformly convex on every
nonempty bounded subset of `C`, then `(x_n)` and `(z_n)` of the canonical Chapter 26 projected
forward-backward-forward specialization `JγA = P[C, hC]`, `Bf = gradg` converge strongly to the
unique point of `Argmin[C] g.asEReal`. -/
theorem tsengProjectedGradient_tendsto_to_unique_argminOn_of_uniformlyConvexOnEveryBoundedSubset
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {gradg : H → H}
    (hC_dom : C ⊆ effectiveDomain g)
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (g x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradg x)) C)
    (β : Set.Ioi (0 : ℝ))
    (hgrad_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg C)
    (hargmin : (Argmin[C] g.asEReal).Nonempty)
    (γ : Set.Ioi (0 : ℝ)) (hγ_lt : (γ : ℝ) < β)
    (hUniform :
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ C →
          ∃ φ : NNReal → EReal, UniformlyConvexOn g S φ)
    (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    let x := projectedForwardBackwardForwardIteration (P[C, hC]) gradg C hC γ x0
    let z := projectedForwardBackwardForwardResolventSequence (P[C, hC]) gradg C hC γ x0
    ∃ p ∈ Argmin[C] g.asEReal,
      Tendsto x atTop (𝓝 p) ∧
        Tendsto z atTop (𝓝 p) ∧
        Argmin[C] g.asEReal = ({p} : Set H) := by
  have hUniform' :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ SetValuedOperator.dom (∂ ι[C]) →
          ∃ φ : NNReal → EReal, UniformlyConvexOn (ι[C]) S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ SetValuedOperator.dom (∂ ι[C]) →
            ∃ φ : NNReal → EReal, UniformlyConvexOn g S φ := by
    right
    intro S hS_nonempty hS_bounded hS_sub
    exact hUniform S hS_nonempty hS_bounded <|
      Set.Subset.trans hS_sub (subdifferential_indicator_dom_subset hC_closed hC_convex x0)
  have hprox :=
    proxIndicator_eq_projectionPoint_of_nonempty_isClosed_convex
      ⟨(x0 : H), x0.2⟩ hC_closed hC_convex γ
  simpa [argminOn_asEReal_eq_inter_argmin_indicator_add g C, indicator_mem_gammaZero, hprox] using
    tsengAlgorithm_tendsto_to_unique_argmin_of_uniformlyConvexOnEveryBoundedSubset
      (indicator_mem_gammaZero hC_closed hC_convex x0)
      hg
      (subdifferential_indicator_dom_subset hC_closed hC_convex x0)
      hC_dom
      hgrad
      β
      hC_closed
      hC_convex
      subset_rfl
      (by
        simpa [argminOn_asEReal_eq_inter_argmin_indicator_add g C] using
          hargmin)
      (lipschitzOnWith_union_subdifferential_indicator_dom
        hC_closed hC_convex x0 hgrad_lipschitz)
      γ
      hγ_lt
      hUniform'
      x0

end TsengAlgorithm

end ERealFunction
