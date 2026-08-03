import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap16.Corollary_16_50
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap17.Corollary_17_42
import BauschkeLean.Chap18.Remark_18_16
import BauschkeLean.Chap18.Theorem_18_13
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap22.Example_22_4
import BauschkeLean.Chap26.Proposition_26_16
import BauschkeLean.Chap26.Proposition_26_25
import BauschkeLean.Chap28.Corollary_28_9

open Filter SetValuedOperator
open scoped Gradient InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 28.12 is the explicit proximal-gradient recursion `(28.36)` and its
  strong-convergence, uniqueness, and linear-rate consequences for `Argmin (f + g)`.
- `core/canonical`: the reusable Chapter 26 owner is `forwardBackwardIteration` for
  `A = ∂ f` and `B = ∇ g`.
- `bridge/view`: this file keeps the two-sequence source recursion `(x, y)` explicit and adds the
  companion identifications with the Chapter 26 forward-backward orbit and iteration.
Semantic recall: the source writes `γ ∈ [0, 2β[`, but the local scaled-proximity API
is organized around `γ : PosReal`; accordingly, the statements formalize the positive-step regime
`0 < γ < 2β` while keeping `(28.36)` and `Argmin (f + g.toEReal).asEReal` source-facing. -/

section ForwardBackwardSplitting

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A pair of sequences `x`, `y` satisfies the forward-backward recursion `(28.36)` for `f`,
the differentiable convex term `g`, step size `γ`, and initial point `x0`. -/
structure IsForwardBackwardProximalGradientOrbit
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ) (γ : PosReal) (x0 : H)
    (x y : ℕ → H) : Prop where
  /-- The orbit starts at the prescribed point `x0`. -/
  x_zero : x 0 = x0
  /-- The forward step is `y_n = x_n - γ ∇g(x_n)`. -/
  y_eq : ∀ n : ℕ, y n = x n - (γ : ℝ) • ∇ g (x n)
  /-- The backward step is `x_{n+1} = Prox_{γ f}(y_n)`. -/
  x_succ_eq : ∀ n : ℕ, x (n + 1) = Prox[γ, f, hf] (y n)

namespace IsForwardBackwardProximalGradientOrbit

variable {f : H → Set.Ioi (⊥ : EReal)} {hf : f ∈ Γ₀(H)} {g : H → ℝ}
variable {γ : PosReal} {x0 : H}
variable {x y : ℕ → H}

local notation "hSub" => subdifferential_isMaximallyMonotone_of_mem_gammaZero hf

/-- The recursion `(28.36)` induces the Chapter 26 forward-backward orbit for `A = ∂ f` and
`B = ∇ g` on `H`. -/
theorem toIsForwardBackwardOrbit
    (hOrbit : IsForwardBackwardProximalGradientOrbit hf g γ x0 x y) :
    IsForwardBackwardOrbit (Set.univ : Set H) (∂ f)
      (fun z : Set.univ ↦ ∇ g z) γ
      (fun n ↦ ⟨x n, Set.mem_univ (x n)⟩) := by
  refine ⟨?_⟩
  intro n
  -- Rewrite the source backward step through the single-valued resolvent realizer.
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal (∂ f) hSub γ
      (x n - (γ : ℝ) • ∇ g (x n))]
  rw [hOrbit.x_succ_eq n, hOrbit.y_eq n]
  rw [← resolventMap_subdifferential_eq_scaledProximityOperator (hf := hf)]
  exact Set.mem_singleton _

end IsForwardBackwardProximalGradientOrbit

/-- Helper for Example 28.12: Proposition 26.16 applied directly to the source orbit yields the
minimizer, uniqueness, and linear rate in one step. -/
lemma forwardBackwardProximalGradient_linearRateCore
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (α : Set.Ioi (0 : ℝ))
    (hstrong : StronglyConvex f (α : ℝ)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β : Set.Ioi (0 : ℝ))
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < 2 * (β : ℝ)) (x0 : H) {x y : ℕ → H}
    (hOrbit : IsForwardBackwardProximalGradientOrbit hf g γ x0 x y) :
    ∃ xbar ∈ Argmin (f + g.toEReal).asEReal,
      Tendsto x atTop (𝓝 xbar) ∧
        Argmin (f + g.toEReal).asEReal = ({xbar} : Set H) ∧
        ∀ n : ℕ,
          dist (x n) xbar ≤
            (1 / ((α : ℝ) * (γ : ℝ) + 1)) ^ n * dist x0 xbar := by
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, by
    have hβ : 0 < (β : ℝ) := Set.mem_Ioi.mp β.2
    simpa using inv_pos.mpr hβ⟩
  let xSub : ℕ → Set.univ := fun n ↦ ⟨x n, Set.mem_univ (x n)⟩
  have hstrongSub : (∂ f).IsStronglyMonotone (α : ℝ) :=
    subdifferential_isStronglyMonotone_of_stronglyConvex f hstrong
  have hcoco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun z : Set.univ ↦ ∇ g z) := by
    -- The local Baillon-Haddad bridge upgrades the `1 / β`-Lipschitz gradient bound.
    simpa [βInv, one_div, inv_inv] using
      gradient_lipschitz_imp_cocoercive_of_differentiable_convex
        g hdiff hconv βInv hgrad_lipschitz
  have hOrbitSub :
      IsForwardBackwardOrbit (Set.univ : Set H) (∂ f)
        (fun z : Set.univ ↦ ∇ g z) γ xSub := by
    simpa [xSub] using hOrbit.toIsForwardBackwardOrbit
  have hArgminEq :
      primal_inclusion_solution_set (∂ f)
          (ofFunction (Set.univ : Set H) (fun z : Set.univ ↦ ∇ g z)) =
        Argmin (f + g.toEReal).asEReal := by
    calc
      primal_inclusion_solution_set (∂ f)
          (ofFunction (Set.univ : Set H) (fun z : Set.univ ↦ ∇ g z)) =
            primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) := by
              rfl
      _ = Argmin (f + g.toEReal).asEReal := by
            symm
            exact argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff
  rcases
      SetValuedOperator.forwardBackwardOrbit_linearRate_of_isStronglyMonotone_of_cocoercive
        (D := Set.univ) (A := ∂ f) (B := fun z : Set.univ ↦ ∇ g z) (x := xSub)
        isClosed_univ
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
        (by intro z hz; simp)
        α β γ hstrongSub hcoco hγ_lt
        hOrbitSub
    with
    ⟨xbar, hxbar, hxbar_tendsto, hsingle, hrate⟩
  refine ⟨xbar, ?_, ?_, ?_, ?_⟩
  · -- Translate the primal inclusion solution back to `Argmin (f + g.toEReal).asEReal`.
    rw [← hArgminEq]
    exact hxbar
  · -- The subtype-valued orbit converges exactly when the underlying `x`-sequence does.
    simpa [xSub] using hxbar_tendsto
  · -- Strong monotonicity yields a singleton minimizer set.
    calc
      Argmin (f + g.toEReal).asEReal =
          primal_inclusion_solution_set (∂ f)
            (ofFunction (Set.univ : Set H) (fun z : Set.univ ↦ ∇ g z)) := hArgminEq.symm
      _ = ({xbar} : Set H) := hsingle
  · intro n
    -- Rewrite the Chapter 26 distance estimate in the source indexing convention.
    simpa [xSub, hOrbit.x_zero, dist_comm] using hrate n

/-- Example 28.12 (1): let `f ∈ Γ₀(H)` be `α`-strongly convex for some `α ∈ ℝ_{++}`, let
`g : H → ℝ` be convex and differentiable with `1 / β`-Lipschitz gradient for some
`β ∈ ℝ_{++}`, and let `γ` be a positive step size with `γ < 2β`. If `x` and `y` satisfy the
forward-backward recursion `(28.36)` from `x0`, then `(x_n)` converges to a minimizer of
`f + g`. -/
theorem forwardBackwardProximalGradient_tendsto_to_argmin_of_stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (α : Set.Ioi (0 : ℝ))
    (hstrong : StronglyConvex f (α : ℝ)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β : Set.Ioi (0 : ℝ))
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < 2 * (β : ℝ)) (x0 : H) {x y : ℕ → H}
    (hOrbit : IsForwardBackwardProximalGradientOrbit hf g γ x0 x y) :
    ∃ xbar ∈ Argmin (f + g.toEReal).asEReal,
      Tendsto x atTop (𝓝 xbar) := by
  -- Project the convergence clause from the specialized Chapter 26 linear-rate package.
  rcases forwardBackwardProximalGradient_linearRateCore
      hf α hstrong g hconv hdiff β hgrad_lipschitz γ hγ_lt x0 hOrbit with
    ⟨xbar, hxbar, hxbar_tendsto, _hsingle, _hrate⟩
  exact ⟨xbar, hxbar, hxbar_tendsto⟩

/-- Example 28.12 (2): under the same assumptions, the minimizer of `f + g` is unique. -/
theorem forwardBackwardProximalGradient_argmin_eq_singleton_of_stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (α : Set.Ioi (0 : ℝ))
    (hstrong : StronglyConvex f (α : ℝ)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β : Set.Ioi (0 : ℝ))
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < 2 * (β : ℝ)) (x0 : H) {x y : ℕ → H}
    (hOrbit : IsForwardBackwardProximalGradientOrbit hf g γ x0 x y) :
    ∃ xbar, Argmin (f + g.toEReal).asEReal = ({xbar} : Set H) := by
  -- Project the singleton argmin clause from the common core lemma.
  rcases forwardBackwardProximalGradient_linearRateCore
      hf α hstrong g hconv hdiff β hgrad_lipschitz γ hγ_lt x0 hOrbit with
    ⟨xbar, _hxbar, _hxbar_tendsto, hsingle, _hrate⟩
  exact ⟨xbar, hsingle⟩

/-- Example 28.12 (3): under the same assumptions, `(x_n)` satisfies the linear error bound
with rate factor `1 / (αγ + 1)` relative to a minimizer of `f + g`. -/
theorem forwardBackwardProximalGradient_linear_rate_to_argmin_of_stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (α : Set.Ioi (0 : ℝ))
    (hstrong : StronglyConvex f (α : ℝ)) (g : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (β : Set.Ioi (0 : ℝ))
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < 2 * (β : ℝ)) (x0 : H) {x y : ℕ → H}
    (hOrbit : IsForwardBackwardProximalGradientOrbit hf g γ x0 x y) :
    ∃ xbar ∈ Argmin (f + g.toEReal).asEReal,
      ∀ n : ℕ,
        dist (x n) xbar ≤
          (1 / ((α : ℝ) * (γ : ℝ) + 1)) ^ n * dist x0 xbar := by
  -- Project the explicit rate estimate from the common linear-rate package.
  rcases forwardBackwardProximalGradient_linearRateCore
      hf α hstrong g hconv hdiff β hgrad_lipschitz γ hγ_lt x0 hOrbit with
    ⟨xbar, hxbar, _hxbar_tendsto, _hsingle, hrate⟩
  exact ⟨xbar, hxbar, hrate⟩

end ForwardBackwardSplitting

end ERealFunction
