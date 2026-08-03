import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap23.Example_23_3
import BauschkeLean.Chap26.ForwardBackwardSplitting
import BauschkeLean.Chap27.Corollary_27_3
import BauschkeLean.Chap29.Definition_29_24

open Filter SetValuedOperator
open scoped Gradient InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private abbrev haugazeauProximalGradientOperator
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) : H → H :=
  fun x ↦ (1 / 2 : ℝ) •
    (x + forwardBackwardSplittingOperator (∂ f)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) (∇ g) γ x)

private theorem haugazeauProximalGradientOperator_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x : H) :
    haugazeauProximalGradientOperator f hf g γ x =
      (1 / 2 : ℝ) • (x + Prox[γ, f, hf] (x - (γ : ℝ) • ∇ g x)) := by
  have hres :
      Function.toSetValuedOperator
          (resolventMap (∂ f) (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ) =
        Function.toSetValuedOperator (Prox[γ, f, hf]) := by
    rw [resolventMap_toSetValuedOperator_eq]
    exact resolvent_subdifferential_eq_scaledProximityOperator f hf γ
  have hpoint :
      resolventMap (∂ f) (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ
          (x - (γ : ℝ) • ∇ g x) =
        Prox[γ, f, hf] (x - (γ : ℝ) • ∇ g x) := by
    have hset := congrFun hres (x - (γ : ℝ) • ∇ g x)
    exact Set.singleton_eq_singleton_iff.mp (by simpa using hset)
  change (1 / 2 : ℝ) •
      (x +
        resolventMap (∂ f) (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ
          (x - (γ : ℝ) • ∇ g x)) =
    (1 / 2 : ℝ) • (x + Prox[γ, f, hf] (x - (γ : ℝ) • ∇ g x))
  rw [hpoint]

-- Semantic recall/local precedent: `lean_leansearch` only returned generic fixed-point iteration
-- lemmas, so this file follows the verified local Chapter 12/18/27/29/30 owners `Prox[γ, f, hf]`,
-- `∇ g`, `specialPolyhedronQ`, and `Argmin`.

/-- The Haugazeau proximal-gradient orbit from Example 30.13, with recursion
`xₙ₊₁ = Q(x₀, xₙ, zₙ)` and `zₙ = (1 / 2) (xₙ + Prox_{γ f} (xₙ - γ ∇ g(xₙ)))`. -/
def haugazeauProximalGradientOrbit
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x0 : H) : ℕ → H
  | 0 => x0
  | n + 1 =>
      let xn := haugazeauProximalGradientOrbit f hf g γ x0 n
      specialPolyhedronQ x0 xn (haugazeauProximalGradientOperator f hf g γ xn)

/-- The forward sequence `yₙ = xₙ - γ ∇ g(xₙ)` attached to the Haugazeau proximal-gradient
orbit. -/
def haugazeauProximalGradientForwardSequence
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x0 : H) : ℕ → H :=
  fun n ↦
    haugazeauProximalGradientOrbit f hf g γ x0 n -
      (γ : ℝ) • ∇ g (haugazeauProximalGradientOrbit f hf g γ x0 n)

/-- The midpoint sequence `zₙ = (1 / 2) (xₙ + Prox_{γ f} yₙ)` attached to the Haugazeau
proximal-gradient orbit. -/
def haugazeauProximalGradientMidpointSequence
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x0 : H) : ℕ → H :=
  fun n ↦
    haugazeauProximalGradientOperator f hf g γ
      (haugazeauProximalGradientOrbit f hf g γ x0 n)

/-- The Haugazeau proximal-gradient orbit starts at the prescribed initial point. -/
@[simp] theorem haugazeauProximalGradientOrbit_zero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x0 : H) :
    haugazeauProximalGradientOrbit f hf g γ x0 0 = x0 := by
  rfl

/-- The forward sequence is given by `yₙ = xₙ - γ ∇ g(xₙ)`. -/
theorem haugazeauProximalGradientForwardSequence_eq
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x0 : H) (n : ℕ) :
    haugazeauProximalGradientForwardSequence f hf g γ x0 n =
      haugazeauProximalGradientOrbit f hf g γ x0 n -
        (γ : ℝ) • ∇ g (haugazeauProximalGradientOrbit f hf g γ x0 n) := by
  rfl

/-- The midpoint sequence is given by `zₙ = (1 / 2) (xₙ + Prox_{γ f} yₙ)`. -/
theorem haugazeauProximalGradientMidpointSequence_eq
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x0 : H) (n : ℕ) :
    haugazeauProximalGradientMidpointSequence f hf g γ x0 n =
      (1 / 2 : ℝ) •
        (haugazeauProximalGradientOrbit f hf g γ x0 n +
          Prox[γ, f, hf] (haugazeauProximalGradientForwardSequence f hf g γ x0 n)) := by
  rw [haugazeauProximalGradientMidpointSequence, haugazeauProximalGradientOperator_apply]
  rfl

/-- The Haugazeau proximal-gradient orbit satisfies the source recursion
`xₙ₊₁ = Q(x₀, xₙ, zₙ)`. -/
@[simp] theorem haugazeauProximalGradientOrbit_succ
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (γ : PosReal) (x0 : H) (n : ℕ) :
    haugazeauProximalGradientOrbit f hf g γ x0 (n + 1) =
      specialPolyhedronQ x0
        (haugazeauProximalGradientOrbit f hf g γ x0 n)
        (haugazeauProximalGradientMidpointSequence f hf g γ x0 n) := by
  simp [haugazeauProximalGradientOrbit, haugazeauProximalGradientMidpointSequence]

/-- Helper for Example 30.13: for a convex differentiable real-valued `g`, the minimizer set of
`f + g` agrees with the zero set of `∂ f + ∇ g`. -/
theorem argmin_add_toEReal_eq_haugazeauProximalGradient_zeroSet
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : H → ℝ} (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g) :
    Argmin (f + g.toEReal).asEReal =
      ((∂ f) + (∇ g).toSetValuedOperator).zeros := sorry

/-- Helper for Example 30.13: under the standing convexity hypotheses and nonemptiness of the
minimizer set, `Argmin (f + g)` is Chebyshev. -/
theorem isChebyshev_argmin_add_toEReal_of_haugazeauProximalGradient
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : H → ℝ} (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (hargmin : (Argmin (f + g.toEReal).asEReal).Nonempty) :
    IsChebyshev (Argmin (f + g.toEReal).asEReal) := sorry

/-- Example 30.13: let `f ∈ Γ₀(H)`, let `β ∈ ℝ_{++}`, let `g : H → ℝ` be convex and
differentiable with `(1 / β)`-Lipschitz gradient, let `γ ∈ ]0, 2β[`, suppose
`Argmin (f + g) ≠ ∅`, let `x₀ ∈ H`, and define the sequences `xₙ`, `yₙ`, and `zₙ` by
`yₙ = xₙ - γ ∇ g(xₙ)`, `zₙ = (1 / 2) (xₙ + Prox_{γ f} yₙ)`, and
`xₙ₊₁ = Q(x₀, xₙ, zₙ)`. Then `xₙ → P_{Argmin (f + g)} x₀`, written here on the project API as
convergence of `haugazeauProximalGradientOrbit` to the metric projection of `x₀` onto
`Argmin (f + g.toEReal).asEReal`. -/
theorem tendsto_haugazeauProximalGradientOrbit_to_projection_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (g : H → ℝ) (β γ : PosReal)
    (hconv : _root_.ConvexOn ℝ Set.univ g) (hdiff : Differentiable ℝ g)
    (hgrad :
      LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g))
    (hγ : (γ : ℝ) < 2 * (β : ℝ))
    (hargmin : (Argmin (f + g.toEReal).asEReal).Nonempty)
    (x0 : H) :
    Tendsto (haugazeauProximalGradientOrbit f hf g γ x0) atTop
      (𝓝
        (P[Argmin (f + g.toEReal).asEReal,
          isChebyshev_argmin_add_toEReal_of_haugazeauProximalGradient
            hf hconv hdiff hargmin] x0)) := sorry

end

end ERealFunction
