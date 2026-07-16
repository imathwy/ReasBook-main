import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)
open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ω : E → EReal} {C : Set E} {σ : ℝ} {xk xNext gradf : E} {t : ℝ}

/-
Text 9.4 is `source-facing` in the Chapter 9 mirror-descent API. Domain sampling in the relevant
convex-analysis layer points to these existing owners:
- Chapter 9's `IsBregmanPotentialOn ω C σ` for the primitive mirror-map data on `C`;
- Chapter 9's `bregmanDistance` / `B[ω]` for the step objective;
- Chapter 3's owner `subdifferential` / `subdifferential_domain` for the constrained optimality
  condition;
- Chapter 4's Fenchel owner `conjugate_function` together with the conjugate-side bridge used to
  pass from constrained subgradient membership to the gradient of the conjugate.

The right abstraction layer is therefore:
- `source-facing`: the mirror step over `C` and the textbook conclusion
  `x⁺ = ∇ ω̃∗(∇ω(xᵏ) - t g_f)`;
- `core/canonical`: the constrained potential `ω̃ = ω + extendedIndicator C`;
- `bridge/view`: the intermediate constrained-subgradient and conjugate-subdifferential
  formulations.

The primitive data are the Bregman-potential owner `hω : IsBregmanPotentialOn ω C σ` and the
current-point hypothesis `xk ∈ C ∩ dom(∂ ω)`. The constrained potential and conjugate-side
formulations are derived API from those owners; they should not replace the source-facing mirror
step as the main public statement. -/

-- Proof sketch: because `hω.subset_effective_domain` makes `ω` finite on `C`, the objective
-- `x ↦ ⟪t g_f, x⟫ + B[ω] x xk` on `C` agrees, up to an additive constant independent of `x`, with
-- the unconstrained extended-real objective
-- `x ↦ (ω + δ_C)(x) - ⟪∇ω(xk) - t g_f, x⟫`. Fermat's rule for that constrained potential therefore
-- gives the textbook optimality condition
-- `∇ω(xk) - t g_f ∈ ∂ (ω + δ_C) (x⁺)`, expressed on the chapter's continuous-dual bridge
-- `strongDualSubdifferential`.
/-- Text 9.4 bridge: if `ω` is a Bregman potential on `C` and `x^k ∈ C ∩ dom(∂ ω)`, then the
mirror-descent step
`x⁺ ∈ argmin_{x ∈ C} {⟪t g_f, x⟫ + B_ω(x, x^k)}`
is equivalent to the constrained subgradient condition
`∇ω(x^k) - t g_f ∈ ∂ (ω + δ_C)(x⁺)`. -/
lemma mirror_descent_step_isMinOn_iff_dual_mem_subdifferential_add_indicator
    (hω : IsBregmanPotentialOn ω C σ) (hxk : xk ∈ C ∩ subdifferential_domain ω) :
    IsMinOn (fun x ↦ inner ℝ (t • gradf) x + B[ω] x xk) C xNext ↔
      toDualMap ℝ E (∇ (fun y ↦ (ω y).toReal) xk - t • gradf) ∈
        strongDualSubdifferential (ω + extendedIndicator C) xNext :=
  sorry

-- Proof sketch: combine the constrained-subgradient bridge above with Fenchel conjugacy for
-- `ω̃ = ω + δ_C`. Strong convexity of the constrained potential makes `ω̃∗` differentiable at the
-- dual point, so the singleton subdifferential there is represented by the gradient of
-- `y ↦ ((ω̃∗) y).toReal`. Transporting back through the Riesz map identifies the primal vector
-- `x⁺` with that gradient.
/-- Text 9.4: letting `ω̃ = ω + δ_C`, if `ω` is a Bregman potential on `C` and
`x^k ∈ C ∩ dom(∂ ω)`, then the mirror-descent update step
`x⁺ ∈ argmin_{x ∈ C} {⟪t g_f, x⟫ + B_ω(x, x^k)}`
is equivalent to the source-facing conjugate formula
`x⁺ = ∇ ω̃∗(∇ω(x^k) - t g_f)`, expressed in Lean via the real-valued restriction of `ω̃∗`. -/
theorem mirror_descent_step_isMinOn_iff_eq_gradient_conjugate_add_indicator
    (hω : IsBregmanPotentialOn ω C σ) (hxk : xk ∈ C ∩ subdifferential_domain ω) :
    IsMinOn (fun x ↦ inner ℝ (t • gradf) x + B[ω] x xk) C xNext ↔
      xNext =
        ∇ (fun y ↦ ((((ω + extendedIndicator C)∗) y).toReal))
          (∇ (fun y ↦ (ω y).toReal) xk - t • gradf) :=
  sorry

end
