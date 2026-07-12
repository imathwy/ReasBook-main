import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_5
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_47

noncomputable section

open scoped Gradient StrongConvex WithTopConvexAnalysis

universe u

/- Definition 6.37 lies in the whole-space strong-convexity / subdifferential domain.

Sampled owner-style declarations:
- `S0On` with the notation `𝒮^0_σ(Q)` in `Chap03/Definition_3_47`, the chapter's source-facing
  owner for positive-parameter strong convexity;
- mathlib `StrongConvexOn`, the canonical whole-space strong-convexity owner;
- `subdifferential` with the notation `∂ f(x)` in `Chap03/Definition_3_1_5`, the chapter owner
  for subgradients of `WithTop ℝ`-valued functions;
- `strongConvexOnWith_normSeminorm_iff` and
  `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` in `Chap02/Definition_2_14`, the
  ambient-norm bridge from the core owner to the textbook quadratic lower-tangent inequality.

Best owner abstraction:
- core/canonical: `f ∈ 𝒮^0_σ(Set.univ)`, equivalently `0 < σ ∧ StrongConvexOn Set.univ σ f`;
- bridge/view: the real-valued subgradient membership formula and the differentiable gradient
  specialization.

Primitive data:
- the modulus `σ : ℝ`;
- the real-valued objective `f : E → ℝ`.

Derived API:
- positivity of `σ` and the core owner `StrongConvexOn Set.univ σ f`, via `mem_S0On_iff`;
- the source-facing subgradient characterization below, phrased through the existing owner `∂`;
- the differentiable specialization with `∇ f x`.

Source/core/bridge triage:
- core/canonical main entry: `f ∈ 𝒮^0_σ(Set.univ)`;
- bridge/view: `mem_subdifferential_coe_iff`,
  `mem_S0On_univ_iff_exists_subgradient_lower_tangent_quadratic`, and
  `mem_S0On_univ_iff_gradient_inequality_of_differentiable`.

Definition 6.37 introduces no new owner beyond the earlier chapter surface `𝒮^0_σ(Set.univ)`.
This file therefore recalls that owner directly and keeps the textbook subgradient and gradient
formulas only as bridge theorems, instead of rebuilding parallel local definitions such as
`StrongConvexWithParameter`, `IsSubgradientAt`, or a second real-valued `subdifferential`.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (σ : ℝ) (f : E → ℝ)

/- Definition 6.37, owner form: positive whole-space strong convexity. -/
#check (f ∈ 𝒮^0_σ(Set.univ))

end

/-- For a real-valued function, membership in the Chapter 3 subdifferential owner is exactly the
usual affine lower-support inequality. -/
theorem mem_subdifferential_coe_iff {f : E → ℝ} {x g : E} :
    g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x) ↔
      ∀ y : E, f y ≥ f x + inner ℝ g (y - x) := by
  constructor
  · intro hg y
    have hy : y ∈ dom (fun z ↦ (f z : WithTop ℝ)) := by
      simp [withTopEffectiveDomain]
    have hineq :
        (((f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa [mem_subdifferential_iff] using (mem_subdifferential_iff.mp hg).2 hy
    exact_mod_cast hineq
  · intro hg
    refine mem_subdifferential_iff.mpr ?_
    refine ⟨by simp [withTopEffectiveDomain], ?_⟩
    intro y hy
    have hineq :
        (((f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      exact_mod_cast hg y
    simpa using hineq

/-- Definition 6.37, source-facing bridge: positive whole-space strong convexity is equivalent to
positivity of `σ` together with the existence, at each base point, of a subgradient supporting the
function with the quadratic term `(σ / 2) * ‖y - x‖²`. -/
theorem mem_S0On_univ_iff_exists_subgradient_lower_tangent_quadratic
    {σ : ℝ} {f : E → ℝ} :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
            f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  sorry

/-- For a differentiable function, the source-facing Definition 6.37 bridge reduces to the
gradient lower-support inequality with the same quadratic term. -/
theorem mem_S0On_univ_iff_gradient_inequality_of_differentiable
    [CompleteSpace E] {σ : ℝ} {f : E → ℝ} (hf : Differentiable ℝ f) :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  sorry

end
