import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap22.Example_22_4
import BauschkeLean.Chap26.Proposition_26_13

open Filter
open SetValuedOperator
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Proposition 28.8 is the fixed-step Peaceman--Rachford proximal recursion
  `(28.32)` for the convex minimization problem `minimize (f + g)(x)`.
- `core/canonical`: the reusable convergence owner is the Chapter 26 operator theorem
  `SetValuedOperator.peacemanRachford_tendsto_to_solution_of_uniformlyMonotone` for a pair of
  maximally monotone operators.
- `bridge/view`: this file keeps the textbook `Prox`-based recursion and the minimizer surface
  `Argmin (f + g).asEReal`, then bridges them to the subdifferential operator orbit and the primal
  inclusion solution set `primal_inclusion_solution_set (∂ f) (∂ g)`.
-/

section PeacemanRachfordAlgorithm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A triple of sequences `x`, `z`, `y` satisfies the Peaceman--Rachford proximal recursion
`(28.32)` for `f`, `g`, step size `γ`, and initial point `y0`. -/
structure IsPeacemanRachfordProximalOrbit
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (γ : PosReal) (y0 : H) (x z y : ℕ → H) : Prop where
  /-- The orbit starts from the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The first proximal step is `x_n = Prox_{γ g}(y_n)`. -/
  x_eq : ∀ n : ℕ, x n = Prox[γ, g, hg] (y n)
  /-- The second proximal step is `z_n = Prox_{γ f}(2 x_n - y_n)`. -/
  z_eq : ∀ n : ℕ, z n = Prox[γ, f, hf] ((2 : ℝ) • x n - y n)
  /-- The reflected correction is `y_(n+1) = y_n + 2 (z_n - x_n)`. -/
  y_succ_eq : ∀ n : ℕ, y (n + 1) = y n + (2 : ℝ) • (z n - x n)

/-- Helper for Proposition 28.8: the scaled proximal map `Prox[γ, f, hf]` is the resolvent of the
subdifferential `∂ f`. -/
private theorem resolventMapSubdifferential_eq_scaledProximityOperator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    SetValuedOperator.resolventMap (∂ f)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ = Prox[γ, f, hf] := by
  -- Compare the resolvent and prox operators on their singleton-valued set-valued realizations.
  have hrealizer :
      (SetValuedOperator.resolventMap (∂ f)
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ).toSetValuedOperator =
        (Prox[γ, f, hf]).toSetValuedOperator := by
    calc
      (SetValuedOperator.resolventMap (∂ f)
          (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ).toSetValuedOperator =
          J[((γ : ℝ) • (∂ f : SetValuedOperator H H))] := by
            simpa using
              SetValuedOperator.resolventMap_toSetValuedOperator_eq (∂ f)
                (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ
      _ = (Prox[γ, f, hf]).toSetValuedOperator := by
            rw [← subdifferential_posReal_smul_eq_smul f γ, resolvent_def]
            simpa [scaledProximityOperator] using
              (singleton_proximityOperator_eq_inverse_add_subdifferential
                (smul_mem_gammaZero f hf γ)).symm
  ext x
  -- Evaluating both set-valued operators at `x` reduces to equality of singleton values.
  have hx := congrArg (fun T : SetValuedOperator H H ↦ T x) hrealizer
  simpa [Function.toSetValuedOperator_apply, Set.singleton_eq_singleton_iff] using hx

/-- Helper for Proposition 28.8: every zero of `(∂ f) + (∂ g)` is a minimizer of `f + g`. -/
private theorem mem_argmin_of_mem_zeros_subdifferential_add
    {f g : H → Set.Ioi (⊥ : EReal)} {p : H}
    (hp : p ∈ ((∂ f) + (∂ g)).zeros) :
    p ∈ Argmin (f + g).asEReal := by
  -- Route through the Chapter 16 chain rule with `L = id`, then apply Fermat's rule.
  have hp_zero : p ∈ (∂ (f + g ∘ (ContinuousLinearMap.id ℝ H))).zeros := by
    rw [SetValuedOperator.mem_zeros_iff] at hp ⊢
    exact subdifferential_add_adjoint_image_subset_subdifferential_add_comp
      f g (ContinuousLinearMap.id ℝ H) p (by
        simpa [ContinuousLinearMap.adjointImageSubdifferential] using hp)
  -- The identity-map spelling of the objective is definitionally the same as `f + g`.
  simpa [argmin_eq_zeros_subdifferential] using hp_zero

/-- Helper for Proposition 28.8: a zero witness together with `Argmin (f + g).asEReal = {xbar}`
forces `xbar` to solve the primal inclusion for `(∂ f, ∂ g)`. -/
private theorem xbar_mem_primalInclusionSolutionSet_of_singletonArgmin
    {f g : H → Set.Ioi (⊥ : EReal)} (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    {xbar : H} (hxbar : Argmin (f + g).asEReal = ({xbar} : Set H)) :
    xbar ∈ primal_inclusion_solution_set (∂ f) (∂ g) := by
  rcases hzero with ⟨p, hp⟩
  -- Turn the zero witness into a minimizer and then use the singleton hypothesis.
  have hp_argmin : p ∈ Argmin (f + g).asEReal :=
    mem_argmin_of_mem_zeros_subdifferential_add hp
  have hpx : p = xbar := by
    simpa [hxbar] using hp_argmin
  -- Rewriting the original zero witness identifies `xbar` as an inclusion solution.
  simpa [hpx] using hp

namespace IsPeacemanRachfordProximalOrbit

/-- The source proximal recursion is the Chapter 26 Peaceman--Rachford orbit for the pair of
subdifferentials `(∂ f, ∂ g)`. -/
theorem toSubdifferentialOrbit
    {f g : H → Set.Ioi (⊥ : EReal)} {hf : f ∈ Γ₀(H)} {hg : g ∈ Γ₀(H)}
    {γ : PosReal} {y0 : H} {x z y : ℕ → H}
    (hOrbit : IsPeacemanRachfordProximalOrbit hf hg γ y0 x z y) :
    SetValuedOperator.IsPeacemanRachfordOrbit (∂ f) (∂ g)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg) γ y0 x z y := by
  refine ⟨hOrbit.y_zero, ?_, ?_, hOrbit.y_succ_eq⟩
  · intro n
    -- Rewrite the source prox step as the canonical resolvent step for `∂ g`.
    rw [hOrbit.x_eq n, ← resolventMapSubdifferential_eq_scaledProximityOperator hg γ]
  · intro n
    -- Rewrite the second prox step as the canonical resolvent step for `∂ f`.
    rw [hOrbit.z_eq n, ← resolventMapSubdifferential_eq_scaledProximityOperator hf γ]

/-- The operator-level Peaceman--Rachford orbit for `(∂ f, ∂ g)` specializes back to the source
proximal recursion `(28.32)`. -/
theorem ofSubdifferentialOrbit
    {f g : H → Set.Ioi (⊥ : EReal)} {hf : f ∈ Γ₀(H)} {hg : g ∈ Γ₀(H)}
    {γ : PosReal} {y0 : H} {x z y : ℕ → H}
    (hOrbit : SetValuedOperator.IsPeacemanRachfordOrbit (∂ f) (∂ g)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg) γ y0 x z y) :
    IsPeacemanRachfordProximalOrbit hf hg γ y0 x z y := by
  refine ⟨hOrbit.y_zero, ?_, ?_, hOrbit.y_succ_eq⟩
  · intro n
    -- Move the operator orbit back to the source prox recursion for `g`.
    rw [← resolventMapSubdifferential_eq_scaledProximityOperator hg γ, hOrbit.x_eq n]
  · intro n
    -- Move the operator orbit back to the source prox recursion for `f`.
    rw [← resolventMapSubdifferential_eq_scaledProximityOperator hf γ, hOrbit.z_eq n]

/-- The textbook proximal recursion and the Chapter 26 operator recursion agree for
`(∂ f, ∂ g)`. -/
theorem iff_subdifferentialOrbit
    {f g : H → Set.Ioi (⊥ : EReal)} {hf : f ∈ Γ₀(H)} {hg : g ∈ Γ₀(H)}
    {γ : PosReal} {y0 : H} {x z y : ℕ → H} :
    IsPeacemanRachfordProximalOrbit hf hg γ y0 x z y ↔
      SetValuedOperator.IsPeacemanRachfordOrbit (∂ f) (∂ g)
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
        (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg) γ y0 x z y := by
  constructor
  · exact toSubdifferentialOrbit
  · exact ofSubdifferentialOrbit

end IsPeacemanRachfordProximalOrbit

/-- Proposition 28.8: let `f, g ∈ Γ₀(H)` with `zer (∂ f + ∂ g) ≠ ∅`, assume `g` is uniformly
convex, let `γ ∈ ℝ_{++}`, and let `xbar` be the unique minimizer of `f + g`, encoded by
`Argmin (f + g).asEReal = {xbar}`. If `x`, `z`, and `y` satisfy the Peaceman--Rachford recursion
`(28.32)` from `y0`, then `x_n` converges strongly to `xbar`. -/
theorem peacemanRachfordAlgorithm_tendsto_to_unique_minimizer
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty) {φ : NNReal → EReal}
    (hg_uniform : UniformlyConvex g φ) (γ : PosReal) (xbar : H)
    (hxbar : Argmin (f + g).asEReal = ({xbar} : Set H)) (y0 : H) {x z y : ℕ → H}
    (hOrbit : IsPeacemanRachfordProximalOrbit hf hg γ y0 x z y) :
    Tendsto x atTop (𝓝 xbar) := by
  -- First translate the source recursion to the Chapter 26 operator orbit.
  have hOrbit' : SetValuedOperator.IsPeacemanRachfordOrbit (∂ f) (∂ g)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg) γ y0 x z y :=
    hOrbit.toSubdifferentialOrbit
  -- Use the singleton minimizer hypothesis to produce the operator-side solution point.
  have hxbar' : xbar ∈ primal_inclusion_solution_set (∂ f) (∂ g) :=
    xbar_mem_primalInclusionSolutionSet_of_singletonArgmin hzero hxbar
  -- Invoke the operator-level convergence owner with uniform monotonicity from uniform convexity.
  exact SetValuedOperator.peacemanRachford_tendsto_to_solution_of_uniformlyMonotone
    (∂ f) (∂ g)
    (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
    (subdifferential_isMaximallyMonotone_of_mem_gammaZero hg)
    (subdifferential_isUniformlyMonotone_of_uniformlyConvex g hg_uniform) γ xbar hxbar' y0
    hOrbit'

end PeacemanRachfordAlgorithm

end ERealFunction
