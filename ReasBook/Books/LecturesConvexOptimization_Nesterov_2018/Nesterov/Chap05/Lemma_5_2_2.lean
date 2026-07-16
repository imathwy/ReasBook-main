import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Corollary_5_1_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_2_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient NewtonDecrement AuxiliaryCentralPathNewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear tilt preserves the positive-definite-Hessian owner on `dom`. -/
instance auxiliaryCentralPathObjective_hasPositiveDefiniteHessianOn
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) :
    HasPositiveDefiniteHessianOn dom (auxiliaryCentralPathObjective f y0 t) where
  isPositive {x} hx := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx : (hessian f x).IsPositive)
  posdef {x} hx {u} hu := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.posdef hx hu : 0 < inner ℝ u (hessian f x u))

/-- The Hessian of the tilted objective `ψ(t; ·)` is nondegenerate at every domain point once the
ambient objective carries the chapter's positive-definite-Hessian owner. -/
theorem auxiliaryCentralPathObjective_hessian_det_ne_zero
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) {y : E} (hy : y ∈ dom) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).det ≠ 0 := by
  have hdet : (hessian f y).det ≠ 0 := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy
  simpa [auxiliaryCentralPathObjective_hessian_eq] using hdet

/-- The approximate centering condition for the tilted objective `ψ(t; ·)` at `y`, expressed as
the bound `λ_{ψ(t; ·)}(y) ≤ β / M_f` on the canonical domain-membership Newton-decrement surface
for the tilted objective, with the positive self-concordance parameter carried on the canonical
`NNRealˣ` surface. -/
def satisfies_approximate_centering_condition
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ)
    (β : ℝ) : Prop :=
  λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ)

-- Proof sketch: unfold `satisfies_approximate_centering_condition`.
/-- Expanding `satisfies_approximate_centering_condition` recovers the inequality
`λ_{ψ(t; ·)}(y) ≤ β / M_f`. -/
theorem satisfies_approximate_centering_condition_iff
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ) (β : ℝ) :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ) := Iff.rfl

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}

/-- A linear tilt preserves the Chapter 5 self-concordance owner, so the updated path parameter
`t₊` determines a canonical intermediate Newton step for `ψ(t₊; ·)` on the same domain. -/
theorem auxiliaryCentralPathObjective_isSelfConcordantOnWith
    (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (y0 : dom) (t : ℝ) :
    IsSelfConcordantOnWith dom Mf (auxiliaryCentralPathObjective f y0 t) := by
  let hf : IsSelfConcordantOnWith dom Mf f := inferInstance
  simpa [auxiliaryCentralPathObjective, quadraticAffineObjective, sub_eq_add_neg,
    inner_smul_left, add_assoc, add_left_comm, add_comm] using
    hf.add_quadraticAffineObjective 0 (-(t : ℝ) • ∇ f (y0 : E))
      (0 : E →L[ℝ] E) ContinuousLinearMap.isPositive_zero

private instance pathFollowingUpdate_auxiliaryCentralPathObjective_isSelfConcordantOnWith
    (y0 : dom) (t : ℝ) [IsSelfConcordantOnWith dom (Mf : NNReal) f] :
    IsSelfConcordantOnWith dom (Mf : NNReal) (auxiliaryCentralPathObjective f y0 t) :=
  auxiliaryCentralPathObjective_isSelfConcordantOnWith f (Mf : NNReal) y0 t

private abbrev pathFollowingObjectiveNorm
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (y : E) (hy : y ∈ dom) : ℝ :=
  HessianDualLocalNorm.ofPosDefMem f hy
    ((toDual ℝ E) (∇ f (y0 : E)))

/-- The path-following map sending `(t, y)` to the intermediate Newton update `(t₊, y₊)` for the
tilted objective based at `y₀` and path increment parameter `γ`, defined on the canonical
positive-definite-Hessian owner over `dom`. The scalar update is the ordinary expression
`t₊ = t - γ / (M_f ‖∇ f(y₀)‖*_y)`, so the denominator positivity is kept explicit as part of the
input data. The vector update is the canonical intermediate Newton next point for the tilted
objective at the updated parameter `t₊`. -/
def pathFollowingUpdate
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) : ℝ × E :=
  let hMf : 0 < (Mf : ℝ) := by
    have hMfNNReal : 0 < (Mf : NNReal) := by
      exact pos_iff_ne_zero.mpr (Units.ne_zero Mf)
    exact_mod_cast hMfNNReal
  let denominator : Set.Ioi (0 : ℝ) :=
    ⟨(Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy, mul_pos hMf hObjectiveNorm⟩
  let tPlus :=
    (t : ℝ) - gamma / (denominator : ℝ)
  (tPlus,
    selfConcordantNewtonNextPoint
      (auxiliaryCentralPathObjective f y0 tPlus)
      (Mf : NNReal) .intermediate y hy
      (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tPlus hy))

namespace PathFollowingUpdate

/-- Source-facing notation for the path-following map `𝒫_γ`, with the ambient objective data
kept explicit because they are not inferable from `(t, y)` alone. -/
scoped notation:max
  "𝒫[" f "; " Mf "; " y0 " | " hy "; " hObjectiveNorm "; " gamma "](" t ", " y ")" =>
  pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma

end PathFollowingUpdate

open scoped PathFollowingUpdate

-- Proof sketch: unfold `pathFollowingUpdate`.
/-- The first coordinate of `pathFollowingUpdate` is the scalar update
`t₊ = t - γ / (M_f ‖∇ f(y₀)‖*_y)`. -/
theorem pathFollowingUpdate_fst
    (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1 =
      (t : ℝ) - gamma / ((Mf : ℝ) *
        HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E)))) := by
  simp [pathFollowingUpdate, pathFollowingObjectiveNorm]

/-- The second coordinate of `pathFollowingUpdate` is the canonical intermediate Newton next
point for the tilted objective at the updated parameter `t₊`. -/
theorem pathFollowingUpdate_snd
    (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2 =
      selfConcordantNewtonNextPoint
        (auxiliaryCentralPathObjective f y0
          (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1)
        (Mf : NNReal) .intermediate y hy
        (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0
          (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1 hy) := by
  simp only [pathFollowingUpdate, pathFollowingObjectiveNorm]

/-- The centering threshold `β = τ² (1 + τ + τ / (1 + τ + τ²))` used in the path-following
small-step estimate. -/
def pathFollowingCenteringBeta (τ : ℝ) : ℝ :=
  τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ)))

-- Proof sketch: unfold `pathFollowingCenteringBeta`.
/-- Expanding `pathFollowingCenteringBeta τ` recovers the textbook formula
`τ² (1 + τ + τ / (1 + τ + τ²))`. -/
theorem pathFollowingCenteringBeta_def (τ : ℝ) :
    pathFollowingCenteringBeta τ =
      τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := rfl

/-- The admissible path-parameter increment bound
`τ - τ² (1 + τ + τ / (1 + τ + τ²))` from `(5.2.15)`. -/
def pathFollowingGammaRadius (τ : ℝ) : ℝ :=
  τ - pathFollowingCenteringBeta τ

-- Proof sketch: unfold `pathFollowingGammaRadius` and then rewrite with
-- `pathFollowingCenteringBeta_def`.
/-- Expanding `pathFollowingGammaRadius τ` gives the bound from `(5.2.15)`. -/
theorem pathFollowingGammaRadius_def (τ : ℝ) :
    pathFollowingGammaRadius τ =
      τ - τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
  simp [pathFollowingGammaRadius, pathFollowingCenteringBeta]

/-- Under the hypotheses of Lemma 5.2.2, the updated point produced by `pathFollowingUpdate`
belongs to `dom`; this is derived from the canonical intermediate Newton step for
`ψ(t₊; ·)`, not taken as primitive path-following data. -/
theorem pathFollowingUpdate_snd_mem
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2 ∈ dom := by
  sorry

-- Proof sketch: let `λ = ‖∇f(y) - t ∇f(y₀)‖*_y`, `λ₁ = ‖∇f(y) - t₊ ∇f(y₀)‖*_y`, and
-- `λ₊ = ‖∇f(y₊) - t₊ ∇f(y₀)‖*_{y₊}`. The assumption `hcenter` gives
-- `λ ≤ pathFollowingCenteringBeta τ / M_f`, while the path-parameter update and the bound on
-- `|γ|` imply `λ₁ ≤ τ / M_f`. Applying the intermediate-step decrement estimate `(5.2.8)` to the
-- tilted objective then yields
-- `λ₊ ≤ pathFollowingCenteringBeta τ / M_f`, which is exactly the same approximate-centering
-- condition at `(t₊, y₊)`.
/-- Lemma 5.2.2: if `(t, y)` satisfies the approximate centering condition `(5.2.13)` with
`β = τ² (1 + τ + τ / (1 + τ + τ²))` and `τ ≤ 1 / 2`, then the path-following update
`𝒫_γ(t, y)` also satisfies the same centering condition whenever its computed first coordinate
lies in `[0, 1]` and `|γ| ≤ τ - τ² (1 + τ + τ / (1 + τ + τ²))`. The updated point is read
through the canonical intermediate Newton owner for the tilted objective `ψ(t₊; ·)`, so its
domain membership is derived rather than assumed separately. -/
theorem pathFollowingUpdate_preserves_approximate_centering_condition
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    satisfies_approximate_centering_condition f y0
      (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1
      (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2
      (pathFollowingUpdate_snd_mem y0 t hy hObjectiveNorm htau hcenter hgamma) Mf
      (pathFollowingCenteringBeta τ) := by
  sorry

end
