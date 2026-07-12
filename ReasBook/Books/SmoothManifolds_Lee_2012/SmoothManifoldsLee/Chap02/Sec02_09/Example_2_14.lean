import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff
open Metric

universe uE uH uM

/-- The open unit ball in `ℝ^n`, viewed as a bundled open subset. -/
def unitOpenBall (n : ℕ) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨ball (0 : EuclideanSpace ℝ (Fin n)) 1, isOpen_ball⟩

-- Proof sketch: identify this map with the inverse branch of the standard radial homeomorphism
-- between `ℝ^n` and the open unit ball and use its smoothness on the ball.
/-- The map `x ↦ x / √(1 - ‖x‖^2)` is smooth on the open unit ball. -/
theorem unitBall_symm_contMDiff (n : ℕ) :
    ContMDiff
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ∞
      (fun x : unitOpenBall n ↦
        ((Homeomorph.unitBall : EuclideanSpace ℝ (Fin n) ≃ₜ unitOpenBall n).symm x :
          EuclideanSpace ℝ (Fin n))) := by
  -- Restrict the ambient smooth inverse radial map to the open-ball subtype.
  intro x
  change ContMDiffAt
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    ∞
    (fun x : unitOpenBall n ↦
      (OpenPartialHomeomorph.univUnitBall.symm x : EuclideanSpace ℝ (Fin n)))
    x
  refine (contMDiffAt_subtype_iff
    (U := unitOpenBall n)
    (f := fun y : EuclideanSpace ℝ (Fin n) ↦
      (OpenPartialHomeomorph.univUnitBall.symm y : EuclideanSpace ℝ (Fin n)))
    (x := x)).2 ?_
  -- The ambient inverse branch is smooth on the open unit ball, so it is smooth at `x`.
  simpa [unitOpenBall] using
    (OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
      (n := (⊤ : ℕ∞)) (E := EuclideanSpace ℝ (Fin n))).contMDiffOn.contMDiffAt
      (isOpen_ball.mem_nhds x.2)

-- Proof sketch: this is the standard radial compactification map, whose smoothness is the manifold
-- version of the Euclidean `ContDiff` theorem for `OpenPartialHomeomorph.univUnitBall`.
/-- The map `y ↦ y / √(1 + ‖y‖^2)` is smooth from `ℝ^n` to the open unit ball. -/
theorem unitBall_contMDiff (n : ℕ) :
    ContMDiff
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ∞
      (fun y : EuclideanSpace ℝ (Fin n) ↦
        show unitOpenBall n from
          (Homeomorph.unitBall : EuclideanSpace ℝ (Fin n) ≃ₜ unitOpenBall n) y)
      := by
  let f : EuclideanSpace ℝ (Fin n) → unitOpenBall n := fun y ↦
    show unitOpenBall n from
      (Homeomorph.unitBall : EuclideanSpace ℝ (Fin n) ≃ₜ unitOpenBall n) y
  -- Remove the codomain subtype pointwise and use the ambient smooth radial compactification.
  intro y
  refine (ContMDiffAt.subtypeVal_comp_iff (unitOpenBall n) f y).1 ?_
  change ContMDiffAt
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    ∞
    (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((Homeomorph.unitBall : EuclideanSpace ℝ (Fin n) ≃ₜ unitOpenBall n) y :
        EuclideanSpace ℝ (Fin n)))
    y
  -- After coercing back to the ambient space, this is exactly `Homeomorph.unitBall`.
  simpa using
    ((Homeomorph.contDiff_unitBall (n := (⊤ : ℕ∞))
      (E := EuclideanSpace ℝ (Fin n))).contMDiff.contMDiffAt : ContMDiffAt
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        ∞
        (fun y : EuclideanSpace ℝ (Fin n) ↦
          ((Homeomorph.unitBall : EuclideanSpace ℝ (Fin n) ≃ₜ unitOpenBall n) y :
            EuclideanSpace ℝ (Fin n)))
        y)

/-- Example 2.14 (1): the explicit maps
`x ↦ x / √(1 - ‖x‖^2)` and `y ↦ y / √(1 + ‖y‖^2)` define a diffeomorphism between the open unit
ball in `ℝ^n` and `ℝ^n`. -/
def unitOpenBallDiffeomorph (n : ℕ) :
    unitOpenBall n
      ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
        EuclideanSpace ℝ (Fin n) where
  toEquiv := (Homeomorph.unitBall :
    EuclideanSpace ℝ (Fin n) ≃ₜ unitOpenBall n).symm.toEquiv
  contMDiff_toFun := unitBall_symm_contMDiff n
  contMDiff_invFun := unitBall_contMDiff n

-- Proof sketch: unfold `unitOpenBallDiffeomorph`; its forward map is definitionally the explicit
-- formula used to build the diffeomorphism.
/-- The forward map of `unitOpenBallDiffeomorph` is `Homeomorph.unitBall.symm`, i.e. the explicit
formula from the example. -/
theorem unitOpenBallDiffeomorph_apply (n : ℕ)
    (x : unitOpenBall n) :
    unitOpenBallDiffeomorph n x =
      (Homeomorph.unitBall :
        EuclideanSpace ℝ (Fin n) ≃ₜ unitOpenBall n).symm x := rfl

section SmoothChart

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞ω) M]

-- Proof sketch: `he` puts `e` in the smooth maximal atlas, so `contMDiffOn_of_mem_maximalAtlas`
-- applies to `e`; then transfer that `ContMDiffOn` statement to the canonical homeomorphism
-- `e.toHomeomorphSourceTarget`.
/-- A smooth chart in the maximal atlas is smooth as a map from its source subtype to its target
subtype. -/
theorem smoothChart_contMDiff_toHomeomorphSourceTarget
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I (⊤ : ℕ∞ω) M) :
    ContMDiff I I ∞
      (fun x : (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) ↦
        show (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) from
          e.toHomeomorphSourceTarget x) := by
  let f : (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) →
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) := fun x ↦
    show (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) from
      e.toHomeomorphSourceTarget x
  -- Coerce away the target subtype so the goal matches the ambient chart map.
  intro x
  refine (ContMDiffAt.subtypeVal_comp_iff
    (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) f x).1 ?_
  refine (contMDiffAt_subtype_iff
    (U := (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M))
    (f := fun x : M ↦ e x) (x := x)).2 ?_
  -- A maximal-atlas chart is smooth at every source point.
  simpa using
    (contMDiffAt_of_mem_maximalAtlas
      (I := I) (n := (ω : ℕ∞ω)) (e := e) he x.2).of_le (by simp)

-- Proof sketch: apply the symmetric maximal-atlas smoothness theorem to `e`, then transfer it to
-- the inverse homeomorphism on the target and source subtypes.
/-- The inverse of a smooth chart in the maximal atlas is smooth between the target and source
subtypes. -/
theorem smoothChart_symm_contMDiff_toHomeomorphSourceTarget
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I (⊤ : ℕ∞ω) M) :
    ContMDiff I I ∞
      (fun y : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) ↦
        show (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) from
          e.toHomeomorphSourceTarget.symm y) := by
  let f : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) →
      (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) := fun y ↦
    show (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) from
      e.toHomeomorphSourceTarget.symm y
  -- Coerce away the source subtype so the goal matches the ambient inverse chart map.
  intro y
  refine (ContMDiffAt.subtypeVal_comp_iff
    (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) f y).1 ?_
  refine (contMDiffAt_subtype_iff
    (U := (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H))
    (f := fun y : H ↦ e.symm y) (x := y)).2 ?_
  -- The inverse of a maximal-atlas chart is smooth at every target point.
  simpa using
    (contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := (ω : ℕ∞ω)) (e := e) he y.2).of_le (by simp)

/-- Example 2.14 (2): every smooth coordinate chart in the maximal atlas is a diffeomorphism from
its source open set onto its image. -/
def smoothChartDiffeomorph
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I (⊤ : ℕ∞ω) M) :
    (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) ≃ₘ⟮I, I⟯
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) where
  toEquiv := e.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := smoothChart_contMDiff_toHomeomorphSourceTarget e he
  contMDiff_invFun := smoothChart_symm_contMDiff_toHomeomorphSourceTarget e he

-- Proof sketch: unfold `smoothChartDiffeomorph`; the underlying equivalence is exactly the
-- homeomorphism induced by the open partial homeomorphism `e`.
/-- The forward map of `smoothChartDiffeomorph` is the homeomorphism induced by the chart. -/
theorem smoothChartDiffeomorph_apply
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I (⊤ : ℕ∞ω) M)
    (x : (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M)) :
    smoothChartDiffeomorph e he x = e.toHomeomorphSourceTarget x := rfl

end SmoothChart
