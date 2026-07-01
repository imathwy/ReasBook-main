import Mathlib
import SmoothManifoldsLee.Chap03.Sec03_17.Definition_3_17_extra_1
import SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the statement
-- shapes were fixed from the local smooth-submersion API in `Proposition_4_28`, the curve-velocity
-- API in `Definition_3_17_extra_1`, and the canonical mathlib tangent-bundle owners.

noncomputable section

open Bundle
open scoped ContDiff Manifold

universe uι uE uH uM

section FiniteProductProjections

variable {ι : Type uι} [Fintype ι]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
variable {H : ι → Type uH} [∀ i, TopologicalSpace (H i)]
variable {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
variable {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  [∀ i, IsManifold (I i) ∞ (M i)]
  [IsManifold (ModelWithCorners.pi I) ∞ (∀ i, M i)]

/-- Example 4.2 (1): for a finite product of smooth manifolds, each coordinate projection is a
smooth submersion. -/
theorem finite_product_projection_isSmoothSubmersion (i : ι) :
    Manifold.IsSmoothSubmersion (ModelWithCorners.pi I) (I i) (fun x : ∀ j, M j ↦ x i) := sorry

end FiniteProductProjections

/-- The projection of `ℝ^(n+k)` onto its first `n` coordinates. -/
def euclidean_first_projection (n k : ℕ) :
    EuclideanSpace ℝ (Fin (n + k)) → EuclideanSpace ℝ (Fin n) :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x (Fin.castLE (Nat.le_add_right n k) i)

/-- The first-coordinate projection is computed by evaluating the source vector on the corresponding
head index. -/
theorem euclidean_first_projection_apply {n k : ℕ} (x : EuclideanSpace ℝ (Fin (n + k)))
    (i : Fin n) :
    euclidean_first_projection n k x i = x (Fin.castLE (Nat.le_add_right n k) i) := sorry

/-- Example 4.2 (2): the projection `ℝ^(n+k) → ℝ^n` onto the first `n` coordinates is a smooth
submersion. -/
theorem euclidean_first_projection_isSmoothSubmersion (n k : ℕ) :
    Manifold.IsSmoothSubmersion (𝓡 (n + k)) (𝓡 n) (euclidean_first_projection n k) := sorry

section CurveImmersionCriterion

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Example 4.2 (3): for a smooth curve on a parameter interval, pointwise injectivity of the
within-interval manifold derivative is equivalent to nonvanishing within-interval velocity. This is
the formal interval version of Lee's criterion that `γ` is a smooth immersion exactly when
`γ'(t) ≠ 0` for all parameters. -/
theorem smooth_curve_injective_mfderivWithin_iff_forall_velocityWithin_ne_zero
    {J : Set ℝ} {γ : ℝ → M} (hJ : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ) J t)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ J) :
    (∀ t ∈ J, Function.Injective (mfderivWithin 𝓘(ℝ) I γ J t)) ↔
      ∀ t ∈ J, curve_velocityWithin I γ J t ≠ 0 := sorry

end CurveImmersionCriterion

section TangentBundleProjection

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Example 4.2 (4): the tangent-bundle projection `TM → M`, with the canonical smooth structure
on `TM`, is a smooth submersion. -/
theorem tangentBundle_projection_isSmoothSubmersion :
    Manifold.IsSmoothSubmersion I.tangent I (TotalSpace.proj : TangentBundle I M → M) := sorry

end TangentBundleProjection

/-- The torus-of-revolution parameterization from Example 4.2 (d). -/
def torus_revolution_map : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
  fun p ↦
    let u := p 0
    let v := p 1
    WithLp.toLp 2
      ![(2 + Real.cos (2 * Real.pi * u)) * Real.cos (2 * Real.pi * v),
        (2 + Real.cos (2 * Real.pi * u)) * Real.sin (2 * Real.pi * v),
        Real.sin (2 * Real.pi * u)]

/-- The explicit coordinate formula for `torus_revolution_map`. -/
theorem torus_revolution_map_apply (p : EuclideanSpace ℝ (Fin 2)) :
    torus_revolution_map p =
      WithLp.toLp 2
        ![(2 + Real.cos (2 * Real.pi * p 0)) * Real.cos (2 * Real.pi * p 1),
          (2 + Real.cos (2 * Real.pi * p 0)) * Real.sin (2 * Real.pi * p 1),
          Real.sin (2 * Real.pi * p 0)] := sorry

/-- The standard torus of revolution in `ℝ^3`, written as the level set
`(sqrt (x^2 + y^2) - 2)^2 + z^2 = 1`. -/
def torus_revolution_surface : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 2) ^ 2 + x 2 ^ 2 = 1}

/-- Membership in `torus_revolution_surface` is the standard torus equation in Cartesian
coordinates. -/
theorem mem_torus_revolution_surface_iff {x : EuclideanSpace ℝ (Fin 3)} :
    x ∈ torus_revolution_surface ↔
      (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 2) ^ 2 + x 2 ^ 2 = 1 := sorry

/-- Example 4.2 (5): the explicit torus parameterization is a smooth immersion
`ℝ^2 → ℝ^3`. -/
theorem torus_revolution_map_isImmersion :
    Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ torus_revolution_map := sorry

/-- Example 4.2 (6): the image of the torus parameterization is the torus of revolution obtained by
rotating the circle `(y - 2)^2 + z^2 = 1` about the `z`-axis. -/
theorem range_torus_revolution_map :
    Set.range torus_revolution_map = torus_revolution_surface := sorry
