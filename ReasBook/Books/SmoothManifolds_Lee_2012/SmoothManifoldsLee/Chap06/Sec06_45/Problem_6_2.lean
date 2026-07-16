import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_40.Theorem_6_18
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_40.Theorem_6_19

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` pointed to mathlib's `WhitneyEmbedding` existence
-- theorems, and the local Chapter 6 Whitney immersion/embedding files were used to match the
-- intrinsic manifold API surface adopted in this repository.

open scoped ContDiff Manifold

namespace Manifold

section

universe uM

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold n M] [IsManifold (𝓡 n) ∞ M]

/-- Helper for Problem 6-2: on a `0`-dimensional smooth manifold, every manifold derivative has
trivial source tangent space, so it is automatically injective. -/
lemma injectiveMfderivZeroDimensional {N : ℕ} {M : Type uM} [TopologicalSpace M]
    [TopologicalManifold 0 M] [IsManifold (𝓡 0) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    Function.Injective (mfderiv (𝓡 0) (𝓡 N) f x) := by
  -- The tangent space of a `0`-manifold has dimension `0`.
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 0) x) = 0 :=
    tangentSpace_finrank_eq_of_n_dimensional_manifold x
  -- Therefore every tangent vector is zero, so any derivative out of it is injective.
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 0) x) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 0))
    infer_instance
  have hzero : ∀ v : TangentSpace (𝓡 0) x, v = 0 :=
    finrank_zero_iff_forall_zero.mp hfin
  intro v w _
  rw [hzero v, hzero w]

/-- Helper for Problem 6-2: a boundaryless `0`-manifold satisfies the zero-dimensional Whitney
immersion theorem by viewing it as a manifold with boundary in dimension `0`. -/
lemma zeroDimensionalWhitneyImmersionBoundaryless {M : Type uM} [TopologicalSpace M]
    [TopologicalManifold 0 M] [IsManifold (𝓡 0) ∞ M] :
    ∃ F : M → EuclideanSpace ℝ (Fin 0), IsImmersion (𝓡 0) (𝓡 0) ∞ F := by
  refine ⟨fun _ ↦ 0, ?_⟩
  -- The constant map is smooth, so immersion reduces to pointwise injectivity of its derivative.
  have hConst : ContMDiff (𝓡 0) (𝓡 0) ∞ (fun _ : M ↦ (0 : EuclideanSpace ℝ (Fin 0))) :=
    contMDiff_const
  rw [is_immersion_iff_forall_injective_mfderiv hConst]
  intro x
  -- In dimension `0`, every tangent-space derivative is injective by source triviality.
  simpa using
    (injectiveMfderivZeroDimensional
      (N := 0)
      (f := fun _ : M ↦ (0 : EuclideanSpace ℝ (Fin 0)))
      x)

/-- Helper for Problem 6-2: in positive dimension, the strong Whitney embedding theorem gives the
required immersion after forgetting the embedding field. -/
lemma succWhitneyImmersionFromStrongWhitneyEmbedding {k : ℕ} {M : Type uM}
    [TopologicalSpace M] [TopologicalManifold (k + 1) M] [IsManifold (𝓡 (k + 1)) ∞ M] :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * (k + 1))),
      IsImmersion (𝓡 (k + 1)) (𝓡 (2 * (k + 1))) ∞ F :=
  by
    -- The stronger embedding statement in dimension `k + 1` immediately yields an immersion.
    have hEmbedding :
        ∃ F : M → EuclideanSpace ℝ (Fin (2 * (k + 1))),
          IsSmoothEmbedding (𝓡 (k + 1)) (𝓡 (2 * (k + 1))) ∞ F :=
      strong_whitney_embedding (Nat.succ_pos k)
    rcases hEmbedding with ⟨F, hF⟩
    exact ⟨F, hF.isImmersion⟩

/-- Problem 6-2. In the boundaryless case `∂ M = ∅`, every smooth `n`-manifold admits a smooth
immersion into `ℝ^(2n)`. -/
theorem whitney_immersion_boundaryless :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n)), IsImmersion (𝓡 n) (𝓡 (2 * n)) ∞ F :=
  by
    -- Route correction: reuse the earlier Whitney immersion and strong embedding theorems instead
    -- of rebuilding the Sard-theoretic construction inside this single-item file.
    cases n with
    | zero =>
        -- The zero-dimensional branch is handled by the boundary-model identification helper.
        simpa using
          (zeroDimensionalWhitneyImmersionBoundaryless :
            ∃ F : M → EuclideanSpace ℝ (Fin 0), IsImmersion (𝓡 0) (𝓡 0) ∞ F)
    | succ k =>
        -- The positive-dimensional branch reduces to the strong embedding theorem.
        simpa using
          (succWhitneyImmersionFromStrongWhitneyEmbedding :
            ∃ F : M → EuclideanSpace ℝ (Fin (2 * (k + 1))),
              IsImmersion (𝓡 (k + 1)) (𝓡 (2 * (k + 1))) ∞ F)

end

end Manifold
