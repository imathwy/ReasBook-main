import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_1

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` found only general Whitney immersion APIs in mathlib,
-- so the source-facing theorem follows the neighboring Section 6.40 boundaryless owner pattern
-- from `Theorem_6_19`: `[TopologicalManifold n M] [IsManifold (𝓡 n) ∞ M]`.

open scoped ContDiff Manifold
open Set

namespace Manifold

noncomputable section

section

universe uM

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold n M] [IsManifold (𝓡 n) ∞ M]

/-- Helper for Theorem 6.20: the last coordinate index of `Fin N` under the hypothesis `0 < N`.
-/
private def lastCoordinateIndex {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (Nat.succ_pos 0)⟩

/-- Helper for Theorem 6.20: the order-preserving embedding of the first `N - 1` coordinates into
`Fin N`. -/
private def dropLastCoordinateEmbedding {N : ℕ} (hN : 0 < N) :
    Fin (N - 1) → Fin N :=
  fun i ↦ ⟨i.1, lt_trans i.2 (Nat.sub_lt hN (Nat.succ_pos 0))⟩

/-- Helper for Theorem 6.20: the algebraic oblique projection along the line `ℝ v` onto the
last-coordinate hyperplane. -/
private noncomputable def obliqueProjectionToLastHyperplaneLinearMap {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin (N - 1)) where
  toFun x :=
    (EuclideanSpace.equiv (Fin (N - 1)) ℝ).symm fun i ↦
      x (dropLastCoordinateEmbedding hN i) -
        (x (lastCoordinateIndex hN) / v (lastCoordinateIndex hN)) *
          v (dropLastCoordinateEmbedding hN i)
  map_add' x y := by
    ext i
    simp [sub_eq_add_neg, mul_add, add_mul, div_eq_mul_inv]
    ring
  map_smul' a x := by
    ext i
    simp [sub_eq_add_neg, div_eq_mul_inv]
    ring

/-- Helper for Theorem 6.20: the codimension-one oblique projection along the line `ℝ v` onto the
last-coordinate hyperplane, written as a continuous linear map. -/
private noncomputable def obliqueProjectionToLastHyperplaneCLM {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin (N - 1)) where
  toLinearMap := obliqueProjectionToLastHyperplaneLinearMap hN v
  cont := by
    exact (obliqueProjectionToLastHyperplaneLinearMap hN v).continuous_of_finiteDimensional

/-- Helper for Theorem 6.20: the oblique projection along `v` subtracts the unique multiple of
`v` that kills the last coordinate. -/
private lemma obliqueProjectionToLastHyperplaneCLM_apply {N : ℕ} (hN : 0 < N)
    (v x : EuclideanSpace ℝ (Fin N)) (i : Fin (N - 1)) :
    obliqueProjectionToLastHyperplaneCLM hN v x i =
      x (dropLastCoordinateEmbedding hN i) -
        (x (lastCoordinateIndex hN) / v (lastCoordinateIndex hN)) *
          v (dropLastCoordinateEmbedding hN i) := by
  -- The continuous linear map is defined from the explicit coordinate formula.
  rfl

/-- Helper for Theorem 6.20: the kernel of the oblique projection along `v` is exactly the line
spanned by `v`, provided the last coordinate of `v` is nonzero. -/
private lemma obliqueProjectionToLastHyperplaneCLM_eq_zero_iff_smul {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N))
    (hv : v (lastCoordinateIndex hN) ≠ 0)
    {x : EuclideanSpace ℝ (Fin N)} :
    obliqueProjectionToLastHyperplaneCLM hN v x = 0 ↔ ∃ a : ℝ, a • v = x := by
  constructor
  · intro hx
    refine ⟨x (lastCoordinateIndex hN) / v (lastCoordinateIndex hN), ?_⟩
    ext j
    have hj :
        j = lastCoordinateIndex hN ∨
          ∃ i : Fin (N - 1), dropLastCoordinateEmbedding hN i = j := by
      by_cases hlast : j.1 = N - 1
      · left
        apply Fin.ext
        simpa [lastCoordinateIndex, hlast]
      · right
        refine ⟨⟨j.1, ?_⟩, ?_⟩
        · have hjle : j.1 ≤ N - 1 := Nat.le_pred_of_lt j.2
          exact lt_of_le_of_ne hjle hlast
        · apply Fin.ext
          rfl
    rcases hj with rfl | ⟨i, rfl⟩
    · -- The chosen scalar matches the last coordinate by construction.
      simp [smul_eq_mul]
      field_simp [hv]
    · have hcoord : obliqueProjectionToLastHyperplaneCLM hN v x i = 0 := by
        simpa using congrArg (fun y ↦ y i) hx
      rw [obliqueProjectionToLastHyperplaneCLM_apply] at hcoord
      simpa [smul_eq_mul] using (sub_eq_zero.mp hcoord).symm
  · rintro ⟨a, rfl⟩
    ext i
    -- A vector on the line `ℝ v` is killed by the oblique projection by direct computation.
    rw [obliqueProjectionToLastHyperplaneCLM_apply]
    simp [smul_eq_mul, hv]

/-- Helper for Theorem 6.20: rewrite the kernel of the oblique projection as the line `ℝ v`. -/
private lemma obliqueProjectionToLastHyperplaneCLM_ker_eq_span_singleton {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N))
    (hv : v (lastCoordinateIndex hN) ≠ 0) :
    LinearMap.ker (obliqueProjectionToLastHyperplaneCLM hN v).toLinearMap =
      Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin N))) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_span_singleton]
    exact (obliqueProjectionToLastHyperplaneCLM_eq_zero_iff_smul hN v hv).1 hx
  · intro hx
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_span_singleton] at hx
    exact (obliqueProjectionToLastHyperplaneCLM_eq_zero_iff_smul hN v hv).2 hx

/-- Helper for Theorem 6.20: the ambient line `ℝ v` viewed inside the Euclidean tangent space at
`e x`. -/
private def ambientLineAt
    {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (v : EuclideanSpace ℝ (Fin (2 * n))) (x : M) :
    Submodule ℝ (TangentSpace (𝓡 (2 * n)) (e x)) :=
  Submodule.span ℝ
    ({(show TangentSpace (𝓡 (2 * n)) (e x) from v)} :
      Set (TangentSpace (𝓡 (2 * n)) (e x)))

/-- Helper for Theorem 6.20: membership in `ambientLineAt (e := e) v x` means that the tangent
vector is a scalar multiple of the ambient direction `v`. -/
private lemma mem_ambientLineAt_iff
    {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (v : EuclideanSpace ℝ (Fin (2 * n))) (x : M)
    {z : TangentSpace (𝓡 (2 * n)) (e x)} :
    z ∈ ambientLineAt (e := e) v x ↔
      ∃ a : ℝ, a • (show TangentSpace (𝓡 (2 * n)) (e x) from v) = z := by
  -- `ambientLineAt` was defined as the span of the singleton `{v}` inside the tangent fiber.
  rw [ambientLineAt, Submodule.mem_span_singleton]

/-- Helper for Theorem 6.20: a smooth embedding sends a nonzero tangent vector to a nonzero
ambient derivative vector. -/
private lemma mfderiv_ne_zero_of_ne_zero
    {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ e)
    (x : M) {u : TangentSpace (𝓡 n) x} (hu : u ≠ 0) :
    mfderiv (𝓡 n) (𝓡 (2 * n)) e x u ≠ 0 := by
  have heCont : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e := he.isImmersion.contMDiff
  have heInj :
      Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).1 he.isImmersion x
  -- Injectivity of the manifold derivative rules out nonzero tangent vectors mapping to zero.
  intro hZero
  apply hu
  apply heInj
  simpa using hZero

/-- Helper for Theorem 6.20: record the projective class of a nonzero ambient tangent direction of
the embedding `e`. -/
private noncomputable def ambientProjectiveTangentDirection
    {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ e)
    (x : M) (u : TangentSpace (𝓡 n) x) (hu : u ≠ 0) :
    Projectivization ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
  Projectivization.mk ℝ
    (show EuclideanSpace ℝ (Fin (2 * n)) from
      mfderiv (𝓡 n) (𝓡 (2 * n)) e x u)
    (show
      (show EuclideanSpace ℝ (Fin (2 * n)) from
        mfderiv (𝓡 n) (𝓡 (2 * n)) e x u) ≠ 0 from
        mfderiv_ne_zero_of_ne_zero (e := e) he x hu)

/-- Helper for Theorem 6.20: if the projective class of `v` is avoided by every nonzero ambient
tangent direction of `e`, then the line `ℝ v` misses every tangent image. -/
private lemma projectiveDirectionAvoidanceGivesLineDisjointness
    {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ e)
    {v : EuclideanSpace ℝ (Fin (2 * n))} (hv : v ≠ 0)
    (havoid :
      ∀ (x : M) (u : TangentSpace (𝓡 n) x) (hu : u ≠ 0),
        ambientProjectiveTangentDirection (e := e) he x u hu ≠
          Projectivization.mk ℝ v hv) :
    ∀ x : M,
      Disjoint
        (LinearMap.range (mfderiv (𝓡 n) (𝓡 (2 * n)) e x).toLinearMap)
        (ambientLineAt (e := e) v x) := by
  intro x
  refine Submodule.disjoint_def.2 ?_
  intro z hzRange hzLine
  rcases hzRange with ⟨u, rfl⟩
  rw [mem_ambientLineAt_iff] at hzLine
  rcases hzLine with ⟨a, ha⟩
  by_cases hu : u = 0
  · -- The zero tangent vector always maps to the zero ambient derivative vector.
    simpa [hu] using ha
  · -- A nonzero common vector would identify the tangent direction with the projective class of
    -- `v`, contradicting the avoidance hypothesis.
    exfalso
    exact havoid x u hu <| by
      dsimp [ambientProjectiveTangentDirection]
      exact
        (Projectivization.mk_eq_mk_iff' ℝ
          (mfderiv (𝓡 n) (𝓡 (2 * n)) e x u)
          v
          (mfderiv_ne_zero_of_ne_zero (e := e) he x hu)
          hv).2 ⟨a, by simpa using ha⟩

/-- Helper for Theorem 6.20: choose a direction with nonzero last coordinate whose line misses
every embedded tangent line of `e`. -/
private lemma existsProjectionDirectionAvoidingTangentLines
    {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hn : 1 < n)
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ e) :
    ∃ v : EuclideanSpace ℝ (Fin (2 * n)),
      v (lastCoordinateIndex (show 0 < 2 * n by nlinarith [hn])) ≠ 0 ∧
        ∀ x : M,
          Disjoint
            (LinearMap.range (mfderiv (𝓡 n) (𝓡 (2 * n)) e x).toLinearMap)
            (ambientLineAt (e := e) v x) := by
  -- Route correction: the projection and derivative interfaces below are stable. The remaining
  -- missing step is the projectivized tangent-direction argument that produces one ambient line
  -- avoiding every tangent image of the strong embedding.
  -- The bridge from projective avoidance to tangent-line disjointness is now isolated in
  -- `projectiveDirectionAvoidanceGivesLineDisjointness`; only the geometric existence step
  -- remains here.
  -- TODO: realize the source proof on the projectivized tangent bundle of `e`, show the bad
  -- directions form a proper subset of `ℙ(ℝ^(2n))`, and pick a representative with nonzero last
  -- coordinate.
  have _ := hn
  have _ := he
  sorry

/-- Helper for Theorem 6.20: projecting a smooth embedding along a line disjoint from every
tangent image produces an immersion. -/
private lemma isImmersion_compObliqueProjection_of_disjointTangentLines
    {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hn : 1 < n)
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ e)
    {v : EuclideanSpace ℝ (Fin (2 * n))}
    (hv : v (lastCoordinateIndex (show 0 < 2 * n by nlinarith [hn])) ≠ 0)
    (hdisj :
      ∀ x : M,
        Disjoint
          (LinearMap.range (mfderiv (𝓡 n) (𝓡 (2 * n)) e x).toLinearMap)
          (ambientLineAt (e := e) v x)) :
    IsImmersion
      (𝓡 n)
      (𝓡 (2 * n - 1))
      ∞
      (fun x ↦ obliqueProjectionToLastHyperplaneCLM (show 0 < 2 * n by nlinarith [hn]) v (e x)) := by
  let hN : 0 < 2 * n := by
    nlinarith [hn]
  let P : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n - 1)) :=
    obliqueProjectionToLastHyperplaneCLM hN v
  let F : M → EuclideanSpace ℝ (Fin (2 * n - 1)) := fun x ↦ P (e x)
  have heCont : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e := he.isImmersion.contMDiff
  have hFCont : ContMDiff (𝓡 n) (𝓡 (2 * n - 1)) ∞ F := by
    -- The projected map is smooth because it is the composition of a smooth embedding with a
    -- continuous linear map.
    simpa [F, P, Function.comp] using P.contMDiff.comp heCont
  have heInj :
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).1 he.isImmersion
  -- To prove immersion, it suffices to show that each projected derivative stays injective.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFCont).2 ?_
  intro x u w huw
  have hPdiff :
      mfderiv (𝓡 n) (𝓡 (2 * n - 1)) F x (u - w) = 0 := by
    -- Equality of derivative values implies that the derivative kills the difference.
    have hsub :
        mfderiv (𝓡 n) (𝓡 (2 * n - 1)) F x u -
          mfderiv (𝓡 n) (𝓡 (2 * n - 1)) F x w = 0 := by
      simpa [huw]
    simpa [map_sub] using hsub
  have hComp :
      mfderiv (𝓡 n) (𝓡 (2 * n - 1)) F x = P.comp (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
    -- The chain rule identifies the projected derivative with the composed linear map.
    simpa [F, P, Function.comp] using
      (mfderiv_comp (x := x)
        (g := P)
        (f := e)
        (P.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
        (heCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
  have hInKernel :
      mfderiv (𝓡 n) (𝓡 (2 * n)) e x (u - w) ∈ LinearMap.ker P.toLinearMap := by
    -- The derivative difference lands in the kernel of the oblique projection.
    have hPzero : P (mfderiv (𝓡 n) (𝓡 (2 * n)) e x (u - w)) = 0 := by
      calc
        P (mfderiv (𝓡 n) (𝓡 (2 * n)) e x (u - w)) =
            mfderiv (𝓡 n) (𝓡 (2 * n - 1)) F x (u - w) := by
              rw [hComp]
              rfl
        _ = 0 := hPdiff
    simpa [LinearMap.mem_ker] using hPzero
  have hInLine :
      mfderiv (𝓡 n) (𝓡 (2 * n)) e x (u - w) ∈ ambientLineAt (e := e) v x := by
    -- The kernel computation identifies that kernel with the ambient line `ℝ v`.
    have hInSpan :
        mfderiv (𝓡 n) (𝓡 (2 * n)) e x (u - w) ∈
          Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin (2 * n)))) := by
      rw [← obliqueProjectionToLastHyperplaneCLM_ker_eq_span_singleton hN v hv]
      exact hInKernel
    simpa [ambientLineAt] using hInSpan
  have hInRange :
      mfderiv (𝓡 n) (𝓡 (2 * n)) e x (u - w) ∈
        LinearMap.range (mfderiv (𝓡 n) (𝓡 (2 * n)) e x).toLinearMap := by
    -- The derivative value is tautologically in its own range.
    exact ⟨u - w, rfl⟩
  have hAmbientZero :
      mfderiv (𝓡 n) (𝓡 (2 * n)) e x (u - w) = 0 := by
    -- Disjointness of the tangent image and the chosen ambient line forces the overlap to vanish.
    exact (Submodule.disjoint_def.mp (hdisj x)) _ hInRange hInLine
  have hDiffZero : u - w = 0 := by
    -- Injectivity of the original embedding derivative kills the tangent difference itself.
    apply heInj x
    simpa using hAmbientZero
  exact sub_eq_zero.mp hDiffZero

/-- Theorem 6.20 (Strong Whitney Immersion Theorem). If `n > 1`, every smooth `n`-manifold admits
a smooth immersion into `ℝ^(2n - 1)`. -/
theorem strong_whitney_immersion (hn : 1 < n) :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n - 1)),
      IsImmersion (𝓡 n) (𝓡 (2 * n - 1)) ∞ F := by
  have hAssemble :
      (∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
        IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ e) →
      ∃ F : M → EuclideanSpace ℝ (Fin (2 * n - 1)),
        IsImmersion (𝓡 n) (𝓡 (2 * n - 1)) ∞ F := by
    intro hEmbedding
    obtain ⟨e, he⟩ := hEmbedding
    obtain ⟨v, hv, hdisj⟩ := existsProjectionDirectionAvoidingTangentLines
      (M := M) (n := n) hn he
    refine ⟨
      fun x ↦ obliqueProjectionToLastHyperplaneCLM
        (show 0 < 2 * n by nlinarith [hn]) v (e x),
      ?_⟩
    -- Compose the strong embedding with the chosen oblique projection direction.
    exact isImmersion_compObliqueProjection_of_disjointTangentLines
      (M := M) (n := n) hn he hv hdisj
  -- Route correction: the local projection-to-immersion assembly is verified, but the intended
  -- dependency-closed strong embedding owner in dimension `2 * n` is currently blocked by the
  -- broken `Lemma_6_14` chain behind `Theorem_6_19`.
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have _ := hn0
  have _ := hAssemble
  -- TODO: once the earlier strong embedding theorem compiles in dependency order again, feed its
  -- witness directly to `hAssemble`.
  sorry

end

end

end Manifold
