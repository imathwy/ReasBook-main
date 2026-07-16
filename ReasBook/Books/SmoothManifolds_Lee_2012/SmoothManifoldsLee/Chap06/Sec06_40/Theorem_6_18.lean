import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Maps.Proper.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_14.Proposition_3_10
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_39.Corollary_6_11

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the local
-- Section 6.40 Whitney files and mathlib's `WhitneyEmbedding` module were inspected directly.
-- The source-facing owner here follows the repository convention that "with or without boundary"
-- is expressed by `SmoothManifoldWithBoundary n M`, with smoothness measured against
-- `leeBoundaryModelWithCorners n`.

open scoped ContDiff Manifold
open Manifold
open Bundle
open MeasureTheory
open Set

section

universe uM

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]

/-- Helper for Theorem 6.18: package the ambient derivative vectors of `G` as a smooth map on the
full tangent bundle of `M`. -/
noncomputable def ambientTangentVector
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))} :
    TangentBundle (leeBoundaryModelWithCorners n) M → EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  fun u ↦ (tangentMap (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) G u).2

/-- Helper for Theorem 6.18: on a concrete tangent vector `u ∈ T_x M`, the ambient tangent-vector
map returns the manifold derivative `mfderiv ... G x u`. -/
lemma ambientTangentVector_apply
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (x : M) (u : TangentSpace (leeBoundaryModelWithCorners n) x) :
    ambientTangentVector (n := n) (G := G) ⟨x, u⟩ =
      mfderiv (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) G x u := by
  -- Route correction: in the direct `tangentMap` spelling, the second component is exactly the
  -- manifold derivative on the chosen tangent vector.
  simpa [ambientTangentVector] using
    (tangentMap_snd
      (I := leeBoundaryModelWithCorners n)
      (I' := 𝓡 (2 * n + 1))
      (f := G)
      (x := x)
      (X := u))

/-- Helper for Theorem 6.18: the ambient tangent-vector map is smooth when `G` is smooth. -/
lemma ambientTangentVector_contMDiff
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : ContMDiff (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ G) :
    ContMDiff
      (leeBoundaryModelWithCorners n).tangent
      (𝓡 (2 * n + 1))
      ∞
      (ambientTangentVector (n := n) (G := G)) := by
  -- Compose the smooth bundled derivative with the smooth projection to the tangent fiber.
  simpa [ambientTangentVector, Function.comp] using
    (contMDiff_snd_tangentBundle_modelSpace
      (EuclideanSpace ℝ (Fin (2 * n + 1)))
      (𝓡 (2 * n + 1))).comp
      ((hG.contMDiff_tangentMap (m := ∞) le_rfl))

/-- Helper for Theorem 6.18: some ambient direction with nonzero last coordinate is missed by all
ambient derivative vectors of `G`. -/
lemma existsDirectionOutsideAmbientTangentRange
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ G) :
    ∃ v : EuclideanSpace ℝ (Fin (2 * n + 1)),
      v (Fin.last (2 * n)) ≠ 0 ∧
        v ∉ Set.range (ambientTangentVector (n := n) (G := G)) := by
  -- Route correction: the normalized `ambientTangentVector` is ready, so the intended next step is
  -- to apply Corollary 6.11 to this tangent-bundle map, convert the resulting Euclidean
  -- measure-zero statement into an a.e.-dense complement, and choose a point in the open
  -- half-space where the last coordinate is nonzero.
  -- TODO: provide the missing separation/countability bridge for
  -- `TangentBundle (leeBoundaryModelWithCorners n) M` (or an equivalent chartwise density lemma),
  -- then finish the witness choice by intersecting the dense complement with that half-space.
  sorry

/-- Helper for Theorem 6.18: identify `ℝ^(2 * n + 1)` with its coordinate functions. -/
noncomputable def ambientCoordinateCLM :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] (Fin (2 * n + 1) → ℝ) :=
  ↑(EuclideanSpace.equiv (Fin (2 * n + 1)) ℝ)

/-- Helper for Theorem 6.18: drop the last coordinate of `ℝ^(2 * n + 1)` as a continuous linear
map into `ℝ^(2 * n)`. -/
noncomputable def dropLastCoordinatesCLM :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  ((↑(EuclideanSpace.equiv (Fin (2 * n)) ℝ).symm :
      (Fin (2 * n) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).comp
    ((ContinuousLinearMap.pi
      (fun i : Fin (2 * n) =>
        (ContinuousLinearMap.proj
          (R := ℝ)
          (ι := Fin (2 * n + 1))
          (φ := fun _ : Fin (2 * n + 1) => ℝ)
          (i := Fin.castSucc i)))).comp
      (ambientCoordinateCLM (n := n))))

/-- Helper for Theorem 6.18: evaluate the last coordinate of `ℝ^(2 * n + 1)` as a continuous
linear functional. -/
noncomputable def lastCoordinateCLM :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj
      (R := ℝ)
      (ι := Fin (2 * n + 1))
      (φ := fun _ : Fin (2 * n + 1) => ℝ)
      (i := Fin.last (2 * n))).comp
    ambientCoordinateCLM

/-- Helper for Theorem 6.18: record the first `2 * n` coordinates of a direction
`v ∈ ℝ^(2 * n + 1)`. -/
noncomputable def truncatedDirection
    (v : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  (EuclideanSpace.equiv (Fin (2 * n)) ℝ).symm fun i ↦ v (Fin.castSucc i)

/-- Helper for Theorem 6.18: the codimension-one oblique projection along the line `ℝ v` onto the
last-coordinate hyperplane, written as a continuous linear map. -/
noncomputable def projectionAlongLastHyperplaneCLM
    (v : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  dropLastCoordinatesCLM (n := n) -
    (lastCoordinateCLM (n := n)).smulRight
      ((v (Fin.last (2 * n)))⁻¹ • truncatedDirection (n := n) v)

/-- Helper for Theorem 6.18: the projection along `v` subtracts the unique multiple of `v` that
kills the last coordinate. -/
lemma projectionAlongLastHyperplaneCLM_apply
    (v x : EuclideanSpace ℝ (Fin (2 * n + 1))) (i : Fin (2 * n)) :
    projectionAlongLastHyperplaneCLM (n := n) v x i =
      x (Fin.castSucc i) -
        (x (Fin.last (2 * n)) / v (Fin.last (2 * n))) * v (Fin.castSucc i) := by
  -- Expanding the linear map shows the coordinatewise projection formula directly.
  simp [projectionAlongLastHyperplaneCLM, dropLastCoordinatesCLM, lastCoordinateCLM,
    ambientCoordinateCLM, truncatedDirection, div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_assoc]

/-- Helper for Theorem 6.18: the kernel of the oblique projection along `v` is exactly the line
spanned by `v`, provided the last coordinate of `v` is nonzero. -/
lemma projectionAlongLastHyperplaneCLM_eq_zero_iff_smul
    (v : EuclideanSpace ℝ (Fin (2 * n + 1)))
    (hv : v (Fin.last (2 * n)) ≠ 0)
    {x : EuclideanSpace ℝ (Fin (2 * n + 1))} :
    projectionAlongLastHyperplaneCLM (n := n) v x = 0 ↔ ∃ a : ℝ, x = a • v := by
  constructor
  · intro hx
    refine ⟨x (Fin.last (2 * n)) / v (Fin.last (2 * n)), ?_⟩
    ext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hcoord : projectionAlongLastHyperplaneCLM (n := n) v x i = 0 := by
        simpa using congrArg (fun y ↦ y i) hx
      rw [projectionAlongLastHyperplaneCLM_apply] at hcoord
      exact (sub_eq_zero.mp hcoord).trans (by simp [smul_eq_mul, mul_comm])
    · -- The chosen scalar matches the last coordinate by construction.
      simp [smul_eq_mul]
      field_simp [hv]
  · rintro ⟨a, rfl⟩
    ext i
    -- A vector on the line `ℝ v` is killed by the projection by a direct coordinate computation.
    rw [projectionAlongLastHyperplaneCLM_apply]
    simp [smul_eq_mul, hv]

/-- Helper for Theorem 6.18: the with-boundary weak Whitney theorem should supply a proper smooth
embedding into `ℝ^(2 * n + 1)`. -/
lemma existsProperSmoothEmbedding_withBoundary :
    ∃ G : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ G ∧
        IsProperMap G := by
  -- Route correction: importing `Theorem_6_15` would be the correct dependency-closed reuse, but
  -- that earlier file does not currently compile in this repo state.
  -- TODO: once `Theorem_6_15.lean` compiles, replace this local frontier by a direct reuse of
  -- `weak_whitney_embedding_with_boundary`.
  sorry

/-- Helper for Theorem 6.18: the remaining codimension-one step says that a proper smooth
embedding into `ℝ^(2 * n + 1)` can be projected to a smooth immersion into `ℝ^(2 * n)`. -/
lemma existsGoodProjection_isImmersion_ofProperSmoothEmbedding
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ G)
    (hproper : IsProperMap G) :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n)),
      IsImmersion (leeBoundaryModelWithCorners n) (𝓡 (2 * n)) ∞ F := by
  -- Route correction: the linear-algebra half is now isolated in
  -- `projectionAlongLastHyperplaneCLM_eq_zero_iff_smul`, but the tangent-range half still needs
  -- the missing-direction lemma above before the final injectivity argument can be assembled.
  -- TODO: combine `existsDirectionOutsideAmbientTangentRange` with the proved kernel-line lemma
  -- to finish the pointwise `mfderiv` injectivity check for the projected map
  -- `projectionAlongLastHyperplaneCLM v ∘ G`.
  sorry

/-- Theorem 6.18 (Whitney Immersion Theorem). Every smooth `n`-manifold with or without boundary
admits a smooth immersion into `ℝ^(2n)`. -/
theorem whitney_immersion :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n)),
      IsImmersion (leeBoundaryModelWithCorners n) (𝓡 (2 * n)) ∞ F := by
  -- First obtain the proper smooth embedding promised by the weak Whitney theorem with boundary.
  obtain ⟨G, hG, hproper⟩ := existsProperSmoothEmbedding_withBoundary (n := n) (M := M)
  -- The only remaining work is the codimension-one projection step isolated above.
  exact existsGoodProjection_isImmersion_ofProperSmoothEmbedding hG hproper

end
