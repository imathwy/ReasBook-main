import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.IsLocalHomeomorph
import SmoothManifoldsLee.Chap01.Sec01_04.Example_1_23
import SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28

open scoped Manifold ContDiff

-- Declarations for this item will be appended below by the statement pipeline.

/-- The cubic counterexample is smooth as a map of smooth manifolds on `ℝ`. -/
-- Proof sketch: identify the map with the polynomial function `x ↦ x^3` and apply the standard
-- `ContMDiff` closure theorem for powers of smooth maps.
theorem cubicMap_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ cubicMap := by
  simpa [cubicMap] using ((contMDiff_id : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ fun x : ℝ ↦ x).pow 3)

/-- The cubic map is a topological submersion of `ℝ`. -/
-- Proof sketch: reuse the upstream owner chain
-- `cubicMap_isOpenEmbedding.isLocalHomeomorph.isTopologicalSubmersion`.
theorem cubicMap_isTopologicalSubmersion :
    Topology.IsTopologicalSubmersion cubicMap :=
  cubicMap_isOpenEmbedding.isLocalHomeomorph.isTopologicalSubmersion

/-- The cubic map is not a smooth submersion for the standard smooth structures on `ℝ`. -/
-- Proof sketch: if `cubicMap` were a smooth submersion, then
-- `Manifold.is_smooth_submersion_iff_forall_surjective_mfderiv` would force every manifold
-- derivative to be surjective, contradicting `cubicMap_not_surjective_mfderiv_zero`.
theorem cubicMap_not_isSmoothSubmersion :
    ¬ Manifold.IsSmoothSubmersion 𝓘(ℝ) 𝓘(ℝ) cubicMap := by
  intro hsubmersion
  -- A smooth submersion has surjective manifold derivative at each source point.
  have hsurj : Function.Surjective (mfderiv% cubicMap 0) :=
    hsubmersion.surjective_mfderiv 0
  -- Compute the derivative at the origin as the zero map.
  rw [mfderiv_eq_fderiv] at hsurj
  change Function.Surjective (fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0) at hsurj
  have hzero : fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 = 0 := by
    simpa using
      (fderiv_pow_ring 3 :
        fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 =
          (3 • (0 : ℝ) ^ (3 - 1)) • ContinuousLinearMap.id ℝ ℝ)
  rw [hzero] at hsurj
  -- The zero map `ℝ →L[ℝ] ℝ` cannot be surjective because it misses `1`.
  rcases hsurj 1 with ⟨x, hx⟩
  simp at hx

/-- The manifold derivative of the cubic counterexample at `0` is not surjective, so this example
is not a smooth submersion at the origin. -/
-- Proof sketch: compute that the derivative of `x ↦ x^3` at `0` is the zero continuous linear map,
-- and observe that the zero map `ℝ →L[ℝ] ℝ` is not surjective.
theorem cubicMap_not_surjective_mfderiv_zero :
    ¬ Function.Surjective (mfderiv% cubicMap 0) := by
  rw [mfderiv_eq_fderiv]
  change ¬ Function.Surjective (fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0)
  have hzero : fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 = 0 := by
    simpa using
      (fderiv_pow_ring 3 :
        fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 =
          (3 • (0 : ℝ) ^ (3 - 1)) • ContinuousLinearMap.id ℝ ℝ)
  rw [hzero]
  intro hsurj
  rcases hsurj 1 with ⟨x, hx⟩
  simp at hx

/-- Exercise 4.27: the cubic map `x ↦ x^3` on `ℝ` is a topological submersion but not a smooth
submersion for the standard smooth structures. -/
-- Proof sketch: combine `cubicMap_isTopologicalSubmersion` with
-- `cubicMap_not_isSmoothSubmersion`.
theorem cubic_submersion_counterexample :
    Topology.IsTopologicalSubmersion cubicMap ∧
      ¬ Manifold.IsSmoothSubmersion 𝓘(ℝ) 𝓘(ℝ) cubicMap := by
  exact ⟨cubicMap_isTopologicalSubmersion, cubicMap_not_isSmoothSubmersion⟩
