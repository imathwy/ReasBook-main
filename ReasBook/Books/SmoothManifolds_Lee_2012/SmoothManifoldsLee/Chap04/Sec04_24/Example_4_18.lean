import Mathlib
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open Topology
open scoped Manifold ContDiff

local notation "Plane" => ℝ × ℝ

/-- The map `t ↦ (t^3, 0)` from `ℝ` to `ℝ²`. -/
def cubicAxisMap : ℝ → Plane :=
  fun t ↦ (t ^ 3, 0)

/-- Example 4.18 (1): The map `γ(t) = (t^3, 0)` is smooth. -/
-- Proof sketch: Each coordinate is a smooth real-valued function; the first is a polynomial and
-- the second is constant, so the product map is smooth.
theorem cubicAxisMap_contDiff :
    ContDiff ℝ ∞ cubicAxisMap := by
  -- View `γ` as the product of the cubic coordinate and the constant zero coordinate.
  simpa [cubicAxisMap] using
    (((contDiff_id : ContDiff ℝ ∞ fun t : ℝ ↦ t).pow 3).prodMk
      (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ ↦ (0 : ℝ)))

/-- Helper for Example 4.18: the range of the real cubic map is order-connected. -/
lemma real_cubic_range_ordConnected :
    Set.OrdConnected (Set.range (fun t : ℝ ↦ t ^ (3 : ℕ))) := by
  -- The image of the connected line under a continuous map is preconnected.
  refine (isPreconnected_range ?_).ordConnected
  simpa using (continuous_id.pow 3 : Continuous fun t : ℝ ↦ t ^ (3 : ℕ))

/-- Helper for Example 4.18: the real cubic map is a topological embedding. -/
lemma real_cubic_isEmbedding :
    IsEmbedding (fun t : ℝ ↦ t ^ (3 : ℕ)) := by
  -- Strict monotonicity makes the cubic an order embedding onto its range.
  have hodd : Odd (3 : ℕ) := by decide
  exact (Odd.strictMono_pow (R := ℝ) hodd).isEmbedding_of_ordConnected
    real_cubic_range_ordConnected

/-- Example 4.18 (2): The map `γ(t) = (t^3, 0)` is a topological embedding. -/
-- Proof sketch: The first coordinate `t ↦ t^3` is strictly monotone and hence a homeomorphism
-- onto its image; the constant second coordinate identifies the image with the x-axis in `ℝ²`.
theorem cubicAxisMap_isEmbedding :
    IsEmbedding cubicAxisMap := by
  -- Factor `γ` as the cubic map followed by the inclusion of the x-axis in `ℝ²`.
  simpa [cubicAxisMap] using
    (isEmbedding_prodMkLeft (0 : ℝ)).comp real_cubic_isEmbedding

/-- Example 4.18 (3): The derivative of `γ(t) = (t^3, 0)` vanishes at `0`. -/
-- Proof sketch: Compute the Fréchet derivative coordinatewise. The derivative of `t ↦ t^3` at `0`
-- is `3 * 0^2 = 0`, and the second coordinate is constant.
theorem cubicAxisMap_fderiv_zero :
    fderiv ℝ cubicAxisMap 0 = 0 := by
  -- Differentiate the two coordinate functions separately and recombine them.
  have hprod :
      fderiv ℝ cubicAxisMap 0 =
        (fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0).prod
          (fderiv ℝ (fun _ : ℝ ↦ (0 : ℝ)) 0) := by
    have hpow : DifferentiableAt ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 := differentiableAt_id.pow 3
    have hconst : DifferentiableAt ℝ (fun _ : ℝ ↦ (0 : ℝ)) 0 :=
      differentiableAt_const (c := (0 : ℝ))
    simpa [cubicAxisMap] using hpow.fderiv_prodMk hconst
  -- The cubic derivative vanishes at the origin, and the constant coordinate has zero derivative.
  have hpow_zero : fderiv ℝ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 = 0 := by
    simpa using (fderiv_pow_ring (𝕜 := ℝ) (𝔸 := ℝ) (x := 0) 3)
  rw [hprod, hpow_zero, fderiv_const_apply]
  ext <;> simp

/-- Helper for Example 4.18: the manifold derivative of `cubicAxisMap` at `0` is not injective. -/
lemma cubicAxisMap_mfderiv_not_injective_zero :
    ¬ Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) cubicAxisMap 0) := by
  -- In Euclidean model spaces, the manifold derivative is the ordinary Fréchet derivative.
  rw [mfderiv_eq_fderiv, cubicAxisMap_fderiv_zero]
  intro hinj
  -- The zero linear map identifies `0` and `1`, so it cannot be injective.
  have hmap : (0 : ℝ →L[ℝ] Plane) 0 = (0 : ℝ →L[ℝ] Plane) 1 := by
    simp
  have h01 : (0 : ℝ) = 1 := hinj hmap
  exact zero_ne_one h01

/-- The map `γ(t) = (t^3, 0)` is not a smooth immersion. -/
-- Proof sketch: a smooth immersion into `ℝ²` has nonzero derivative at every point. At `0`, the
-- derivative of `cubicAxisMap` vanishes by `cubicAxisMap_fderiv_zero`, so the immersion condition
-- fails there.
theorem cubicAxisMap_not_isImmersion :
    ¬ IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ cubicAxisMap := by
  intro himmersion
  -- A smooth immersion has injective manifold derivative at every point.
  have hcontMDiff : ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ cubicAxisMap :=
    cubicAxisMap_contDiff.contMDiff
  have hinj :
      Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) cubicAxisMap 0) :=
    ((Manifold.is_immersion_iff_forall_injective_mfderiv hcontMDiff).mp himmersion) 0
  exact cubicAxisMap_mfderiv_not_injective_zero hinj

/-- Example 4.18 (4): The map `γ(t) = (t^3, 0)` is not a smooth embedding. -/
-- Proof sketch: A smooth embedding is a smooth immersion together with a topological embedding.
-- The immersion field of `IsSmoothEmbedding` is ruled out by `cubicAxisMap_not_isImmersion`.
theorem cubicAxisMap_not_isSmoothEmbedding :
    ¬ IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ cubicAxisMap := by
  intro h
  exact cubicAxisMap_not_isImmersion h.isImmersion
