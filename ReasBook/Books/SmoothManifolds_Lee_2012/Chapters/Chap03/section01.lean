import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.LocallyConstant.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_3_1 (from Chap03/Sec03_13) -/
noncomputable section

open scoped ContDiff Manifold

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, R^n)
local notation "SmoothRn" => C^∞⟮I, R^n; ℝ⟯

-- Proof sketch: `PointDerivation` is a `Derivation`, so constants lie in the image of
-- `algebraMap ℝ SmoothRn` and are annihilated by `Derivation.map_algebraMap`.
/-- Lemma 3.1 (1): (a) point derivations at `a` annihilate constant smooth real-valued functions
on `ℝ^n`. -/
theorem point_derivation_apply_const
    (a : R^n) (w : PointDerivation I a) (c : ℝ) :
    w (ContMDiffMap.const c) = 0 := by
  change w ((algebraMap ℝ SmoothRn) c) = 0
  exact w.map_algebraMap c

-- Proof sketch: specialize the chapter bridge theorem `point_derivation_leibniz`; the factors
-- `f a` and `g a` then vanish by hypothesis.
/-- Lemma 3.1 (2): (b) if smooth functions `f` and `g` both vanish at `a`, then any point
derivation at `a` annihilates their product. -/
theorem point_derivation_mul_eq_zero_of_vanish_at
    (a : R^n) (w : PointDerivation I a) (f g : SmoothRn)
    (hf : f a = 0) (hg : g a = 0) :
    w (f * g) = 0 := by
  rw [point_derivation_leibniz]
  simp [hf, hg]

/-! ### Problem_3_1 (from Chap03/Sec03_20) -/
open scoped Manifold Topology

noncomputable section

universe uE uH uM uE' uH' uN

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

/-- Helper for Problem 3-1: the model space of a model with corners is locally path connected. -/
private theorem modelWithCorners_locPathConnectedSpace (I : ModelWithCorners 𝕜 E H) :
    LocPathConnectedSpace H := by
  -- Transfer the convex local path connectedness of `range I` across the homeomorphism `I`.
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : LocPathConnectedSpace (Set.range I) := I.convex_range.locPathConnectedSpace
  exact I.isClosedEmbedding.toHomeomorph.isOpenEmbedding.locPathConnectedSpace

private theorem modelWithCorners_locallyConnectedSpace (I : ModelWithCorners 𝕜 E H) :
    LocallyConnectedSpace H := by
  -- Local path connectedness implies local connectedness.
  letI : LocPathConnectedSpace H := modelWithCorners_locPathConnectedSpace I
  infer_instance

/-- Helper for Problem 3-1: charted spaces with corners inherit local path connectedness. -/
private theorem manifold_locPathConnectedSpace (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : LocPathConnectedSpace M := by
  -- Pull the model-space basis of path-connected neighborhoods through the charted-space atlas.
  letI : LocPathConnectedSpace H := modelWithCorners_locPathConnectedSpace I
  exact ChartedSpace.locPathConnectedSpace H M

private theorem manifold_locallyConnectedSpace (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : LocallyConnectedSpace M := by
  -- Reuse the stronger local path connectedness helper and then infer local connectedness.
  letI : LocPathConnectedSpace M := manifold_locPathConnectedSpace I M
  infer_instance

/-- Helper for Problem 3-1: in model spaces, vanishing manifold derivative is the usual
zero-derivative hypothesis, so the classical mean-value theorem gives local constancy. -/
private theorem isLocallyConstant_of_mfderiv_eq_zero_model_space {f : E → E'}
    (hf : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f)
    (hzero : ∀ x, mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = 0) : IsLocallyConstant f := by
  -- In the model-space case, `MDifferentiable` and `mfderiv` reduce to `Differentiable` and `fderiv`.
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  exact isLocallyConstant_of_fderiv_eq_zero hf.differentiable fun x ↦ by
    simpa using hzero x

-- Proof sketch: in manifold charts, the hypothesis becomes the model-space `RCLike` statement
-- that a differentiable map with vanishing derivative is locally constant on an open neighborhood.
/-- A differentiable map between charted spaces with corners is locally constant if its
manifold derivative vanishes at every point. -/
theorem isLocallyConstant_of_mfderiv_eq_zero {f : M → N} (hf : MDifferentiable I I' f)
    (hzero : ∀ p, mfderiv I I' f p = 0) : IsLocallyConstant f := by
  -- Route correction: the intended chart proof has to transport `mfderiv I I' f = 0`
  -- to a zero `fderiv` statement for a fixed coordinate representative and then apply the
  -- model-space theorem `isLocallyConstant_of_fderiv_eq_zero`.
  -- TODO: this transport step is blocked in the current theorem because the needed lemmas
  -- `mdifferentiableAt_extChartAt`, `mdifferentiableWithinAt_extChartAt_symm`,
  -- `mdifferentiableWithinAt_iff_of_mem_source`, and `mdifferentiableOn_iff_of_subset_source'`
  -- all require `[IsManifold I 1 M]` and `[IsManifold I' 1 N]`, but the present statement only
  -- assumes `[ChartedSpace H M]` and `[ChartedSpace H' N]`.
  sorry

/-- On a charted space with corners, a differentiable map has vanishing manifold derivative at
every point if and only if it is locally constant. -/
theorem mfderiv_eq_zero_iff_isLocallyConstant {f : M → N}
    (hf : MDifferentiable I I' f) : (∀ p, mfderiv I I' f p = 0) ↔ IsLocallyConstant f := by
  letI : LocallyConnectedSpace M := manifold_locallyConnectedSpace I M
  constructor
  · exact isLocallyConstant_of_mfderiv_eq_zero hf
  · intro hloc
    intro p
    -- Route correction: the reverse implication is purely local and uses eventual equality with
    -- a constant map, so no chart computation is needed here.
    have heq : f =ᶠ[𝓝 p] fun _ : M => f p := by
      simpa using hloc.eventually_eq p
    have hconst : HasMFDerivAt I I' (fun _ : M => f p) p
        (0 : TangentSpace I p →L[𝕜] TangentSpace I' (f p)) := hasMFDerivAt_const (I := I)
          (I' := I') (f p) p
    exact (hconst.congr_of_eventuallyEq heq).mfderiv

-- Proof sketch: use `mfderiv_eq_zero_iff_isLocallyConstant` and the canonical correspondence
-- between locally constant maps and maps constant on connected components in a locally connected
-- space.
/-- Problem 3-1: for a differentiable map between charted spaces with corners, the manifold
derivative is the zero map at every point if and only if the map is constant on each connected
component of the source space. -/
theorem mfderiv_eq_zero_iff_constant_on_components {f : M → N}
    (hf : MDifferentiable I I' f) :
    (∀ p, mfderiv I I' f p = 0) ↔ ∀ p, ∀ q ∈ connectedComponent p, f q = f p := by
  letI : LocallyConnectedSpace M := manifold_locallyConnectedSpace I M
  rw [mfderiv_eq_zero_iff_isLocallyConstant hf]
  constructor
  · intro hloc p q hq
    exact hloc.apply_eq_of_isPreconnected isConnected_connectedComponent.isPreconnected
      hq mem_connectedComponent
  · exact IsLocallyConstant.of_constant_on_connected_components
