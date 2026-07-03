import Mathlib
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_35_extra_2 (from Chap05/Sec05_35) -/
open scoped Manifold ContDiff

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

/-- A tangent vector at a boundary point is tangent to the boundary when it is the velocity of a
smooth curve through that point whose image stays in the boundary near the parameter value `0`. -/
def IsBoundaryTangentVector (p : M) (v : TangentSpace I p) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
    ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo (-ε) ε) ∧
    (∀ t ∈ Set.Ioo (-ε) ε, γ t ∈ I.boundary M) ∧
    ∃ hγ : γ 0 = p,
      hγ ▸ curve_velocityWithin I γ (Set.Ioo (-ε) ε) 0 = v

omit [IsManifold I ∞ M] in
/-- A boundary-tangent vector is based at a boundary point. -/
theorem IsBoundaryTangentVector.mem_boundary {p : M} {v : TangentSpace I p}
    (hv : IsBoundaryTangentVector p v) : p ∈ I.boundary M := by
  rcases hv with ⟨ε, hε, γ, _, hγ_boundary, hγ0, _⟩
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  simpa [hγ0] using hγ_boundary 0 h0

/-- A tangent vector has an inward half-curve realization when it is represented by a smooth curve
defined on a right half-interval `[0, ε)` through the boundary point `p`. -/
def HasInwardCurveVelocity (p : M) (v : TangentSpace I p) : Prop :=
  p ∈ I.boundary M ∧
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ico 0 ε) ∧
      ∃ hγ : γ 0 = p,
        hγ ▸ curve_velocityWithin I γ (Set.Ico 0 ε) 0 = v

/-- A tangent vector has an outward half-curve realization when it is represented by a smooth curve
defined on a left half-interval `(-ε, 0]` through the boundary point `p`. -/
def HasOutwardCurveVelocity (p : M) (v : TangentSpace I p) : Prop :=
  p ∈ I.boundary M ∧
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioc (-ε) 0) ∧
      ∃ hγ : γ 0 = p,
        hγ ▸ curve_velocityWithin I γ (Set.Ioc (-ε) 0) 0 = v

/-- Definition 5.35-extra-2 (1): an inward-pointing tangent vector at a boundary point is a vector
that is not tangent to the boundary and is realized by a smooth curve on a right half-interval. -/
@[mk_iff isInwardPointing_iff]
class IsInwardPointing (p : M) (v : TangentSpace I p) : Prop where
  /-- An inward-pointing vector is not tangent to the boundary. -/
  not_isBoundaryTangentVector : ¬IsBoundaryTangentVector p v
  /-- An inward-pointing vector has an inward half-curve realization. -/
  hasInwardCurveVelocity : HasInwardCurveVelocity p v

/-- An inward-pointing vector canonically yields its inward half-curve realization as a `Fact`. -/
instance isInwardPointing_fact_hasInwardCurveVelocity (p : M) (v : TangentSpace I p)
    [h : IsInwardPointing p v] : Fact (HasInwardCurveVelocity p v) where
  out := h.hasInwardCurveVelocity

/-- Definition 5.35-extra-2 (2): an outward-pointing tangent vector at a boundary point is a
vector that is not tangent to the boundary and is realized by a smooth curve on a left
half-interval. -/
@[mk_iff isOutwardPointing_iff]
class IsOutwardPointing (p : M) (v : TangentSpace I p) : Prop where
  /-- An outward-pointing vector is not tangent to the boundary. -/
  not_isBoundaryTangentVector : ¬IsBoundaryTangentVector p v
  /-- An outward-pointing vector has an outward half-curve realization. -/
  hasOutwardCurveVelocity : HasOutwardCurveVelocity p v

/-- An outward-pointing vector canonically yields its outward half-curve realization as a `Fact`. -/
instance isOutwardPointing_fact_hasOutwardCurveVelocity (p : M) (v : TangentSpace I p)
    [h : IsOutwardPointing p v] : Fact (HasOutwardCurveVelocity p v) where
  out := h.hasOutwardCurveVelocity

/-! ### Definition_5_35_extra_3 (from Chap05/Sec05_35) -/
open scoped ContDiff Manifold

section

universe uM

variable {n : ℕ} [NeZero n]
variable (M : Type uM) [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

/-- Definition 5.35-extra-3: a boundary defining function on a smooth manifold with boundary is a
smooth real-valued function that is nonnegative everywhere, vanishes exactly on the manifold
boundary, and has nonzero manifold derivative at every boundary point. -/
structure BoundaryDefiningFunction where
  /-- The underlying smooth real-valued function. -/
  toSmoothMap : C^∞⟮𝓡∂ n, M; ℝ⟯
  /-- The function takes values in `[0, ∞)`. -/
  nonneg_toSmoothMap : ∀ x : M, 0 ≤ toSmoothMap x
  /-- The zero set of the function is exactly the boundary of the manifold. -/
  zero_preimage : toSmoothMap ⁻¹' {0} = (𝓡∂ n).boundary M
  /-- The manifold derivative is nonzero at every boundary point. -/
  mfderiv_ne_zero :
    ∀ p : M, p ∈ (𝓡∂ n).boundary M → mfderiv (𝓡∂ n) 𝓘(ℝ) toSmoothMap p ≠ 0

/-- A boundary defining function can be used as its underlying real-valued function. -/
noncomputable instance : CoeFun (BoundaryDefiningFunction (n := n) (M := M)) (fun _ ↦ M → ℝ) where
  coe f := f.toSmoothMap

end

/-! ### Definition_5_35_extra_4 (from Chap05/Sec05_35) -/
open scoped ContDiff
open Manifold

noncomputable section

local notation "Plane" => ℝ × ℝ

namespace Set

/-- A subset of `ℝ²` admits an embedded-curve structure when its subtype carries a smooth
boundaryless `1`-manifold structure for which the inclusion into `ℝ²` is an embedded
submanifold. -/
abbrev AdmitsEmbeddedCurveStructure (S : Set Plane) : Prop :=
  ∃ _ : ChartedSpace ℝ S, ∃ _ : IsManifold 𝓘(ℝ) ⊤ S,
    IsEmbeddedSubmanifold 𝓘(ℝ, Plane) 𝓘(ℝ) S

/-- A subset of `ℝ²` admits an immersed-curve structure with topology `t` when that topology on the
subtype supports a smooth `1`-manifold structure whose inclusion into `ℝ²` is an immersion. -/
abbrev IsImmersedCurveWithTopology (S : Set Plane) (t : TopologicalSpace S) : Prop :=
  let _ : TopologicalSpace S := t
  ∃ _ : ChartedSpace ℝ S, ∃ _ : IsManifold 𝓘(ℝ) ⊤ S,
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane)

/-- A subset of `ℝ²` admits an immersed-curve structure when some topology on its subtype supports
such a smooth immersed-curve structure. -/
abbrev AdmitsImmersedCurveStructure (S : Set Plane) : Prop :=
  ∃ t : TopologicalSpace S, IsImmersedCurveWithTopology S t

end Set

/-! ### Proposition_5_35 (from Chap05/Sec05_35) -/
open scoped ContDiff Manifold

section TangentSpaceToSubmanifoldByCurves

universe uE uE' uH uH' uM

open Manifold Set

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S] [BoundarylessManifold J S]

local notation "BasedSmoothCurveAt" => @SmoothCurveAt E' _ _ H' _ J { x // x ∈ S } _ _

/-- Helper for Proposition 5.35: the ambient owner `IsImmersedSubmanifold` is the assertion that
the subtype inclusion `S ↪ M` is an immersion for the chosen smooth structure on `S`. -/
abbrev IsImmersedSubmanifold
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type uH} [TopologicalSpace H]
    {H' : Type uH'} [TopologicalSpace H']
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (J : ModelWithCorners ℝ E' H') (S : Set M)
    [ChartedSpace H' S] [IsManifold J ∞ S] : Prop :=
  Manifold.IsImmersion J I ∞ (Subtype.val : S → M)

-- Proof sketch: for `→`, write `v` as `d(Subtype.val)_p w` and realize `w ∈ TₚS` by a based
-- smooth curve in the boundaryless immersed submanifold `S` through `p`; composing with the
-- inclusion gives the required ambient velocity. For `←`, differentiate the inclusion-composed
-- curve at `0` and use the immersion hypothesis on `Subtype.val : S → M` to see that its ambient
-- velocity lies in the range of `d(Subtype.val)_p`.
omit [BoundarylessManifold J S] in
/-- Helper for Proposition 5.35: every intrinsic tangent vector to the submanifold `S` at `p` is
represented by a based smooth curve in `S` through `p`. -/
lemma exists_based_smoothCurveAt_tangentVector_eq (p : S) (w : TangentSpace J p) :
    ∃ γ : BasedSmoothCurveAt p, γ.tangentVector = w := by
  -- Realize the tangent vector by a quotient class of based smooth curves.
  rcases Quotient.exists_rep ((curveVelocityClassEquivTangentSpace J p).symm w) with ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  -- Evaluating the curve-class equivalence on that representative recovers the target vector.
  have hclass := congrArg (curveVelocityClassEquivTangentSpace J p) hγ
  simpa [curveVelocityClassEquivTangentSpace_apply, curveVelocityClassToTangentSpace] using hclass

omit [BoundarylessManifold J S] in
/-- Helper for Proposition 5.35: the subtype inclusion of an immersed submanifold is
manifold-differentiable at each point. -/
lemma subtype_val_mdifferentiableAt_of_isImmersedSubmanifold
    (hS : IsImmersedSubmanifold I J S) (p : S) :
    MDifferentiableAt J I (Subtype.val : S → M) p := by
  let hι : Manifold.IsImmersionAt J I ∞ (Subtype.val : S → M) p := hS.isImmersionAt p
  have hdomChart :
      hι.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := S) (m := 1) (n := ∞)
      (by simp) hι.domChart_mem_maximalAtlas
  have hcodChart :
      hι.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) (m := 1) (n := ∞)
      (by simp) hι.codChart_mem_maximalAtlas
  -- Express differentiability in the source and target charts supplied by the immersion datum.
  rw [← mdifferentiableWithinAt_univ]
  rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas
      (s := Set.univ)
      (e := hι.domChart) (e' := hι.codChart)
      hdomChart hcodChart
      hι.mem_domChart_source hι.mem_codChart_source]
  simp only [continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  -- Replace the chart expression by the linear normal form valid on the immersion chart target.
  have hEq :
      ((hι.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm)
        =ᶠ[nhdsWithin (hι.domChart.extend J p) (range J)]
      hι.equiv ∘ fun x : E' ↦ (x, (0 : hι.complement)) := by
    exact hι.writtenInCharts.eventuallyEq_of_mem
      ((hι.domChart).extend_target_mem_nhdsWithin (I := J) hι.mem_domChart_source)
  have hxrange : hι.domChart.extend J p ∈ range J := by
    rw [OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hxtarget : hι.domChart.extend J p ∈ (hι.domChart.extend J).target :=
    mem_of_mem_nhdsWithin hxrange
      ((hι.domChart).extend_target_mem_nhdsWithin (I := J) hι.mem_domChart_source)
  have hEq0 :
      ((hι.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm)
          (hι.domChart.extend J p) =
        (hι.equiv ∘ fun x : E' ↦ (x, (0 : hι.complement))) (hι.domChart.extend J p) :=
    hι.writtenInCharts hxtarget
  have hlin :
      DifferentiableWithinAt ℝ
        (hι.equiv ∘ fun x : E' ↦ (x, (0 : hι.complement)))
        (range J)
        (hι.domChart.extend J p) := by
    fun_prop
  exact hlin.congr_of_eventuallyEq hEq hEq0

omit [BoundarylessManifold J S] in
/-- Helper for Proposition 5.35: the ambient velocity of a curve in `S`, viewed in `M`, is the
differential of the subtype inclusion applied to the curve's intrinsic tangent vector. -/
lemma ambient_velocity_eq_subtype_mfderiv_tangentVector
    (hS : IsImmersedSubmanifold I J S) {p : S} (γ : BasedSmoothCurveAt p) :
    γ.source ▸ curve_velocityWithin I (((↑) : S → M) ∘ γ) γ.sourceSet 0 =
      mfderiv J I (Subtype.val : S → M) p γ.tangentVector := by
  rcases γ with ⟨r, f, hs, hsm⟩
  -- The source interval is an open interval around `0`, so the curve chain rule applies there.
  have hzero : 0 ∈ Set.Ioo (-(r : ℝ)) (r : ℝ) := by
    constructor
    · exact neg_lt_zero.mpr r.2
    · exact r.2
  have hsourceSet : UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 := by
    exact isOpen_Ioo.uniqueMDiffWithinAt (I := 𝓘(ℝ)) hzero
  have hsub : MDifferentiableAt J I (Subtype.val : S → M) (f 0) := by
    simpa [hs] using
      subtype_val_mdifferentiableAt_of_isImmersedSubmanifold (hS := hS) (p := p)
  have hγ :
      MDifferentiableWithinAt 𝓘(ℝ) J f (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 := by
    exact (hsm.mdifferentiableOn (by simp)) 0 hzero
  -- Route correction: differentiate the inclusion-composed curve via the chain rule instead of
  -- unfolding tangent vectors directly.
  have hcomp :
      curve_velocityWithin I (((↑) : S → M) ∘ f) (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 =
        mfderiv J I (Subtype.val : S → M) (f 0)
          (curve_velocityWithin J f (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0) :=
    composite_curve_velocity
      (I := J) (I' := I) (J := Set.Ioo (-(r : ℝ)) (r : ℝ)) (t₀ := 0)
      (F := (Subtype.val : S → M)) (γ := f) hsourceSet hsub hγ
  cases hs
  simpa [SmoothCurveAt.tangentVector, SmoothCurveAt.sourceSet] using hcomp

/-- Proposition 5.35: for a boundaryless immersed submanifold `S ⊆ M`, an ambient tangent vector
at `p` belongs to `TₚS` exactly when it is the velocity at `0` of the inclusion of a based smooth
curve in `S`. -/
theorem tangentVector_mem_submanifold_iff_exists_curve
    (hS : IsImmersedSubmanifold I J S) (p : S) (v : TangentSpace I (p : M)) :
    v ∈ T[J; p] ↔
      ∃ γ : BasedSmoothCurveAt p,
        γ.source ▸ curve_velocityWithin I (((↑) : S → M) ∘ γ) γ.sourceSet 0 = v :=
    by
  constructor
  · intro hv
    -- Unpack tangent-space membership as a range witness for the inclusion differential.
    rw [show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl,
      LinearMap.mem_range] at hv
    rcases hv with ⟨w, rfl⟩
    rcases exists_based_smoothCurveAt_tangentVector_eq (p := p) w with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    -- The ambient velocity is the image of the curve's intrinsic tangent vector.
    calc
      γ.source ▸ curve_velocityWithin I (((↑) : S → M) ∘ γ) γ.sourceSet 0
          = mfderiv J I (Subtype.val : S → M) p γ.tangentVector :=
        ambient_velocity_eq_subtype_mfderiv_tangentVector (hS := hS) (γ := γ)
      _ = mfderiv J I (Subtype.val : S → M) p w := by rw [hγ]
  · rintro ⟨γ, hγ⟩
    -- The differential image of the curve's intrinsic tangent vector is its ambient velocity.
    rw [show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl,
      LinearMap.mem_range]
    refine ⟨γ.tangentVector, ?_⟩
    exact (ambient_velocity_eq_subtype_mfderiv_tangentVector
      (hS := hS) (γ := γ)).symm.trans hγ

end TangentSpaceToSubmanifoldByCurves
