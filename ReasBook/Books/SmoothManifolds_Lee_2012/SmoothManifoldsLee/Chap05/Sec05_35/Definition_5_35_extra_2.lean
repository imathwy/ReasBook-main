import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import SmoothManifolds_Lee_2012.Chap03.Sec03_17.Definition_3_17_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

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
