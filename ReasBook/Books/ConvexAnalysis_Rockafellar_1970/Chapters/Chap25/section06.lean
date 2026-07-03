import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.ClusterPt

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_25_6 (from Chap05) -/
noncomputable section

open Filter
open scoped Pointwise Topology Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Function

/-- Intrinsic differentiability owner on the effective-domain surface `riDom(f)`. -/
def differentiabilitySetWithinRiDom (f : E → WithTopBot ℝ) :
    Set (riDom(f)) :=
  {x | DifferentiableWithinAt ℝ f.realBranch (riDom(f)) (x : E)}

@[simp] theorem mem_differentiabilitySetWithinRiDom
    {f : E → WithTopBot ℝ} {x : riDom(f)} :
    x ∈ differentiabilitySetWithinRiDom f ↔
      DifferentiableWithinAt ℝ f.realBranch (riDom(f)) (x : E) :=
  Iff.rfl

/-- Ambient companion of `differentiabilitySetWithinRiDom`, keeping theorem surfaces free from
subtype-image coercion noise. -/
def differentiabilitySetWithinRiDomAmbient (f : E → WithTopBot ℝ) : Set E :=
  {x | x ∈ riDom(f) ∧ DifferentiableWithinAt ℝ f.realBranch (riDom(f)) x}

@[simp] theorem mem_differentiabilitySetWithinRiDomAmbient
    {f : E → WithTopBot ℝ} {x : E} :
    x ∈ differentiabilitySetWithinRiDomAmbient f ↔
      x ∈ riDom(f) ∧ DifferentiableWithinAt ℝ f.realBranch (riDom(f)) x :=
  Iff.rfl

theorem differentiabilitySetWithinRiDomAmbient_eq_image
    {f : E → WithTopBot ℝ} :
    differentiabilitySetWithinRiDomAmbient f =
      Subtype.val '' differentiabilitySetWithinRiDom f := by
  ext x
  constructor
  · rintro ⟨hx_ri, hx_diff⟩
    exact ⟨⟨x, hx_ri⟩, hx_diff, rfl⟩
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x'.2, hx'⟩

theorem differentiabilitySetWithinRiDomAmbient_subset_dom
    {f : E → WithTopBot ℝ} :
    differentiabilitySetWithinRiDomAmbient f ⊆ dom(f) := by
  intro x hx
  exact intrinsicInterior_subset hx.1

/-- Canonical differential cluster set for Theorem 25.6: cluster points in the continuous dual of
relative Fréchet derivatives of the finite real branch `f.realBranch`, taken along the intrinsic
differentiability owner `differentiabilitySetWithinRiDom` (via its ambient companion), approaching
`x`. -/
def differentialClusterPointsAt (f : E → WithTopBot ℝ) (x : E) : Set (StrongDual ℝ E) :=
  {xStar | MapClusterPt xStar
      (𝓝[differentiabilitySetWithinRiDomAmbient f] x)
      (fun y ↦ fderivWithin ℝ f.realBranch (riDom(f)) y)}

/-- Sequence form of `differentialClusterPointsAt`: a dual vector belongs to this set exactly when
it is the limit of relative Fréchet derivatives along a sequence in the ambient companion of
`differentiabilitySetWithinRiDom f` converging to `x`. -/
theorem mem_differentialClusterPointsAt_iff_exists_tendsto
    {f : E → WithTopBot ℝ} {x : E} {xStar} :
    xStar ∈ differentialClusterPointsAt f x ↔
      ∃ xSeq : ℕ → E,
        Tendsto xSeq atTop (𝓝 x) ∧
        (∀ n, xSeq n ∈ differentiabilitySetWithinRiDomAmbient f) ∧
        Tendsto
          (fun n ↦ fderivWithin ℝ f.realBranch (riDom(f)) (xSeq n))
          atTop (𝓝 xStar) := by
  constructor
  · intro hx
    rcases (show MapClusterPt xStar
        (𝓝[differentiabilitySetWithinRiDomAmbient f] x)
        (fun y ↦ fderivWithin ℝ f.realBranch (riDom(f)) y) from hx).exists_seq_tendsto with
      ⟨ψ, hψ_deriv, hψ_within⟩
    have hψ_within' := (tendsto_nhdsWithin_iff.1 hψ_within).2
    rcases (Filter.eventually_atTop.1 hψ_within') with ⟨N, hN⟩
    refine ⟨fun n ↦ ψ (n + N), ?_, ?_, ?_⟩
    · exact
        ((tendsto_nhdsWithin_iff.1 hψ_within).1).comp (Filter.tendsto_add_atTop_nat N)
    · intro n
      exact hN (n + N) (Nat.le_add_left N n)
    · simpa [Function.comp] using hψ_deriv.comp (Filter.tendsto_add_atTop_nat N)
  · rintro ⟨xSeq, hxSeq_tendsto, hxSeq_mem_diff, hxSeq_deriv_tendsto⟩
    have hxSeq_within :
        Tendsto xSeq atTop (𝓝[differentiabilitySetWithinRiDomAmbient f] x) :=
      (tendsto_nhdsWithin_iff.2
        ⟨hxSeq_tendsto, Eventually.of_forall hxSeq_mem_diff⟩)
    have hseq_cluster :
        MapClusterPt xStar atTop
          ((fun y ↦ fderivWithin ℝ f.realBranch (riDom(f)) y) ∘ xSeq) :=
      hxSeq_deriv_tendsto.mapClusterPt
    simpa [differentialClusterPointsAt, Function.comp] using
      hseq_cluster.of_comp hxSeq_within

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

-- Proof sketch: combine the interior-point singleton formula from Theorem 25.1 with the Chapter 24
-- closed-graph passage for `_root_.subdifferentialAt`, and express the source limit set through the
-- canonical owner `Function.differentialClusterPointsAt`.
/-- Theorem 25.6 in canonical dual-owner form: for a closed proper convex function with nonempty
relative interior domain, the subdifferential equals the sum of the normal cone and the intrinsic
closed convex hull
of differential cluster points. -/
theorem subdifferentialAt_eq_closure_convexHull_differentialClusterPointsAt_add_normalCone
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f)
    (hdom : (riDom(f)).Nonempty)
    (x : E) :
    (∂ f at x) =
      intrinsicClosure ℝ (convexHull ℝ (Function.differentialClusterPointsAt f x)) +
        N[ℝ](x | dom(f)) := by
  sorry

end
