import Mathlib
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient Topology

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.5 studies the set `D` of points in `interior (dom(f))` where
  Rockafellar's directional differentiability criterion holds, then asserts density of `D`,
  measure-zero complement in `interior (dom(f))`, and continuity of the gradient map on `D` in
  the real inner-product bridge.
- `core/canonical`: the owner abstraction for `D` is
  `Function.HasLinearDirectionalDerivativeAt`, i.e. linearity of
  `y ↦ directionalDerivativeAt f x y` in the Chapter 25 canonical owner layer
  `f : E → WithBotTop 𝕜`.
- `bridge/view`: the proof route for clauses (1) and (2) factors through the directional owner
  `Function.twoSidedDirectionalDerivativeSet` from Theorem 25.4 in each basis direction and the
  Chapter 25 criterion of Theorem 25.2; clause (3) then adds the real inner-product gradient owner
  `∇` and the singleton-subdifferential continuity bridge of Corollary 25.5.1.

Domain-style sampling used here:
- `Function.HasLinearDirectionalDerivativeAt` and
  `Function.differentiableAt_iff_hasLinearDirectionalDerivativeAt` from `Chap05.Theorem_25_2`;
- `Function.twoSidedDirectionalDerivativeSet` and
  `Function.volume_diff_twoSidedDirectionalDerivativeSetAmbient_eq_zero` from
  `Chap05.Theorem_25_4`;
- `Function.continuous_gradient_realBranch_on_open_convex` from
  `Chap05.Corollary_25_5_1`.

Primitive data vs derived API:
- primitive source data: a proper convex function `f : E → WithBotTop 𝕜`;
- primitive owner surface: the canonical intrinsic Rockafellar-locus
  `differentiabilitySetWithinInteriorDom f`;
- derived API: its density, its ambient measure-zero complement statement, and, after adding the
  real Riesz-identification layer, continuity of the restricted gradient map.

Ambient-assumption minimization:
- the owner definitions below stay at the primitive module/topology layer required by
  `Function.HasLinearDirectionalDerivativeAt`;
- clauses (1) and (2) move to the scalar-generic finite-dimensional normed-space layer already
  used by Chapter 25 directional-derivative owners;
- only clause (3) uses the Euclidean gradient owner `∇`, so only that clause is kept in the
  stronger finite-dimensional real inner-product setting.

Layer target: `source-facing`, stated directly on the canonical subtype set inside
`interior (dom(f))` rather than through a parallel local alias.
-/

/- The intrinsic Rockafellar-locus `D` from Theorem 25.5. -/
/-- The set of points of `interior (dom(f))` where Rockafellar's directional criterion
(`HasLinearDirectionalDerivativeAt`) holds. For finite convex real-valued branches, this matches
ordinary differentiability via Theorem 25.2. -/
def differentiabilitySetWithinInteriorDom (f : E → WithBotTop 𝕜) :
    Set (interior (dom(f))) :=
  {x | f.HasLinearDirectionalDerivativeAt (x : E)}

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)] in
@[simp] theorem mem_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop 𝕜} {x : interior (dom(f))} :
    x ∈ differentiabilitySetWithinInteriorDom f ↔
      f.HasLinearDirectionalDerivativeAt (x : E) :=
  Iff.rfl

/-- Ambient owner of `differentiabilitySetWithinInteriorDom`, keeping theorem surfaces free from
subtype-image coercion noise. -/
def differentiabilitySetWithinInteriorDomAmbient (f : E → WithBotTop 𝕜) : Set E :=
  {x | x ∈ interior (dom(f)) ∧ f.HasLinearDirectionalDerivativeAt x}

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)] in
@[simp] theorem mem_differentiabilitySetWithinInteriorDomAmbient
    {f : E → WithBotTop 𝕜} {x : E} :
    x ∈ differentiabilitySetWithinInteriorDomAmbient f ↔
      x ∈ interior (dom(f)) ∧ f.HasLinearDirectionalDerivativeAt x :=
  Iff.rfl

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)] in
theorem differentiabilitySetWithinInteriorDomAmbient_eq_image
    {f : E → WithBotTop 𝕜} :
    differentiabilitySetWithinInteriorDomAmbient f =
      Subtype.val '' differentiabilitySetWithinInteriorDom f := by
  ext x
  constructor
  · rintro ⟨hx_int, hx_diff⟩
    exact ⟨⟨x, hx_int⟩, hx_diff, rfl⟩
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x'.2, hx'⟩

end Function

end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function

-- Proof sketch: choose a finite basis of `E`, apply Theorem 25.4 to each basis
-- direction to obtain dense two-sided directional-derivative sets with measure-zero complements,
-- intersect those finitely many dense sets, and use Theorem 25.2 to identify that finite
-- intersection with `differentiabilitySetWithinInteriorDom f`.
/-- Theorem 25.5 (1): for a proper convex function on a finite-dimensional normed space over
`𝕜`, the intrinsic Rockafellar-locus `D` is dense in `interior (dom(f))`. -/
theorem dense_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    Dense (differentiabilitySetWithinInteriorDom f) := sorry

-- Proof sketch: as in clause (1), express
-- `differentiabilitySetWithinInteriorDom f` as the
-- finite intersection of the basis-direction two-sided directional-derivative sets from Theorem
-- 25.4, then take the finite union of their measure-zero complements inside `interior (dom(f))`.
/-- Theorem 25.5 (2): for any additive Haar measure on a finite-dimensional normed space over
`𝕜`, the complement of the intrinsic Rockafellar-locus `D` in `interior (dom(f))` has measure
zero. -/
theorem volume_diff_differentiabilitySetWithinInteriorDom_eq_zero
    [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    μ
        ((interior (dom(f))) \
          differentiabilitySetWithinInteriorDomAmbient f) =
      0 := sorry

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

-- Proof sketch: on
-- `differentiabilitySetWithinInteriorDom f`, Theorem 25.1 identifies
-- the
-- subdifferential with the singleton carried by the gradient of `f.realBranch`; Corollary 25.5.1
-- then gives continuity of that singleton branch on the open convex set `interior (dom(f))`,
-- which restricts to continuity of the gradient map on the intrinsic subtype `D`.
/-- Theorem 25.5 (3): the gradient mapping of the finite real branch is continuous on the
Rockafellar-locus `D` in the real inner-product bridge. -/
theorem continuous_gradientOn_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop ℝ} (hf_proper : f.IsProper) (hf_convex : f.IsConvex ℝ) :
    Continuous
      (fun x : differentiabilitySetWithinInteriorDom f ↦
        ∇ f.realBranch (x : E)) := sorry

end Function

end
