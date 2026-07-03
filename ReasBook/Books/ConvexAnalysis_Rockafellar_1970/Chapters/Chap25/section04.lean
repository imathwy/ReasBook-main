import Mathlib.MeasureTheory.Group.Measure

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_25_4 (from Chap05) -/
noncomputable section

open scoped Rockafellar Topology

universe u v

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [SMul 𝕜 E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.4 fixes a nonzero direction `y` and studies points in
  `interior (dom(f))` where the one-sided directional derivatives coincide, i.e.
  `f'(x; y) = -f'(x; -y)`. It asserts relative density of that set in `interior (dom(f))`,
  measure-zero complement, and continuity of `x ↦ f'(x; y)` on that set.
- `core/canonical`: the owner abstractions already present upstream are `dom(·)`,
  `Function.directionalDerivativeAt`, `Function.IsProper`, and `Function.IsConvex`.
- `bridge/view`: this file introduces the intrinsic source set owner
  `twoSidedDirectionalDerivativeSet` and its ambient counterpart
  `twoSidedDirectionalDerivativeAmbientSet`; the continuity theorem stays on the intrinsic owner,
  while the measure theorem uses the ambient owner directly (instead of subtype-image coercion
  syntax on theorem surfaces).
- redundant source guard elimination: the textbook side condition `y ≠ 0` is omitted from the
  public theorem surfaces, because the owner is still meaningful at `y = 0`; there
  `twoSidedDirectionalDerivativeSet f 0 = Set.univ`, the density and measure-zero-complement
  clauses are immediate, and the restricted directional-derivative map is the constant zero map.

Abstraction audit for this pass:
- codomain/ambient layer: the directional-derivative owner already lives on
  `f : E → WithTopBot 𝕜` (set upstream in `Lemma_23_0_1`); this file keeps that primitive owner
  and introduces no extra concrete-codomain wrapper.
- scalar/ambient structure: no `InnerProductSpace` assumptions are exposed; owner definitions stay
  on the primitive field/order/topological-action layer, while zero-direction simp lemmas and
  topology-sensitive density/continuity/measure statements are kept on the scalar-generic
  normed-space topology layer where the finite-point zero-direction theorem is available.
- owner correctness: the owner `twoSidedDirectionalDerivativeSet` is intrinsic to directional
  derivatives and is based on the relative domain `interior (dom(f))`.
- topology language: the primary theorem uses intrinsic relative density (`Dense` on the subtype
  `interior (dom(f))`) and intrinsic continuity (`Continuous` on the restricted owner).
-/

/-- The source set `D` of Theorem 25.4, owned intrinsically on the relative domain
`interior (dom(f))`: points where the directional derivative in direction `y` matches the opposite
one-sided derivative in direction `-y`. -/
def twoSidedDirectionalDerivativeSet (f : E → WithTopBot 𝕜) (y : E) :
    Set (interior (dom(f))) :=
  {x | directionalDerivativeAt f (x : E) y = -directionalDerivativeAt f (x : E) (-y)}

/-!
The ambient-set owner is a bridge view of the intrinsic owner on `interior (dom(f))`.
Keeping this as an image of the intrinsic owner avoids a second independent predicate owner.
-/
/-- Ambient bridge of the two-sided directional-derivative locus. -/
def twoSidedDirectionalDerivativeAmbientSet (f : E → WithTopBot 𝕜) (y : E) : Set E :=
  Subtype.val '' twoSidedDirectionalDerivativeSet f y

/-! Textbook `D` notation for the intrinsic and ambient owner sets from Theorem 25.4. -/
/-- Textbook notation for the intrinsic two-sided directional-derivative owner. -/
scoped[Rockafellar] notation "D₂[" f "; " y "]" =>
  Function.twoSidedDirectionalDerivativeSet f y

/-- Textbook notation for the ambient two-sided directional-derivative owner. -/
scoped[Rockafellar] notation "D₂ₐ[" f "; " y "]" =>
  Function.twoSidedDirectionalDerivativeAmbientSet f y

/-! Membership in the intrinsic owner is exactly the directional-derivative symmetry equation. -/
@[simp] theorem mem_twoSidedDirectionalDerivativeSet
    {f : E → WithTopBot 𝕜} {y : E} {x : interior (dom(f))} :
    x ∈ D₂[f; y] ↔
      directionalDerivativeAt f (x : E) y = -directionalDerivativeAt f (x : E) (-y) :=
  Iff.rfl

@[simp] theorem mem_twoSidedDirectionalDerivativeAmbientSet
    {f : E → WithTopBot 𝕜} {y : E} {x : E} :
    x ∈ D₂ₐ[f; y] ↔
      x ∈ interior (dom(f)) ∧
        directionalDerivativeAt f x y = -directionalDerivativeAt f x (-y) := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x'.2, hx'⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩

theorem twoSidedDirectionalDerivativeAmbientSet_eq_image
    {f : E → WithTopBot 𝕜} {y : E} :
    D₂ₐ[f; y] = Subtype.val '' D₂[f; y] :=
  rfl

end Function

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [SMul 𝕜 E]

namespace Function

@[simp] theorem twoSidedDirectionalDerivativeSet_zero_eq_univ
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    D₂[f; (0 : E)] = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    have h0 : directionalDerivativeAt f (x : E) 0 = (0 : WithTopBot 𝕜) :=
      Function.directionalDerivativeAt_zero_of_finite_point hf_convex
        (interior_subset x.2) (hf_proper.ne_bot (x : E))
    have h0neg : directionalDerivativeAt f (x : E) (-0) = (0 : WithTopBot 𝕜) := by
      simpa [neg_zero] using h0
    change directionalDerivativeAt f (x : E) 0 = -(directionalDerivativeAt f (x : E) (-0))
    rw [h0, h0neg]
    simp

@[simp] theorem twoSidedDirectionalDerivativeAmbientSet_zero_eq_interior
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    D₂ₐ[f; (0 : E)] = interior (dom(f)) := by
  ext x
  constructor
  · intro hx
    exact (mem_twoSidedDirectionalDerivativeAmbientSet.mp hx).1
  · intro hx
    have h0 : directionalDerivativeAt f x 0 = (0 : WithTopBot 𝕜) :=
      Function.directionalDerivativeAt_zero_of_finite_point hf_convex
        (interior_subset hx) (hf_proper.ne_bot x)
    have h0neg : directionalDerivativeAt f x (-0) = (0 : WithTopBot 𝕜) := by
      simpa [neg_zero] using h0
    exact (mem_twoSidedDirectionalDerivativeAmbientSet.mpr ⟨hx, by
      rw [h0, h0neg]
      simp⟩)

end Function

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function

-- Proof sketch: when `y = 0`, the owner is all of `interior (dom(f))` and the restricted
-- directional-derivative map is constant zero. For `y ≠ 0`, combine the Chapter 24
-- lower-semicontinuity/continuity criterion for
-- directional derivatives on `interior (dom(f))` with one-dimensional convex restrictions along
-- lines parallel to `y`.
/-- Theorem 25.4, intrinsic topology form: for a proper convex function and fixed direction, the
relative owner
`D₂[f; y] ⊆ interior (dom(f))` is dense in `interior (dom(f))`, and
the directional derivative in direction `y` is continuous on this intrinsic domain. -/
theorem dense_and_continuous_directionalDerivativeOn_twoSidedDirectionalDerivativeSet
    [FiniteDimensional 𝕜 E]
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    {y : E} :
    Dense (D₂[f; y]) ∧
      Continuous (fun x : D₂[f; y] ↦
        directionalDerivativeAt f (x : E) y) := by
  by_cases hy : y = 0
  · subst hy
    have hzero :
        ∀ x : interior (dom(f)), directionalDerivativeAt f (x : E) 0 = 0 := fun x ↦
          Function.directionalDerivativeAt_zero_of_finite_point hf_convex
            (interior_subset x.2) (hf_proper.ne_bot (x : E))
    have hzero' :
        ∀ x : D₂[f; 0], directionalDerivativeAt f (x : E) 0 = 0 :=
      fun x ↦ hzero x.1
    refine ⟨?_, ?_⟩
    · rw [twoSidedDirectionalDerivativeSet_zero_eq_univ hf_proper hf_convex]
      exact dense_univ
    · simpa [hzero'] using
        (continuous_const :
          Continuous fun _ : D₂[f; 0] ↦ (0 : WithTopBot 𝕜))
  · sorry

-- Proof sketch: when `y = 0`, the ambient owner is `interior (dom(f))`, so the
-- complement has measure zero trivially. For `y ≠ 0`, use one-dimensional convex slices along
-- lines parallel to `y`, apply the finite jump-count argument on each slice, then integrate
-- slice-nullness via the Haar-measure disintegration/Fubini step.
/-- Theorem 25.4, measure form: for any additive Haar measure on a finite-dimensional
normed space over the same scalar field, the complement of the ambient owner
`D₂ₐ[f; y]` inside `interior (dom(f))` has measure zero. -/
theorem volume_diff_twoSidedDirectionalDerivativeSetAmbient_eq_zero
    [FiniteDimensional 𝕜 E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    {y : E} :
    μ ((interior (dom(f))) \ D₂ₐ[f; y]) = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp [twoSidedDirectionalDerivativeAmbientSet_zero_eq_interior hf_proper hf_convex]
  · sorry

/-- The density clause of Theorem 25.4 in intrinsic relative-topology owner form. -/
theorem dense_twoSidedDirectionalDerivativeSet
    [FiniteDimensional 𝕜 E]
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    {y : E} :
    Dense (D₂[f; y]) := by
  exact
    (dense_and_continuous_directionalDerivativeOn_twoSidedDirectionalDerivativeSet
      hf_proper hf_convex).1

/-- The continuity clause of Theorem 25.4 in intrinsic owner form. -/
theorem continuous_directionalDerivativeOn_twoSidedDirectionalDerivativeSet
    [FiniteDimensional 𝕜 E]
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    {y : E} :
    Continuous (fun x : D₂[f; y] ↦
      directionalDerivativeAt f (x : E) y) := by
  exact
    (dense_and_continuous_directionalDerivativeOn_twoSidedDirectionalDerivativeSet
      hf_proper hf_convex).2

end Function

end
