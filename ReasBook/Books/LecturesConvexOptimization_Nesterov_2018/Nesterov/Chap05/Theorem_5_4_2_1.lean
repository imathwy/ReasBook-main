import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Theorem 5.4.2.1 lies in the chapter's based-polar-set / finite-dimensional convex-geometry
domain.

Sampled owner-style declarations:
- project `polarSet`
- project `mem_polarSetAt_iff`
- mathlib `NormedSpace.isClosed_polar`
- mathlib `NormedSpace.isBounded_polar_of_mem_nhds_zero`

Best owner abstraction:
- source-facing: the compact-convex conclusion for the based polar body `polarSetAt Q xBar`
- core/canonical: the chapter owner `polarSet`
- bridge/view: the based displacement-set owner `polarSetAt`

Primitive data:
- a set `Q : Set E`
- a base point `xBar : E`
- for compactness and boundedness: `xBar ∈ interior Q`
- for the separate interior-nonemptiness companion: `Convex ℝ Q` together with the chapter
  no-affine-line hypothesis on `Q`

Derived API:
- unconditional closedness and convexity of `polarSetAt Q xBar`
- compactness and boundedness from the interior-point hypothesis
- nonempty interior under the extra source-facing convex/no-affine-line assumptions
- the trivial base-point-free fact `0 ∈ polarSetAt Q xBar`

This theorem file should not be tied to the display model `EuclideanSpace ℝ (Fin n)`: the owner
`polarSetAt` already lives on real inner-product spaces, and the proof sketch only uses finite
dimensionality. The correct public surface is therefore a finite-dimensional real inner-product
space. The owner-level geometry also separates cleanly into two layers: `polarSetAt Q xBar` is
always an intersection of closed convex half-spaces, so its closedness and convexity are
unconditional, while compactness and boundedness use only the interior ball around `xBar`. The
chapter’s convexity and no-affine-line assumptions remain only on the separate interior-nonempty
companion theorem, where they belong.
-/

section RealInnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : Set E} {xBar : E}

-- Proof sketch: each defining inequality `inner ℝ s (x - xBar) ≤ 1` cuts out a convex
-- half-space, and arbitrary intersections of convex sets are convex.
/-- The based polar set is convex. -/
theorem polarSetAt_convex :
    Convex ℝ (polarSetAt Q xBar) := sorry

-- Proof sketch: each defining inequality `inner ℝ s (x - xBar) ≤ 1` cuts out a closed
-- half-space, and arbitrary intersections of closed sets are closed.
/-- The based polar set is closed. -/
theorem polarSetAt_isClosed :
    IsClosed (polarSetAt Q xBar) := sorry

-- Proof sketch: if `xBar ∈ interior Q`, then some ball around `xBar` lies in `Q`; evaluating the
-- defining inequalities on that ball gives a uniform norm bound on every `s ∈ polarSetAt Q xBar`.
/-- The polar set of an interior point is bounded. -/
theorem polarSetAt_isBounded
    (hxBar : xBar ∈ interior Q) :
    Bornology.IsBounded (polarSetAt Q xBar) := sorry

-- Proof sketch: for every `x ∈ Q`, the defining inequality for `polarSetAt Q xBar` at `s = 0`
-- reduces to `0 ≤ 1`.
/-- The origin belongs to every polar set. -/
theorem zero_mem_polarSetAt {Q : Set E} {xBar : E} :
    (0 : E) ∈ polarSetAt Q xBar := by
  rw [polarSetAt, mem_polarSet_iff]
  intro x hx
  simp

end RealInnerProduct

section FiniteDimensionalReal

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {Q : Set E} {xBar : E}

-- Proof sketch: `polarSetAt Q xBar` is convex unconditionally. If `xBar ∈ interior Q`, the
-- interior ball around `xBar` gives boundedness, and in finite-dimensional real inner-product
-- space boundedness plus closedness gives compactness by Heine-Borel.
/-- Theorem 5.4.2.1, at the intrinsic owner level: if `xBar` is an interior point of `Q`, then
the based polar set `P(xBar) = polarSetAt Q xBar` is compact and convex. The textbook convexity
and no-affine-line assumptions are redundant for this conclusion. -/
theorem polarSetAt_isCompact_convex
    (hxBar : xBar ∈ interior Q) :
    IsCompact (polarSetAt Q xBar) ∧ Convex ℝ (polarSetAt Q xBar) := sorry

-- Proof sketch: use the interior ball around `xBar` together with the absence of affine lines in
-- `Q` to show that a small Euclidean ball around the origin satisfies the defining inequalities of
-- `polarSetAt Q xBar`.
/-- The polar set of an interior point has nonempty interior. -/
theorem polarSetAt_interior_nonempty
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hxBar : xBar ∈ interior Q) :
    (interior (polarSetAt Q xBar)).Nonempty := sorry

end FiniteDimensionalReal

end
