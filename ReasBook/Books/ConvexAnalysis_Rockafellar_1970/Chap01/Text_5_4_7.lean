import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.7 defines the function generated from `h` by applying Theorem 5.3 to
  the cone of the epigraph of `h`.
- `core/canonical`: the owner abstractions already introduced in the chapter are
  `ConvexOn 𝕜 (Set.univ : Set E)` from Definition 4.2, `Function.verticalInfimum` from
  Theorem 5.3, and the generated cone owner `cone[𝕜] (epi h)` from Text 5.4.6.
- `bridge/view`: the source-facing owner is the generated function `sublinearHull h`. The
  raw construction route `verticalInfimum (PointedCone.hull 𝕜 (epi h))` is retained only as a
  secondary bridge/specification. The maximal-minorant interpretation is deferred to `Text_5_4_8`,
  where the extra hypothesis `u 0 ≤ 0` appears explicitly.
- Primitive data vs derived API: `h` and the generated function are primitive; the `sInf`
  description and convexity statement are derived from the owner-side API.
- Ambient minimization: the owner construction and its defining `sInf` formula only need the
  primitive `verticalInfimum` and `PointedCone.hull` layers, so they are kept under the weaker
  ordered-semiring assumptions. The stronger ordered-ring assumptions are isolated to the convexity
  theorem, where `Function.isConvex_verticalInfimum` genuinely requires them.
- Layer target: `source-facing`; this file introduces the generated function itself and records its
  convexity, while the implementation continues to reuse the pointed-cone hull and vertical-infimum
  owners upstream.

Domain-style sampling used here:
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`;
- `Function.isConvex_verticalInfimum`;

The source assumes `h` is convex, but the cone-of-epigraph construction itself depends only on
`h`, so that hypothesis is not part of the primitive definition.
-/

namespace Function

open PointedCone

section Basic

variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Text 5.4.7: the sublinear hull of `h`, defined as the vertical infimum of the generated cone
of its epigraph. -/
def sublinearHull (h : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  verticalInfimum (cone[𝕜] (epi h))

/-- Source-facing owner specification: the sublinear hull of `h` is the vertical infimum of the
generated cone `cone[𝕜] (epi h)`. -/
theorem sublinearHull_eq_verticalInfimum (h : E → WithTopBot 𝕜) :
    sublinearHull h =
      verticalInfimum (cone[𝕜] (epi h)) :=
  rfl

/-- Secondary bridge/view form on the raw owner spelling `PointedCone.hull 𝕜 (epi h)`. -/
theorem sublinearHull_eq_verticalInfimum_hull_epi (h : E → WithTopBot 𝕜) :
    sublinearHull h = verticalInfimum (hull 𝕜 (epi h)) := by
  simpa using sublinearHull_eq_verticalInfimum (h := h)

/-- The value of `sublinearHull h` at `x` is the infimum of the scalar heights in the vertical
fiber of the generated epigraph cone above `x`, stated at the intrinsic owner
`Function.verticalHeights`. -/
theorem sublinearHull_eq_sInf_verticalHeights (h : E → WithTopBot 𝕜) (x : E) :
    sublinearHull h x =
      sInf (verticalHeights (cone[𝕜] (epi h)) x) := by
  simpa [sublinearHull] using
    verticalInfimum_eq_sInf_verticalHeights ((cone[𝕜] (epi h) : Set (E × 𝕜))) x

end Basic

-- Proof sketch: the generated cone of the epigraph of `h` is convex because it is a pointed
-- cone. Apply
-- `Function.isConvex_verticalInfimum` from Theorem 5.3 to its underlying set.
section Convex

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

local instance : DecidableLT 𝕜 := Classical.decRel (· < ·)

/-- Helper for Text 5.4.7: use the concrete multiplication action of `𝕜` on `WithTopBot 𝕜` in the
owner-side convexity inequality. -/
local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

/-- Helper for Text 5.4.7: left multiplication by a nonnegative finite scalar is monotone on
`WithTopBot 𝕜`. -/
private theorem mul_le_mul_left_coe_withTopBot {a : 𝕜} (ha : 0 ≤ a) {u v : WithTopBot 𝕜}
    (h : u ≤ v) :
    (a : WithTopBot 𝕜) * u ≤ (a : WithTopBot 𝕜) * v := by
  -- Reduce first along the outer `WithTop`; the finite branch then drops to monotonicity on
  -- `WithBot 𝕜`.
  induction v using WithTop.recTopCoe with
  | top =>
      by_cases ha0 : a = 0
      · simp [ha0]
      · have ha0' : (a : WithTopBot 𝕜) ≠ 0 := by
          exact_mod_cast ha0
        rw [WithTop.mul_top ha0']
        exact le_top
  | coe v =>
      induction u using WithTop.recTopCoe with
      | top =>
          exfalso
          simp at h
      | coe u =>
          have huv : u ≤ v := WithTop.coe_le_coe.mp h
          have ha' : (0 : WithBot 𝕜) ≤ ((a : 𝕜) : WithBot 𝕜) := by
            exact WithBot.coe_le_coe.mpr ha
          exact WithTop.coe_le_coe.mpr (mul_le_mul_of_nonneg_left huv ha')

/-- Helper for Text 5.4.7: a nonnegative scalar preserves an upper bound by a finite height in
`WithTopBot 𝕜`. -/
private theorem smul_le_smul_coe_of_le_coe {a μ : 𝕜} (ha : 0 ≤ a) {z : WithTopBot 𝕜}
    (hz : z ≤ (μ : WithTopBot 𝕜)) :
    a • z ≤ a • (μ : WithTopBot 𝕜) := by
  -- Route correction: package the codomain transport through a reusable monotonicity lemma, then
  -- use it as a thin adapter for the local scalar action.
  change ((a : WithTopBot 𝕜) * z ≤ ((a : WithTopBot 𝕜) * (μ : WithTopBot 𝕜)))
  exact mul_le_mul_left_coe_withTopBot ha hz

variable [DenselyOrdered 𝕜]

/-- Theorem 5.3, specialized to Text 5.4.7 on the canonical owner surface: the function
generated from `h` by the cone-of-epigraph construction is convex on the whole space. -/
theorem convexOn_sublinearHull (h : E → WithTopBot 𝕜) :
    (sublinearHull h).IsConvex 𝕜 := by
  -- Rewrite the generated function back to the vertical infimum attached to the convex cone.
  simpa [sublinearHull] using
    Function.isConvex_verticalInfimum ((cone[𝕜] (epi h)).convex)

/-- Bridge form of `convexOn_sublinearHull` on the chapter shorthand owner. -/
theorem isConvex_sublinearHull (h : E → WithTopBot 𝕜) :
    (sublinearHull h).IsConvex 𝕜 :=
  convexOn_sublinearHull h

end Convex

end Function

end
