import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_7_5_1 (from Chap02) -/
universe u

section

open AffineMap Filter
open scoped Rockafellar

variable {𝕜 E : Type u}
variable [Ring 𝕜] [LinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [IsStrictOrderedRing 𝕜]
  [ContinuousAdd 𝕜] [ContinuousMul 𝕜]
  [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddTorsor E]
  [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.5.1 upgrades the boundary-limit formula from Theorem 7.5 to the
  closed proper convex case, replacing the boundary value `cl(f) y` by `f y` and requiring only
  `x ∈ dom(f)`.
- `core/canonical`: the primitive owner abstractions for this chapter-level item are
  `Function.IsConvex 𝕜`, `Function.IsProper`, `LowerSemicontinuous`, `dom(·)`, `lineMap`, and the
  one-sided filter
  `nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜))`.
- `bridge/view`: the textbook expression `(1 - λ)x + λ y` is rendered by
  `lineMap x y λ`, while closedness is represented directly by
  `LowerSemicontinuous f`, so the boundary value can be stated as `f y`.

Domain-style sampling used here:
- `Function.IsConvex.lt_affine_upper_bound` from Theorem 4.2;
- `Function.IsProper` and `LowerSemicontinuous` as primitive data for the closed proper convex
  condition;
- `dom(·)` from Definition 4.4;
- `AffineMap.lineMap_continuous` from mathlib's topological affine-space owner API;
- `lowerSemicontinuousWithinAt_iff` and `tendsto_order` for the order-topological endpoint
  argument.

Primitive data vs derived API:
- primitive inputs: convexity, properness, and lower semicontinuity of `f`, a point
  `x ∈ dom(f)`, and an arbitrary endpoint `y`;
- derived API: the left-limit identification of the segment profile with the endpoint value `f y`.

Layer target: `source-facing`, stated directly on the canonical owner layer used elsewhere in the
chapter.
-/

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: for the profile `g t = f (lineMap x y t)`, lower semicontinuity of `f`
-- composed with the continuous map `lineMap x y` gives the lower one-sided bound at `t = 1`. If
-- `f y = ⊤`, this already implies `g t → ⊤`. If `f y` is finite, convexity gives the strict
-- affine upper estimate `g t < (1 - t) α + t β` whenever `f x < α`, `f y < β`, and
-- `0 < t < 1`. Choosing `α > f x` and an intermediate `β` with `f y < β < a` for a prescribed
-- upper neighborhood endpoint `a > f y`, continuity of the scalar affine function forces
-- `g t < a` near `1`.
/-- Corollary 7.5.1: for a closed proper convex function `f`, if `x ∈ dom(f)`, then the values of
`f` along the segment `t ↦ lineMap x y t` converge to `f y` as `t → 1` from the left,
for every endpoint `y`. The closed/proper/convex hypothesis is exposed at its primitive owner
layer as convexity, properness, and lower semicontinuity. -/
theorem tendsto_lineMap_left_to_value
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    {x y : E} (hx : x ∈ dom(f)) :
    Tendsto (fun t : 𝕜 ↦ f (lineMap x y t))
      (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
      (nhds (f y)) := by
  let g : 𝕜 → WithBotTop 𝕜 := fun t ↦ f (lineMap x y t)
  have hg_lsc : LowerSemicontinuousWithinAt g (Set.Iio (1 : 𝕜)) (1 : 𝕜) := by
    have hline : Continuous fun t : 𝕜 ↦ lineMap x y t := by
      simpa using (AffineMap.lineMap_continuous : Continuous (lineMap x y))
    simpa [g, Function.comp] using
      (hf_closed.lowerSemicontinuousWithinAt (Set.univ : Set E) (lineMap x y (1 : 𝕜))).comp
        hline.continuousAt.continuousWithinAt
        (by intro t ht; simp)
  by_cases hfy_top : f y = ⊤
  · refine (tendsto_order.2 ?_)
    constructor
    · intro a ha
      exact (lowerSemicontinuousWithinAt_iff.mp hg_lsc) a <| by simpa [g, hfy_top] using ha
    · intro a ha
      have ha' : f y < a := by
        simpa [g] using ha
      have htop : (⊤ : WithBotTop 𝕜) < a := by
        rwa [hfy_top] at ha'
      exact (not_lt_of_ge (show a ≤ (⊤ : WithBotTop 𝕜) from le_top) htop).elim
  · have hfy_bot : f y ≠ ⊥ := hf_proper.ne_bot y
    lift f y to 𝕜 using ⟨hfy_top, hfy_bot⟩ with fy hfy
    have hfx_top : f x ≠ ⊤ := (mem_effectiveDomain.mp hx).ne
    have hfx_bot : f x ≠ ⊥ := hf_proper.ne_bot x
    lift f x to 𝕜 using ⟨hfx_top, hfx_bot⟩ with fx hfx
    have h_id :
        Tendsto (fun t : 𝕜 ↦ t)
          (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
          (nhds (1 : 𝕜)) := by
      simpa using
        (continuousAt_id.continuousWithinAt :
          ContinuousWithinAt (fun t : 𝕜 ↦ t) (Set.Iio (1 : 𝕜)) (1 : 𝕜))
    have hpos : ∀ᶠ t in nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)), 0 < t :=
      (tendsto_order.1 h_id).1 0 zero_lt_one
    have h_upper_to_coe :
        ∀ ⦃β : 𝕜⦄, fy < β →
          ∀ᶠ t in nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)), g t < (β : WithBotTop 𝕜) := by
      intro β hfy_lt_beta
      rcases exists_between hfy_lt_beta with ⟨γ, hfy_lt_gamma, hgamma_lt_beta⟩
      let α : 𝕜 := fx + 1
      have hfx_lt_alpha : f x < α := by
        simpa [hfx, α] using
          (WithBotTop.coe_lt_coe_iff.mpr (lt_add_of_pos_right fx zero_lt_one) :
            (fx : WithBotTop 𝕜) < ((fx + 1 : 𝕜) : WithBotTop 𝕜))
      have hfy_lt_gamma' : f y < γ := by
        simpa [hfy] using
          (WithBotTop.coe_lt_coe_iff.mpr hfy_lt_gamma :
            (fy : WithBotTop 𝕜) < (γ : WithBotTop 𝕜))
      have hscalar :
          Tendsto (fun t : 𝕜 ↦ ((1 - t) * α + t * γ : 𝕜))
            (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
            (nhds γ) := by
        have hcont : Continuous fun t : 𝕜 ↦ ((1 - t) * α + t * γ : 𝕜) := by
          continuity
        have hcont' :
            Tendsto (fun t : 𝕜 ↦ ((1 - t) * α + t * γ : 𝕜))
              (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
              (nhds (((1 - (1 : 𝕜)) * α + (1 : 𝕜) * γ : 𝕜))) :=
          hcont.continuousAt.continuousWithinAt
        simpa using hcont'
      have hscalar_lt :
          ∀ᶠ t in nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)), ((1 - t) * α + t * γ : 𝕜) < β :=
        (tendsto_order.1 hscalar).2 β hgamma_lt_beta
      filter_upwards [hpos, self_mem_nhdsWithin, hscalar_lt] with t ht0 ht1 htβ
      have hconv : g t < (((1 - t) * α + t * γ : 𝕜) : WithBotTop 𝕜) := by
        simpa [g, lineMap_apply_module] using
          hf.lt_affine_upper_bound x y α γ t hfx_lt_alpha hfy_lt_gamma' ht0 ht1
      exact lt_trans hconv
        (show (((1 - t) * α + t * γ : 𝕜) : WithBotTop 𝕜) < (β : WithBotTop 𝕜) by
          simpa using (WithBotTop.coe_lt_coe_iff.mpr htβ :
            (((1 - t) * α + t * γ : 𝕜) : WithBotTop 𝕜) < (β : WithBotTop 𝕜)))
    refine (tendsto_order.2 ?_)
    constructor
    · intro a ha
      exact (lowerSemicontinuousWithinAt_iff.mp hg_lsc) a <| by simpa [g, hfy] using ha
    · intro a ha
      by_cases ha_top : a = (⊤ : WithBotTop 𝕜)
      · subst ha_top
        filter_upwards [h_upper_to_coe (show fy < fy + 1 by
          exact lt_add_of_pos_right fy zero_lt_one)] with t ht
        exact lt_trans ht (WithBotTop.coe_lt_top (fy + 1))
      · have ha_bot : a ≠ ⊥ := by
          exact ne_of_gt (lt_of_lt_of_le (WithBotTop.bot_lt_coe fy) ha.le)
        lift a to 𝕜 using ⟨ha_top, ha_bot⟩ with β hβ
        have hfy_lt_beta' : (fy : WithBotTop 𝕜) < (β : WithBotTop 𝕜) := by
          simpa [g, hfy, hβ] using ha
        have hfy_lt_beta : fy < β := WithBotTop.coe_lt_coe_iff.mp hfy_lt_beta'
        simpa [hβ] using h_upper_to_coe hfy_lt_beta

end Function.IsConvex

end

/-! ### Theorem_7_5 (from Chap02) -/
section

open AffineMap Filter
open scoped Rockafellar

variable {𝕜 E α : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [Preorder α] [ConditionallyCompleteLattice α] [TopologicalSpace α]
  [TopologicalSpace (WithBotTop α)]
  [AddCommMonoid α] [SMul 𝕜 α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 7.5 gives the boundary-limit formula for a convex function along the
  segment from a point `x ∈ ri (dom f)` to an arbitrary point `y`, with value at the boundary
  represented by the closure `cl(f) y`.
- `core/canonical`: the owner abstractions already present in the project are `Function.IsConvex`,
  `Function.IsProper`, the effective-domain owners `dom(·)` and `riDom[𝕜](·)`, Rockafellar's closure
  owner `cl(·)`, the affine-combination owner `lineMap`, and the filter owner
  `Tendsto ... (nhdsWithin 1 (Set.Iio 1))`, with codomain neighborhoods taken in the
  ambient topological structure on `WithBotTop α`.
- `bridge/view`: the textbook formula
  `(1 - λ) x + λ y` is rendered canonically by `lineMap x y λ`, and the one-sided limit
  `λ ↑ 1` is rendered by `nhdsWithin (1 : 𝕜) (Set.Iio 1)`.

Domain-style sampling used here:
- `riDom[𝕜](·)` and `dom(·)` from Definition 4.4;
- `Function.IsProper` from Definition 4.6;
- `Function.IsConvex` from Theorem 4.2;
- Rockafellar's closure owner `cl(·)` from Text 7.0.4.

Primitive data vs derived API:
- primitive inputs for the numbered theorem: the convex function `f`, the properness hypothesis,
  the base point `x ∈ riDom[𝕜](f)`, and an arbitrary endpoint `y`;
- derived companion API: the intrinsic-closure specialization/extension where the endpoint
  hypothesis is stated explicitly as `y ∈ intrinsicClosure 𝕜 dom(f)`.

Layer target: the main theorem stays `source-facing`, but it is stated directly on the canonical
owner layer of `Tendsto`, `lineMap`, and `cl(·)` rather than as a bespoke "limit exists"
wrapper.

Ambient-space refinement: this chapter-level boundary theorem is kept on the established
finite-dimensional normed-space scalar layer over an ordered/topological scalar `𝕜`, with
intrinsic/relative-domain operators `riDom[𝕜](·)` and `intrinsicClosure 𝕜`; only the codomain is
generalized to the ordered extended layer `WithBotTop α` used by the chapter closure owner `cl(·)`.
-/

namespace Function.IsConvex

variable {f : E → WithBotTop α}

/-- Theorem 7.5: if `f` is a proper convex function and `x ∈ riDom[𝕜](f)`, then for every `y`
the values of `f` along the segment `λ ↦ lineMap x y λ` converge to `cl(f) y` as
`λ → 1` from the left. -/
-- Proof sketch: if `y ∈ intrinsicClosure 𝕜 dom(f)`, use the companion intrinsic-closure theorem
-- below. If `y ∉ intrinsicClosure 𝕜 dom(f)`, the Chapter 7 closure/domain theorems identify the
-- boundary value as `cl(f) y = ⊤`, and properness forces the segment profile to tend to `⊤` as
-- the endpoint leaves the closure of the effective domain.
theorem tendsto_lineMap_to_lowerSemicontinuousHull
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) {x y : E} (hx : x ∈ riDom[𝕜](f)) :
    Tendsto (fun t : 𝕜 ↦ f (lineMap x y t))
      (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
      (nhds (cl(f) y)) := sorry

/-- Boundary-value extension of the segment-limit formula: if
`y ∈ intrinsicClosure 𝕜 dom(f)`, then the same convergence to `cl(f) y` holds without assuming
properness of `f`. -/
-- Proof sketch: use Lemma 7.3 to place `(x, α)` in `ri(epi f)` for every scalar `α > f x`, then
-- apply Theorem 6.1 to the segment joining `(x, α)` to a point of `closure (epi f)` over `y`.
-- This gives the upper bound on the limsup. The lower bound comes from lower semicontinuity of
-- `cl(f)` and the pointwise inequality `cl(f) ≤ f`. When `f` is improper, Corollary 7.2.1
-- identifies the whole segment profile with `⊥` on the intrinsic closure of the effective domain.
theorem tendsto_lineMap_to_lowerSemicontinuousHull_of_mem_intrinsicClosure_dom
    (hf : f.IsConvex 𝕜) {x y : E} (hx : x ∈ riDom[𝕜](f))
    (hy : y ∈ intrinsicClosure 𝕜 dom(f)) :
    Tendsto (fun t : 𝕜 ↦ f (lineMap x y t))
      (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
      (nhds (cl(f) y)) := sorry

end Function.IsConvex

end
