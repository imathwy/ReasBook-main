import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open AffineMap Filter
open scoped Rockafellar

variable {𝕜 E : Type u}
variable [Ring 𝕜] [LinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [IsStrictOrderedRing 𝕜]
  [ContinuousAdd 𝕜] [ContinuousMul 𝕜]
  [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
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

variable {f : E → WithTopBot 𝕜}

private theorem withTopBot_exists_coe_of_ne_top_ne_bot {z : WithTopBot 𝕜}
    (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥) :
    ∃ a : 𝕜, (a : WithTopBot 𝕜) = z := by
  cases hz : z using WithTop.recTopCoe with
  | top => exact False.elim (hz_top hz)
  | coe z' =>
      cases hz' : z' using WithBot.recBotCoe with
      | bot => exact False.elim (hz_bot (by simp [hz, hz']))
      | coe a => exact ⟨a, rfl⟩

private theorem withTopBot_coe_lt_coe {a b : 𝕜} :
    (a : WithTopBot 𝕜) < (b : WithTopBot 𝕜) ↔ a < b := by
  change
    (((a : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
        (((b : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) ↔ a < b
  rw [WithTop.coe_lt_coe, WithBot.coe_lt_coe]

private theorem withTopBot_coe_lt_top (a : 𝕜) :
    (a : WithTopBot 𝕜) < ⊤ :=
  WithTop.coe_lt_top (a : WithBot 𝕜)

private theorem withTopBot_bot_lt_coe (a : 𝕜) :
    (⊥ : WithTopBot 𝕜) < (a : WithTopBot 𝕜) := by
  change
    ((⊥ : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
      (((a : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜))
  exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)

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
  let g : 𝕜 → WithTopBot 𝕜 := fun t ↦ f (lineMap x y t)
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
      have htop : (⊤ : WithTopBot 𝕜) < a := by
        rwa [hfy_top] at ha'
      exact (not_lt_of_ge (show a ≤ (⊤ : WithTopBot 𝕜) from le_top) htop).elim
  · have hfy_bot : f y ≠ ⊥ := hf_proper.ne_bot y
    rcases withTopBot_exists_coe_of_ne_top_ne_bot hfy_top hfy_bot with ⟨fy, hfy⟩
    have hfx_top : f x ≠ ⊤ := (mem_effectiveDomain.mp hx).ne
    have hfx_bot : f x ≠ ⊥ := hf_proper.ne_bot x
    rcases withTopBot_exists_coe_of_ne_top_ne_bot hfx_top hfx_bot with ⟨fx, hfx⟩
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
          ∀ᶠ t in nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)), g t < (β : WithTopBot 𝕜) := by
      intro β hfy_lt_beta
      rcases exists_between hfy_lt_beta with ⟨γ, hfy_lt_gamma, hgamma_lt_beta⟩
      let α : 𝕜 := fx + 1
      have hfx_lt_alpha : f x < α := by
        simpa [hfx, α] using
          (withTopBot_coe_lt_coe.mpr (lt_add_of_pos_right fx zero_lt_one) :
            (fx : WithTopBot 𝕜) < ((fx + 1 : 𝕜) : WithTopBot 𝕜))
      have hfy_lt_gamma' : f y < γ := by
        simpa [hfy] using
          (withTopBot_coe_lt_coe.mpr hfy_lt_gamma :
            (fy : WithTopBot 𝕜) < (γ : WithTopBot 𝕜))
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
      have hconv : g t < (((1 - t) * α + t * γ : 𝕜) : WithTopBot 𝕜) := by
        simpa [g, lineMap_apply_module] using
          ((Function.isConvex_iff_lt_affine_upper_bound f).mp hf
            x y α γ t hfx_lt_alpha hfy_lt_gamma' ht0 ht1)
      exact lt_trans hconv
        (show (((1 - t) * α + t * γ : 𝕜) : WithTopBot 𝕜) < (β : WithTopBot 𝕜) by
          exact withTopBot_coe_lt_coe.mpr htβ)
    refine (tendsto_order.2 ?_)
    constructor
    · intro a ha
      exact (lowerSemicontinuousWithinAt_iff.mp hg_lsc) a <| by simpa [g, hfy] using ha
    · intro a ha
      by_cases ha_top : a = (⊤ : WithTopBot 𝕜)
      · subst ha_top
        filter_upwards [h_upper_to_coe (show fy < fy + 1 by
          exact lt_add_of_pos_right fy zero_lt_one)] with t ht
        exact lt_trans ht (withTopBot_coe_lt_top (fy + 1))
      · have ha_bot : a ≠ ⊥ := by
          rw [← hfy] at ha
          exact ne_of_gt (lt_of_lt_of_le (withTopBot_bot_lt_coe fy) ha.le)
        rcases withTopBot_exists_coe_of_ne_top_ne_bot ha_top ha_bot with ⟨β, hβ⟩
        have hfy_lt_beta' : (fy : WithTopBot 𝕜) < (β : WithTopBot 𝕜) := by
          simpa [g, hfy, hβ] using ha
        have hfy_lt_beta : fy < β := withTopBot_coe_lt_coe.mp hfy_lt_beta'
        simpa [hβ] using h_upper_to_coe hfy_lt_beta

end Function.IsConvex

end
