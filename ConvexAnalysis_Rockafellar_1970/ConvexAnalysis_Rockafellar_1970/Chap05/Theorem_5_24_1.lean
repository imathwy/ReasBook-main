import Mathlib.Analysis.Convex.Deriv
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1

noncomputable section

open Filter
open Set
open scoped Rockafellar Topology

/-!
Source/core/bridge triage for this item.

  theorem for the right and left derivatives of a proper convex function on an ordered scalar line,
  stated at
  interior points of `dom(f)` for the continuity clauses.
- `core/canonical`: the chapter owner abstraction for directional variation is
  `Function.directionalDifferenceQuotientAt` / `Function.directionalDerivativeAt`, and the ambient
  convexity owner is `Function.IsConvex 𝕜`; properness is carried separately by
  `Function.IsProper` exactly where the one-sided continuity and finiteness clauses need it.
- `bridge/view`: the source's one-sided derivatives are the right/left secant
  slope envelopes of the Chapter 23 directional quotient owner. On `dom(f)` they agree with the
  directional derivatives in directions `1` and `-1`; off `dom(f)` the same secant-slope owner
  gives the textbook `±∞` extension without introducing a second package of chosen data.

Domain-style sampling used here:
- `Function.directionalDifferenceQuotientAt` and `Function.directionalDerivativeAt` from
  `Chap05/Lemma_23_0_1`, which are the chapter owners for directional derivatives;
- `ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior`,
  `ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior`,
  `ConvexOn.monotoneOn_rightDeriv`, `ConvexOn.monotoneOn_leftDeriv`, and
  `ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior` from
  `Mathlib/Analysis/Convex/Deriv.lean`, which organize the finite-valued one-dimensional convex
  theory around secant slopes and one-sided derivatives on the interior of the domain;
- `ConvexOn.secant_mono` from `Mathlib/Analysis/Convex/Slope.lean`, which is the canonical slope
  monotonicity owner behind the source inequality
  `f'_+(z₁) ≤ f'_-(x) ≤ f'_+(x) ≤ f'_-(z₂)`.

Primitive data vs derived API:
- primitive source-facing owners: `Function.rightDerivative` and `Function.leftDerivative`;
- derived API: the identification with the Chapter 23 directional derivative at a finite point,
  the atomic order inequalities between the one-sided derivatives, monotonicity, finiteness on
  `interior (dom(f))`, the four one-sided limit formulas, and the companion
  `Function.leftLim` / `Function.rightLim` bridge equalities;
- assumption split used below: the directional-derivative bridge uses convexity plus the explicit
  finite-point guard `x ∈ dom(f)` and `f x ≠ ⊥`, the order and monotonicity facts use only
  convexity, and the one-sided finiteness/continuity statements use convexity + properness at
  points of `interior (dom(f))`.

Layer target: `source-facing`.

Notation evaluation:
- the textbook symbols are surfaced by ordinary scoped notation as `f′+` and `f′-`, so theorem
  statements can stay close to the source while keeping the canonical owners
  `Function.rightDerivative` and `Function.leftDerivative` as definitions.
- mathlib's `rightDeriv` / `leftDeriv` are interior-point finite-valued companion owners, so they
  stay part of the domain-style sampling rather than replacing the source-facing extended-real
  owners below.
-/

namespace Function

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Internal secant-slope set for the source right derivative. This is proof-facing scaffolding,
not a second public owner. -/
private def rightDerivativeSlopeSet (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : Set (WithTopBot 𝕜) :=
  directionalDifferenceQuotientAt f x 1 '' {t : 𝕜 | 0 < t ∧ x + t ∈ dom(f)}

/-- Internal secant-slope set for the source left derivative. This is proof-facing scaffolding,
not a second public owner. -/
private def leftDerivativeSlopeSet (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : Set (WithTopBot 𝕜) :=
  (fun t : 𝕜 ↦ -directionalDifferenceQuotientAt f x (-1) t) ''
    {t : 𝕜 | 0 < t ∧ x - t ∈ dom(f)}

/-- The source right derivative `f'_+(x)` on the line, extended by the canonical empty-infimum /
secant-slope rule outside `dom(f)`. The definition is built directly from the Chapter 23
directional-difference owner and keeps the owner at the slope level rather than packaging extra
data. -/
def rightDerivative (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : WithTopBot 𝕜 :=
  sInf (rightDerivativeSlopeSet f x)

/-- The source left derivative `f'_-(x)` on the line, written through the Chapter 23
directional-difference owner in direction `-1` and the same secant-slope extension rule outside
`dom(f)`. -/
def leftDerivative (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : WithTopBot 𝕜 :=
  sSup (leftDerivativeSlopeSet f x)

/-- Textbook one-sided right derivative notation for `Function.rightDerivative`. -/
scoped[Rockafellar] notation:max f "′+" => Function.rightDerivative f

/-- Textbook one-sided left derivative notation for `Function.leftDerivative`. -/
scoped[Rockafellar] notation:max f "′-" => Function.leftDerivative f

variable {f : 𝕜 → WithTopBot 𝕜}

section Topological

variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]

-- Proof sketch: once `x ∈ dom(f)`, the secant-slope infimum defining `f'_+(x)` is exactly the
-- Chapter 23 right directional derivative in direction `1`.
/-- At a finite point of a convex function, the source right derivative is the Chapter 23
directional derivative in direction `1`. -/
theorem rightDerivative_eq_directionalDerivativeAt_one
    (hf_convex : f.IsConvex 𝕜) {x : 𝕜} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    f′+ x = directionalDerivativeAt f x 1 := by
  sorry

-- Proof sketch: on `dom(f)`, the source left derivative is the negated Chapter 23 directional
-- derivative in direction `-1`.
/-- At a finite point of a convex function, the source left derivative is the negative of the
Chapter 23 directional derivative in direction `-1`. -/
theorem leftDerivative_eq_neg_directionalDerivativeAt_neg_one
    (hf_convex : f.IsConvex 𝕜) {x : 𝕜} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    f′- x = -directionalDerivativeAt f x (-1) := by
  sorry

end Topological

/-- If `x` lies to the right of some finite point of `f` but does not itself belong to `dom(f)`,
then the source left derivative at `x` is `+∞`. -/
theorem leftDerivative_eq_top_of_not_mem_dom_of_nonempty_inter_Iio
    {x : 𝕜} (hx : x ∉ dom(f)) (hy : (dom(f) ∩ Iio x).Nonempty) :
    f′- x = ⊤ := by
  rcases hy with ⟨y, hy_dom, hyx⟩
  have hx_top : f x = ⊤ := by
    by_contra hx_top
    exact hx ((mem_effectiveDomain).2 (lt_top_iff_ne_top.mpr hx_top))
  let t : 𝕜 := x - y
  have ht : 0 < t := sub_pos.mpr hyx
  have hsub : x - t = y := by
    dsimp [t]
    linarith
  have hxt : x - t ∈ dom(f) := by
    simpa [hsub] using hy_dom
  have htop_mem :
      (⊤ : WithTopBot 𝕜) ∈
        (fun t : 𝕜 ↦ -directionalDifferenceQuotientAt f x (-1) t) ''
          {t : 𝕜 | 0 < t ∧ x - t ∈ dom(f)} := by
    refine ⟨t, ⟨ht, hxt⟩, ?_⟩
    change -directionalDifferenceQuotientAt f x (-1) t = ⊤
    unfold directionalDifferenceQuotientAt
    have hadd : x + t • (-1 : 𝕜) = y := by
      dsimp [t]
      linarith
    rw [hadd, hx_top]
    have hdiv : (⊥ : WithTopBot 𝕜) / (t : WithTopBot 𝕜) = ⊥ := by
      have h_inv : 0 < t⁻¹ := inv_pos.mpr ht
      simpa [WithBotTop.div_eq_mul_inv, WithBotTop.coe_inv] using
        (WithBotTop.bot_mul_coe_of_pos (a := t⁻¹) h_inv)
    change -(((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) / (t : WithTopBot 𝕜)) = ⊤
    rw [show ((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) = (⊥ : WithTopBot 𝕜) by simp,
      hdiv]
    simp
  unfold leftDerivative leftDerivativeSlopeSet
  exact top_le_iff.mp (le_sSup htop_mem)

/-- If `x` lies to the left of some finite point of `f` but does not itself belong to `dom(f)`,
then the source right derivative at `x` is `-∞`. -/
theorem rightDerivative_eq_bot_of_not_mem_dom_of_nonempty_inter_Ioi
    {x : 𝕜} (hx : x ∉ dom(f)) (hy : (dom(f) ∩ Ioi x).Nonempty) :
    f′+ x = ⊥ := by
  rcases hy with ⟨y, hy_dom, hxy⟩
  have hx_top : f x = ⊤ := by
    by_contra hx_top
    exact hx ((mem_effectiveDomain).2 (lt_top_iff_ne_top.mpr hx_top))
  let t : 𝕜 := y - x
  have ht : 0 < t := sub_pos.mpr hxy
  have hadd : x + t = y := by
    dsimp [t]
    linarith
  have hxt : x + t ∈ dom(f) := by
    simpa [hadd] using hy_dom
  have hbot_mem :
      (⊥ : WithTopBot 𝕜) ∈
        directionalDifferenceQuotientAt f x 1 ''
          {t : 𝕜 | 0 < t ∧ x + t ∈ dom(f)} := by
    refine ⟨t, ⟨ht, hxt⟩, ?_⟩
    unfold directionalDifferenceQuotientAt
    have hsmul : x + t • (1 : 𝕜) = y := by
      dsimp [t]
      linarith
    change (((show WithTopBot 𝕜 from f (x + t • (1 : 𝕜))) - (show WithTopBot 𝕜 from f x)) /
      (t : WithTopBot 𝕜)) = ⊥
    rw [hsmul, hx_top]
    change (((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) /
      (t : WithTopBot 𝕜)) = ⊥
    have hdiv : (⊥ : WithTopBot 𝕜) / (t : WithTopBot 𝕜) = ⊥ := by
      have h_inv : 0 < t⁻¹ := inv_pos.mpr ht
      simpa [WithBotTop.div_eq_mul_inv, WithBotTop.coe_inv] using
        (WithBotTop.bot_mul_coe_of_pos (a := t⁻¹) h_inv)
    rw [show ((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) = (⊥ : WithTopBot 𝕜) by simp,
      hdiv]
  unfold rightDerivative rightDerivativeSlopeSet
  exact le_bot_iff.mp (sInf_le hbot_mem)

-- Proof sketch: compare the relevant secant slopes directly. For `z < x`, every right secant at
-- `z` is bounded above by every left secant at `x` by convex slope monotonicity, and the empty
-- set cases reproduce the textbook `±∞` extension outside `dom(f)`.
/-- The source secant-order inequality `f'_+(z) ≤ f'_-(x)` for `z < x`. -/
theorem rightDerivative_le_leftDerivative_of_lt
    (hf_convex : f.IsConvex 𝕜) {z x : 𝕜} (hzx : z < x) :
    f′+ z ≤ f′- x := by
  sorry

/-- The source inequality `f'_-(x) ≤ f'_+(x)`. -/
theorem leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (x : 𝕜) :
    f′- x ≤ f′+ x := by
  sorry

/-- The source right derivative is nondecreasing. -/
theorem monotone_rightDerivative
    (hf_convex : f.IsConvex 𝕜)
    : Monotone (f′+) := by
  sorry

/-- The source left derivative is nondecreasing. -/
theorem monotone_leftDerivative
    (hf_convex : f.IsConvex 𝕜)
    : Monotone (f′-) := by
  sorry

section Topological

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]

/-- On the interior of the effective domain, the source right derivative is finite. -/
theorem rightDerivative_lt_top_of_mem_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    f′+ x < ⊤ := by
  sorry

/-- On the interior of the effective domain, the source left derivative is finite. -/
theorem bot_lt_leftDerivative_of_mem_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    ⊥ < f′- x := by
  sorry

-- Proof sketch: the order chain implies that `rightDerivative` is right-continuous and that its
-- left limit is `leftDerivative`; the same argument with the roles reversed gives the two formulas
-- for `leftDerivative`.
/-- On `interior (dom(f))`, the source right derivative is right-continuous. -/
theorem tendsto_rightDerivative_right
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′+) (𝓝[>] x) (𝓝 (f′+ x)) := by
  sorry

/-- On `interior (dom(f))`, the left limit of the source right derivative at `x` is the source
left derivative at `x`. -/
theorem tendsto_rightDerivative_left
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′+) (𝓝[<] x) (𝓝 (f′- x)) := by
  sorry

/-- On `interior (dom(f))`, the right limit of the source left derivative at `x` is the source
right derivative at `x`. -/
theorem tendsto_leftDerivative_right
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′-) (𝓝[>] x) (𝓝 (f′+ x)) := by
  sorry

/-- On `interior (dom(f))`, the source left derivative is left-continuous. -/
theorem tendsto_leftDerivative_left
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′-) (𝓝[<] x) (𝓝 (f′- x)) := by
  sorry

/-- On `interior (dom(f))`, the canonical strict right limit of the source right derivative agrees
with its value. -/
theorem rightLim_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′+).rightLim x = f′+ x := by
  exact rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_rightDerivative_right hf_convex hf_proper hx)

/-- On `interior (dom(f))`, the canonical strict left limit of the source right derivative is the
source left derivative. -/
theorem leftLim_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′+).leftLim x = f′- x := by
  exact leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_rightDerivative_left hf_convex hf_proper hx)

/-- The canonical strict right limit of the source left derivative is the source right derivative.
-/
theorem rightLim_leftDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′-).rightLim x = f′+ x := by
  exact rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_leftDerivative_right hf_convex hf_proper hx)

/-- On `interior (dom(f))`, the canonical strict left limit of the source left derivative agrees
with its value. -/
theorem leftLim_leftDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′-).leftLim x = f′- x := by
  exact leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_leftDerivative_left hf_convex hf_proper hx)

end Topological

end Function
