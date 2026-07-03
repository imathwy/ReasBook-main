import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_1_2_1 (from Chap03) -/
noncomputable section

open scoped BigOperators WithTopConvexAnalysis

universe u

variable {X : Type u} {ι : Type*} [Fintype ι]
  [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Proposition 3.1.2.1 lies in the chapter's closed-convex weighted pointwise-supremum domain.

Primary domain:
- weighted pointwise suprema of `WithTop ℝ`-valued functions on a real topological module.

Sampled owner-style declarations:
- `pointwiseSupremumOn` and `pointwiseSupremumOn_apply`
- `pointwiseSupremumOnEffectiveDomain`
- `ClosedConvexOn.pointwise_sSup`
- `ClosedConvexOn.nonneg_smul` and `ClosedConvexOn.add_inter`

Best owner abstraction:
- source-facing: this proposition, which bridges componentwise closed-convexity and nonnegative
  weights to the chapter owner theorem for pointwise suprema
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`, and
  `ClosedConvexOn.pointwise_sSup`
- bridge/view: the weighted slice family
  `fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x`

Primitive data:
- a weight set `Δ : Set (ι → ℝ)`
- a family `f : ι → X → WithTop ℝ`
- nonemptiness of `Δ`
- coordinatewise nonnegativity of the weights in `Δ`
- closed-convexity of each component `f i`

Derived API:
- the weighted-slice pointwise-supremum owner
  `pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)`
- the closed-convexity theorem below for that owner

This proposition is not recall-only: its mathematical content is the bridge from the componentwise
assumptions on the family `f i` and the coordinatewise nonnegative weight functions in `Δ` to
the slicewise hypothesis required by `ClosedConvexOn.pointwise_sSup`. The later file
`Proposition_3_9` therefore
reuses this theorem directly instead of keeping a second public copy of the same bridge. -/

-- Proof sketch: first prove each weighted slice is a closed convex function by finite induction on
-- the sum, using the nonnegative weighted-add rule at each step. Then identify the effective
-- epigraph of the pointwise supremum with the intersection of the slice effective epigraphs. The
-- closedness and convexity fields of `ClosedConvexFunction` then follow from intersection
-- stability.
/-- Helper for Proposition 3.1.2.1: the constant zero `WithTop ℝ`-valued function is closed and
convex. -/
lemma closedConvexFunction_zero : ClosedConvexFunction (fun _ : X ↦ (0 : WithTop ℝ)) := by
  -- The zero function is the coercion of a continuous convex real-valued function.
  simpa using
    (closedConvexFunction_coe_of_convexOn_continuous
      (f := fun _ : X ↦ (0 : ℝ))
      (convexOn_const (0 : ℝ) convex_univ)
      continuous_const)

/-- Helper for Proposition 3.1.2.1: every admissible nonnegative weighted slice is a closed convex
function. -/
lemma closedConvexFunction_weighted_slice
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    (hΔ_nonneg : ∀ ⦃weights⦄, weights ∈ Δ → ∀ i, 0 ≤ weights i)
    (hf : ∀ i, ClosedConvexFunction (f i))
    {weights : ι → ℝ} (hs : weights ∈ Δ) :
    ClosedConvexFunction (fun x ↦ ∑ i, (weights i : WithTop ℝ) * f i x) := by
  classical
  -- Build the finite weighted sum by inserting one nonnegative weighted summand at a time.
  have hzero : ClosedConvexFunction
      (fun x ↦ ∑ i ∈ (∅ : Finset ι), (weights i : WithTop ℝ) * f i x) := by
    simpa using closedConvexFunction_zero (X := X)
  have hstep : ∀ a s, a ∉ s →
      ClosedConvexFunction (fun x ↦ ∑ i ∈ s, (weights i : WithTop ℝ) * f i x) →
      ClosedConvexFunction (fun x ↦ ∑ i ∈ insert a s, (weights i : WithTop ℝ) * f i x) := by
    intro a s ha hsCC
    -- The induction step is the nonnegative weighted-add rule with coefficient `1` on the tail.
    have hsum :=
      ClosedConvexFunction.nonneg_weighted_add (hf a) hsCC (hΔ_nonneg hs a) zero_le_one
    simpa [Finset.sum_insert, ha, smul_eq_mul, Pi.add_apply, one_smul] using hsum
  simpa using Finset.induction hzero hstep (Finset.univ : Finset ι)

/-- Helper for Proposition 3.1.2.1: each admissible weighted slice lies below the pointwise
supremum. -/
lemma weighted_slice_le_pointwiseSupremumOn
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    {weights : ι → ℝ} (hs : weights ∈ Δ) (x : X) :
    (∑ i, (weights i : WithTop ℝ) * f i x) ≤
      pointwiseSupremumOn Δ (fun y weights ↦ ∑ i, (weights i : WithTop ℝ) * f i y) x := by
  -- The chosen slice is one member of the supremum-defining image set.
  rw [pointwiseSupremumOn_apply]
  refine le_csSup ?_ ?_
  · exact ⟨⊤, fun _ _ ↦ le_top⟩
  · exact ⟨weights, hs, rfl⟩

/-- Helper for Proposition 3.1.2.1: the effective epigraph of the weighted pointwise supremum is
the intersection of the slice effective epigraphs. -/
lemma effectiveEpigraph_pointwiseSupremumOn_nonneg_weighted_eq_iInter
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    (hΔ_nonempty : Δ.Nonempty) :
    WithTopConvexAnalysis.effectiveEpigraph
        (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) =
      ⋂ weights : Δ,
        WithTopConvexAnalysis.effectiveEpigraph
          (fun x ↦ ∑ i, ((weights.1 i : ℝ) : WithTop ℝ) * f i x) := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_iInter]
    intro weights
    rcases WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp hp with ⟨hpdom, hple⟩
    have hslicele := weighted_slice_le_pointwiseSupremumOn (f := f) weights.2 p.1
    have hslicedom : p.1 ∈ dom (fun x ↦ ∑ i, ((weights.1 i : ℝ) : WithTop ℝ) * f i x) := by
      rw [mem_withTopEffectiveDomain_iff]
      exact
        lt_of_le_of_lt (le_trans hslicele hple)
          (show (p.2 : WithTop ℝ) < ⊤ from WithTop.coe_lt_top p.2)
    exact WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr ⟨hslicedom, le_trans hslicele hple⟩
  · intro hp
    rw [Set.mem_iInter] at hp
    rcases hΔ_nonempty with ⟨weights0, hs0⟩
    refine WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr ?_
    constructor
    · rw [mem_withTopEffectiveDomain_iff, pointwiseSupremumOn_apply]
      refine lt_of_le_of_lt ?_ (show (p.2 : WithTop ℝ) < ⊤ from WithTop.coe_lt_top p.2)
      refine csSup_le ?_ ?_
      · exact ⟨_, ⟨weights0, hs0, rfl⟩⟩
      · intro z hz
        rcases hz with ⟨weights, hs, rfl⟩
        exact (WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp (hp ⟨weights, hs⟩)).2
    · rw [pointwiseSupremumOn_apply]
      refine csSup_le ?_ ?_
      · exact ⟨_, ⟨weights0, hs0, rfl⟩⟩
      · intro z hz
        rcases hz with ⟨weights, hs, rfl⟩
        exact (WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp (hp ⟨weights, hs⟩)).2

/-- Proposition 3.1.2.1: for a nonempty family of coordinatewise nonnegative finite weights, the
weighted pointwise supremum built from the finite sums `x ↦ ∑ i, weights i * f i x` of closed
convex functions is again a closed convex function. -/
theorem closedConvexFunction_pointwiseSupremumOn_nonneg_weighted
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    (hΔ_nonempty : Δ.Nonempty)
    (hΔ_nonneg : ∀ ⦃weights⦄, weights ∈ Δ → ∀ i, 0 ≤ weights i)
    (hf : ∀ i, ClosedConvexFunction (f i)) :
    ClosedConvexFunction
      (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) := by
  refine ⟨subset_rfl, ?_, ?_⟩
  · -- The supremum effective epigraph is an intersection of closed slice effective epigraphs.
    rw [show constrainedEpigraph
        (dom (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)))
        (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) =
        WithTopConvexAnalysis.effectiveEpigraph
          (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) by
      rfl]
    rw [effectiveEpigraph_pointwiseSupremumOn_nonneg_weighted_eq_iInter
      (Δ := Δ) (f := f) hΔ_nonempty]
    refine isClosed_iInter ?_
    intro weights
    -- Each slice is closed because the slice itself is a closed convex function.
    have hslice :=
      closedConvexFunction_weighted_slice (Δ := Δ) (f := f) hΔ_nonneg hf weights.2
    simpa [WithTopConvexAnalysis.effectiveEpigraph] using hslice.isClosed_constrainedEpigraph
  · -- The same effective-epigraph intersection identity preserves convexity as well.
    rw [show constrainedEpigraph
        (dom (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)))
        (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) =
        WithTopConvexAnalysis.effectiveEpigraph
          (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) by
      rfl]
    rw [effectiveEpigraph_pointwiseSupremumOn_nonneg_weighted_eq_iInter
      (Δ := Δ) (f := f) hΔ_nonempty]
    refine convex_iInter ?_
    intro weights
    -- Each slice contributes a convex effective epigraph to the intersection.
    have hslice :=
      closedConvexFunction_weighted_slice (Δ := Δ) (f := f) hΔ_nonneg hf weights.2
    simpa [WithTopConvexAnalysis.effectiveEpigraph] using hslice.convex_constrainedEpigraph

end

/-! ### Proposition_3_1_2_2 (from Chap03) -/
universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/- Proposition 3.1.2.2 lies in the chapter's support-function / positive-homogeneity domain.

Sampled declarations in this domain:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply` from `Definition_3_9`
- `supportFunction_smul` from `Proposition_3_10`

Best owner abstraction:
- the existing chapter theorem `supportFunction_smul`

Primitive data:
- a set `Q : Set E`
- a nonemptiness witness `hQ : Q.Nonempty`
- a direction `x : E`
- a bundled nonnegative scalar `τ : NNReal`

Derived API:
- the support-function homogeneity identity itself

Source/core/bridge triage:
- source-facing: the textbook positive-homogeneity statement for support functions
- core/canonical: the already formalized chapter theorem `supportFunction_smul`
- bridge/view: this numbered file is recall-only

This file therefore recalls the existing chapter theorem directly instead of keeping a duplicate
public declaration with the same interface. -/

/- Proposition 3.1.2.2 recalls the chapter theorem `supportFunction_smul`. -/
recall supportFunction_smul
    (Q : Set E) (hQ : Q.Nonempty) (x : E) (τ : NNReal) :
    ξ[Q] (τ • x) = (τ : EReal) * ξ[Q] x

/-! ### Proposition_3_1_2_3 (from Chap03) -/
/- Proposition 3.1.2.3 lies in the chapter's support-function / effective-domain domain.

Sampled owner-style declarations:
- `extendedRealEffectiveDomain` in `Definition_3_1_1_2`
- `supportFunction` in `Definition_3_9`
- `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded` in `Proposition_3_11`
- `supportFunction_dom_eq_univ_of_nonempty_bounded` in `Proposition_3_11`

Best owner abstraction:
- the existing chapter theorem
  `supportFunction_dom_eq_univ_of_nonempty_bounded`, together with its pointwise companion
  `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded`

Primitive data:
- a set `Q : Set E` in a real inner-product space `E`
- hypotheses `Q.Nonempty` and `Bornology.IsBounded Q`

Derived API:
- pointwise finiteness of `supportFunction Q`
- the domain identity `dom (supportFunction Q) = Set.univ`

Source/core/bridge triage:
- source-facing: the bounded-set support-function finiteness statement
- core/canonical: `supportFunction_dom_eq_univ_of_nonempty_bounded`
- bridge/view: the pointwise companion theorem

This file previously duplicated the exact pointwise companion theorem already formalized in
`Proposition_3_11` and also kept a renamed shell for the global domain theorem. Since the chapter
already has the owner theorem family, and that family has now been generalized to arbitrary real
inner-product spaces, this numbered item is recall-only and keeps no parallel local theorem names.
The textbook `ℝⁿ` statement remains an immediate specialization. -/

recall supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded

recall supportFunction_dom_eq_univ_of_nonempty_bounded

/-! ### Remark_3_1_2_1 (from Chap03) -/
noncomputable section

open scoped Pointwise Topology ENNReal NNReal WithTopConvexAnalysis

universe u

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [ContinuousSMul ℝ E]

/- Remark 3.1.2.1 lies in the Minkowski-functional / gauge domain.

Sampled owner-style declarations:
- mathlib `egauge`
- mathlib `egauge_eq_top`
- mathlib `gauge`
- project `IsPositivelyHomogeneousOn`

Best owner abstraction:
- the mathlib extended gauge owner `egauge ℝ≥0 Q`, with `gauge Q` as its finite real-valued view

Primitive data:
- a set `Q : Set E`
- the convexity hypothesis `Convex ℝ Q`
- the neighborhood-of-zero hypothesis `(0 : E) ∈ interior Q`

Derived API:
- the source-facing `WithTop ℝ` bridge `minkowskiFunctional Q`
- the finite-value bridge `minkowskiFunctional_eq_gauge` on `dom (ψ[Q])`
- the whole-space finiteness bridge `dom_minkowskiFunctional_eq_univ_of_zero_mem_interior`
- the whole-space equality bridge `minkowskiFunctional_eq_gauge_of_zero_mem_interior`
- degree-one positive homogeneity on `Set.univ`, recorded through the chapter owner
  `IsPositivelyHomogeneousOn 1 Set.univ`
- whole-space convexity `ConvexOn ℝ Set.univ`

Source/core/bridge triage:
- source-facing: the textbook remark that the Minkowski functional is positively homogeneous and
  convex, together with the `WithTop ℝ` notation `ψ[Q]` used downstream in subdifferential
  statements;
- core/canonical: mathlib `egauge` and `gauge`;
- bridge/view: `minkowskiFunctional`, which repackages `egauge ℝ≥0 Q` in the chapter's
  `WithTop ℝ` codomain, `minkowskiFunctional_eq_gauge` on the canonical effective domain
  `dom (ψ[Q])`, and the whole-space bridges obtained from `(0 : E) ∈ interior Q`.

The bounded and closed hypotheses from the textbook remark are redundant for these two
consequences, so the refined statement keeps only the convexity and interior-point assumptions
actually used by the canonical gauge API.
-/

section MinkowskiFunctional

private def ennrealToWithTopReal (x : ℝ≥0∞) : WithTop ℝ :=
  if x = ⊤ then ⊤ else ((x.toReal : ℝ) : WithTop ℝ)

/-- The textbook Minkowski functional `ψ_Q`, viewed as a `WithTop ℝ`-valued function so that the
value is `⊤` when no nonnegative scaling of `Q` contains the point. This is the chapter's
`WithTop ℝ` bridge of the canonical extended gauge `egauge ℝ≥0 Q`. -/
abbrev minkowskiFunctional {F : Type u} [SMul ℝ F] (Q : Set F) : F → WithTop ℝ :=
  fun x ↦ ennrealToWithTopReal (egauge ℝ≥0 Q x)

namespace MinkowskiFunctional

scoped notation:max "ψ[" Q "]" => minkowskiFunctional Q

end MinkowskiFunctional

open scoped MinkowskiFunctional

section GaugeBridge

variable {F : Type u}
variable [AddCommGroup F] [Module ℝ F]

/-- On the effective domain `dom (ψ[Q])`, the source-facing Minkowski functional agrees with
mathlib's canonical real-valued gauge. -/
theorem minkowskiFunctional_eq_gauge
    {Q : Set F} {x : F} (hx : x ∈ dom (ψ[Q])) :
    ψ[Q] x = (gauge Q x : WithTop ℝ) := by
  -- Read the finite `WithTop` value as a real number before comparing with the canonical gauge.
  let e : ℝ≥0∞ := egauge ℝ≥0 Q x
  have he_ne_top : e ≠ ⊤ := by
    intro he_top
    have : ψ[Q] x = ⊤ := by
      simp [minkowskiFunctional, ennrealToWithTopReal, e, he_top]
    simp [this] at hx
  have hrealpart : withTopRealPart (ψ[Q]) x = e.toReal := by
    apply WithTop.coe_injective
    rw [coe_withTopRealPart hx]
    simp [minkowskiFunctional, ennrealToWithTopReal, e, he_ne_top]
  have hreal_eq_gauge : e.toReal = gauge Q x := by
    by_cases hs : {r : ℝ | 0 < r ∧ x ∈ r • Q}.Nonempty
    · have hlower : e.toReal ≤ gauge Q x := by
        -- Every positive scale witnessing membership bounds the extended gauge from above.
        have hs' : {r ∈ Set.Ioi (0 : ℝ) | x ∈ r • Q}.Nonempty := by
          rcases hs with ⟨r, hr, hxr⟩
          exact ⟨r, hr, hxr⟩
        rw [gauge_def]
        refine le_csInf hs' ?_
        intro r hr
        let c : ℝ≥0 := ⟨r, le_of_lt hr.1⟩
        have he_le : e ≤ (c : ℝ≥0∞) := by
          have hc_mem : x ∈ c • Q := by
            simpa [c, NNReal.smul_def] using hr.2
          simpa [c, e] using egauge_le_of_mem_smul (𝕜 := ℝ≥0) (c := c) hc_mem
        have htoReal : e.toReal ≤ r := by
          simpa [c] using ENNReal.toReal_mono (by simp) he_le
        exact htoReal
      have hupper : gauge Q x ≤ e.toReal := by
        -- Approximate the infimum defining `egauge` by an actual scaling witness.
        refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
        let r : ℝ≥0 := ⟨e.toReal + ε, add_nonneg ENNReal.toReal_nonneg hε.le⟩
        have he_lt : e < (r : ℝ≥0∞) := by
          have htoReal_lt : e.toReal < (r : ℝ) := by
            change e.toReal < e.toReal + ε
            exact lt_add_of_pos_right e.toReal hε
          exact (ENNReal.toReal_lt_toReal he_ne_top (by simp)).1 (by simpa [r] using htoReal_lt)
        rcases egauge_lt_iff.1 he_lt with ⟨c, hxc, hc_lt⟩
        have hc_real : (c : ℝ) < e.toReal + ε := by
          simpa [r] using hc_lt
        have hc_mem : x ∈ (c : ℝ) • Q := by
          simpa [NNReal.smul_def] using hxc
        exact (gauge_le_of_mem c.2 hc_mem).trans_lt hc_real
      exact le_antisymm hlower hupper
    · have hgauge_zero : gauge Q x = 0 := by
        -- If no positive scaling contains `x`, then the gauge infimum is taken over the empty set.
        have hempty : {r ∈ Set.Ioi (0 : ℝ) | x ∈ r • Q} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro r hr
          exact hs ⟨r, hr.1, hr.2⟩
        rw [gauge_def, hempty, Real.sInf_empty]
      have hx_zero : x ∈ (0 : ℝ≥0) • Q := by
        by_contra hx_zero
        have he_top : e = ⊤ := by
          simpa [e] using
            (egauge_eq_top (𝕜 := ℝ≥0) (s := Q) (x := x)).2 fun c ↦ by
              rcases eq_or_lt_of_le c.2 with hc0 | hc
              · have hc0' : c = 0 := NNReal.eq (by simpa using hc0.symm)
                subst hc0'
                simpa using hx_zero
              · intro hxc
                exact hs ⟨(c : ℝ), hc, by simpa [NNReal.smul_def] using hxc⟩
        exact he_ne_top he_top
      have he_zero : e = 0 := by
        have he_le_zero : e ≤ 0 := by
          have h0 : egauge ℝ≥0 Q x ≤ ‖(0 : ℝ≥0)‖ₑ :=
            egauge_le_of_mem_smul (𝕜 := ℝ≥0) (c := (0 : ℝ≥0)) hx_zero
          have hnorm_zero : ‖(0 : ℝ≥0)‖ₑ = (0 : ℝ≥0∞) := by
            rfl
          rw [hnorm_zero] at h0
          simpa [e] using h0
        exact le_antisymm he_le_zero bot_le
      simp [he_zero, hgauge_zero]
  -- Coercing the finite real part back to `WithTop ℝ` gives the desired source-to-canonical bridge.
  calc
    ψ[Q] x = ((withTopRealPart (ψ[Q]) x : ℝ) : WithTop ℝ) := (coe_withTopRealPart hx).symm
    _ = (e.toReal : WithTop ℝ) := by rw [hrealpart]
    _ = (gauge Q x : WithTop ℝ) := by rw [hreal_eq_gauge]

end GaugeBridge

end MinkowskiFunctional

open scoped MinkowskiFunctional

/-- If `0` lies in the interior of `Q`, then the source-facing Minkowski functional is finite
everywhere. -/
theorem dom_minkowskiFunctional_eq_univ_of_zero_mem_interior
    {Q : Set E} (hQ_zero : (0 : E) ∈ interior Q) :
    dom (ψ[Q]) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  -- Interior at the origin gives absorbency, so some positive scaling of `Q` contains `x`.
  have hQ_absorbent : Absorbent ℝ Q :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hQ_zero)
  obtain ⟨r, hr_pos, hxr⟩ := hQ_absorbent.gauge_set_nonempty (x := x)
  have he_ne_top : egauge ℝ≥0 Q x ≠ ⊤ := by
    intro he_top
    rw [egauge_eq_top] at he_top
    exact he_top ⟨r, hr_pos.le⟩ (by simpa using hxr)
  -- Finite extended gauge means the `WithTop ℝ`-valued Minkowski functional is finite as well.
  simp [minkowskiFunctional, ennrealToWithTopReal, he_ne_top]

/-- If `0` lies in the interior of `Q`, then the source-facing Minkowski functional agrees
everywhere with mathlib's canonical real-valued gauge. -/
theorem minkowskiFunctional_eq_gauge_of_zero_mem_interior
    {Q : Set E} (hQ_zero : (0 : E) ∈ interior Q) (x : E) :
    ψ[Q] x = (gauge Q x : WithTop ℝ) := by
  have hx : x ∈ dom (ψ[Q]) := by
    simp [dom_minkowskiFunctional_eq_univ_of_zero_mem_interior hQ_zero]
  simpa using minkowskiFunctional_eq_gauge hx

/-- Canonical gauge companion to Remark 3.1.2.1. -/
-- Proof sketch: obtain absorbency from the interior-neighborhood hypothesis, then combine
-- `gauge_smul_of_nonneg` for degree-one positive homogeneity with `gauge_add_le` to build the
-- whole-space `ConvexOn` witness.
theorem gauge_posHom_and_convexOn_univ_of_convex_zero_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q) (hQ_zero : (0 : E) ∈ interior Q) :
    IsPositivelyHomogeneousOn 1 Set.univ (gauge Q) ∧
      ConvexOn ℝ Set.univ (gauge Q) := by
  have hQ_absorbent : Absorbent ℝ Q :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hQ_zero)
  constructor
  · refine {
      smul_mem := by
        intro x hx τ
        simp
      map_smul := by
        intro x hx τ
        rw [NNReal.smul_def, gauge_smul_of_nonneg (s := Q) (a := (τ : ℝ)) τ.2]
        have hτ : (τ : ℝ).rpow (1 : ℝ) = (τ : ℝ) := by
          exact Real.rpow_one (τ : ℝ)
        rw [hτ] }
    -- Positive homogeneity is exactly the canonical scaling law for the gauge.
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    -- The source proof's convex combination estimate becomes gauge subadditivity after scaling.
    have hineq :
        gauge Q (a • x + b • y) ≤ a * gauge Q x + b * gauge Q y := by
      calc
      gauge Q (a • x + b • y)
          ≤ gauge Q (a • x) + gauge Q (b • y) := gauge_add_le hQ_convex hQ_absorbent _ _
      _ = a * gauge Q x + b * gauge Q y := by
        rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul]
    simpa [smul_eq_mul] using hineq

/-- Remark 3.1.2.1: if `Q` is convex and contains `0` in its interior, then the everywhere-finite
real representative `withTopRealPart (ψ[Q])` of its Minkowski functional is positively homogeneous
of degree `1` and convex on all of the ambient real topological vector space. In the textbook
Euclidean bounded closed case, this is exactly the same Minkowski-functional conclusion. -/
-- Proof sketch: first use `(0 : E) ∈ interior Q` to identify `ψ[Q]` with the everywhere-finite
-- canonical gauge `gauge Q`, then transport degree-one positive homogeneity and whole-space
-- convexity from the canonical gauge owner API.
theorem minkowskiFunctional_posHom_and_convexOn_univ_of_convex_zero_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q) (hQ_zero : (0 : E) ∈ interior Q) :
    IsPositivelyHomogeneousOn 1 Set.univ (withTopRealPart (ψ[Q])) ∧
      ConvexOn ℝ Set.univ (withTopRealPart (ψ[Q])) := by
  -- Transport the canonical gauge properties through the everywhere-finite pointwise equality.
  have hEq : withTopRealPart (ψ[Q]) = gauge Q := by
    funext x
    have hx : x ∈ dom (ψ[Q]) := by
      simp [dom_minkowskiFunctional_eq_univ_of_zero_mem_interior hQ_zero]
    apply WithTop.coe_injective
    rw [coe_withTopRealPart hx, minkowskiFunctional_eq_gauge_of_zero_mem_interior hQ_zero]
  simpa [hEq] using
    gauge_posHom_and_convexOn_univ_of_convex_zero_mem_interior hQ_convex hQ_zero

/-! ### Remark_3_1_2_2 (from Chap03) -/
universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "Z" => WithLp 2 (E × ℝ)

open WithLp
open scoped ConvexAnalysis
open scoped SupportFunction

/- 
Remark 3.1.2.2 lies in the chapter's support-function / extended-real supremum domain.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`, the chapter's source-facing `EReal`-valued support
  supremum owner;
- `supportFunction_apply` from `Definition_3_9`, the defining evaluation formula for that owner;
- `supportFunction_convexHull_eq` from `Definition_3_9`, showing that the chapter owner is the
  ambient support-function abstraction rather than a coordinate-bound wrapper;
- `extendedRealEffectiveDomain` / notation `dom` from `Definition_3_1_1_2`, the chapter owner for
  finite-value domains of `EReal`-valued functions;
- the canonical `WithLp.toLp 2` transport, since mathlib's `L²` product owner lives on
  `WithLp 2 (E × ℝ)` rather than on the raw product.

Best owner abstraction:
- source-facing: the raw lifted set `quadraticSupportLift Q ⊆ E × ℝ`;
- core/canonical: the chapter owner `supportFunction`, applied to the canonical `L²` bridge
  `quadraticSupportLiftL2 Q ⊆ WithLp 2 (E × ℝ)`;
- bridge/view: `quadraticSupportLiftL2`, together with the defining evaluation formula and the
  whole-space `dom` description.

Primitive data:
- a set `Q : Set E`.

Derived API:
- `quadraticSupportLift Q`;
- its canonical `L²` bridge `quadraticSupportLiftL2 Q`;
- `supportFunction_quadraticSupportLift_apply`;
- the explicit whole-space value formula and its effective-domain corollaries.

The regularized supremum is not kept as a second root owner. Its intrinsic content is the chapter
support function of the canonical `L²` bridge of the lifted set
`{(y, -(‖y‖² / 2)) | y ∈ Q} ⊆ E × ℝ`. The raw product lift remains the source-facing object, while
the thin bridge `quadraticSupportLiftL2` is the ergonomics layer required because mathlib's
inner-product product owner lives on `WithLp 2 (E × ℝ)`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`.
-/

/-- The lifted set whose support function is the quadratically regularized support formula. -/
def quadraticSupportLift (Q : Set E) : Set (E × ℝ) :=
  (fun y : E ↦ (y, -(‖y‖ ^ 2) / 2)) '' Q

/-- The canonical `L²`-product view of `quadraticSupportLift Q`, where the support-function owner
acts. This is only the `WithLp.toLp 2` codomain bridge, not a second mathematical owner. -/
abbrev quadraticSupportLiftL2 (Q : Set E) : Set Z :=
  toLp 2 '' quadraticSupportLift Q

/-- Remark 3.1.2.2: the support function of the lifted set `quadraticSupportLift Q` sends
`(g, γ)` to the supremum over `y ∈ Q` of `⟪g, y⟫ - (γ / 2) ‖y‖²`, viewed in `EReal`. -/
theorem supportFunction_quadraticSupportLift_apply (Q : Set E) (g : E) (γ : ℝ) :
    ξ[quadraticSupportLiftL2 Q] (toLp 2 (g, γ)) =
      sSup
        ((fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' Q) := by
  -- Rewrite the support function on the lifted `L²` set as the image of the raw quadratic slice.
  rw [supportFunction_apply]
  have himage :
      (fun z : Z ↦ ((inner ℝ z (toLp 2 (g, γ)) : ℝ) : EReal)) '' quadraticSupportLiftL2 Q =
        (fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' Q := by
    ext a
    constructor
    · rintro ⟨z, ⟨w, ⟨y, hyQ, rfl⟩, rfl⟩, rfl⟩
      refine ⟨y, hyQ, ?_⟩
      simp only
      rw [WithLp.prod_inner_apply, real_inner_comm]
      congr
      norm_num [inner]
      ring
    · rintro ⟨y, hyQ, rfl⟩
      refine ⟨toLp 2 (y, -(‖y‖ ^ 2) / 2), ?_, ?_⟩
      · exact ⟨(y, -(‖y‖ ^ 2) / 2), ⟨y, hyQ, rfl⟩, rfl⟩
      · simp only
        rw [WithLp.prod_inner_apply, real_inner_comm]
        congr
        norm_num [inner]
        ring
  rw [himage]

/-- Helper for Remark 3.1.2.2: for `γ > 0`, the quadratic slice is obtained by completing the
square around the maximizer `γ⁻¹ • g`. -/
lemma quadratic_support_complete_square (g y : E) {γ : ℝ} (hγ : 0 < γ) :
    inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 =
      ‖g‖ ^ 2 / (2 * γ) - (γ / 2) * ‖y - γ⁻¹ • g‖ ^ 2 := by
  -- Expand the norm square and collect the linear and quadratic terms in `y`.
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  rw [norm_sub_sq_real]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ)]
  rw [real_inner_smul_right, real_inner_comm y g]
  field_simp [hγ0]
  ring

/-- The positive-parameter branch of the whole-space lifted support function equals
`‖g‖² / (2γ)`. In the textbook specialization `E = EuclideanSpace ℝ (Fin n)`, this remains valid
even in the degenerate case `n = 0`. -/
-- Proof sketch: maximize the concave quadratic at `y = g / γ`.
theorem supportFunction_quadraticSupportLift_univ_eq_of_pos (g : E) {γ : ℝ} (hγ : 0 < γ) :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 (g, γ)) =
      ((((‖g‖ ^ 2) / (2 * γ) : ℝ) : EReal)) := by
  -- Rewrite the whole-space support value as one `sSup` over the scalar quadratic slices.
  rw [supportFunction_quadraticSupportLift_apply]
  let S : Set EReal :=
    (fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' (Set.univ : Set E)
  change sSup S = ((((‖g‖ ^ 2) / (2 * γ) : ℝ) : EReal))
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    -- The completed-square form shows every slice lies below the peak value.
    simp only
    rw [quadratic_support_complete_square g y hγ]
    have hnonneg : 0 ≤ (γ / 2) * ‖y - γ⁻¹ • g‖ ^ 2 := by
      positivity
    exact_mod_cast sub_le_self _ hnonneg
  · intro w hw
    -- The candidate `y = γ⁻¹ • g` kills the square term and attains the upper bound.
    refine ⟨((‖g‖ ^ 2) / (2 * γ) : ℝ), ?_, ?_⟩
    · refine ⟨γ⁻¹ • g, Set.mem_univ _, ?_⟩
      simp only
      rw [quadratic_support_complete_square g (γ⁻¹ • g) hγ]
      simp
    · simpa using hw

/-- The whole-space lifted support function takes the value `0` at `(0, 0)`. -/
-- Proof sketch: every term in the defining supremum is `0`.
theorem supportFunction_quadraticSupportLift_univ_eq_zero :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 ((0 : E), (0 : ℝ))) =
      (0 : EReal) := by
  -- At `(0, 0)`, every slice value is exactly `0`, so the supremum is `0`.
  rw [supportFunction_quadraticSupportLift_apply]
  simp

/-- Helper for Remark 3.1.2.2: for `γ < 0`, every real threshold is exceeded by some quadratic
slice, so the whole-space supremum is unbounded above. -/
lemma quadratic_support_large_of_neg [Nontrivial E]
    (g : E) {γ : ℝ} (hγ : γ < 0) (R : ℝ) :
    ∃ y : E, R ≤ inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 := by
  -- Pick any nonzero ray and make the positive quadratic growth dominate the linear term.
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  let a : ℝ := -(γ / 2) * ‖u‖ ^ 2
  have ha : 0 < a := by
    have hneg : 0 < -(γ / 2) := by
      linarith
    have hu_sq : 0 < ‖u‖ ^ 2 := by
      have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
      nlinarith
    exact mul_pos hneg hu_sq
  let c : ℝ := inner ℝ g u
  let t : ℝ := max 1 ((|c| + |R| + 1) / a)
  refine ⟨t • u, ?_⟩
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht : 0 ≤ t := by
    linarith
  have hbound : |c| + |R| + 1 ≤ a * t := by
    have hquot : (|c| + |R| + 1) / a ≤ t := le_max_right _ _
    simpa [mul_comm] using (div_le_iff₀ ha).mp hquot
  have hc : -|c| ≤ c := neg_abs_le c
  have hstep1 : t * (-|c|) ≤ t * c := by
    exact mul_le_mul_of_nonneg_left hc ht
  have hstep2 : |R| + 1 ≤ a * t - |c| := by
    nlinarith
  have hnonneg : 0 ≤ a * t - |c| := by
    have : 0 ≤ |R| + 1 := by
      positivity
    linarith
  have hstep3 : a * t - |c| ≤ t * (a * t - |c|) := by
    nlinarith
  have hstep4 : t * (a * t - |c|) ≤ t * c + a * t ^ 2 := by
    nlinarith
  have hR : R ≤ |R| + 1 := by
    have hRabs : R ≤ |R| := le_abs_self R
    linarith
  have hexpr : inner ℝ g (t • u) - (γ / 2) * ‖t • u‖ ^ 2 = t * c + a * t ^ 2 := by
    simp [c, a, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    ring
  linarith [hR, hstep1, hstep2, hstep3, hstep4, hexpr]

/-- On a nontrivial real inner-product space, the negative-parameter branch of the whole-space
lifted support function is unbounded above. -/
-- Proof sketch: choose any nonzero vector and scale it to infinity, so the quadratic term
-- dominates with positive sign.
theorem supportFunction_quadraticSupportLift_univ_eq_top_of_neg [Nontrivial E]
    (g : E) {γ : ℝ} (hγ : γ < 0) :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 (g, γ)) =
      ⊤ := by
  -- Rewrite to the scalar supremum and contradict any assumption of a finite upper bound.
  rw [supportFunction_quadraticSupportLift_apply]
  let S : Set EReal :=
    (fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' (Set.univ : Set E)
  change sSup S = ⊤
  by_contra htop
  have hslt : sSup S < ⊤ := lt_top_iff_ne_top.mpr htop
  rcases quadratic_support_large_of_neg g hγ ((sSup S).toReal + 1) with ⟨y, hy⟩
  have hy' : ((((sSup S).toReal + 1 : ℝ) : EReal)) ≤
      ((inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hy
  have hsbot : sSup S ≠ ⊥ := by
    -- The slice at `y = 0` already shows that the supremum is not `⊥`.
    intro hsbot
    have hzero_mem : (0 : EReal) ≤ sSup S := by
      apply le_sSup
      refine ⟨0, Set.mem_univ _, ?_⟩
      simp
    simp [hsbot] at hzero_mem
  have hlt : sSup S < ((((sSup S).toReal + 1 : ℝ) : EReal)) := by
    rw [← EReal.coe_toReal hslt.ne hsbot]
    exact_mod_cast (show (sSup S).toReal < (sSup S).toReal + 1 by linarith)
  have hmem : ((inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal) ≤ sSup S := by
    apply le_sSup
    exact ⟨y, Set.mem_univ _, rfl⟩
  exact not_lt_of_ge (le_trans hy' hmem) hlt

/-- Helper for Remark 3.1.2.2: if `g ≠ 0`, then the linear slice `y ↦ ⟪g, y⟫` exceeds every real
threshold along the ray generated by `g`. -/
lemma quadratic_support_large_of_zero_ne_zero {g : E} (hg : g ≠ 0) (R : ℝ) :
    ∃ y : E, R ≤ inner ℝ g y := by
  -- Scale `g` so that the value becomes `R + |R| + 1`, which is strictly above `R`.
  have hg_sq : 0 < ‖g‖ ^ 2 := by
    have hg_norm : 0 < ‖g‖ := norm_pos_iff.mpr hg
    nlinarith
  let t : ℝ := (R + |R| + 1) / (‖g‖ ^ 2)
  refine ⟨t • g, ?_⟩
  have ht_eval : inner ℝ g (t • g) = R + |R| + 1 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp [t]
    field_simp [ne_of_gt hg_sq]
  have hR : R ≤ R + |R| + 1 := by
    have hRabs : 0 ≤ |R| := abs_nonneg R
    linarith
  linarith [ht_eval, hR]

/-- For a nonzero vector `g`, the zero-parameter branch of the whole-space lifted support
function is unbounded above. -/
-- Proof sketch: with `γ = 0`, the defining supremum is the support function of the whole space,
-- which is unbounded above when `g ≠ 0`.
theorem supportFunction_quadraticSupportLift_univ_eq_top_of_zero_ne_zero {g : E} (hg : g ≠ 0) :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 (g, 0)) =
      ⊤ := by
  -- Route correction: this branch is purely linear, so use the ray generated by `g` itself.
  rw [supportFunction_quadraticSupportLift_apply]
  simp only [zero_div, zero_mul, sub_zero]
  let S : Set EReal := (fun y : E ↦ ((inner ℝ g y : ℝ) : EReal)) '' (Set.univ : Set E)
  change sSup S = ⊤
  by_contra htop
  have hslt : sSup S < ⊤ := lt_top_iff_ne_top.mpr htop
  rcases quadratic_support_large_of_zero_ne_zero hg ((sSup S).toReal + 1) with ⟨y, hy⟩
  have hy' : ((((sSup S).toReal + 1 : ℝ) : EReal)) ≤ ((inner ℝ g y : ℝ) : EReal) := by
    exact_mod_cast hy
  have hsbot : sSup S ≠ ⊥ := by
    -- The point `y = 0` contributes the finite value `0`.
    intro hsbot
    have hzero_mem : (0 : EReal) ≤ sSup S := by
      apply le_sSup
      refine ⟨0, Set.mem_univ _, ?_⟩
      simp
    simp [hsbot] at hzero_mem
  have hlt : sSup S < ((((sSup S).toReal + 1 : ℝ) : EReal)) := by
    rw [← EReal.coe_toReal hslt.ne hsbot]
    exact_mod_cast (show (sSup S).toReal < (sSup S).toReal + 1 by linarith)
  have hmem : ((inner ℝ g y : ℝ) : EReal) ≤ sSup S := by
    apply le_sSup
    exact ⟨y, Set.mem_univ _, rfl⟩
  exact not_lt_of_ge (le_trans hy' hmem) hlt

/-- On a nontrivial real inner-product space, the finite-value domain `dom` of the whole-space
lifted support function is exactly `(E × {γ > 0}) ∪ {(0, 0)}` in the raw `(g, γ)` coordinates. -/
-- Proof sketch: use the four whole-space value formulas above; under nontriviality the
-- displayed values are
-- always finite reals or `⊤`, never `⊥`, so `dom` excludes exactly the `⊤` branch.
theorem supportFunction_quadraticSupportLift_univ_dom [Nontrivial E] :
    toLp 2 ⁻¹' dom ξ[quadraticSupportLiftL2 (Set.univ : Set E)] =
      {p : E × ℝ | 0 < p.2 ∨ (p.1 = 0 ∧ p.2 = 0)} := by
  -- Split the raw coordinates by the sign of `γ` and invoke the branch formulas above.
  ext p
  rcases p with ⟨g, γ⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro hp
    rcases hp with ⟨hp_top, _⟩
    by_cases hγpos : 0 < γ
    · exact Or.inl hγpos
    · have hγle : γ ≤ 0 := le_of_not_gt hγpos
      by_cases hγzero : γ = 0
      · right
        constructor
        · by_contra hg
          exact hp_top (by
            simpa [hγzero] using
              supportFunction_quadraticSupportLift_univ_eq_top_of_zero_ne_zero hg)
        · exact hγzero
      · have hγneg : γ < 0 := lt_of_le_of_ne hγle hγzero
        exact False.elim (hp_top (supportFunction_quadraticSupportLift_univ_eq_top_of_neg g hγneg))
  · intro hp
    rcases hp with hγpos | ⟨hg0, hγ0⟩
    · constructor
      · rw [supportFunction_quadraticSupportLift_univ_eq_of_pos g hγpos]
        exact EReal.coe_ne_top _
      · rw [supportFunction_quadraticSupportLift_univ_eq_of_pos g hγpos]
        exact EReal.coe_ne_bot _
    · subst hg0
      subst hγ0
      constructor
      · rw [supportFunction_quadraticSupportLift_univ_eq_zero]
        norm_num
      · rw [supportFunction_quadraticSupportLift_univ_eq_zero]
        norm_num

/-- On a nontrivial real inner-product space, the whole-space lifted support function lies in
`dom` at `(g, γ)` exactly when `γ > 0` or `(g, γ) = (0, 0)`. -/
theorem supportFunction_quadraticSupportLift_univ_mem_dom_iff [Nontrivial E] (g : E) (γ : ℝ) :
    toLp 2 (g, γ) ∈ dom ξ[quadraticSupportLiftL2 (Set.univ : Set E)] ↔
      0 < γ ∨ (g = 0 ∧ γ = 0) := by
  -- This is the pointwise restatement of the raw-coordinate domain equality.
  change (g, γ) ∈ toLp 2 ⁻¹' dom ξ[quadraticSupportLiftL2 (Set.univ : Set E)] ↔
    0 < γ ∨ (g = 0 ∧ γ = 0)
  rw [supportFunction_quadraticSupportLift_univ_dom]
  rfl

end

/-! ### Remark_3_1_2_3 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

local notation "P" => ℝ × E

/- Remark 3.1.2.3 lies in the convex-perspective / positive-homogeneity domain.

Sampled owner-style declarations:
- mathlib `ConvexCone`
- mathlib `ConvexOn`
- project `IsPositivelyHomogeneousOn`

Best owner abstraction:
- source-facing data: `perspectiveCone` and `perspectiveTransform`
- core/canonical owner for the domain: `ConvexCone ℝ (ℝ × E)`
- canonical owner predicates on that data: `ConvexOn` and `IsPositivelyHomogeneousOn`

Primitive data:
- a real `ℝ`-module `E`
- the cone owner `perspectiveCone E : ConvexCone ℝ (ℝ × E)`
- the transform `perspectiveTransform : (E → ℝ) → P → ℝ`

Derived API:
- `mem_perspectiveCone_iff`
- `perspectiveTransform_apply_of_pos`
- `perspectiveTransform_zero`
- the positive-homogeneity and convexity theorems for the perspective transform

Source/core/bridge triage:
- source-facing: `perspectiveCone`, `perspectiveTransform`
- core/canonical: `ConvexCone`, `ConvexOn`, `IsPositivelyHomogeneousOn`
- bridge/view: the small membership and evaluation lemmas relating the source-facing construction
  to those owner predicates

There is no upstream perspective-transform owner in the chapter or in mathlib, so this file keeps
the source-facing construction itself. The domain, however, is genuinely a convex cone, so the
refined file uses the canonical cone owner instead of a parallel bare-set definition.
-/

/-- The cone consisting of pairs `(τ, x)` with `τ > 0`, together with the origin. -/
def perspectiveCone (E : Type u) [AddCommMonoid E] [Module ℝ E] : ConvexCone ℝ (ℝ × E) where
  carrier := {z : ℝ × E | 0 < z.1 ∨ z = 0}
  smul_mem' := fun c hc z hz ↦ by
    rcases hz with hz | rfl
    · left
      change 0 < c * z.1
      simpa [smul_eq_mul] using mul_pos hc hz
    · right
      simp
  add_mem' := fun x hx y hy ↦ by
    rcases hx with hx | rfl
    · rcases hy with hy | rfl
      · left
        change 0 < x.1 + y.1
        exact add_pos hx hy
      · left
        simpa using hx
    · simpa using hy

/-- Membership in `perspectiveCone` means either strictly positive first coordinate or the
point is the origin. -/
@[simp]
theorem mem_perspectiveCone_iff
    {z : P} :
    z ∈ perspectiveCone E ↔ 0 < z.1 ∨ z = 0 :=
  Iff.rfl

/-- The perspective transform of a function `f : E → ℝ`, extended by the value `0` away from the
region `τ > 0`. On `perspectiveCone`, this agrees with the usual formula
`(τ, x) ↦ τ f (τ⁻¹ • x)` together with the value `0` at the origin. In the textbook case
`E = ℝⁿ`, this is the usual perspective transform. -/
def perspectiveTransform
    (f : E → ℝ) :
    P → ℝ :=
  fun z ↦
    if _ : 0 < z.1 then
      z.1 * f (z.1⁻¹ • z.2)
    else
      0

/-- On pairs with positive first coordinate, `perspectiveTransform f` is given by the usual
perspective formula. -/
theorem perspectiveTransform_apply_of_pos
    (f : E → ℝ)
    {z : P} (hz : 0 < z.1) :
    perspectiveTransform f z = z.1 * f (z.1⁻¹ • z.2) := by
  simp [perspectiveTransform, hz]

/-- At the origin, `perspectiveTransform f` takes the prescribed value `0`. -/
@[simp] theorem perspectiveTransform_zero
    (f : E → ℝ) :
    perspectiveTransform f 0 = 0 := by
  simp [perspectiveTransform]

/-- Helper for Remark 3.1.2.3: a point of `perspectiveCone` with nonpositive first coordinate is
the origin. -/
theorem eq_zero_of_mem_perspectiveCone_of_not_pos
    {z : P} (hz : z ∈ perspectiveCone E) (hzpos : ¬ 0 < z.1) :
    z = 0 := by
  -- A cone point is either strictly positive in the first coordinate or already the origin.
  rcases mem_perspectiveCone_iff.mp hz with hz' | hz'
  · exact (hzpos hz').elim
  · exact hz'

/-- Helper for Remark 3.1.2.3: the normalized perspective weights are nonnegative and sum to
`1`. -/
theorem perspective_weights_nonneg_sum_one
    {a b τ₁ τ₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    0 < a * τ₁ + b * τ₂ ∧
      0 ≤ a * τ₁ / (a * τ₁ + b * τ₂) ∧
      0 ≤ b * τ₂ / (a * τ₁ + b * τ₂) ∧
      a * τ₁ / (a * τ₁ + b * τ₂) + b * τ₂ / (a * τ₁ + b * τ₂) = 1 := by
  -- One coefficient is positive because `a + b = 1`; the corresponding term makes the sum
  -- strictly positive.
  have hτ : 0 < a * τ₁ + b * τ₂ := by
    have hab_pos : 0 < a ∨ 0 < b := by
      by_cases ha0 : a = 0
      · right
        nlinarith [hb, hab]
      · left
        exact lt_of_le_of_ne ha fun h => ha0 h.symm
    rcases hab_pos with ha_pos | hb_pos
    · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hτ₁) (mul_nonneg hb hτ₂.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hτ₁.le) (mul_pos hb_pos hτ₂)
  refine ⟨hτ, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg ha hτ₁.le) hτ.le
  · exact div_nonneg (mul_nonneg hb hτ₂.le) hτ.le
  · -- After combining the fractions, the numerator is exactly the denominator.
    rw [← add_div]
    field_simp [hτ.ne']

/-- Helper for Remark 3.1.2.3: the normalized point of the convex combination is the same convex
combination of the normalized points. -/
theorem perspective_normalized_combination_eq
    {a b τ₁ τ₂ : ℝ} {x₁ x₂ : E}
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    (a * τ₁ + b * τ₂)⁻¹ • (a • x₁ + b • x₂) =
      (a * τ₁ / (a * τ₁ + b * τ₂)) • (τ₁⁻¹ • x₁) +
        (b * τ₂ / (a * τ₁ + b * τ₂)) • (τ₂⁻¹ • x₂) := by
  -- Distribute the outer normalization, then match the scalar coefficients term by term.
  rw [smul_add, smul_smul, smul_smul]
  rw [smul_smul, smul_smul]
  congr 1 <;> rw [div_eq_mul_inv] <;> field_simp [hτ₁.ne', hτ₂.ne']

/-- The perspective transform is positively homogeneous of degree `1` on `perspectiveCone` for
every `f : E → ℝ`. In the textbook case `E = ℝⁿ`, this is exactly the same perspective
homogeneity statement. -/
theorem perspectiveTransform_isPositivelyHomogeneousOn
    {f : E → ℝ} :
    IsPositivelyHomogeneousOn 1 (perspectiveCone E) (perspectiveTransform f) := by
  refine ⟨?_, ?_⟩
  · intro x hx τ
    by_cases hτ : τ = 0
    · -- Zero scaling sends every point to the origin, which lies in the cone.
      rw [hτ]
      simp [mem_perspectiveCone_iff]
    · -- Positive scaling preserves positivity of the first coordinate.
      have hτ_pos : 0 < (τ : ℝ) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hτ)
      rcases mem_perspectiveCone_iff.mp hx with hx_pos | hx_zero
      · refine mem_perspectiveCone_iff.mpr (Or.inl ?_)
        change 0 < (τ : ℝ) * x.1
        simpa using mul_pos hτ_pos hx_pos
      · refine mem_perspectiveCone_iff.mpr (Or.inr ?_)
        subst hx_zero
        simp
  · intro x hx τ
    by_cases hτ : τ = 0
    · -- The `τ = 0` branch is exactly the prescribed value at the origin.
      simp [hτ, perspectiveTransform_zero, Real.rpow_one]
    · have hτ_pos : 0 < (τ : ℝ) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hτ)
      by_cases hx_pos : 0 < x.1
      · -- In the positive branch, expand the perspective formula and cancel the extra scalar.
        have hsmul_pos : 0 < (τ • x : P).1 := by
          change 0 < (τ : ℝ) * x.1
          simpa using mul_pos hτ_pos hx_pos
        have hmul_ne : (τ : ℝ) * x.1 ≠ 0 := by
          exact mul_ne_zero (show (τ : ℝ) ≠ 0 from by exact_mod_cast hτ) hx_pos.ne'
        have hcancel :
            (((τ : ℝ) * x.1)⁻¹ : ℝ) * (τ : ℝ) = x.1⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul₀ hmul_ne]
          rw [mul_assoc, mul_inv_cancel₀ hx_pos.ne', mul_one]
        calc
          perspectiveTransform f (τ • x)
              = (τ • x).1 * f (((τ • x).1)⁻¹ • (τ • x).2) :=
                  perspectiveTransform_apply_of_pos f hsmul_pos
          _ = ((τ : ℝ) * x.1) * f ((((τ : ℝ) * x.1)⁻¹ : ℝ) • ((τ : ℝ) • x.2)) := by
                rfl
          _ = ((τ : ℝ) * x.1) * f (x.1⁻¹ • x.2) := by
                rw [show ((((τ : ℝ) * x.1)⁻¹ : ℝ) • ((τ : ℝ) • x.2)) =
                    x.1⁻¹ • x.2 by
                    rw [smul_smul, hcancel]]
          _ = (τ : ℝ) * (x.1 * f (x.1⁻¹ • x.2)) := by ring
          _ = Real.rpow (τ : ℝ) 1 • perspectiveTransform f x := by
                rw [perspectiveTransform_apply_of_pos f hx_pos]
                simp [Real.rpow_one, smul_eq_mul]
      · -- A nonpositive cone point is the origin, so both sides vanish.
        have hx_zero : x = 0 := eq_zero_of_mem_perspectiveCone_of_not_pos hx hx_pos
        subst hx_zero
        simp [perspectiveTransform_zero, Real.rpow_one]

/-- If `f` is convex on `E`, then its perspective transform is convex on `perspectiveCone`. In
the textbook case `E = ℝⁿ`, this is exactly the same perspective-convexity statement. -/
theorem perspectiveTransform_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ (perspectiveCone E) (perspectiveTransform f) := by
  refine ⟨(perspectiveCone E).convex, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases hx_pos : 0 < x.1
  · by_cases hy_pos : 0 < y.1
    · -- Route correction: keep the source proof's normalized-weight argument on the strictly
      -- positive branch instead of switching to an ad hoc concrete recursion.
      have hweights := perspective_weights_nonneg_sum_one ha hb hab hx_pos hy_pos
      rcases hweights with ⟨hτ_pos, hw₁_nonneg, hw₂_nonneg, hw_sum⟩
      set τ : ℝ := a * x.1 + b * y.1
      have hτ_pos' : 0 < τ := by simpa [τ] using hτ_pos
      have hjensen :
          f (τ⁻¹ • (a • x.2 + b • y.2)) ≤
            (a * x.1 / τ) * f (x.1⁻¹ • x.2) +
              (b * y.1 / τ) * f (y.1⁻¹ • y.2) := by
        -- Apply convexity of `f` to the normalized points with the normalized perspective weights.
        simpa [τ, smul_eq_mul, perspective_normalized_combination_eq hx_pos hy_pos] using
          hf.2 (by simp : x.1⁻¹ • x.2 ∈ Set.univ) (by simp : y.1⁻¹ • y.2 ∈ Set.univ)
            hw₁_nonneg hw₂_nonneg hw_sum
      have hscaled := mul_le_mul_of_nonneg_left hjensen hτ_pos'.le
      have hcomb_pos : 0 < (a • x + b • y : P).1 := by
        change 0 < a * x.1 + b * y.1
        simpa [τ] using hτ_pos'
      calc
        perspectiveTransform f (a • x + b • y)
            = τ * f (τ⁻¹ • (a • x.2 + b • y.2)) := by
                -- Expanding the perspective transform on the positive combined first coordinate
                -- recovers the normalized source-proof expression.
                simpa [τ] using perspectiveTransform_apply_of_pos f hcomb_pos
        _ ≤ τ *
              ((a * x.1 / τ) * f (x.1⁻¹ • x.2) +
                (b * y.1 / τ) * f (y.1⁻¹ • y.2)) := hscaled
        _ = a * perspectiveTransform f x + b * perspectiveTransform f y := by
              rw [perspectiveTransform_apply_of_pos f hx_pos, perspectiveTransform_apply_of_pos f hy_pos]
              field_simp [hτ_pos'.ne']
        _ = a • perspectiveTransform f x + b • perspectiveTransform f y := by
              simp [smul_eq_mul]
    · -- If `y` is not positive, membership forces `y = 0`, so homogeneity handles the branch.
      have hy_zero : y = 0 := eq_zero_of_mem_perspectiveCone_of_not_pos hy hy_pos
      subst hy_zero
      have hmap :=
        (perspectiveTransform_isPositivelyHomogeneousOn (f := f)).map_smul hx
          ⟨a, ha⟩
      exact le_of_eq <| by
        simpa [Real.rpow_one, smul_eq_mul, perspectiveTransform_zero, hab] using hmap
  · -- If `x` is not positive, membership forces `x = 0`, and we reduce to the other branch.
    have hx_zero : x = 0 := eq_zero_of_mem_perspectiveCone_of_not_pos hx hx_pos
    subst hx_zero
    have hmap :=
      (perspectiveTransform_isPositivelyHomogeneousOn (f := f)).map_smul hy
        ⟨b, hb⟩
    exact le_of_eq <| by
      simpa [Real.rpow_one, smul_eq_mul, perspectiveTransform_zero, hab, add_comm] using hmap

/-- Remark 3.1.2.3: if `f` is convex on `E`, then its perspective transform
`(τ, x) ↦ τ f (τ⁻¹ • x)` is positively homogeneous on the cone `τ > 0` together with the origin,
and it is convex on that same domain. For the source statement, take `E = ℝⁿ`. -/
-- Proof sketch: for positive homogeneity, expand the definition and rewrite
-- `(c * τ)⁻¹ • (c • x) = τ⁻¹ • x` for `c ≥ 0`; the case `c = 0` reduces to the value at the
-- origin. For convexity, apply convexity of `f` to the normalized points
-- `x₁ / τ₁` and `x₂ / τ₂` with weights proportional to `τ₁` and `τ₂`.
theorem perspectiveTransform_posHomogeneous_and_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    IsPositivelyHomogeneousOn 1 (perspectiveCone E) (perspectiveTransform f) ∧
      ConvexOn ℝ (perspectiveCone E) (perspectiveTransform f) := by
  exact ⟨perspectiveTransform_isPositivelyHomogeneousOn, perspectiveTransform_convexOn hf⟩

end

/-! ### Theorem_3_1_2 (from Chap03) -/
/- Theorem 3.1.2 is recall-only in the real convex-analysis / epigraph domain.

Primary domain:
- convexity of the epigraph of a real-valued function on a convexity domain, with the textbook
  specialization `s ⊆ ℝⁿ`.

Sampled owner-style declarations:
- mathlib `ConvexOn`;
- mathlib `ConvexOn.convex_epigraph`;
- mathlib `convexOn_iff_convex_epigraph`;
- the chapter bridge `convexOn_iff_convex_effective_epigraph` in `Theorem_3_3`, which handles the
  `WithTop ℝ`-valued effective-epigraph variant by reducing to the same owner theorem.

Best owner abstraction:
- `convexOn_iff_convex_epigraph`.

Primitive data:
- a scalar type `𝕜`, ambient module `E`, and codomain ordered additive module `β` in the owner
  theorem;
- in the textbook specialization, `𝕜 = ℝ`, `E = EuclideanSpace ℝ (Fin n)`, and `β = ℝ`.

Derived API:
- convexity of the epigraph `{p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}`;
- the one-direction owner theorem `ConvexOn.convex_epigraph`.

Source/core/bridge triage:
- source-facing: the Euclidean textbook epigraph characterization of convexity;
- core/canonical: mathlib `convexOn_iff_convex_epigraph`;
- bridge/view: the Euclidean specialization recorded below.

The previous declaration `convexOn_iff_convex_epigraph_euclidean` was an exact-interface duplicate
of the mathlib owner theorem. This file therefore recalls the canonical owner directly instead of
keeping a second public theorem name for the same mathematics; the textbook Euclidean statement is
its immediate specialization.
-/

recall convexOn_iff_convex_epigraph

/-! ### Theorem_3_1_2_1 (from Chap03) -/
noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Theorem 3.1.2.1 is recall-only in the chapter's `ClosedConvexOn` owner API.

Primary domain:
- closure properties of closed convex `WithTop ℝ`-valued functions on a feasible set in a real
  topological module.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.nonneg_smul` from `Theorem_3_1_5`
- `ClosedConvexOn.add_inter` from `Theorem_3_1_5`
- `ClosedConvexOn.max_inter` from `Theorem_3_1_5`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witnesses `hf`, `hf₁`, `hf₂`
- the nonnegative scalar `β`

Derived API:
- `ClosedConvexOn.nonneg_smul`
- `ClosedConvexOn.add_inter`
- `ClosedConvexOn.max_inter`

Source/core/bridge triage:
- source-facing: the three closure properties recorded under Theorem 3.1.2.1
- core/canonical: the owner namespace `ClosedConvexOn`
- bridge/view: this later numbered file, which now directly recalls the owner theorems instead of
  introducing parallel aliases `smul_nonneg`, `add`, and `max`

The earlier file `Theorem_3_1_5` already owns these exact closure operations with the chapter's
canonical names. This file therefore reuses those owner entries directly rather than keeping a
second public vocabulary for the same mathematics.
-/

recall ClosedConvexOn.nonneg_smul
    {Q : Set X} {f : X → WithTop ℝ} {β : ℝ}
    (hf : ClosedConvexOn Q f) (hβ : 0 ≤ β) :
    ClosedConvexOn Q ((β : WithTop ℝ) • f)

recall ClosedConvexOn.add_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ + f₂)

recall ClosedConvexOn.max_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ ⊔ f₂)

end

/-! ### Theorem_3_1_2_2 (from Chap03) -/
noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Theorem 3.1.2.2 belongs to the chapter's closed-convex affine-pullback calculus.

Primary domain:
- closed convex `WithTop ℝ`-valued functions and affine preimages of constrained epigraphs on real
  topological modules.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- `ClosedConvexOn.convex_constrainedEpigraph`
- mathlib `ContinuousAffineMap`
- mathlib `ConvexOn.comp_affineMap`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witness `hφ : ClosedConvexOn S φ`
- the continuous affine map `g : X →ᴬ[ℝ] Y`

Derived API:
- the owner pullback theorem `ClosedConvexOn.comp_continuousAffineMap`
- the Euclidean specialization `ClosedConvexOn.comp_affineMap`
- the epigraph-preimage bridge used in the proof

Source/core/bridge triage:
- source-facing: the theorem asserting closed convexity of the affine pullback on `g ⁻¹' S`
- core/canonical: `ClosedConvexOn`
- bridge/view: the constrained-epigraph preimage under
  `g.prodMap (ContinuousAffineMap.id ℝ ℝ)`, together with the Euclidean specialization from
  affine maps to continuous affine maps

The public owner theorem therefore lives directly in the `ClosedConvexOn` namespace at the
continuous-affine-map level. The textbook `ℝⁿ` affine-map statement remains as a thin
finite-dimensional specialization, while the epigraph preimage argument stays internal to the
proof rather than becoming a parallel wrapper declaration.
-/

namespace ClosedConvexOn

section ContinuousAffineMap

variable {X Y : Type*}
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
variable {S : Set Y} {φ : Y → WithTop ℝ}

/-- Closed convexity is preserved by precomposition with a continuous affine map. This is the
canonical owner-level pullback theorem; Euclidean affine-map statements should be derived from it.
-/
-- Proof sketch: identify the constrained epigraph of the pullback with the preimage of
-- `constrainedEpigraph S φ` under the affine map `(x, t) ↦ (g x, t)`. Closedness follows from
-- continuity of this map, and convexity follows from preservation of convexity under affine
-- preimages.
theorem comp_continuousAffineMap
    (hφ : ClosedConvexOn S φ) (g : X →ᴬ[ℝ] Y) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g) := by
  let G : X × ℝ →ᴬ[ℝ] Y × ℝ := g.prodMap (ContinuousAffineMap.id ℝ ℝ)
  have hpreimage :
      constrainedEpigraph (g ⁻¹' S) (φ ∘ g) =
        G ⁻¹' constrainedEpigraph S φ := by
    ext p
    simp [G, constrainedEpigraph]
  refine ⟨fun x hx ↦ hφ.subset_withTopEffectiveDomain hx, ?_, ?_⟩
  · rw [hpreimage]
    exact hφ.isClosed_constrainedEpigraph.preimage G.continuous
  · have hconv : Convex ℝ (G ⁻¹' constrainedEpigraph S φ) := by
      simpa using hφ.convex_constrainedEpigraph.affine_preimage G.toAffineMap
    simpa [hpreimage] using hconv

end ContinuousAffineMap

section AffineMap

/-- Theorem 3.1.2.2: if `φ` is closed and convex on `S ⊆ ℝᵐ` and `g : ℝⁿ → ℝᵐ` is affine, then
the pullback `x ↦ φ (g x)` is closed and convex on the affine preimage `{x | g x ∈ S}`. This is
the finite-dimensional specialization of `ClosedConvexOn.comp_continuousAffineMap`. -/
theorem comp_affineMap
    {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin m))}
    {φ : EuclideanSpace ℝ (Fin m) → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g) :=
  comp_continuousAffineMap hφ ⟨g, g.continuous_of_finiteDimensional⟩

end AffineMap

end ClosedConvexOn

end

/-! ### Theorem_3_1_2_3 (from Chap03) -/
noncomputable section

universe u v

open scoped ConvexAnalysis

variable {X : Type u} {Y : Type v}

/- Theorem 3.1.2.3 lies in the chapter's convex-analysis / infimal-projection domain.

Sampled owner-style declarations:
- chapter `extendedRealEffectiveDomain` / notation `dom` in `Definition_3_1_1_2`
- chapter `extendedRealRealPart` and `coe_extendedRealRealPart` in `Definition_3_1_1_3`
- mathlib `ConvexOn`
- mathlib `sInf`

Best owner abstraction:
- source-facing owner: the constrained `EReal`-valued fiberwise infimum `partialInfProjection`
- core/canonical convexity owner:
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)` for
  `ψ = partialInfProjection Q (Real.toEReal ∘ φ)`

Primitive data:
- a feasible set `Q : Set (X × Y)`
- an extended-real objective `φ : X × Y → EReal`

Derived API:
- the source-facing constrained infimum `partialInfProjection Q φ`
- the displayed fiber-value specification theorem `partialInfProjection_eq_sInf`
- the finite-value bridge
  `extendedRealRealPart_partialInfProjection_eq_sInf`

Source/core/bridge triage:
- source-facing: the constrained fiberwise infimum over `Q`
- core/canonical: the chapter `EReal` convexity owner
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)`
- bridge/view: the finite-value real surface
  `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ))`

A `WithTop ℝ`-valued owner would not faithfully represent unbounded-below fibers, so this file
keeps the constrained source-facing owner directly in `EReal` and then uses the chapter's
canonical `EReal` convexity bridge on its finite-value domain.
-/

/-- The constrained partial infimum of `φ` over the fiber of `Q` above `x`, recorded in `EReal`
so that unbounded-below fibers are represented faithfully by `⊥`. -/
def partialInfProjection (Q : Set (X × Y)) (φ : X × Y → EReal) : X → EReal :=
  fun x ↦ sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x})

/-- Evaluating the constrained partial infimum gives the infimum of the `φ`-values attained on
the feasible fiber above `x`. -/
@[simp] theorem partialInfProjection_eq_sInf
    {Q : Set (X × Y)} {φ : X × Y → EReal} {x : X} :
    partialInfProjection Q φ x =
      sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) :=
  rfl

/-- At a point where the constrained partial infimum is finite, its canonical real part agrees
with the textbook infimum of the real fiber values. -/
theorem extendedRealRealPart_partialInfProjection_eq_sInf
    {Q : Set (X × Y)} {φ : X × Y → ℝ} {x : X}
    (hx : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ))) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ)) x =
      sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) := sorry

section RealConvex

variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

/-- Theorem 3.1.2.3: if `Q ⊆ X × Y` is convex and `φ : X × Y → ℝ` is convex on `Q`, then the
constrained partial infimum is convex in the chapter's `EReal` sense: its finite real part is
convex on its finite-value domain. The companion theorem
`extendedRealRealPart_partialInfProjection_eq_sInf` identifies that finite real part with the
textbook fiberwise real infimum wherever the partial infimum is finite. -/
theorem partialInfProjection_convexOn
    {Q : Set (X × Y)} {φ : X × Y → ℝ}
    (hQ : Convex ℝ Q) (hφ : ConvexOn ℝ Q φ) :
    ConvexOn ℝ (dom (partialInfProjection Q (Real.toEReal ∘ φ)))
      (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ))) := sorry

end RealConvex

end

/-! ### Theorem_3_1_2_4 (from Chap03) -/
noncomputable section

universe u v

open scoped WithTopConvexAnalysis

variable {ι : Type u} {X : Type v}

/- Theorem 3.1.2.4 is a recall-only `Set.univ` specialization in the chapter's closed-convex
pointwise-supremum domain.

Relevant sampled declarations in this domain:
- `pointwiseSupremumOn` in `Theorem_3_1_8`, the source-facing owner for subset-indexed pointwise
  suprema of `WithTop ℝ`-valued families;
- `pointwiseSupremumOnEffectiveDomain` in `Theorem_3_1_8`, the canonical effective-domain bridge
  for that owner;
- `ClosedConvexOn` in `Definition_3_1_1_5`, the chapter owner predicate for closed convexity on a
  feasible set;
- `ClosedConvexOn.pointwise_sSup` in `Theorem_3_1_8`, the owner theorem for closed-convex
  stability under subset-indexed pointwise suprema.

Best owner abstraction:
- core/canonical owner: `ClosedConvexOn.pointwise_sSup` on
  `pointwiseSupremumOn Δ φ`;
- bridge/view: the `Δ = Set.univ` specialization used in this numbered textbook item.

Primitive data:
- none in this file; the pointwise-supremum owner and its effective-domain bridge already live
  upstream.

Derived API:
- this recall-only `Set.univ` specialization.

Source/core/bridge triage:
- source-facing: Theorem 3.1.2.4 as the all-indices specialization of the pointwise-supremum
  closed-convexity theorem;
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`, and
  `ClosedConvexOn.pointwise_sSup`;
- bridge/view: the passage from an arbitrary subset `Δ` to `Set.univ`.

The previous file introduced a second theorem name `ClosedConvexOn.pointwise_iSup` for this
specialization. The owner theorem already exists upstream on the correct abstraction layer, so this
file is now recall-only and keeps no parallel local theorem copy.
-/

section

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] [Nonempty ι]
variable {Q : Set X} {φ : X → ι → WithTop ℝ}

/- Theorem 3.1.2.4: for a nonempty index type, if each slice `x ↦ φ x y` is closed and convex on
`Q`, then the pointwise supremum over all indices is closed and convex on its canonical effective
domain. -/
#check
  (show (∀ y : ι, ClosedConvexOn Q (fun x ↦ φ x y)) →
      ClosedConvexOn (pointwiseSupremumOnEffectiveDomain Q (Set.univ : Set ι) φ)
        (pointwiseSupremumOn (Set.univ : Set ι) φ) from
    fun hφ ↦ by
      let ⟨i⟩ := ‹Nonempty ι›
      exact ClosedConvexOn.pointwise_sSup ⟨i, by simp⟩ (fun y _ ↦ hφ y))

end

end
