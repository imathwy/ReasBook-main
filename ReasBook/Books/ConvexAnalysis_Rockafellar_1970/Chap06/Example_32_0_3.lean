import ConvexAnalysis_Rockafellar_1970.Chap06.Example_32_0_2

noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Example 32.0.3 keeps the same source objective `f` from Example 32.0.2 and
  changes only the feasible set to
  `D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}`, asserting that `f` is unbounded above on `D`.
- `core/canonical`: the owner abstractions already present upstream are the Chapter 2 function
  `quadraticOverLinearFunction`, the Example 32.0.2 source objective owner
  `QuadraticOverLinearCounterexample.objective`, the source scalar-threshold unboundedness owner,
  and the supremum owner `sSup`.
- `bridge/view`: the source witness curve `t ↦ (t, t⁴)` is kept only as a theorem-level bridge
  from the explicit quartic strip to the previously introduced owner `objective`; it is not a new
  public wrapper for the example function.

Domain-style sampling used here:
- `QuadraticOverLinearCounterexample.objective` from `Example_32_0_2`;
- `QuadraticOverLinearCounterexample.objective_eq_on_posSecond` from the same file;
- `quadraticOverLinearFunction` from `Chap02/Theorem_10_1_4`;
- `sSup` / `sSup_eq_top` as the canonical supremum-owner layer for an extended codomain with `⊤`,
  with a codomain-recursion bridge theorem used only as a derived step.

Primitive data vs derived API:
- primitive public data: the quartic source set `quarticSet`;
- primitive bridge data: the quartic path `t ↦ (t, t⁴)`, exposed only through the pointwise
  evaluation theorem below;
- derived API: the coordinate membership view for `quarticSet`, the quartic boundary-curve
  membership theorem, the convexity and boundedness of `quarticSet`, the quartic-path source
  formula for `objective`, the codomain-recursion bridge for strict-below-`⊤` targets, and the
  supremum companion form.

Layer target: `source-facing`, reusing the previously introduced owner `objective` instead of
repeating its defining expression in a second Chapter 32 file.
-/

namespace QuadraticOverLinearCounterexample

section Ordered

variable {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜]

/-- Example 32.0.3: the source set
`D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}`. -/
def quarticSet : Set (𝕜 × 𝕜) :=
  {ξ : 𝕜 × 𝕜 | ξ.1 ^ 4 ≤ ξ.2 ∧ ξ.2 ≤ 1}

@[simp] theorem mem_quarticSet_iff {ξ : 𝕜 × 𝕜} :
    ξ ∈ quarticSet ↔ ξ.1 ^ 4 ≤ ξ.2 ∧ ξ.2 ≤ 1 := by
  rfl

end Ordered

section OrderedCommRing

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The source boundary curve `t ↦ (t, t⁴)` stays in `D` for `0 ≤ t ≤ 1`. -/
theorem quarticCurve_mem_quarticSet {t : 𝕜} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t, t ^ 4) ∈ (quarticSet : Set (𝕜 × 𝕜)) := by
  rw [mem_quarticSet_iff]
  refine ⟨le_rfl, ?_⟩
  exact pow_le_one₀ ht0 ht1

/-- Example 32.0.3: the counterexample set `D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}` is convex. -/
theorem quarticSet_convex :
    Convex 𝕜 (quarticSet : Set (𝕜 × 𝕜)) := by
  have hLower : Convex 𝕜 {ξ : 𝕜 × 𝕜 | ξ.1 ^ 4 ≤ ξ.2} := by
    have hpow : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun x : 𝕜 ↦ x ^ 4) := by
      simpa using (show Even 4 by decide).convexOn_pow
    simpa using hpow.convex_epigraph
  refine hLower.inter ?_
  simpa using convex_halfSpace_le (LinearMap.snd 𝕜 𝕜 𝕜).isLinear (1 : 𝕜)

end OrderedCommRing

section OrderedFieldBridge

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "f" => objective (𝕜 := 𝕜)

/-- Along the source quartic curve `ξ₂ = ξ₁⁴`, the Example 32.0.3 objective specializes to the
source formula `t² / t⁴ - t⁴`; away from `t = 0` this is the positive-branch formula from Example
32.0.2, and at `t = 0` both sides are `0`. -/
theorem objective_eq_on_quarticCurve {t : 𝕜} :
    f (t, t ^ 4) = (t ^ 2 / t ^ 4 - t ^ 4 : 𝕜) := by
  by_cases ht : t = 0
  · subst ht
    simp [objective, quadraticOverLinearFunction]
  · have hpos : 0 < ((t, t ^ 4) : R2).2 := by
      have ht0 : 0 < t ^ 4 := by
        exact lt_of_le_of_ne (by positivity) (Ne.symm <| pow_ne_zero 4 ht)
      simpa using ht0
    simpa using
      (objective_eq_on_posSecond (ξ := ((t, t ^ 4) : R2)) hpos)

end OrderedFieldBridge

section RealBridge

local notation "R2" => ℝ × ℝ
local notation "D" => (quarticSet : Set R2)

/-- Example 32.0.3: the counterexample set `D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}` is bounded. -/
theorem quarticSet_bounded :
    Bornology.IsBounded D := by
  refine
    (show Bornology.IsBounded (Metric.closedBall (0 : R2) 1) from
      Metric.isBounded_closedBall).subset ?_
  intro ξ hξ
  rcases mem_quarticSet_iff.mp hξ with ⟨hlower, hupper⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
  refine max_le_iff.mpr ?_
  have h0pow : ξ.1 ^ 4 ≤ 1 := le_trans hlower hupper
  have h0sq : ξ.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (ξ.1 ^ 2), h0pow]
  have h0norm : ‖ξ.1‖ ≤ 1 := by
    have habs : |ξ.1| ≤ (1 : ℝ) := (sq_le_one_iff_abs_le_one ξ.1).1 h0sq
    simpa [Real.norm_eq_abs] using habs
  have h1nonneg : 0 ≤ ξ.2 := by
    have h0four_nonneg : 0 ≤ ξ.1 ^ 4 := by positivity
    linarith
  have h1norm : ‖ξ.2‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h1nonneg] using hupper
  exact ⟨h0norm, h1norm⟩

end RealBridge

section OrderedFieldUnbounded

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "f" => objective (𝕜 := 𝕜)
local notation "R2" => 𝕜 × 𝕜
local notation "D" => (quarticSet : Set R2)

/-- Source-facing unbounded-above form of Example 32.0.3: every scalar threshold is exceeded by
the objective at some point of `D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}`. -/
theorem objective_unbounded_above_on_quarticSet (β : 𝕜) :
    ∃ ξ ∈ D, (β : WithBotTop 𝕜) < f ξ := by
  let M : 𝕜 := max (β + 2) (1 : 𝕜)
  have hβM : β + 2 ≤ M := le_max_left _ _
  have h1M : (1 : 𝕜) ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one h1M
  have hMle : (1 : 𝕜) ≤ M := h1M
  let t : 𝕜 := 1 / M
  have ht0 : 0 ≤ t := le_of_lt (one_div_pos.mpr hMpos)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (one_div_le hMpos zero_lt_one).2 (by simpa using hMle)
  refine ⟨(t, t ^ 4), ?_, ?_⟩
  · exact quarticCurve_mem_quarticSet ht0 ht1
  · have hM0 : M ≠ 0 := ne_of_gt hMpos
    have hpow_le_one : t ^ 4 ≤ (1 : 𝕜) := pow_le_one₀ ht0 ht1
    have hβ_le_sub_two : β ≤ M - 2 := by linarith
    have hsub_lt_sq : M - 2 < M ^ 2 - 1 := by
      nlinarith [h1M]
    have hβ_lt_sq_sub_one : β < M ^ 2 - 1 := lt_of_le_of_lt hβ_le_sub_two hsub_lt_sq
    have hβ_lt_target : β < M ^ 2 - t ^ 4 := by
      refine lt_of_lt_of_le hβ_lt_sq_sub_one ?_
      linarith [hpow_le_one]
    have hcalc : (t ^ 2 / t ^ 4 - t ^ 4 : 𝕜) = M ^ 2 - t ^ 4 := by
      dsimp [t]
      field_simp [hM0]
    have hcurve : f (t, t ^ 4) = (t ^ 2 / t ^ 4 - t ^ 4 : 𝕜) := by
      simpa using objective_eq_on_quarticCurve
    rw [hcurve]
    have hscalar : β < (t ^ 2 / t ^ 4 - t ^ 4 : 𝕜) := by
      calc
        β < M ^ 2 - t ^ 4 := hβ_lt_target
        _ = (t ^ 2 / t ^ 4 - t ^ 4 : 𝕜) := by simpa using hcalc.symm
    simpa using hscalar

/-- Codomain-recursion bridge form: every strict lower point below `⊤` in `WithBotTop 𝕜`
is exceeded by the objective on `D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}`. This is used as a
derived bridge for the supremum theorem, while the scalar-threshold theorem is the
source-facing primary owner. -/
private theorem objective_unbounded_above_on_quarticSet_withBotTop
    {b : WithBotTop 𝕜} (hb : b < ⊤) :
    ∃ ξ ∈ D, b < f ξ := by
  cases b using WithBotTop.rec with
  | bot =>
    rcases objective_unbounded_above_on_quarticSet (𝕜 := 𝕜) 0 with ⟨ξ, hξ, hξgt⟩
    refine ⟨ξ, hξ, ?_⟩
    exact lt_trans (bot_lt_iff_ne_bot.mpr (WithBotTop.coe_ne_bot 0)) hξgt
  | coe β =>
    simpa using objective_unbounded_above_on_quarticSet (𝕜 := 𝕜) β
  | top =>
    exact False.elim ((lt_irrefl (⊤ : WithBotTop 𝕜)) hb)

end OrderedFieldUnbounded

section OrderedFieldSupremum

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

local notation "f" => objective (𝕜 := 𝕜)
local notation "R2" => 𝕜 × 𝕜
local notation "D" => (quarticSet : Set R2)

/-- Canonical supremum form of Example 32.0.3: the image of `quarticSet` under the source
objective has supremum `⊤`. -/
theorem sSup_image_objective_quarticSet_eq_top :
    sSup (f '' D) = ⊤ := by
  refine (sSup_eq_top).2 ?_
  intro b hb
  rcases objective_unbounded_above_on_quarticSet_withBotTop hb with ⟨ξ, hξ, hξgt⟩
  exact ⟨f ξ, ⟨ξ, hξ, rfl⟩, hξgt⟩

end OrderedFieldSupremum

end QuadraticOverLinearCounterexample
