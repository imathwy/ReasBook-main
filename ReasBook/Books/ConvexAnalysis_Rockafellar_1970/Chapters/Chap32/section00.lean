import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_32_0_2 (from Chap06) -/
noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Example 32.0.2 is the bounded-set counterexample showing that a convex function
  can have finite supremum on a convex set without attaining it.
- `core/canonical`: the owner abstractions are the Chapter 2 function
  `quadraticOverLinearFunction`, the shared set owner `paraboloidEpigraph`, mathlib's supremum
  owner `sSup`, and the standard maximizer predicate `IsMaxOn`.
- `bridge/view`: the textbook function
  `f(ξ₁, ξ₂) = ξ₁² / ξ₂ - ξ₂` on `ξ₂ > 0`, extended by `f(0, 0) = 0` and `f = +∞` otherwise, is
  exactly the Chapter 2 owner evaluated at `(ξ₂ / 2, ξ₁)` and shifted by `-ξ₂`. The bounded set
  `C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂ ≤ 1}` stays at the canonical pair owner layer.

Domain-style sampling used here:
- `quadraticOverLinearFunction` from `Chap02/Theorem_10_1_4`;
- `quadraticOverLinearFunction_effectiveDomain` from the same owner file;
- `paraboloidEpigraph`, `mem_paraboloidEpigraph_iff`, and `paraboloidEpigraph_convex`;
- `sSup`, `csSup_le`, and `IsMaxOn` as the canonical supremum / attainment owners.

Primitive data vs derived API:
- primitive public data: the bounded source set `boundedSet` and the source objective `objective`;
- primitive bridge data: the coordinate change `(ξ₁, ξ₂) ↦ (ξ₂ / 2, ξ₁)` together with the affine
  correction `-ξ₂`, encapsulated once in `objective` through the Chapter 2 owner;
- derived API: the positive-branch source formula, the coordinate membership rewrite for
  `boundedSet`, the source-facing convexity of `objective`, the convexity and boundedness of
  `boundedSet`, the strict upper bound on `boundedSet`, the supremum identity, and the
  nonattainment statements.

Layer target: `bridge/view`. This file reuses the existing Chapter 2 owner directly on the
canonical pair layer; it does not introduce a separate Euclidean-coordinate owner.
-/

namespace QuadraticOverLinearCounterexample

section Ordered

variable {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜]

/-- Example 32.0.2: the bounded source set
`C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂ ≤ 1}` at the canonical pair owner layer. -/
def boundedSet : Set (𝕜 × 𝕜) :=
  (paraboloidEpigraph : Set (𝕜 × 𝕜)) ∩ {ξ : 𝕜 × 𝕜 | ξ.2 ≤ 1}

@[simp] theorem mem_boundedSet_iff {ξ : 𝕜 × 𝕜} :
    ξ ∈ boundedSet ↔ ξ.1 ^ 2 ≤ ξ.2 ∧ ξ.2 ≤ 1 := by
  simp [boundedSet, mem_paraboloidEpigraph_iff]

end Ordered

section Field

variable {𝕜 : Type*} [Field 𝕜]

/-- Canonical linear coordinate bridge for Example 32.0.2:
`(ξ₁, ξ₂) ↦ (ξ₂ / 2, ξ₁)`. -/
private def objectiveLinearMap : (𝕜 × 𝕜) →ₗ[𝕜] (𝕜 × 𝕜) where
  toFun ξ := (ξ.2 / 2, ξ.1)
  map_add' ξ η := by
    ext
    · change (ξ.2 + η.2) / 2 = ξ.2 / 2 + η.2 / 2
      ring
    · simp
  map_smul' a ξ := by
    ext
    · change (a * ξ.2) / 2 = a * (ξ.2 / 2)
      ring
    · simp

@[simp] private theorem objectiveLinearMap_apply (ξ : 𝕜 × 𝕜) :
    objectiveLinearMap ξ = (ξ.2 / 2, ξ.1) :=
  rfl

end Field

section GenericObjective

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]

local notation "R2" => 𝕜 × 𝕜

/-- Example 32.0.2: the source objective, expressed canonically through the Chapter 2 owner
`quadraticOverLinearFunction` after the coordinate change `(ξ₁, ξ₂) ↦ (ξ₂ / 2, ξ₁)` and the
affine correction `-ξ₂`. -/
def objective : R2 → WithTopBot 𝕜 :=
  quadraticOverLinearFunction ∘ objectiveLinearMap +
    fun ξ : R2 ↦ ((-ξ.2 : 𝕜) : WithTopBot 𝕜)

local notation "f" => objective (𝕜 := 𝕜)

@[simp] theorem objective_apply (ξ : R2) :
    f ξ = quadraticOverLinearFunction (ξ.2 / 2, ξ.1) - ξ.2 := by
  simp [objective, objectiveLinearMap_apply, Function.comp]

end GenericObjective

section GenericObjectiveConvex

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]

variable [IsStrictOrderedRing 𝕜]

local notation "f" => objective (𝕜 := 𝕜)

/-- Example 32.0.2: the source objective is convex. This is the canonical Chapter 2
quadratic-over-linear owner pulled back along `(ξ₁, ξ₂) ↦ (ξ₂ / 2, ξ₁)` and then shifted by the
affine functional `ξ ↦ -ξ₂`. -/
theorem objective_isConvex :
    f.IsConvex 𝕜 := by
  refine ((quadraticOverLinearFunction_isConvex (𝕜 := 𝕜)).comp_linearMap
      (objectiveLinearMap (𝕜 := 𝕜))).add_of_bot_lt ?_ ?_ ?_
  · simpa using
      Function.isConvex_coe_of_convexOn_univ
        ((-(LinearMap.snd 𝕜 𝕜 𝕜)).convexOn convex_univ)
  · intro ξ
    exact bot_lt_iff_ne_bot.mpr
      (quadraticOverLinearFunction_neBot (𝕜 := 𝕜) (objectiveLinearMap ξ))
  · intro ξ
    exact WithTopBot.bot_lt_coe _

/-- Canonical set-owner surface for Example 32.0.2: the source objective is convex on `R2`. -/
theorem objective_convexOn_univ :
    ConvexOn 𝕜 (Set.univ : Set (𝕜 × 𝕜)) f :=
  objective_isConvex.isConvexOn convex_univ

end GenericObjectiveConvex

section OrderedFieldBridge

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "f" => objective (𝕜 := 𝕜)

/-- On the positive branch `ξ₂ > 0`, the Example 32.0.2 source formula is exactly the Chapter 2
quadratic-over-linear owner evaluated at `(ξ₂ / 2, ξ₁)` and shifted by `-ξ₂`. -/
theorem objective_eq_on_posSecond {ξ : R2} (hξ : 0 < ξ.2) :
    f ξ = ((((ξ.1) ^ 2) / (ξ.2 : 𝕜)) - ξ.2 : 𝕜) := by
  have hvec : 0 < (ξ.2 / 2 : 𝕜) := by
    simpa using (half_pos hξ)
  have hq :
      quadraticOverLinearFunction (ξ.2 / 2, ξ.1) =
        (((ξ.1) ^ 2 / (ξ.2 : 𝕜) : 𝕜) : WithTopBot 𝕜) := by
    have hq_real :
        (ξ.1 ^ 2 / (2 * (ξ.2 / 2) : 𝕜)) =
          ((ξ.1) ^ 2 / (ξ.2 : 𝕜)) := by
      field_simp [hξ.ne']
    rw [quadraticOverLinearFunction, if_pos hvec]
    exact congrArg (fun t : 𝕜 ↦ (t : WithTopBot 𝕜)) hq_real
  rw [objective_apply (𝕜 := 𝕜), hq]
  simp [div_eq_mul_inv, sub_eq_add_neg]

end OrderedFieldBridge

section OrderedCommRing

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "C" => boundedSet (𝕜 := 𝕜)

/-- Example 32.0.2: the counterexample set `C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂ ≤ 1}` is convex. -/
theorem boundedSet_convex :
    Convex 𝕜 C := by
  simpa [boundedSet] using
    (paraboloidEpigraph_convex (𝕜 := 𝕜)).inter
      (convex_halfSpace_le (LinearMap.snd 𝕜 𝕜 𝕜).isLinear (1 : 𝕜))

end OrderedCommRing

section RealBridge

local notation "R2" => ℝ × ℝ
local notation "C" => boundedSet (𝕜 := ℝ)
local notation "f" => objective (𝕜 := ℝ)

/-- Example 32.0.2: the counterexample set `C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂ ≤ 1}` is bounded. -/
theorem boundedSet_bounded :
    Bornology.IsBounded C := by
  refine
    (show Bornology.IsBounded (Metric.closedBall (0 : R2) 1) from
      Metric.isBounded_closedBall).subset ?_
  intro ξ hξ
  rcases mem_boundedSet_iff.mp hξ with ⟨hpar, hupper⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
  refine max_le_iff.mpr ?_
  have h2nonneg : 0 ≤ ξ.2 := by
    nlinarith [sq_nonneg ξ.1, hpar]
  have hfst : ‖ξ.1‖ ≤ 1 := by
    have h1sq : ξ.1 ^ 2 ≤ (1 : ℝ) := le_trans hpar hupper
    have habs : |ξ.1| ≤ (1 : ℝ) := (sq_le_one_iff_abs_le_one (ξ.1)).1 h1sq
    simpa [Real.norm_eq_abs] using habs
  have hsnd : ‖ξ.2‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h2nonneg] using hupper
  exact ⟨hfst, hsnd⟩

end RealBridge

section OrderedFieldPointwise

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "C" => boundedSet (𝕜 := 𝕜)
local notation "f" => objective (𝕜 := 𝕜)

-- Proof sketch: on `boundedSet`, either `ξ = 0`, when the value is `0`, or `ξ.2 > 0`, when the
-- bridge theorem above rewrites the source expression to `ξ.1 ^ 2 / ξ.2 - ξ.2`. Since
-- `ξ.1 ^ 2 ≤ ξ.2 ≤ 1`, this is at most `1 - ξ.2 < 1`.
/-- Every point of the bounded source set has source objective value strictly below `1`. -/
theorem objective_lt_one {ξ : R2} (hξ : ξ ∈ C) :
    f ξ < (1 : 𝕜) := by
  rcases mem_boundedSet_iff.mp hξ with ⟨hpar, hupper⟩
  have h2nonneg : 0 ≤ ξ.2 := by
    nlinarith [sq_nonneg ξ.1, hpar]
  rcases lt_or_eq_of_le h2nonneg with h2pos | h2zero
  · have hobj : f ξ = ((((ξ.1) ^ 2) / (ξ.2 : 𝕜)) - ξ.2 : 𝕜) :=
      objective_eq_on_posSecond h2pos
    have hdiv_le_one : (ξ.1) ^ 2 / (ξ.2 : 𝕜) ≤ 1 := by
      have hdiv_le : (ξ.1) ^ 2 / (ξ.2 : 𝕜) ≤ (ξ.2 : 𝕜) / ξ.2 := by
        exact div_le_div_of_nonneg_right hpar (le_of_lt h2pos)
      simpa [h2pos.ne'] using hdiv_le
    have hobj_le : (((ξ.1) ^ 2) / (ξ.2 : 𝕜)) - ξ.2 ≤ 1 - ξ.2 := by
      linarith
    have hlt : ((((ξ.1) ^ 2) / (ξ.2 : 𝕜)) - ξ.2 : 𝕜) < 1 := by
      refine lt_of_le_of_lt hobj_le ?_
      linarith
    rw [hobj]
    exact (WithTopBot.coe_lt_coe).2 hlt
  · have hsq1 : ξ.1 ^ 2 = 0 := by
      have hsq1le : ξ.1 ^ 2 ≤ 0 := by
        simpa [h2zero] using hpar
      exact le_antisymm hsq1le (sq_nonneg ξ.1)
    have h1zero : ξ.1 = 0 := sq_eq_zero_iff.mp hsq1
    have hξeq0 : ξ = 0 := by
      ext <;> simp [h1zero, h2zero]
    subst hξeq0
    have hobj0 : f (0 : R2) = (0 : 𝕜) := by
      rw [objective_apply]
      simp [quadraticOverLinearFunction]
    rw [hobj0]
    exact (WithTopBot.coe_lt_coe).2 zero_lt_one

end OrderedFieldPointwise

section OrderedFieldSupremum

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "C" => boundedSet (𝕜 := 𝕜)
local notation "f" => objective (𝕜 := 𝕜)

-- Proof sketch: the boundary points `ξ(t) = (t, t²)` belong to `boundedSet` for `0 < t ≤ 1` and
-- satisfy the bridged source formula
-- `quadraticOverLinearFunction (t² / 2, t) - t² = 1 - t²`. These values approach `1` from below,
-- while the previous theorem gives `1` as an upper bound on the whole image.
/-- Example 32.0.2: the supremum of the source example objective over `boundedSet` is exactly
`1`. -/
theorem sSup_image_objective_boundedSet :
    sSup (f '' C) = (1 : 𝕜) := by
  have hstrict :
      ∀ β : 𝕜, β < 1 → ∃ ξ ∈ C, (β : WithTopBot 𝕜) < f ξ := by
    intro β hβ
    let r : 𝕜 := max β 0
    have hβ_le_r : β ≤ r := le_max_left β 0
    have hr_nonneg : 0 ≤ r := le_max_right β 0
    have hr_lt_one : r < 1 := by
      dsimp [r]
      exact max_lt_iff.mpr ⟨hβ, zero_lt_one⟩
    let t : 𝕜 := (1 - r) / 2
    have ht_pos : 0 < t := by
      dsimp [t]
      simpa using half_pos (sub_pos.mpr hr_lt_one)
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have ht_le_one : t ≤ 1 := by
      have h1mr_le_two : 1 - r ≤ (2 : 𝕜) := by
        linarith [hr_nonneg]
      dsimp [t]
      exact (div_le_iff (show (0 : 𝕜) < 2 by positivity)).2 h1mr_le_two
    have ht_sq_le_one : t ^ 2 ≤ (1 : 𝕜) := pow_le_one₀ ht_nonneg ht_le_one
    have hr_lt_target : r < (1 - t ^ 2 : 𝕜) := by
      dsimp [t]
      linarith [hr_nonneg]
    have hβ_lt_target : β < (1 - t ^ 2 : 𝕜) := lt_of_le_of_lt hβ_le_r hr_lt_target
    have hmem : (t, t ^ 2) ∈ boundedSet := by
      rw [mem_boundedSet_iff]
      exact ⟨le_rfl, ht_sq_le_one⟩
    have hobj : f (t, t ^ 2) = (1 - t ^ 2 : 𝕜) := by
      have hposSecond : 0 < ((t, t ^ 2) : R2).2 := by
        simpa using sq_pos_of_pos ht_pos
      calc
        f (t, t ^ 2)
            = ((((t) ^ 2) / ((t ^ 2) : 𝕜)) - (t ^ 2) : 𝕜) := by
                simpa using objective_eq_on_posSecond hposSecond
        _ = (1 - t ^ 2 : 𝕜) := by
              field_simp [pow_ne_zero 2 ht_pos.ne']
    refine ⟨(t, t ^ 2), hmem, ?_⟩
    calc
      (β : WithTopBot 𝕜) < ((1 - t ^ 2 : 𝕜) : WithTopBot 𝕜) :=
        (WithTopBot.coe_lt_coe).2 hβ_lt_target
      _ = f (t, t ^ 2) := hobj.symm
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · refine ⟨f 0, ?_⟩
    exact ⟨0, by simp [mem_boundedSet_iff], rfl⟩
  · intro a ha
    rcases ha with ⟨ξ, hξ, rfl⟩
    exact le_of_lt (objective_lt_one hξ)
  · intro w hw
    cases w using WithTopBot.rec with
    | bot =>
      refine ⟨f 0, ⟨0, by simp [mem_boundedSet_iff], rfl⟩, ?_⟩
      have hobj0 : f (0 : R2) = (0 : 𝕜) := by
        rw [objective_apply]
        simp [quadraticOverLinearFunction]
      rw [hobj0]
      exact WithTopBot.bot_lt_coe 0
    | coe β =>
      have hβ' : β < (1 : 𝕜) := by
        exact (WithTopBot.coe_lt_coe).1 (by simpa using hw)
      rcases hstrict β hβ' with ⟨ξ, hξ, hlt⟩
      exact ⟨f ξ, ⟨ξ, hξ, rfl⟩, hlt⟩
    | top =>
      exact False.elim (not_top_lt hw)

/-- Example 32.0.2, intrinsic nonattainment form: no point of `boundedSet` attains the
codomain-owner supremum `sSup (objective '' boundedSet)`. -/
theorem not_exists_mem_boundedSet_eq_sSup :
    ¬ ∃ ξ ∈ C, f ξ = sSup (f '' C) := by
  rw [sSup_image_objective_boundedSet]
  rintro ⟨ξ, hξ, hξeq⟩
  exact (ne_of_lt (objective_lt_one hξ)) hξeq

/-- Example 32.0.2 in maximizer language: the source example objective has no maximizer on
`boundedSet`. -/
theorem not_exists_isMaxOn_boundedSet :
    ¬ ∃ ξ ∈ C, IsMaxOn f C ξ := by
  rintro ⟨ξ, hξC, hξmax⟩
  have hsSup_le : sSup (f '' C) ≤ f ξ := by
    apply csSup_le
    · exact ⟨f ξ, Set.mem_image_of_mem f hξC⟩
    · rintro y ⟨z, hz, rfl⟩
      exact hξmax hz
  rw [sSup_image_objective_boundedSet] at hsSup_le
  exact not_le_of_gt (objective_lt_one hξC) hsSup_le

end OrderedFieldSupremum

section OrderedFieldConcreteValue

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "C" => boundedSet (𝕜 := 𝕜)
local notation "f" => objective (𝕜 := 𝕜)

/-- Example 32.0.2, source-value companion form: no point of `boundedSet` attains the concrete
supremum value `1`. This corollary only uses the pointwise strict bound and does not require
completeness assumptions. -/
theorem not_exists_mem_boundedSet_eq_one :
    ¬ ∃ ξ ∈ C, f ξ = (1 : 𝕜) := by
  rintro ⟨ξ, hξ, hξeq⟩
  exact (ne_of_lt (objective_lt_one hξ)) hξeq

end OrderedFieldConcreteValue

end QuadraticOverLinearCounterexample

/-! ### Example_32_0_3 (from Chap06) -/
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

/-! ### Text_32_0_4 (from Chap06) -/
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Text 32.0.4 is a prose bridge from maximizing linear functionals on a convex
  set to the extreme-point geometry used later in Section 32.
- `core/canonical`: the owner abstractions already exist upstream as
  `Set.maximizers`, `LinearMap.isFace_maximizers`, `Set.IsFace`, `𝓕[𝕜](C)`, `IsMaxOn`, and
  `Set.IsFace.extremePoints_subset_of_mem_faces`.
- `bridge/view`: this file should not introduce a second "maximizer face" or "extreme maximizer"
  wrapper. The source-facing content is exactly the earlier face owner theorem, together with the
  standard face-to-extreme-point bridge.

Domain-style sampling used here:
- `Set.maximizers` and `Set.mem_maximizers_iff` from `Chap04/Text_18_0_5`;
- `LinearMap.isFace_maximizers` from `Chap04/Text_18_0_5`;
- `Set.IsFace.mem_faces_iff` and `Set.IsFace.extremePoints_subset_of_mem_faces` from
  `Chap04/Defn_18_1`;
- `Set.extremePoints` as the canonical owner for extreme points;
- `IsMaxOn` as the canonical maximizer predicate.

Primitive data vs derived API:
- primitive owner data: face-family membership `C.maximizers f ∈ 𝓕[𝕜](C)` for the maximizer owner;
- pointwise bridge data: membership in the owner is
  `x ∈ C.maximizers f ↔ x ∈ C ∧ IsMaxOn f C x`;
- derived source-facing API: for linear `h` on convex `C`, the previous chapter theorem
  `LinearMap.isFace_maximizers` supplies this face-family membership automatically.

Abstraction checks:
- codomain/ambient layer: the surface stays at an ordered-module codomain `β`, not `ℝ`/`EReal`;
- scalar minimization: the core theorem now uses only the primitive face owner data, and the
  linear-map/convex-set assumptions appear only in the derived source-facing corollary;
- owner correctness: the bridge uses canonical owners only (`Set.maximizers`, `Set.IsFace`,
  `𝓕[𝕜](C)`, `Set.extremePoints`);
- topology phrasing: this bridge is geometric/order-theoretic and introduces no ambient topology;
- notation surface: existing owner notation already expresses the source sentence directly.

Layer target: `bridge/view`.
-/

/- Text 32.0.4 uses the canonical owner for the maximizer slice of a map on `C`. -/
recall Set.maximizers

/- Membership in the maximizer owner is feasibility plus maximality on `C`. -/
recall Set.mem_maximizers_iff

/- Text 32.0.4: for a convex set `C`, the linear-map maximizer owner `C.maximizers h` is a face.
This is exactly the earlier owner theorem `LinearMap.isFace_maximizers`. -/
recall LinearMap.isFace_maximizers

/- Extreme points are owned canonically by `Set.extremePoints`. -/
recall Set.extremePoints

/- Extreme points of that maximizer face are therefore extreme points of the ambient convex set by
the standard face bridge `Set.IsFace.extremePoints_subset`. -/
recall Set.IsFace.extremePoints_subset

/- Face-family notation bridge used in this file: `F ∈ 𝓕[𝕜](C)` is equivalent to
`F.IsFace 𝕜 C`. -/
recall Set.IsFace.mem_faces_iff

/- Extreme points are monotone along membership in the face family `𝓕[𝕜](·)`. -/
recall Set.IsFace.extremePoints_subset_of_mem_faces

universe u v w

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]

section LinearMapBridge

variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {β : Type w} [AddCommMonoid β] [Module 𝕜 β]
variable [LinearOrder β] [IsOrderedCancelAddMonoid β] [PosSMulStrictMono 𝕜 β]

namespace LinearMap

/-- Text 32.0.4 owner bridge: on a convex set `C`, the linear-map maximizer owner belongs to the
face family `𝓕[𝕜](C)`. -/
theorem maximizers_mem_faces (h : E →ₗ[𝕜] β) {C : Set E} (hC : Convex 𝕜 C) :
    C.maximizers h ∈ 𝓕[𝕜](C) := by
  exact Set.IsFace.mem_faces_iff.2 (isFace_maximizers h hC)

/-- Text 32.0.4 bridge theorem: on a convex set `C`, extreme points of the maximizer face of a
linear map are extreme points of `C`. -/
theorem extremePoints_maximizers_subset (h : E →ₗ[𝕜] β) {C : Set E}
    (hC : Convex 𝕜 C) :
    (C.maximizers h).extremePoints 𝕜 ⊆ C.extremePoints 𝕜 := by
  exact Set.IsFace.extremePoints_subset_of_mem_faces (maximizers_mem_faces h hC)

end LinearMap
end LinearMapBridge

end
