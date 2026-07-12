import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_5

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
