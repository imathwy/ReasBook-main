import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_4_9_1 (from Chap01) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v} {E : Type u}

local notation "P" => 𝕜 × E
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

section Slice

variable {β : Type*} [Top β] [One 𝕜]

/-- Primitive slice owner for Text 5.4.9.1:
`h(1, x) = f x`, `h(λ, x) = ⊤` for `λ ≠ 1`. -/
def perspectiveSlice (f : E → β) : P → β :=
  fun p ↦ if p.1 = 1 then f p.2 else ⊤

@[simp] theorem perspectiveSlice_apply_one (f : E → β) (x : E) :
    perspectiveSlice f (1, x) = f x := by
  simp [perspectiveSlice]

@[simp] theorem perspectiveSlice_apply_of_ne_one
    (f : E → β) {a : 𝕜} (ha : a ≠ 1) (x : E) :
    perspectiveSlice f (a, x) = ⊤ := by
  simp [perspectiveSlice, ha]

end Slice

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item forms the slice function `h(1, x) = f x`, `h(λ, x) = +∞` for
  `λ ≠ 1`, and studies the resulting perspective directly on the intrinsic product space
  `P = 𝕜 × E`.
- `core/canonical`: the owner abstraction is the previously introduced generated-function
  construction `Function.sublinearHull` on modules over the ambient ordered ring `𝕜`.
- `bridge/view`: none is needed in the public API here, because the source-facing owner already
  lives on the intrinsic product space `P = 𝕜 × E`.

Primitive data vs derived API:
- primitive data: the slice function `fun p ↦ if p.1 = 1 then f p.2 else ⊤` on the source-facing
  product space `P`;
- source-facing owner: the generated perspective `perspective f` on `P`;
- derived API: properness/convexity/positive-homogeneity statements for
  `perspective f`, together with the ray epigraph statements;
- bridge data: none.

Domain-style sampling used here:
- `Function.sublinearHull`;
- `Function.isConvex_sublinearHull`;
- `Function.verticalInfimum_eq_sInf`.
-/

open Function
open scoped Pointwise

section Basic

variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Text 5.4.9.1: the perspective generated from the slice function
`h(1, x) = f x`, `h(λ, x) = +∞` for `λ ≠ 1`, on the intrinsic product space `𝕜 × E`. -/
def perspective (f : E → WithTopBot 𝕜) : P → WithTopBot 𝕜 :=
  sublinearHull (perspectiveSlice f)

end Basic

section Pointwise

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

local instance : DecidableLT 𝕜 := Classical.decRel (fun x y ↦ x < y)

/-- Helper for Text 5.4.9.1: a point lies in the epigraph of the slice function exactly when its
first coordinate is `1` and its height lies in the epigraph of `f`. -/
theorem mem_epi_perspectiveSlice_iff
    (f : E → WithTopBot 𝕜) (a : 𝕜) (x : E) (μ : 𝕜) :
    (((a, x), μ) ∈ epi (perspectiveSlice f)) ↔ a = 1 ∧ f x ≤ μ := by
  -- Split on the source-side branch `a = 1` versus `a ≠ 1`.
  by_cases ha : a = 1
  · subst ha
    simp [mem_epi_iff]
  · simp [mem_epi_iff, perspectiveSlice, ha]

/-- Helper for Text 5.4.9.1: the slice epigraph is convex because it is exactly the affine copy of
the epigraph of `f` cut out by the first-coordinate equation `λ = 1`. -/
theorem epi_perspectiveSlice_convex
    (f : E → WithTopBot 𝕜) (hf_convex : f.IsConvex 𝕜) :
    Convex 𝕜 (epi (perspectiveSlice f)) := by
  intro p hp q hq a b ha hb hab
  rcases p with ⟨⟨ap, xp⟩, μp⟩
  rcases q with ⟨⟨aq, xq⟩, μq⟩
  rw [mem_epi_perspectiveSlice_iff] at hp hq ⊢
  rcases hp with ⟨hap, hpμ⟩
  rcases hq with ⟨haq, hqμ⟩
  constructor
  · -- The first coordinate stays pinned to `1` under convex combinations.
    simp [hap, haq, smul_eq_mul, hab, mul_add, add_comm, add_left_comm, add_assoc]
  · -- The remaining height inequality is exactly the convexity inequality for `epi f`.
    have hcombo : (a • (xp, μp) + b • (xq, μq) : E × 𝕜) ∈ epi f :=
      hf_convex hpμ hqμ ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm,
      add_assoc] using hcombo

/-- Helper for Text 5.4.9.1: properness of `f` supplies a finite point, hence a nonempty point in
the slice epigraph at level `λ = 1`. -/
theorem epi_perspectiveSlice_nonempty
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) :
    (epi (perspectiveSlice f)).Nonempty := by
  rcases hf_proper.nonempty_dom with ⟨x0, hx0⟩
  rcases Function.finite_value_of_mem_dom_and_ne_bot (f := f) hx0 (hf_proper.ne_bot x0) with
    ⟨a, ha⟩
  refine ⟨((1, x0), a), ?_⟩
  -- At the slice `λ = 1`, the slice epigraph is exactly the epigraph of `f`.
  rw [mem_epi_perspectiveSlice_iff]
  exact ⟨rfl, by simpa [ha]⟩

/-- Helper for Text 5.4.9.1: fixing a nonnegative first coordinate `λ`, the fiber of the cone over
the slice epigraph is exactly the scaled epigraph `λ • epi f`. -/
theorem mem_cone_epi_perspectiveSlice_iff_mem_smul_epi
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    (lam : 𝕜≥0) (x : E) (μ : 𝕜) :
    ((((lam : 𝕜), x), μ) ∈ cone[𝕜] (epi (perspectiveSlice f))) ↔
      (x, μ) ∈ ((lam : 𝕜) • epi f) := by
  have hcone :
      (cone[𝕜] (epi (perspectiveSlice f)) : Set (P × 𝕜)) =
        (Set.Ici (0 : 𝕜)) • epi (perspectiveSlice f) := by
    simpa using
      PointedCone.cone_eq_nonnegativeRay_of_convex (R := 𝕜)
        (C := epi (perspectiveSlice f))
        (epi_perspectiveSlice_convex (f := f) hf_convex)
        (epi_perspectiveSlice_nonempty (f := f) hf_proper)
  constructor
  · intro hmem
    rw [hcone] at hmem
    rcases hmem with ⟨hc, hmem⟩
    rcases Set.mem_smul_set.mp hmem with ⟨q, hq, hqeq⟩
    rcases q with ⟨⟨a, y⟩, r⟩
    rcases (mem_epi_perspectiveSlice_iff (f := f) a y r).mp hq with ⟨ha, hyr⟩
    subst ha
    have hc_eq : (hc : 𝕜) = (lam : 𝕜) := by
      simpa [Prod.smul_mk, smul_eq_mul] using
        congrArg (fun z : P × 𝕜 => z.1.1) hqeq
    have hxrμ : (hc : 𝕜) • (y, r) = (x, μ) := by
      simpa [Prod.smul_mk] using
        congrArg (fun z : P × 𝕜 => (z.1.2, z.2)) hqeq
    refine Set.mem_smul_set.mpr ⟨(y, r), (mem_epi_iff).2 hyr, ?_⟩
    simpa [hc_eq] using hxrμ
  · intro hmem
    rw [hcone]
    refine ⟨lam.2, ?_⟩
    rcases Set.mem_smul_set.mp hmem with ⟨q, hq, hqeq⟩
    rcases q with ⟨y, r⟩
    refine Set.mem_smul_set.mpr ⟨((1, y), r), ?_, ?_⟩
    · -- Lift the scaled epigraph witness back to the `λ = 1` slice.
      rw [mem_epi_perspectiveSlice_iff]
      exact ⟨rfl, (mem_epi_iff).1 hq⟩
    · -- Repackage the scaled witness into the cone fiber over `((λ, x), μ)`.
      simpa [Prod.smul_mk] using
        congrArg (fun z : E × 𝕜 => (((lam : 𝕜), z.1), z.2)) hqeq

/-- Helper for Text 5.4.9.1: on the nonnegative branch, the perspective is the vertical infimum
of the scaled epigraph `λ • epi f`. -/
theorem perspective_apply_nonneg_eq_verticalInfimum_smul_epi
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    (lam : 𝕜≥0) (x : E) :
    perspective f ((lam : 𝕜), x) =
      Function.verticalInfimum (((lam : 𝕜) • epi f) : Set (E × 𝕜)) x := by
  -- Rewrite both sides as vertical infima over the same scalar fiber.
  rw [perspective, Function.sublinearHull_eq_verticalInfimum]
  rw [Function.verticalInfimum_eq_sInf, Function.verticalInfimum_eq_sInf]
  congr 1
  ext μ
  simpa [Function.verticalSection] using
    mem_cone_epi_perspectiveSlice_iff_mem_smul_epi
      (f := f) hf_proper hf_convex lam x μ

/-- Helper for Text 5.4.9.1: negative first coordinate cannot occur in the cone over the slice
epigraph, so the perspective takes the value `+∞` there. -/
theorem perspective_apply_of_neg
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    {lam : 𝕜} (hλ : lam < 0) (x : E) :
    perspective f (lam, x) = ⊤ := by
  have hcone :
      (cone[𝕜] (epi (perspectiveSlice f)) : Set (P × 𝕜)) =
        (Set.Ici (0 : 𝕜)) • epi (perspectiveSlice f) := by
    simpa using
      PointedCone.cone_eq_nonnegativeRay_of_convex (R := 𝕜)
        (C := epi (perspectiveSlice f))
        (epi_perspectiveSlice_convex (f := f) hf_convex)
        (epi_perspectiveSlice_nonempty (f := f) hf_proper)
  have hsection_empty :
      {μ : 𝕜 | ((lam, x), μ) ∈ cone[𝕜] (epi (perspectiveSlice f))} = ∅ := by
    ext μ
    constructor
    · intro hμ
      rw [hcone] at hμ
      rcases hμ with ⟨hc, hmem⟩
      rcases Set.mem_smul_set.mp hmem with ⟨q, hq, hqeq⟩
      rcases q with ⟨⟨a, y⟩, r⟩
      rcases (mem_epi_perspectiveSlice_iff (f := f) a y r).mp hq with ⟨ha, _⟩
      subst ha
      have hlam_nonneg : 0 ≤ lam := by
        simpa [Prod.smul_mk, smul_eq_mul] using
          congrArg (fun z : P × 𝕜 => z.1.1) hqeq
      exact False.elim ((not_lt_of_ge hlam_nonneg) hλ)
    · simp
  -- An empty fiber means the attached vertical infimum is `⊤`.
  rw [perspective, Function.sublinearHull_eq_verticalInfimum, Function.verticalInfimum_eq_sInf]
  simp [hsection_empty]

/-- Helper for Text 5.4.9.1: properness of `f` supplies a nonempty epigraph. -/
theorem epi_nonempty_of_isProper
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) :
    (epi f).Nonempty := by
  rcases hf_proper.nonempty_dom with ⟨x0, hx0⟩
  rcases Function.finite_value_of_mem_dom_and_ne_bot (f := f) hx0 (hf_proper.ne_bot x0) with
    ⟨a, ha⟩
  refine ⟨(x0, a), ?_⟩
  exact (mem_epi_restrict_iff).2 ⟨by simp, by simp [ha]⟩

/-- Helper for Text 5.4.9.1: the vertical infimum over a positively scaled epigraph is the usual
positive-scalar perspective formula. -/
theorem verticalInfimum_smul_epi_of_pos
    (f : E → WithTopBot 𝕜) {a : 𝕜} (ha : 0 < a) (x : E) :
    Function.verticalInfimum (((a : 𝕜) • epi f) : Set (E × 𝕜)) x =
      a * f (a⁻¹ • x) := by
  have hscaled :
      ((a : 𝕜) • epi f : Set (E × 𝕜)) =
        epi (fun y ↦ (a : WithTopBot 𝕜) * f (a⁻¹ • y)) := by
    ext p
    rcases p with ⟨y, μ⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    rw [mem_epi_iff, mem_epi_iff]
    change f (a⁻¹ • y) ≤ ((a⁻¹ * μ : 𝕜) : WithTopBot 𝕜) ↔
      (a : WithTopBot 𝕜) * f (a⁻¹ • y) ≤ μ
    set z := f (a⁻¹ • y)
    cases z using WithBotTop.rec with
    | bot =>
        rw [WithBotTop.coe_mul_bot_of_pos ha]
        simp
    | top =>
        have hlhs : ¬ ⊤ ≤ (((a⁻¹ * μ : 𝕜)) : WithTopBot 𝕜) := by
          intro h
          exact WithBotTop.coe_ne_top (a⁻¹ * μ) (top_le_iff.mp h)
        constructor
        · intro h
          exact (hlhs h).elim
        · intro h
          rw [WithBotTop.coe_mul_top_of_pos ha] at h
          simp at h
    | coe r =>
        constructor
        · intro h
          rw [← WithBotTop.coe_mul] at h
          have hmulinv : r ≤ a⁻¹ * μ := WithBotTop.coe_le_coe.mp h
          have hdiv : r ≤ μ / a := by
            simpa [div_eq_mul_inv, mul_comm] using hmulinv
          exact WithBotTop.coe_le_coe.mpr <| by
            simpa [mul_comm] using (le_div_iff₀' ha).mp hdiv
        · intro h
          rw [← WithBotTop.coe_mul] at h
          have hmul : a * r ≤ μ := WithBotTop.coe_le_coe.mp h
          have hdiv : r ≤ μ / a := (le_div_iff₀' ha).mpr <| by
            simpa [mul_comm] using hmul
          have hmulinv : r ≤ a⁻¹ * μ := by
            simpa [div_eq_mul_inv, mul_comm] using hdiv
          exact (WithBotTop.coe_le_coe.mpr hmulinv :
            (r : WithTopBot 𝕜) ≤ (((a⁻¹ * μ : 𝕜)) : WithTopBot 𝕜))
  -- Once the scaled epigraph is identified, `verticalInfimum` over an epigraph recovers the owner.
  rw [hscaled]
  simp

/-- Helper for Text 5.4.9.1: the zero-scaled epigraph collapses to the origin, so its vertical
infimum is `0` at the origin and `+∞` elsewhere. -/
theorem verticalInfimum_zero_smul_epi_of_epi_nonempty
    (f : E → WithTopBot 𝕜) (hepi : (epi f).Nonempty) (x : E) :
    Function.verticalInfimum (((0 : 𝕜) • epi f) : Set (E × 𝕜)) x =
      if x = 0 then 0 else ⊤ := by
  have hzeroepi : ((0 : 𝕜) • epi f : Set (E × 𝕜)) = 0 := Set.zero_smul_set hepi
  rw [Function.verticalInfimum_eq_sInf]
  by_cases hx : x = 0
  · subst hx
    simp [Function.verticalHeights, Function.verticalSection, hzeroepi]
  · simp [Function.verticalHeights, Function.verticalSection, hzeroepi, hx]

/-- Helper for Text 5.4.9.1: multiplying a non-bottom extended value by a positive scalar cannot
create `⊥`. -/
theorem mul_withTopBot_ne_bot_of_pos {a : 𝕜} (ha : 0 < a) {z : WithTopBot 𝕜} (hz : z ≠ ⊥) :
    a * z ≠ (⊥ : WithTopBot 𝕜) := by
  -- Reduce to the three canonical branches of `WithTopBot 𝕜`.
  cases z using WithBotTop.rec with
  | bot =>
      exact False.elim (hz rfl)
  | top =>
      simpa [WithBotTop.coe_mul_top_of_pos ha]
  | coe r =>
      simpa [WithBotTop.coe_mul]

/-- Helper for Text 5.4.9.1: the perspective is never `⊥`; the nonnegative branch reduces to
scaled-epigraph vertical infima, while the negative branch is `+∞`. -/
theorem perspective_ne_bot
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    ∀ p : P, perspective f p ≠ ⊥ := by
  intro p
  rcases p with ⟨lam, x⟩
  by_cases hλ : lam < 0
  · -- The negative branch is explicitly `+∞`.
    rw [perspective_apply_of_neg (f := f) hf_proper hf_convex hλ x]
    simp
  · have hλ_nonneg : 0 ≤ lam := by
      exact le_of_not_gt hλ
    have hval :
        perspective f (lam, x) =
          Function.verticalInfimum (((lam : 𝕜) • epi f) : Set (E × 𝕜)) x := by
      simpa using
        perspective_apply_nonneg_eq_verticalInfimum_smul_epi
          (f := f) hf_proper hf_convex ⟨lam, hλ_nonneg⟩ x
    rw [hval]
    by_cases hlam : lam = 0
    · subst hlam
      -- At `λ = 0`, the scaled epigraph collapses to the origin.
      rw [verticalInfimum_zero_smul_epi_of_epi_nonempty
        (f := f) (epi_nonempty_of_isProper (f := f) hf_proper) x]
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp [hx0]
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hλ_nonneg hlam
      -- For `λ > 0`, the scaled-epigraph vertical infimum is the usual positive perspective.
      rw [verticalInfimum_smul_epi_of_pos (f := f) hlam_pos x]
      exact mul_withTopBot_ne_bot_of_pos hlam_pos (hf_proper.ne_bot _)

end Pointwise

section Proper

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

local instance : DecidableLT 𝕜 := Classical.decRel (fun x y ↦ x < y)

-- Proof sketch: apply the source properness argument directly to the owner-side generated
-- function on `P = 𝕜 × E`. Properness of `f` gives a nonempty slice epigraph at `λ = 1`, while
-- convexity of `f` gives the convexity needed for the cone construction to behave properly.
/-- Text 5.4.9.1 (1): if `f` is a proper convex function on a `𝕜`-module `E`, then the generated
perspective `perspective f` from the slice function `h(1, x) = f x`, `h(λ, x) = +∞` for `λ ≠ 1`
is proper on the intrinsic product space `𝕜 × E`.
The closed perspective is the later Chapter 13 owner `cl (perspective f)`. -/
theorem perspective_isProper
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    (perspective f).IsProper := by
  refine ⟨?_, perspective_ne_bot (f := f) hf_proper hf_convex⟩
  refine ⟨(0 : P), ?_⟩
  -- The generated cone always contains the origin, so the perspective is finite there.
  have hzero_epi : ((0 : P), (0 : 𝕜)) ∈ epi (perspective f) := by
    simpa [perspective] using zero_mem_epi_sublinearHull (perspectiveSlice f)
  exact mem_effectiveDomain.mpr <| by
    exact lt_of_le_of_lt ((mem_epi_iff).1 hzero_epi) (by simp)

end Proper

section Convex

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/- Text 5.4.9.1 (2): the convexity of the perspective is exactly the owner theorem from
`Text_5_4_7`, specialized to the intrinsic slice function
`fun p ↦ if p.1 = 1 then f p.2 else ⊤`. -/
theorem perspective_isConvex
    (f : E → WithTopBot 𝕜) :
    (perspective f).IsConvex 𝕜 := by
  simpa [perspective] using
    isConvex_sublinearHull (perspectiveSlice f)

end Convex

section PositivelyHomogeneous

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/- Text 5.4.9.1 (3): the perspective is positively homogeneous. This is exactly the owner theorem
from `Text_5_4_8`, specialized to the same slice function. -/
theorem perspective_positivelyHomogeneous
    (f : E → WithTopBot 𝕜) :
    (perspective f).PositivelyHomogeneous 𝕜 := by
  simpa [perspective] using
    positivelyHomogeneous_sublinearHull (perspectiveSlice f)

/- Companion pointwise form of Text 5.4.9.1 (3): scaling a perspective by a positive scalar
scales its value by the same scalar. -/
theorem perspective_map_smul
    (f : E → WithTopBot 𝕜) {c : 𝕜} (hc : 0 < c) (p : P) :
    perspective f (c • p) = c • perspective f p := by
  exact (perspective_positivelyHomogeneous f).map_smul hc p

end PositivelyHomogeneous

section RaysProper

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

local instance : DecidableLT 𝕜 := Classical.decRel (fun x y ↦ x < y)

-- Proof sketch: fix `x` with `f x < ⊤`, so the slice at `λ = 1` gives a finite point in the
-- ambient epigraph. Restrict the proper owner-side generated function along the half-line
-- `λ ↦ (λ, x)` and translate back to the subtype `[0, ∞)`.
/-- For `x` in the effective domain of `f`, the perspective ray
`λ ↦ perspective f (λ, x)` on `[0, ∞)` is
proper. -/
theorem perspectiveRayOnNonneg_isProper
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    {x : E} (hx : f x < ⊤) :
    (fun t : 𝕜≥0 ↦ perspective f (t, x)).IsProper := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨1, zero_le_one⟩, ?_⟩
    -- The ray meets the original function at `t = 1`.
    have hpersp_one : perspective f ((1 : 𝕜), x) = f x := by
      calc
        perspective f ((1 : 𝕜), x) =
            Function.verticalInfimum (((1 : 𝕜) • epi f) : Set (E × 𝕜)) x := by
          simpa using
            perspective_apply_nonneg_eq_verticalInfimum_smul_epi
              (f := f) hf_proper hf_convex ⟨1, zero_le_one⟩ x
        _ = 1 * f (1⁻¹ • x) := by
          exact verticalInfimum_smul_epi_of_pos (f := f) zero_lt_one x
        _ = f x := by
          simp
    exact mem_effectiveDomain.mpr <| by
      simpa [hpersp_one] using hx
  · intro t
    -- Properness of the ambient perspective gives pointwise exclusion of `⊥` on the ray.
    simpa using (perspective_isProper (f := f) hf_proper hf_convex).ne_bot (t, x)

end RaysProper

section RaysConvex

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

-- Proof sketch: restrict the convex epigraph of the owner-side generated function to the affine
-- half-plane determined by the fixed point `x` and the nonnegative parameter `λ`, then rewrite in
-- the source-facing product coordinates.
/-- For fixed `x`, the perspective ray
`λ ↦ perspective f (λ, x)` is convex on `[0, ∞)` in owner form. -/
theorem perspectiveRayOnNonneg_isConvexOn
    (f : E → WithTopBot 𝕜) (x : E) :
    ConvexOn 𝕜 𝕜≥0 (fun t ↦ perspective f (t, x)) := by
  have hpersp_convexOn : ConvexOn 𝕜 (Set.univ : Set P) (perspective f) := by
    -- Convert the owner epigraph convexity into the Jensen-style `ConvexOn` form on `P`.
    exact convexOn_of_convex_finiteHeight_epigraph
      (s := (Set.univ : Set P)) (f := perspective f)
      (by simpa using perspective_isConvex f) convex_univ
  refine ⟨convex_Ici (0 : 𝕜), ?_⟩
  intro t _ s _ a b ha hb hab
  -- Apply convexity of the ambient perspective to the two points `(t, x)` and `(s, x)`.
  simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc,
    add_smul, hab] using
    hpersp_convexOn.2 (by simp) (by simp) ha hb hab

/-- Bridge form of `perspectiveRayOnNonneg_isConvexOn`: convexity of the restricted epigraph. -/
theorem perspectiveRayOnNonneg_has_convex_epigraph
    (f : E → WithTopBot 𝕜) (x : E) :
    Convex 𝕜 (epi[𝕜≥0] (fun t ↦ perspective f (t, x))) := by
  exact (convexOn_iff_convex_epigraph (s := 𝕜≥0)
    (f := (fun t ↦ perspective f (t, x)))).1
      (perspectiveRayOnNonneg_isConvexOn (f := f) x)

end RaysConvex

end

/-! ### Text_5_4_10 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 5.4.10 writes the gauge as the infimum of nonnegative scalars `λ`
  such that `x ∈ λ • C`, with chapter notation
  `γ(x | C)`.
- `core/canonical`: the matching owner already introduced in Definition 4.8.2 is mathlib's
  extended Minkowski functional `egauge 𝕜 : Set E → E → ℝ≥0∞` at the primitive scalar-action layer
  `[NNNorm 𝕜] [SMul 𝕜 E]`; the chapter surface `γ(x | C)` is the specialization `𝕜 = ℝ≥0`.
- `bridge/view`: the infimum formula is available upstream both at the generic owner layer
  `egauge_eq_sInf_dilates` and at the chapter-default nonnegative specialization
  `egauge_eq_sInf_nonneg_dilates`; this item reuses those owner bridges directly.
- Primitive data vs derived API: the set `C` and point `x` are primitive. Convexity and
  nonemptiness are redundant for the canonical owner and therefore do not belong in the public API.
- Domain-style sampling used here:
  `γ[𝕜](x | C)`,
  `γ(x | C)`,
  `egauge_eq_sInf_dilates`,
  `egauge_eq_sInf_nonneg_dilates`,
  `IsGauge.eq_egauge_unitSublevel`,
  `egauge_le_of_mem_smul`,
  `le_egauge_iff`.
-/

open scoped Pointwise NNReal Rockafellar

section Gauge

variable {𝕜 : Type*} [NNNorm 𝕜]
variable {E : Type*} [SMul 𝕜 E]

/- Owner-level infimum bridge for arbitrary scalar types with `NNNorm`. -/
recall egauge_eq_sInf_dilates (C : Set E) (x : E) :
  γ[𝕜](x | C) = sInf (enorm '' {c : 𝕜 | x ∈ c • C})

end Gauge

section GaugeNNReal

variable {E : Type*} [SMul ℝ≥0 E]

/- Text 5.4.10 reuses the chapter-default nonnegative-scalar specialization from
Definition 4.8.2. -/
recall egauge_eq_sInf_nonneg_dilates (C : Set E) (x : E) :
  γ(x | C) = sInf (enorm '' {c : ℝ≥0 | x ∈ c • C})

end GaugeNNReal

/-! ### Text_5_4_11 (from Chap01) -/
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Rockafellar
open scoped Pointwise
open Function

section

variable {E : Type*} {𝕜 : Type*}
variable [Semifield 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/- Text 5.4.11 studies the source function `x ↦ δ[𝕜](x | C) + 1`. -/
/-- The right scalar multiple of `x ↦ δ[𝕜](x | C) + 1` is
`x ↦ δ[𝕜](x | λ • C) + λ`. -/
theorem rightScalarMul_indicator_add_one
    (C : Set E) (lam : 𝕜≥0) :
    lam •ʳ (δ[𝕜](· | C) + 1) =
      fun x ↦ δ[𝕜](x | (lam : 𝕜) • C) + (lam : 𝕜) := by
  funext x
  by_cases hC_nonempty : C.Nonempty
  · by_cases hlam : (lam : 𝕜) = 0
    · have hlam_eq : lam = 0 := Subtype.ext hlam
      subst hlam_eq
      obtain ⟨y, hy⟩ := hC_nonempty
      -- At `λ = 0`, the scaled epigraph collapses to the origin indicator because `epi (δ + 1)`
      -- is nonempty whenever `C` is nonempty.
      have hepi : (epi (fun z : E ↦ δ[𝕜](z | C) + 1)).Nonempty := by
        refine ⟨(y, 1), ?_⟩
        simp [hy]
      rw [rightScalarMul_zero_apply_eq_origin_indicator_of_epi_nonempty
          (f := fun z : E ↦ δ[𝕜](z | C) + 1) (hepi := hepi)]
      -- A nonempty set has zero dilate `{0}`, so the right-hand side is the same origin indicator.
      rw [Set.zero_smul_set hC_nonempty, ← Set.singleton_zero]
      simp
    · have hlam_pos : 0 < (lam : 𝕜) := lt_of_le_of_ne lam.2 hlam
      -- For a positive scalar, use the explicit rescaling formula from Text 5.4.3.
      rw [rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
          (f := fun z : E ↦ δ[𝕜](z | C) + 1) (a := (lam : 𝕜)) hlam_pos x]
      by_cases hx : x ∈ (lam : 𝕜) • C
      · have hxC : (lam : 𝕜)⁻¹ • x ∈ C := by
          simpa [Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne'] using hx
        simp [indicator_def, hx, hxC, hlam.ne', hlam_pos]
      · have hxC : (lam : 𝕜)⁻¹ • x ∉ C := by
          simpa [Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne'] using hx
        simp [indicator_def, hx, hxC, hlam.ne', hlam_pos]
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    by_cases hlam : (lam : 𝕜) = 0
    · have hlam_eq : lam = 0 := Subtype.ext hlam
      subst hlam_eq
      -- If `C = ∅`, then `δ[𝕜](· | C) + 1` is identically `⊤`, so the zero scalar leaves it unchanged.
      have hf_top : (fun z : E ↦ δ[𝕜](z | C) + 1) = (⊤ : E → WithBotTop 𝕜) := by
        funext z
        simp [hC_empty]
      rw [rightScalarMul_zero_eq_self_of_eq_top (f := fun z : E ↦ δ[𝕜](z | C) + 1) hf_top]
      simp [hC_empty]
    · have hlam_pos : 0 < (lam : 𝕜) := lt_of_le_of_ne lam.2 hlam
      -- The positive-scalar formula again reduces the empty-set case to the `⊤` branch.
      rw [rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
          (f := fun z : E ↦ δ[𝕜](z | C) + 1) (a := (lam : 𝕜)) hlam_pos x]
      simp [hC_empty]

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Preorder 𝕜] [Zero 𝕜]
variable [SMul 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- Nonnegative scalars whose dilates of `C` contain `x`. -/
def nonnegDilates (C : Set E) (x : E) : Set 𝕜≥0 :=
  {c : 𝕜≥0 | x ∈ (c : 𝕜) • C}

/-- The `WithBotTop 𝕜` image of `nonnegDilates C x`. -/
def nonnegDilateValues (C : Set E) (x : E) : Set (WithBotTop 𝕜) :=
  (fun c : 𝕜≥0 ↦ ((c : 𝕜) : WithBotTop 𝕜)) '' nonnegDilates C x

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [SMul 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- The pointwise infimum of the dilated indicator-shift terms in the ordered
`WithBotTop 𝕜` codomain. -/
private theorem iInf_indicator_dilate_add_eq_sInf_nonneg_dilates
    (C : Set E) (x : E) :
    (⨅ a : 𝕜≥0, δ[𝕜](x | (a : 𝕜) • C) + (a : 𝕜)) =
      sInf (nonnegDilateValues C x) := by
  -- Rewrite the set-level target as an image infimum, then simplify each term by the indicator formula.
  rw [nonnegDilateValues, sInf_image]
  simp [nonnegDilates, indicator_def]

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- For the empty set, the generated sublinear hull of `x ↦ δ[𝕜](x | C) + 1` takes the value `0`
at the origin. -/
theorem sublinearHull_indicator_add_one_empty_zero :
    sublinearHull (fun y : E ↦ δ[𝕜](y | (∅ : Set E)) + 1) (0 : E) = 0 := by
  change (sublinearHull
      (fun y : E ↦ (δ[𝕜](y | (∅ : Set E)) : WithBotTop 𝕜) + ((1 : 𝕜) : WithBotTop 𝕜))
      (0 : E) : WithBotTop 𝕜) = 0
  rw [sublinearHull_eq_sInf_verticalHeights]
  have hepi :
      epi (fun y : E ↦ (δ[𝕜](y | (∅ : Set E)) : WithBotTop 𝕜) + ((1 : 𝕜) : WithBotTop 𝕜)) =
        (∅ : Set (E × 𝕜)) := by
    ext p
    rcases p with ⟨y, a⟩
    constructor
    · intro h
      have : ((⊤ : WithBotTop 𝕜) + ((1 : 𝕜) : WithBotTop 𝕜)) ≤ a := by
        simp at h
      rw [WithBotTop.top_add_coe] at this
      simp at this
    · simp
  rw [hepi]
  simp [Function.verticalHeights, Function.verticalSection]

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Semifield 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- Helper for Text 5.4.11: the indicator-shift function `x ↦ δ[𝕜](x | C) + 1` is convex
whenever `C` is convex. -/
private theorem indicator_add_one_isConvex
    (C : Set E) (hC_convex : Convex 𝕜 C) :
    (fun y ↦ δ[𝕜](y | C) + 1).IsConvex 𝕜 := by
  change Convex 𝕜 (epi (fun y : E ↦ δ[𝕜](y | C) + 1))
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, μx⟩
  rcases q with ⟨y, μy⟩
  rw [mem_epi_iff] at hp hq ⊢
  -- Membership in the epigraph forces both base points to lie in `C`.
  have hxC : x ∈ C := by
    by_cases hx : x ∈ C
    · exact hx
    · simp [indicator_def, hx] at hp
  have hyC : y ∈ C := by
    by_cases hy : y ∈ C
    · exact hy
    · simp [indicator_def, hy] at hq
  have hxyC : a • x + b • y ∈ C := hC_convex hxC hyC ha hb hab
  -- The finite-height parts of the epigraph inequalities reduce to lower bounds by `1`.
  have hx_one : (1 : 𝕜) ≤ μx := by
    simpa [indicator_def, hxC] using hp
  have hy_one : (1 : 𝕜) ≤ μy := by
    simpa [indicator_def, hyC] using hq
  have hone :
      (1 : 𝕜) ≤ a • μx + b • μy := by
    have hlin :
        a • (1 : 𝕜) + b • (1 : 𝕜) ≤ a • μx + b • μy :=
      add_le_add
        (smul_le_smul_of_nonneg_left hx_one ha)
        (smul_le_smul_of_nonneg_left hy_one hb)
    simpa [smul_eq_mul, hab] using hlin
  simpa [indicator_def, hxyC] using hone

/-- The positively homogeneous convex function generated by `x ↦ δ[𝕜](x | C) + 1`
is the pointwise infimum of the nonnegative right scalar multiples when `C` is nonempty and
convex. -/
theorem sublinearHull_indicator_add_one_eq_iInf_rightScalarMul
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    sublinearHull (fun y ↦ δ[𝕜](y | C) + 1) =
      fun x ↦ ⨅ a : 𝕜≥0, (a •ʳ (δ[𝕜](· | C) + 1)) x := by
  funext x
  -- Text 5.4.9 applies once we package convexity and rule out the identically `⊤` case.
  have h_convex : (fun y : E ↦ δ[𝕜](y | C) + 1).IsConvex 𝕜 :=
    indicator_add_one_isConvex (C := C) hC_convex
  have h_ne_top : (fun y : E ↦ δ[𝕜](y | C) + 1) ≠ (⊤ : E → WithBotTop 𝕜) := by
    obtain ⟨y, hy⟩ := hC_nonempty
    intro htop
    have : (((1 : 𝕜) : WithBotTop 𝕜)) = ⊤ := by
      simpa [indicator_def, hy] using congrFun htop y
    simpa using this
  exact Function.sublinearHull_eq_iInf_rightScalarMul
    (h := fun y : E ↦ δ[𝕜](y | C) + 1)
    (h_convex := h_convex) (x := x) (hx := Or.inr h_ne_top)

/-- Bridge form of `sublinearHull_indicator_add_one_eq_iInf_rightScalarMul`: the right scalar
multiple terms are rewritten as dilated indicator-shift expressions. -/
theorem sublinearHull_indicator_add_one_eq_iInf_dilate_add
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    sublinearHull (fun y ↦ δ[𝕜](y | C) + 1) =
      fun x ↦ ⨅ a : 𝕜≥0, δ[𝕜](x | (a : 𝕜) • C) + (a : 𝕜) := by
  funext x
  rw [sublinearHull_indicator_add_one_eq_iInf_rightScalarMul
      (C := C) (hC_convex := hC_convex) (hC_nonempty := hC_nonempty)]
  refine iInf_congr ?_
  intro a
  simpa using congrFun (rightScalarMul_indicator_add_one (C := C) (lam := a)) x

/-- Canonical codomain-level endpoint: the generated positively homogeneous convex function of
`x ↦ δ[𝕜](x | C) + 1` is the nonnegative-dilate infimum in `WithBotTop 𝕜` when `C` is nonempty and
convex. -/
theorem sublinearHull_indicator_add_one_eq_sInf_nonneg_dilates
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    sublinearHull (fun y ↦ δ[𝕜](y | C) + 1) =
      fun x ↦
        sInf (nonnegDilateValues C x) := by
  funext x
  rw [sublinearHull_indicator_add_one_eq_iInf_dilate_add
      (C := C) (hC_convex := hC_convex) (hC_nonempty := hC_nonempty)]
  simpa using iInf_indicator_dilate_add_eq_sInf_nonneg_dilates (C := C) (x := x)

end
