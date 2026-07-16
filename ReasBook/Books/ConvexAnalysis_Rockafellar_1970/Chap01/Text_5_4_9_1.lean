import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_8

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Rockafellar

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
    perspectiveSlice (𝕜 := 𝕜) f (1, x) = f x := by
  simp [perspectiveSlice]

@[simp] theorem perspectiveSlice_apply_of_ne_one
    (f : E → β) {a : 𝕜} (ha : a ≠ 1) (x : E) :
    perspectiveSlice (𝕜 := 𝕜) f (a, x) = ⊤ := by
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
  sublinearHull (perspectiveSlice (𝕜 := 𝕜) f)

end Basic

section Pointwise

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

local instance : DecidableLT 𝕜 := Classical.decRel (fun x y ↦ x < y)

/-- Helper for Text 5.4.9.1: a point lies in the epigraph of the slice function exactly when its
first coordinate is `1` and its height lies in the epigraph of `f`. -/
theorem mem_epi_perspectiveSlice_iff
    (f : E → WithTopBot 𝕜) (a : 𝕜) (x : E) (μ : 𝕜) :
    (((a, x), μ) ∈ epi (perspectiveSlice (𝕜 := 𝕜) f)) ↔ a = 1 ∧ f x ≤ μ := by
  rw [mem_epi_iff]
  by_cases ha : a = 1 <;> simp [perspectiveSlice, ha]

/-- Helper for Text 5.4.9.1: the slice epigraph is convex because it is exactly the affine copy of
the epigraph of `f` cut out by the first-coordinate equation `λ = 1`. -/
theorem epi_perspectiveSlice_convex
    (f : E → WithTopBot 𝕜) (hf_convex : f.IsConvex 𝕜) :
    Convex 𝕜 (epi (perspectiveSlice (𝕜 := 𝕜) f)) := by
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
    have hp' : (xp, μp) ∈ epi f := (mem_epi_iff).2 hpμ
    have hq' : (xq, μq) ∈ epi f := (mem_epi_iff).2 hqμ
    have hcombo : (a • (xp, μp) + b • (xq, μq) : E × 𝕜) ∈ epi f :=
      hf_convex hp' hq' ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm,
      add_assoc] using hcombo

/-- Helper for Text 5.4.9.1: properness of `f` supplies a finite point, hence a nonempty point in
the slice epigraph at level `λ = 1`. -/
theorem epi_perspectiveSlice_nonempty
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) :
    (epi (perspectiveSlice (𝕜 := 𝕜) f)).Nonempty := by
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
    ((((lam : 𝕜), x), μ) ∈ cone[𝕜] (epi (perspectiveSlice (𝕜 := 𝕜) f))) ↔
      (x, μ) ∈ ((lam : 𝕜) • epi f) := by
  have hcone :
      (cone[𝕜] (epi (perspectiveSlice (𝕜 := 𝕜) f)) : Set (P × 𝕜)) =
        (Set.Ici (0 : 𝕜)) • epi (perspectiveSlice (𝕜 := 𝕜) f) := by
    simpa using
      PointedCone.cone_eq_nonnegativeRay_of_convex (R := 𝕜)
        (C := epi (perspectiveSlice (𝕜 := 𝕜) f))
        (epi_perspectiveSlice_convex (f := f) hf_convex)
        (epi_perspectiveSlice_nonempty (f := f) hf_proper)
  constructor
  · intro hmem
    change (((lam : 𝕜), x), μ) ∈
      (cone[𝕜] (epi (perspectiveSlice (𝕜 := 𝕜) f)) : Set (P × 𝕜)) at hmem
    rw [hcone] at hmem
    rcases hmem with ⟨hc, hc_nonneg, q, hq, hqeq⟩
    rcases q with ⟨⟨a, y⟩, r⟩
    rcases (mem_epi_perspectiveSlice_iff (f := f) a y r).mp hq with ⟨ha, hyr⟩
    subst ha
    have hc_eq : hc = (lam : 𝕜) := by
      simpa [Prod.smul_mk, smul_eq_mul] using
        congrArg (fun z : P × 𝕜 => z.1.1) hqeq
    have hxrμ : hc • (y, r) = (x, μ) := by
      simpa [Prod.smul_mk] using
        congrArg (fun z : P × 𝕜 => (z.1.2, z.2)) hqeq
    refine Set.mem_smul_set.mpr ⟨(y, r), (mem_epi_iff).2 hyr, ?_⟩
    simpa [hc_eq] using hxrμ
  · intro hmem
    change (((lam : 𝕜), x), μ) ∈
      (cone[𝕜] (epi (perspectiveSlice (𝕜 := 𝕜) f)) : Set (P × 𝕜))
    rw [hcone]
    rcases Set.mem_smul_set.mp hmem with ⟨q, hq, hqeq⟩
    rcases q with ⟨y, r⟩
    refine ⟨(lam : 𝕜), lam.2, ((1, y), r), ?_, ?_⟩
    · -- Lift the scaled epigraph witness back to the `λ = 1` slice.
      rw [mem_epi_perspectiveSlice_iff]
      exact ⟨rfl, (mem_epi_iff).1 hq⟩
    · -- Repackage the scaled witness into the cone fiber over `((λ, x), μ)`.
      have hy : (lam : 𝕜) • y = x := congrArg Prod.fst hqeq
      have hr : (lam : 𝕜) • r = μ := congrArg Prod.snd hqeq
      exact Prod.ext
        (Prod.ext (by
          change (lam : 𝕜) * 1 = (lam : 𝕜)
          rw [mul_one]) hy)
        hr

/-- Helper for Text 5.4.9.1: on the nonnegative branch, the perspective is the vertical infimum
of the scaled epigraph `λ • epi f`. -/
theorem perspective_apply_nonneg_eq_verticalInfimum_smul_epi
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    (lam : 𝕜≥0) (x : E) :
    perspective f ((lam : 𝕜), x) =
      Function.verticalInfimum (((lam : 𝕜) • epi f) : Set (E × 𝕜)) x := by
  -- Rewrite both sides as vertical infima over the same scalar fiber.
  rw [perspective, Function.sublinearHull_eq_verticalInfimum]
  rw [Function.verticalInfimum_eq_sInf_verticalHeights,
    Function.verticalInfimum_eq_sInf_verticalHeights]
  congr 1
  ext z
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨μ,
      (mem_cone_epi_perspectiveSlice_iff_mem_smul_epi
        (f := f) hf_proper hf_convex lam x μ).mp hμ, rfl⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨μ,
      (mem_cone_epi_perspectiveSlice_iff_mem_smul_epi
        (f := f) hf_proper hf_convex lam x μ).mpr hμ, rfl⟩

/-- Helper for Text 5.4.9.1: negative first coordinate cannot occur in the cone over the slice
epigraph, so the perspective takes the value `+∞` there. -/
theorem perspective_apply_of_neg
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    {lam : 𝕜} (hlam : lam < 0) (x : E) :
    perspective f (lam, x) = ⊤ := by
  have hcone :
      (cone[𝕜] (epi (perspectiveSlice (𝕜 := 𝕜) f)) : Set (P × 𝕜)) =
        (Set.Ici (0 : 𝕜)) • epi (perspectiveSlice (𝕜 := 𝕜) f) := by
    simpa using
      PointedCone.cone_eq_nonnegativeRay_of_convex (R := 𝕜)
        (C := epi (perspectiveSlice (𝕜 := 𝕜) f))
        (epi_perspectiveSlice_convex (f := f) hf_convex)
        (epi_perspectiveSlice_nonempty (f := f) hf_proper)
  have hsection_empty :
      {μ : 𝕜 | ((lam, x), μ) ∈ cone[𝕜] (epi (perspectiveSlice (𝕜 := 𝕜) f))} = ∅ := by
    ext μ
    constructor
    · intro hμ
      change ((lam, x), μ) ∈
        (cone[𝕜] (epi (perspectiveSlice (𝕜 := 𝕜) f)) : Set (P × 𝕜)) at hμ
      rw [hcone] at hμ
      rcases hμ with ⟨hc, hc_nonneg, q, hq, hqeq⟩
      rcases q with ⟨⟨a, y⟩, r⟩
      rcases (mem_epi_perspectiveSlice_iff (f := f) a y r).mp hq with ⟨ha, _⟩
      subst ha
      have hc_eq : hc = lam := by
        simpa [Prod.smul_mk, smul_eq_mul] using
          congrArg (fun z : P × 𝕜 => z.1.1) hqeq
      have hlam_nonneg : 0 ≤ lam := by
        simpa [hc_eq] using hc_nonneg
      exact False.elim ((not_lt_of_ge hlam_nonneg) hlam)
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
    induction z using WithTop.recTopCoe with
    | top =>
        have hlhs : ¬ (⊤ : WithTopBot 𝕜) ≤
            ((a⁻¹ * μ : 𝕜) : WithTopBot 𝕜) := by
          intro h
          exact (WithTop.not_top_le_coe _ h).elim
        constructor
        · exact fun h ↦ (hlhs h).elim
        · intro h
          have ha0 : (a : WithTopBot 𝕜) ≠ 0 := by exact_mod_cast ha.ne'
          rw [WithTop.mul_top ha0] at h
          simp at h
    | coe z =>
        induction z using WithBot.recBotCoe with
        | bot =>
            have ha0 : (a : WithBot 𝕜) ≠ 0 := by exact_mod_cast ha.ne'
            constructor
            · intro _
              change ((((a : WithBot 𝕜) * ⊥ : WithBot 𝕜) : WithTopBot 𝕜) ≤
                ((μ : WithBot 𝕜) : WithTopBot 𝕜))
              rw [WithBot.mul_bot ha0]
              exact WithTop.coe_le_coe.mpr bot_le
            · exact fun _ ↦ bot_le
        | coe r =>
            have hbase : r ≤ a⁻¹ * μ ↔ a * r ≤ μ := by
              constructor
              · intro h
                have hdiv : r ≤ μ / a := by simpa [div_eq_mul_inv, mul_comm] using h
                exact by simpa [mul_comm] using (le_div_iff₀' ha).mp hdiv
              · intro h
                have hdiv : r ≤ μ / a :=
                  (le_div_iff₀' ha).mpr (by simpa [mul_comm] using h)
                simpa [div_eq_mul_inv, mul_comm] using hdiv
            exact_mod_cast hbase
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
  induction z using WithTop.recTopCoe with
  | top =>
      have ha0 : (a : WithTopBot 𝕜) ≠ 0 := by exact_mod_cast ha.ne'
      rw [WithTop.mul_top ha0]
      exact top_ne_bot
  | coe z =>
      induction z using WithBot.recBotCoe with
      | bot => exact False.elim (hz rfl)
      | coe r =>
          exact (WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe (a * r))).ne'

/-- Helper for Text 5.4.9.1: the perspective is never `⊥`; the nonnegative branch reduces to
scaled-epigraph vertical infima, while the negative branch is `+∞`. -/
theorem perspective_ne_bot
    (f : E → WithTopBot 𝕜) (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    ∀ p : P, perspective f p ≠ ⊥ := by
  intro p
  rcases p with ⟨lam, x⟩
  by_cases hlam_neg : lam < 0
  · -- The negative branch is explicitly `+∞`.
    rw [perspective_apply_of_neg (f := f) hf_proper hf_convex hlam_neg x]
    simp
  · have hlam_nonneg : 0 ≤ lam := by
      exact le_of_not_gt hlam_neg
    have hval :
        perspective f (lam, x) =
          Function.verticalInfimum (((lam : 𝕜) • epi f) : Set (E × 𝕜)) x := by
      simpa using
        perspective_apply_nonneg_eq_verticalInfimum_smul_epi
          (f := f) hf_proper hf_convex ⟨lam, hlam_nonneg⟩ x
    rw [hval]
    by_cases hlam : lam = 0
    · subst hlam
      -- At `λ = 0`, the scaled epigraph collapses to the origin.
      rw [verticalInfimum_zero_smul_epi_of_epi_nonempty
        (f := f) (epi_nonempty_of_isProper (f := f) hf_proper) x]
      by_cases hx0 : x = 0
      · rw [if_pos hx0]
        exact (WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe (0 : 𝕜))).ne'
      · simp [hx0]
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam_nonneg (Ne.symm hlam)
      -- For `λ > 0`, the scaled-epigraph vertical infimum is the usual positive perspective.
      rw [verticalInfimum_smul_epi_of_pos (f := f) hlam_pos x]
      exact mul_withTopBot_ne_bot_of_pos hlam_pos (hf_proper.ne_bot _)

end Pointwise

section Proper

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
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
    simpa [perspective] using zero_mem_epi_sublinearHull (perspectiveSlice (𝕜 := 𝕜) f)
  exact mem_effectiveDomain.mpr <| by
    exact lt_of_le_of_lt ((mem_epi_iff).1 hzero_epi) (by simp)

end Proper

section Convex

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [DenselyOrdered 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/- Text 5.4.9.1 (2): the convexity of the perspective is exactly the owner theorem from
`Text_5_4_7`, specialized to the intrinsic slice function
`fun p ↦ if p.1 = 1 then f p.2 else ⊤`. -/
theorem perspective_isConvex
    (f : E → WithTopBot 𝕜) :
    (perspective f).IsConvex 𝕜 := by
  simpa [perspective] using
    isConvex_sublinearHull (perspectiveSlice (𝕜 := 𝕜) f)

end Convex

section PositivelyHomogeneous

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) :=
  Function.instSMulWithTopBot_convexAnalysis_Rockafellar_1970_1

/- Text 5.4.9.1 (3): the perspective is positively homogeneous. This is exactly the owner theorem
from `Text_5_4_8`, specialized to the same slice function. -/
theorem perspective_positivelyHomogeneous
    (f : E → WithTopBot 𝕜) :
    (perspective f).PositivelyHomogeneous 𝕜 := by
  simpa [perspective] using
    positivelyHomogeneous_sublinearHull (perspectiveSlice (𝕜 := 𝕜) f)

/- Companion pointwise form of Text 5.4.9.1 (3): scaling a perspective by a positive scalar
scales its value by the same scalar. -/
theorem perspective_map_smul
    (f : E → WithTopBot 𝕜) {c : 𝕜} (hc : 0 < c) (p : P) :
    perspective f (c • p) = c • perspective f p := by
  exact (perspective_positivelyHomogeneous f).map_smul hc p

end PositivelyHomogeneous

section RaysProper

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
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
        _ = ((1 : 𝕜) : WithTopBot 𝕜) * f (((1 : 𝕜)⁻¹) • x) := by
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

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [DenselyOrdered 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) :=
  _root_.instSMulWithTopBot_convexAnalysis_Rockafellar_1970

-- Proof sketch: restrict the convex epigraph of the owner-side generated function to the affine
-- half-plane determined by the fixed point `x` and the nonnegative parameter `λ`.
set_option maxHeartbeats 800000 in
/-- For fixed `x`, the perspective ray
`λ ↦ perspective f (λ, x)` is convex on `[0, ∞)` in owner form. -/
theorem perspectiveRayOnNonneg_isConvexOn
    (f : E → WithTopBot 𝕜) (x : E) :
    ConvexOn 𝕜 𝕜≥0 (fun t ↦ perspective f (t, x)) := by
  have hpersp_convexOn : ConvexOn 𝕜 (Set.univ : Set P) (perspective f) := by
    exact convexOn_of_convex_finiteHeight_epigraph
      (s := (Set.univ : Set P)) (f := perspective f)
      (by simpa using perspective_isConvex f) convex_univ
  refine ⟨convex_Ici (0 : 𝕜), ?_⟩
  intro t _ s _ a b ha hb hab
  have h := hpersp_convexOn.2 (x := (t, x)) (y := (s, x))
    (by simp) (by simp) ha hb hab
  have hxcomb : a • x + b • x = x := by
    rw [← add_smul, hab, one_smul]
  simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hxcomb] using h

/-- Bridge form of `perspectiveRayOnNonneg_isConvexOn`: convexity of the restricted epigraph. -/
theorem perspectiveRayOnNonneg_has_convex_epigraph
    (f : E → WithTopBot 𝕜) (x : E) :
    Convex 𝕜 (epi[𝕜≥0] (fun t ↦ perspective f (t, x))) := by
  exact (perspectiveRayOnNonneg_isConvexOn (f := f) x).convex_finiteHeight_epigraph

end RaysConvex

end
