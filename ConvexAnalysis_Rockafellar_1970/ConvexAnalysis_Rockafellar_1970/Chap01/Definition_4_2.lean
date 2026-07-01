import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Definition 4.2 characterizes convexity of an extended-valued function on a
  subset.
- `core/canonical`: the owner abstraction is mathlib's `ConvexOn 𝕜 C f` for
  `WithTopBot α`-valued functions on a set.
- `bridge/view`: the standard epigraph bridge is `convexOn_iff_convex_epigraph`.
- Primitive data vs derived API: the primitive inputs are a subset and an extended-order-valued
  function; the epigraph reformulation is derived API.
- Layer target: keep this file at the direct owner layer for Rockafellar's extended-valued
  functions.
-/

recall ConvexOn

/- The epigraph formulation is the canonical bridge theorem. -/
recall convexOn_iff_convex_epigraph

section ConvexOnCheck

variable {𝕜 E α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [PartialOrder α] [AddCommMonoid (WithTopBot α)]
variable [SMul 𝕜 (WithTopBot α)]

variable (f : E → WithTopBot α) (S : Set E)

/- Definition 4.2 uses the canonical owner predicate `ConvexOn`. -/
#check ConvexOn 𝕜 S f

end ConvexOnCheck

section

variable {𝕜 E α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedAddMonoid (WithTopBot α)]
variable [Module 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]

/-- Definition 4.2 in canonical owner language: for a `WithTopBot α`-valued map, convexity on
`C` is equivalent to convexity of its codomain-height epigraph. -/
theorem convexOn_withTopBot_iff_convex_epigraph {C : Set E} {f : E → WithTopBot α} :
    ConvexOn 𝕜 C f ↔ Convex 𝕜 {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
  simp [convexOn_iff_convex_epigraph (s := C) (f := f)]

end

noncomputable section FiniteHeightEpigraph

variable {𝕜 E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul := fun r x ↦ (r : WithTopBot 𝕜) * x

omit [IsStrictOrderedRing 𝕜] in
private theorem finite_weighted_sum_lt_withTopBot {a b d u v : 𝕜}
    (h :
      ((a : WithTopBot 𝕜) * (u : WithTopBot 𝕜)) +
          ((b : WithTopBot 𝕜) * (v : WithTopBot 𝕜)) <
        (d : WithTopBot 𝕜)) :
    a * u + b * v < d := by
  have h' :
      ((((a * u + b * v : 𝕜) : WithBot 𝕜) : WithTopBot 𝕜) <
        (d : WithTopBot 𝕜)) := by
    simpa [WithTopBot, WithTop.coe_add, WithTop.coe_mul, WithBot.coe_add, WithBot.coe_mul,
      mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h
  exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp h')

private theorem mul_le_mul_left_coe_withTopBot {a : 𝕜} (ha : 0 ≤ a)
    {u v : WithTopBot 𝕜} (h : u ≤ v) :
    (a : WithTopBot 𝕜) * u ≤ (a : WithTopBot 𝕜) * v := by
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
          have ha' : (0 : WithBot 𝕜) ≤ ((a : 𝕜) : WithBot 𝕜) :=
            WithBot.coe_le_coe.mpr ha
          exact WithTop.coe_le_coe.mpr (mul_le_mul_of_nonneg_left huv ha')

private theorem exists_pair_above_of_weighted_sum_lt_withTopBot
    {u v : WithTopBot 𝕜} {a b d : 𝕜}
    (ha : 0 < a) (hb : 0 < b)
    (h : (a : WithTopBot 𝕜) * u + (b : WithTopBot 𝕜) * v < d) :
    ∃ r t : 𝕜, u < r ∧ v < t ∧ a * r + b * t ≤ d := by
  induction u using WithTop.recTopCoe with
  | top =>
      exfalso
      simp [ha.ne'] at h
  | coe u =>
      induction u using WithBot.recBotCoe with
      | bot =>
          induction v using WithTop.recTopCoe with
          | top =>
              exfalso
              simp [hb.ne'] at h
          | coe v =>
              induction v using WithBot.recBotCoe with
              | bot =>
                  refine ⟨0, d / b, ?_, ?_, ?_⟩
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe 0)
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe (d / b))
                  · have hEq : a * 0 + b * (d / b) = d := by
                      field_simp [hb.ne']
                      ring
                    linarith
              | coe v =>
                  let t : 𝕜 := v + 1
                  let r : 𝕜 := (d - b * t) / a
                  refine ⟨r, t, ?_, ?_, ?_⟩
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe r)
                  · exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr (by simp [t]))
                  · have hEq : a * r + b * t = d := by
                      dsimp [r, t]
                      field_simp [ha.ne']
                      ring
                    linarith
      | coe u =>
          induction v using WithTop.recTopCoe with
          | top =>
              exfalso
              simp [hb.ne'] at h
          | coe v =>
              induction v using WithBot.recBotCoe with
              | bot =>
                  let r : 𝕜 := u + 1
                  let t : 𝕜 := (d - a * r) / b
                  refine ⟨r, t, ?_, ?_, ?_⟩
                  · exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr (by simp [r]))
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe t)
                  · have hEq : a * r + b * t = d := by
                      dsimp [r, t]
                      field_simp [hb.ne']
                      ring
                    linarith
              | coe v =>
                  have hreal : a * u + b * v < d :=
                    finite_weighted_sum_lt_withTopBot h
                  let δ : 𝕜 := d - (a * u + b * v)
                  let r : 𝕜 := u + δ / (2 * a)
                  let t : 𝕜 := v + δ / (2 * b)
                  have hδ : 0 < δ := by
                    dsimp [δ]
                    linarith
                  refine ⟨r, t, ?_, ?_, ?_⟩
                  · have hr_aux : 0 < δ / (2 * a) := by
                      dsimp [δ]
                      positivity
                    exact WithTop.coe_lt_coe.mpr
                      (WithBot.coe_lt_coe.mpr (by dsimp [r]; linarith))
                  · have ht_aux : 0 < δ / (2 * b) := by
                      dsimp [δ]
                      positivity
                    exact WithTop.coe_lt_coe.mpr
                      (WithBot.coe_lt_coe.mpr (by dsimp [t]; linarith))
                  · dsimp [r, t, δ]
                    have hsum :
                        a * (u + (d - (a * u + b * v)) / (2 * a)) +
                            b * (v + (d - (a * u + b * v)) / (2 * b)) =
                          a * u + b * v + (d - (a * u + b * v)) / 2 +
                            (d - (a * u + b * v)) / 2 := by
                      field_simp [ha.ne', hb.ne']
                      ring
                    rw [hsum]
                    linarith

/-- A `ConvexOn` map to `WithTopBot 𝕜` has a convex chapter epigraph `epi[s] f`. -/
theorem ConvexOn.convex_finiteHeight_epigraph {s : Set E} {f : E → WithTopBot 𝕜}
    (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 (epi[s] f) := by
  rw [epi_eq_setOf_mem_and_le]
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ (a : WithTopBot 𝕜) * f x + (b : WithTopBot 𝕜) * f y :=
      hf.2 hx hy ha hb hab
    _ ≤ (a : WithTopBot 𝕜) * (r : WithTopBot 𝕜) +
        (b : WithTopBot 𝕜) * (t : WithTopBot 𝕜) := by
      exact add_le_add
        (mul_le_mul_left_coe_withTopBot ha hr)
        (mul_le_mul_left_coe_withTopBot hb ht)
    _ = (a * r + b * t : 𝕜) := by
      simp [WithTop.coe_add, WithTop.coe_mul, WithBot.coe_add, WithBot.coe_mul]

/-- Convexity of the chapter epigraph recovers `ConvexOn` for `WithTopBot 𝕜`. -/
theorem convexOn_of_convex_finiteHeight_epigraph {s : Set E} {f : E → WithTopBot 𝕜}
    (h_epi : Convex 𝕜 (epi[s] f)) (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f := by
  have h_epi' : Convex 𝕜 {(x, y) : E × 𝕜 | x ∈ s ∧ f x ≤ y} := by
    simpa [epi_eq_setOf_mem_and_le] using h_epi
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  change f (a • x + b • y) ≤ (a : WithTopBot 𝕜) * f x + (b : WithTopBot 𝕜) * f y
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by
      linarith
    subst b
    simp
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by
      linarith
    subst a
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let rhs : WithTopBot 𝕜 := (a : WithTopBot 𝕜) * f x + (b : WithTopBot 𝕜) * f y
  refine (WithTop.le_of_forall_lt_iff_le).1 ?_
  intro z hz
  induction z using WithBot.recBotCoe with
  | bot =>
      exact (not_lt_of_ge bot_le hz).elim
  | coe d =>
      obtain ⟨r, t, hur, hvt, hsum⟩ :=
        exists_pair_above_of_weighted_sum_lt_withTopBot ha_pos hb_pos hz
      have hx_epi : (x, r) ∈ {(x, y) : E × 𝕜 | x ∈ s ∧ f x ≤ y} := ⟨hx, hur.le⟩
      have hy_epi : (y, t) ∈ {(x, y) : E × 𝕜 | x ∈ s ∧ f x ≤ y} := ⟨hy, hvt.le⟩
      have hcombo := h_epi' hx_epi hy_epi ha hb hab
      have hcombo' : f (a • x + b • y) ≤ (a * r + b * t : 𝕜) := by
        simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm,
          add_assoc] using hcombo.2
      calc
        f (a • x + b • y) ≤ (a * r + b * t : 𝕜) := hcombo'
        _ ≤ (d : WithTopBot 𝕜) := by
          exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr hsum)

/-- Definition 4.2 finite-height epigraph form: for `WithTopBot 𝕜`-valued maps over an ordered
field, `ConvexOn` is equivalent to convexity of the chapter finite-height epigraph together with
convexity of the base set. -/
theorem convexOn_withTopBot_iff_convex_finiteHeight_epigraph
    {s : Set E} {f : E → WithTopBot 𝕜} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 (epi[s] f) ∧ Convex 𝕜 s := by
  constructor
  · intro h
    exact ⟨h.convex_finiteHeight_epigraph, h.1⟩
  · intro h
    exact convexOn_of_convex_finiteHeight_epigraph h.1 h.2

end FiniteHeightEpigraph
