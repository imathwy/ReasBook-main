import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

namespace Function

/-- Helper for Corollary 4.7.2: the scalar action on `WithBotTop α` scales finite values and
fixes the two boundary points. -/
local instance instSmulWithBotTop {𝕜 : Type u} {α : Type v} [SMul 𝕜 α] : SMul 𝕜 (WithBotTop α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

/-- Helper for Corollary 4.7.2: the local negation on `WithBotTop α` swaps the two boundary
points and negates finite values. -/
private def withBotTopNeg {α : Type v} [Neg α] : WithBotTop α → WithBotTop α
  | ⊥ => ⊤
  | (a : α) => (-a : α)
  | ⊤ => ⊥

/-- Helper for Corollary 4.7.2: the local `WithBotTop` negation extends the base negation. -/
local instance instNegWithBotTop {α : Type v} [Neg α] : Neg (WithBotTop α) := ⟨withBotTopNeg⟩

/-- Helper for Corollary 4.7.2: finite `WithBotTop` values negate coefficientwise. -/
@[simp] private theorem withBotTop_neg_coe {α : Type v} [Neg α] (a : α) :
    -((a : WithBotTop α)) = ((-a : α) : WithBotTop α) :=
  rfl

/-- Helper for Corollary 4.7.2: negation sends the top boundary point to the bottom one. -/
@[simp] private theorem withBotTop_neg_top {α : Type v} [Neg α] :
    -((⊤ : WithBotTop α)) = (⊥ : WithBotTop α) :=
  rfl

/-- Helper for Corollary 4.7.2: negation sends the bottom boundary point to the top one. -/
@[simp] private theorem withBotTop_neg_bot {α : Type v} [Neg α] :
    -((⊥ : WithBotTop α)) = (⊤ : WithBotTop α) :=
  rfl

/-- Helper for Corollary 4.7.2: a `WithBotTop α` value away from both boundary points is finite. -/
private theorem withBotTop_exists_coe_of_ne_top_ne_bot {α : Type v} {z : WithBotTop α}
    (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥) :
    ∃ a : α, (a : WithBotTop α) = z := by
  cases z using WithBotTop.rec with
  | bot =>
      exact False.elim (hz_bot rfl)
  | coe a =>
      exact ⟨a, rfl⟩
  | top =>
      exact False.elim (hz_top rfl)

local instance instDecidableLTCor472 (α : Type v) [LT α] : DecidableLT α :=
  Classical.decRel (fun a b => a < b)

/-- Helper for Corollary 4.7.2: the scalar action on `WithTopBot α` scales finite values and fixes
the two boundary points. -/
local instance instSmulWithTopBot {𝕜 : Type u} {α : Type v} [SMul 𝕜 α] : SMul 𝕜 (WithTopBot α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

/-- Helper for Corollary 4.7.2: reinterpret a `WithBotTop α` value in the `WithTopBot α`
boundary convention while preserving bottom, top, and finite values. -/
def withBotTopToWithTopBot {α : Type u} : WithBotTop α → WithTopBot α
  | ⊥ => ⊥
  | (a : α) => (a : WithTopBot α)
  | ⊤ => ⊤

/-- Helper for Corollary 4.7.2: the boundary-convention change sends `⊥` to `⊥`. -/
@[simp] theorem withBotTopToWithTopBot_bot {α : Type u} :
    withBotTopToWithTopBot (α := α) (⊥ : WithBotTop α) = (⊥ : WithTopBot α) :=
  rfl

/-- Helper for Corollary 4.7.2: the boundary-convention change fixes finite values. -/
@[simp] theorem withBotTopToWithTopBot_coe {α : Type u} (a : α) :
    withBotTopToWithTopBot (α := α) (a : WithBotTop α) = (a : WithTopBot α) :=
  rfl

/-- Helper for Corollary 4.7.2: the boundary-convention change sends `⊤` to `⊤`. -/
@[simp] theorem withBotTopToWithTopBot_top {α : Type u} :
    withBotTopToWithTopBot (α := α) (⊤ : WithBotTop α) = (⊤ : WithTopBot α) :=
  rfl

/-- Helper for Corollary 4.7.2: the boundary-convention change preserves the non-bottom
condition. -/
theorem withBotTopToWithTopBot_ne_bot_iff {α : Type u} {z : WithBotTop α} :
    withBotTopToWithTopBot z ≠ (⊥ : WithTopBot α) ↔ z ≠ (⊥ : WithBotTop α) := by
  -- Compare the three extended-value cases explicitly.
  cases z using WithBotTop.rec with
  | bot =>
      simp [withBotTopToWithTopBot]
  | coe a =>
      constructor
      · intro _
        simp
      · intro _ hz
        cases hz
  | top =>
      constructor
      · intro _ hz
        cases hz
      · intro _ hz
        cases hz

/-- Helper for Corollary 4.7.2: the boundary-convention change commutes with scalar
multiplication. -/
theorem withBotTopToWithTopBot_smul {𝕜 : Type u} {α : Type v} [SMul 𝕜 α]
    (c : 𝕜) (z : WithBotTop α) :
    withBotTopToWithTopBot (c • z) = c • withBotTopToWithTopBot z := by
  -- Both scalar actions were chosen to agree on each of the three cases.
  cases z using WithBotTop.rec with
  | bot =>
      rfl
  | coe a =>
      rfl
  | top =>
      rfl

/-- Helper for Corollary 4.7.2: when both summands avoid `⊥`, the boundary-convention change
commutes with addition. -/
theorem withBotTopToWithTopBot_add_of_ne_bot {α : Type u} [Add α]
    {a b : WithBotTop α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    withBotTopToWithTopBot (a + b) =
      withBotTopToWithTopBot a + withBotTopToWithTopBot b := by
  -- The only owner mismatch is the treatment of `⊥`, so exclude it first.
  cases a using WithBotTop.rec with
  | bot =>
      contradiction
  | coe a =>
      cases b using WithBotTop.rec with
      | bot =>
          contradiction
      | coe b =>
          rfl
      | top =>
          rfl
  | top =>
      cases b using WithBotTop.rec with
      | bot =>
          contradiction
      | coe b =>
          rfl
      | top =>
          rfl

/-- Helper for Corollary 4.7.2: the boundary-convention change preserves and reflects order. -/
theorem withBotTopToWithTopBot_le_iff {α : Type u} [Preorder α]
    {a b : WithBotTop α} :
    withBotTopToWithTopBot a ≤ withBotTopToWithTopBot b ↔ a ≤ b := by
  -- The two owners encode the same order once the boundary constructors are matched up.
  cases a using WithBotTop.rec with
  | bot =>
      cases b using WithBotTop.rec with
      | bot =>
          simp [withBotTopToWithTopBot]
      | coe b =>
          simp [withBotTopToWithTopBot]
      | top =>
          simp [withBotTopToWithTopBot]
  | coe a =>
      cases b using WithBotTop.rec with
      | bot =>
          constructor
          · intro h
            simp [withBotTopToWithTopBot] at h
            have h' : (a : WithBot α) ≤ (⊥ : WithBot α) := WithTop.coe_le_coe.mp h
            simp at h'
          · intro h
            simp at h
      | coe b =>
          constructor
          · intro h
            change (((a : WithBot α) : WithTop (WithBot α)) ≤
                ((b : WithBot α) : WithTop (WithBot α))) at h
            have h' : (a : WithBot α) ≤ (b : WithBot α) := WithTop.coe_le_coe.mp h
            simpa using h'
          · intro h
            change (((a : WithBot α) : WithTop (WithBot α)) ≤
                ((b : WithBot α) : WithTop (WithBot α)))
            have h' : (a : WithBot α) ≤ (b : WithBot α) := by
              simpa using h
            exact WithTop.coe_le_coe.mpr h'
      | top =>
          simp [withBotTopToWithTopBot]
  | top =>
      cases b using WithBotTop.rec with
      | bot =>
          constructor
          · intro h
            cases h
          · intro h
            cases h
      | coe b =>
          constructor
          · intro h
            simp [withBotTopToWithTopBot] at h
            cases h
          · intro h
            have h' : (⊤ : WithTop α) ≤ (b : WithTop α) := WithBot.coe_le_coe.mp h
            exact False.elim ((WithTop.not_top_le_coe _ h').elim)
      | top =>
          simp [withBotTopToWithTopBot]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 4.7.2 states that a positively homogeneous proper convex function
  satisfies the one-sided symmetry inequality `f (-x) ≥ -f x`.
- `core/canonical`: the owner abstractions are the chapter predicates
  `Function.PositivelyHomogeneous`,
  `Function.IsProper`, and `Function.IsConvex`.
- `bridge/view`: the proof only needs the pointwise `⊥`-exclusion hypothesis
  `∀ x, f x ≠ ⊥`, while the textbook properness phrasing is recovered as a thin companion from the
  owner consequence `Function.IsProper.ne_bot`.

Domain-style sampling used here:
- the chapter's global epigraph-convexity predicate for `WithBotTop 𝕜`-valued functions from
  `Theorem_4_2`;
- the properness owner `Function.IsProper` and its canonical consequence `Function.IsProper.ne_bot`
  from `Definition_4_6`;
- the positive-homogeneity pattern from `Definition_4_8` and the subadditivity equivalence from
  `Theorem_4_7`, adapted here to the canonical ordered extended codomain layer `WithBotTop 𝕜`.
- Primitive data vs derived API: the function `f` is primitive; positive homogeneity and convexity
  are the upstream owner inputs, while the one-sided symmetry inequality is derived API. The proof
  uses the properness owner only through `Function.IsProper.ne_bot`, so the main theorem is
  refined to the primitive pointwise `⊥`-exclusion hypothesis and the properness form is demoted
  to a thin companion. The proof uses no coordinate data, so the zero-at-origin lemma is kept at
  the weaker layer `[Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommMonoid E]
  [Module 𝕜 E]`, while the symmetry inequality adds only the extra structure it actually uses:
  `[DivisionRing 𝕜] [PosMulReflectLT 𝕜] [AddCommGroup E]`.
-/

section ZeroValue

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

/-- Helper for Corollary 4.7.2: a positively homogeneous `WithBotTop 𝕜`-valued function that is
nowhere equal to `⊥` takes nonnegative value at the origin. -/
theorem zero_le_apply_zero_of_positivelyHomogeneous {f : E → WithBotTop 𝕜}
    (hf_hom : f.PositivelyHomogeneous 𝕜) (hf_ne_bot : ∀ y : E, f y ≠ ⊥) :
    (0 : WithBotTop 𝕜) ≤ f 0 := by
  by_cases hzero_top : f 0 = ⊤
  · simp [hzero_top]
  · have hzero_ne_bot : f 0 ≠ ⊥ := hf_ne_bot 0
    rcases withBotTop_exists_coe_of_ne_top_ne_bot hzero_top hzero_ne_bot with ⟨a, ha⟩
    -- Positive homogeneity at the origin identifies the finite value `a` with `2 • a`.
    have hhom_zero : (a : WithBotTop 𝕜) = (2 : 𝕜) • (a : WithBotTop 𝕜) := by
      simpa [ha] using hf_hom.map_smul (zero_lt_two : (0 : 𝕜) < (2 : 𝕜)) (0 : E)
    -- Descend to `𝕜`, then cancel one copy of `a` to force `a = 0`.
    have hzero_eq : a = 0 := by
      rw [show
          (2 : 𝕜) • ((a : 𝕜) : WithBotTop 𝕜) = ((2 * a : 𝕜) : WithBotTop 𝕜) by
          rfl] at hhom_zero
      have htwo : a = 2 * a := by
        exact WithBotTop.coe_injective hhom_zero
      have hadd : a + a = a := by
        simpa [two_mul] using htwo.symm
      apply add_left_cancel (a := a)
      simpa [add_zero] using hadd
    -- The only finite possibility at the origin is `0`, so the claimed nonnegativity is immediate.
    rw [← ha, hzero_eq]
    exact le_rfl

end ZeroValue

section Transport

variable {𝕜 : Type v} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜] [PosMulMono 𝕜] [PosMulReflectLT 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

/-- Helper for Corollary 4.7.2: Theorem 4.7 transported from `WithTopBot` to the `WithBotTop`
owner used in this file. -/
theorem isConvex_iff_subadditive_of_positivelyHomogeneous_withBotTop
    {f : E → WithBotTop 𝕜} (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_ne_bot : ∀ y : E, f y ≠ ⊥) :
    f.IsConvex 𝕜 ↔ ∀ x y : E, f (x + y) ≤ f x + f y := by
  let g : E → WithTopBot 𝕜 := withBotTopToWithTopBot ∘ f
  have hg_hom : g.PositivelyHomogeneous 𝕜 := by
    intro a x
    -- Positive homogeneity survives the boundary-convention change.
    calc
      g (a • x) = withBotTopToWithTopBot (f (a • x)) := rfl
      _ = withBotTopToWithTopBot (a • f x) := by
        simpa using congrArg withBotTopToWithTopBot (hf_hom a x)
      _ = a • g x := by
        simpa [g] using withBotTopToWithTopBot_smul (c := a) (z := f x)
  have hg_ne_bot : ∀ y : E, g y ≠ ⊥ := by
    intro y
    -- The non-`⊥` hypothesis is owner-independent.
    simpa [g] using (withBotTopToWithTopBot_ne_bot_iff (z := f y)).2 (hf_ne_bot y)
  have hg_eq : (g : E → WithTopBot 𝕜) = (show E → WithTopBot 𝕜 from f) := by
    funext x
    -- As raw terms, `g` is just `f` read through the other boundary convention.
    change withBotTopToWithTopBot (f x) = (show WithTopBot 𝕜 from f x)
    cases hfx : f x using WithBotTop.rec with
    | bot =>
        rfl
    | coe a =>
        rfl
    | top =>
        rfl
  constructor
  · intro hf_conv
    have hg_conv : g.IsConvex 𝕜 := by
      simpa [hg_eq] using hf_conv
    have hsub_g :
        ∀ x y : E, g (x + y) ≤ g x + g y :=
      (isConvex_iff_subadditive_of_positivelyHomogeneous hg_hom hg_ne_bot).mp hg_conv
    intro x y
    have hxy :
        withBotTopToWithTopBot (f (x + y)) ≤
          withBotTopToWithTopBot (f x) + withBotTopToWithTopBot (f y) := by
      simpa [g] using hsub_g x y
    rw [← withBotTopToWithTopBot_add_of_ne_bot (hf_ne_bot x) (hf_ne_bot y)] at hxy
    exact (withBotTopToWithTopBot_le_iff (a := f (x + y)) (b := f x + f y)).mp hxy
  · intro hsub
    have hsub_g : ∀ x y : E, g (x + y) ≤ g x + g y := by
      intro x y
      have hxy :
          withBotTopToWithTopBot (f (x + y)) ≤
            withBotTopToWithTopBot (f x + f y) :=
        (withBotTopToWithTopBot_le_iff (a := f (x + y)) (b := f x + f y)).mpr (hsub x y)
      rw [withBotTopToWithTopBot_add_of_ne_bot (hf_ne_bot x) (hf_ne_bot y)] at hxy
      simpa [g] using hxy
    have hg_conv : g.IsConvex 𝕜 :=
      (isConvex_iff_subadditive_of_positivelyHomogeneous hg_hom hg_ne_bot).mpr hsub_g
    simpa [hg_eq] using hg_conv

end Transport

section Symmetry

variable {𝕜 : Type v} [DivisionRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [PosMulReflectLT 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-- Helper for Corollary 4.7.2: a positively homogeneous convex function satisfies the one-sided
symmetry inequality `f (-x) ≥ -f x` as soon as it is nowhere equal to `⊥`. This is the
owner-minimal form of the corollary; the textbook properness phrasing is recovered below as a thin
companion. -/
theorem apply_neg_ge_neg_apply {f : E → WithBotTop 𝕜}
    (hf_hom : f.PositivelyHomogeneous 𝕜) (hf_ne_bot : ∀ y : E, f y ≠ ⊥)
    (hf_convex : f.IsConvex 𝕜)
    (x : E) :
    f (-x) ≥ -f x := by
  have hsubadd :=
    (isConvex_iff_subadditive_of_positivelyHomogeneous_withBotTop hf_hom hf_ne_bot).mp
      hf_convex
  have hzero_nonneg : (0 : WithBotTop 𝕜) ≤ f 0 :=
    zero_le_apply_zero_of_positivelyHomogeneous hf_hom hf_ne_bot
  -- Source proof core: `f 0 ≤ f x + f (-x)` comes from subadditivity at `x + (-x) = 0`.
  have hsum_nonneg : (0 : WithBotTop 𝕜) ≤ f x + f (-x) := by
    simpa using hzero_nonneg.trans (by simpa using hsubadd x (-x))
  by_cases hfx_top : f x = ⊤
  · simp [hfx_top]
  · by_cases hnegx_top : f (-x) = ⊤
    · simp [hnegx_top]
    · have hx_ne_bot : f x ≠ ⊥ := hf_ne_bot x
      have hnegx_ne_bot : f (-x) ≠ ⊥ := hf_ne_bot (-x)
      rcases withBotTop_exists_coe_of_ne_top_ne_bot hfx_top hx_ne_bot with ⟨a, ha⟩
      rcases withBotTop_exists_coe_of_ne_top_ne_bot hnegx_top hnegx_ne_bot with ⟨b, hb⟩
      -- Once both values are finite, the extended inequality descends to the base field.
      have hsum_nonneg' : (0 : 𝕜) ≤ a + b := by
        have hsum_nonneg'' : ((0 : 𝕜) : WithBotTop 𝕜) ≤ ((a + b : 𝕜) : WithBotTop 𝕜) := by
          simpa [ha, hb] using hsum_nonneg
        exact WithBotTop.coe_le_coe.mp hsum_nonneg''
      have hneg_ab : -a ≤ b := by
        exact (neg_le_iff_add_nonneg).2 (by simpa [add_comm] using hsum_nonneg')
      -- Transport the scalar inequality back to `WithBotTop 𝕜`.
      have hneg : -(f x) ≤ f (-x) := by
        rw [← ha, ← hb]
        simpa using
          (WithBotTop.coe_le_coe.mpr hneg_ab :
            (((-a : 𝕜) : WithBotTop 𝕜) ≤ ((b : 𝕜) : WithBotTop 𝕜)))
      simpa [ha, hb, ge_iff_le] using hneg

/-- Corollary 4.7.2: if `f` is a positively homogeneous proper convex function, then
`f (-x) ≥ -f x` for every `x`. This companion adds no new mathematics: its only use of
`f.IsProper` is to recover the pointwise `⊥`-exclusion required by
`Function.apply_neg_ge_neg_apply`. -/
theorem apply_neg_ge_neg_apply_of_proper {f : E → WithBotTop 𝕜}
    (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) (x : E) :
    f (-x) ≥ -f x :=
  apply_neg_ge_neg_apply hf_hom hf_proper.ne_bot hf_convex x

end Symmetry

end Function

end
