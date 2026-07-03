import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_4_7_1 (from Chap01) -/
open scoped BigOperators

universe u v w z

noncomputable section

namespace Function

/-- Helper for Corollary 4.7.1: the canonical scalar action on `WithBotTop α` scales finite values
and fixes both boundary points. -/
local instance instSMulWithBotTopCorollary471 {𝕜 : Type u} {α : Type v} [SMul 𝕜 α] :
    SMul 𝕜 (WithBotTop α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

/-- Helper for Corollary 4.7.1: the transported `WithTopBot α` owner uses the matching scalar
action that scales finite values and fixes both boundary points. -/
local instance instSMulWithTopBotCorollary471 {𝕜 : Type u} {α : Type v} [SMul 𝕜 α] :
    SMul 𝕜 (WithTopBot α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

local instance instDecidableLTCorollary471 (α : Type u) [LT α] : DecidableLT α :=
  Classical.decRel (fun a b => a < b)

/-- Helper for Corollary 4.7.1: reinterpret a `WithBotTop α` value in the `WithTopBot α`
boundary convention while preserving the mathematical bottom, top, and finite values. -/
def withBotTopToWithTopBot {α : Type u} : WithBotTop α → WithTopBot α
  | ⊥ => ⊥
  | (a : α) => (a : WithTopBot α)
  | ⊤ => ⊤

/-- Helper for Corollary 4.7.1: the boundary-preserving convention change sends `⊥` to `⊥`. -/
@[simp] theorem withBotTopToWithTopBot_bot {α : Type u} :
    withBotTopToWithTopBot (α := α) (⊥ : WithBotTop α) = (⊥ : WithTopBot α) :=
  rfl

/-- Helper for Corollary 4.7.1: the boundary-preserving convention change fixes finite values. -/
@[simp] theorem withBotTopToWithTopBot_coe {α : Type u} (a : α) :
    withBotTopToWithTopBot (α := α) (a : WithBotTop α) = (a : WithTopBot α) :=
  rfl

/-- Helper for Corollary 4.7.1: the boundary-preserving convention change sends `⊤` to `⊤`. -/
@[simp] theorem withBotTopToWithTopBot_top {α : Type u} :
    withBotTopToWithTopBot (α := α) (⊤ : WithBotTop α) = (⊤ : WithTopBot α) :=
  rfl

/-- Helper for Corollary 4.7.1: the owner-change map agrees with the canonical cast into
`WithTopBot α`. -/
theorem withBotTopToWithTopBot_eq_cast {α : Type u} (z : WithBotTop α) :
    withBotTopToWithTopBot z = (show WithTopBot α from z) := by
  -- Compare the three extended-value cases directly; only the owner notation changes.
  cases z using WithBotTop.rec with
  | bot =>
      simpa [withBotTopToWithTopBot]
  | coe a =>
      rfl
  | top =>
      simpa [withBotTopToWithTopBot]

/-- Helper for Corollary 4.7.1: the boundary-preserving convention change preserves the
non-bottom condition. -/
theorem withBotTopToWithTopBot_ne_bot_iff {α : Type u} {z : WithBotTop α} :
    withBotTopToWithTopBot z ≠ (⊥ : WithTopBot α) ↔ z ≠ (⊥ : WithBotTop α) := by
  -- Split on the three extended-value cases and compare the boundary constructors explicitly.
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

/-- Helper for Corollary 4.7.1: the boundary-convention change commutes with scalar
multiplication. -/
theorem withBotTopToWithTopBot_smul {𝕜 : Type u} {α : Type v} [SMul 𝕜 α]
    (c : 𝕜) (z : WithBotTop α) :
    withBotTopToWithTopBot (c • z) = c • withBotTopToWithTopBot z := by
  -- Split on the three extended-value cases; both scalar actions were chosen to agree pointwise.
  cases z using WithBotTop.rec with
  | bot =>
      rfl
  | coe a =>
      rfl
  | top =>
      rfl

/-- Helper for Corollary 4.7.1: when neither summand is `⊥`, the boundary-convention change
commutes with addition. -/
theorem withBotTopToWithTopBot_add_of_ne_bot {α : Type u} [Add α]
    {a b : WithBotTop α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    withBotTopToWithTopBot (a + b) =
      withBotTopToWithTopBot a + withBotTopToWithTopBot b := by
  -- The only mismatch between the two owners is the treatment of `⊥`, so we exclude it first.
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

/-- Helper for Corollary 4.7.1: the boundary-convention change is order-preserving and
order-reflecting. -/
theorem withBotTopToWithTopBot_le_iff {α : Type u} [Preorder α]
    {a b : WithBotTop α} :
    withBotTopToWithTopBot a ≤ withBotTopToWithTopBot b ↔ a ≤ b := by
  -- Compare the three boundary cases explicitly; the two owners encode the same raw order data.
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
            -- Reduce the outer `WithTop` comparison, then the inner `WithBot` comparison.
            change (((a : WithBot α) : WithTop (WithBot α)) ≤
                ((b : WithBot α) : WithTop (WithBot α))) at h
            have h' : (a : WithBot α) ≤ (b : WithBot α) := WithTop.coe_le_coe.mp h
            simpa using h'
          · intro h
            -- Rebuild the order proof by reversing the two coercion bridges.
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
Source/core/bridge triage:

- `source-facing`: Corollary 4.7.1 states that a positively homogeneous convex function satisfies
  the finite positive-weight inequality
  `f (∑ λᵢ xᵢ) ≤ ∑ λᵢ f (xᵢ)`.
- `core/canonical`: the primitive finite-sum owner theorem is stated at the subadditivity layer:
  positive homogeneity plus two-point additive sublinearity imply the finite positive-weight
  inequality in an arbitrary ordered additive codomain. The source-facing convex statement is then
  a thin `WithBotTop` corollary via Theorem 4.7.
- `bridge/view`: concrete ambient-model specializations are downstream corollaries. The
  finite-weight inequality itself is derived directly in the owner codomain by combining two-point
  subadditivity with induction on the nonempty finset `t`.

Domain-style sampling used here:
- the chapter owner predicate `Function.IsConvex` on `f`;
- the chapter owner theorem
  `Function.isConvex_iff_subadditive_of_positivelyHomogeneous`;
- the chapter owner predicate `Function.PositivelyHomogeneous` on `f`.

Primitive data vs derived API:
- primitive input: the function `f : E → F` and the finite family `(t, w, x)`;
  - owner data: `f.PositivelyHomogeneous 𝕜` together with two-point subadditivity
  `∀ u v, f (u + v) ≤ f u + f v`;
  - derived API: the convex/source-facing corollary obtained from Theorem 4.7 by adding
  `f.IsConvex 𝕜` and the non-`⊥` side condition.
-/

section SubadditiveSum

variable {𝕜 : Type u} [LT 𝕜] [Zero 𝕜]
variable {E : Type v} [AddCommMonoid E] [SMul 𝕜 E]
variable {F : Type z} [AddCommMonoid F] [Preorder F] [AddLeftMono F] [SMul 𝕜 F]
variable {ι : Type w}

-- Proof sketch for the primitive owner theorem: induction on the nonempty finset `t` together
-- with two-point subadditivity yields
-- `f (∑ i∈t, w i • x i) ≤ ∑ i∈t, f (w i • x i)`. Positive homogeneity rewrites each summand
-- `f (w i • x i)` as `w i • f (x i)`.
/-- Primitive finite-sum owner theorem: a positively homogeneous subadditive function satisfies the
finite positive-weight inequality on every nonempty finite family. -/
theorem PositivelyHomogeneous.map_sum_le_of_subadditive
    {f : E → F} (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hsub_add : ∀ u v : E, f (u + v) ≤ f u + f v)
    (t : Finset ι) (w : ι → 𝕜) (x : ι → E)
    (ht : t.Nonempty) (hw : ∀ i ∈ t, 0 < w i) :
    f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i • f (x i) := by
  have hsum : f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, f (w i • x i) := by
    refine ht.cons_induction ?_ ?_
    · intro a
      simp
    · intro a s ha hs ih
      calc
        f (∑ i ∈ Finset.cons a s ha, w i • x i) = f (w a • x a + ∑ i ∈ s, w i • x i) := by
          simp
        _ ≤ f (w a • x a) + f (∑ i ∈ s, w i • x i) := hsub_add _ _
        _ ≤ f (w a • x a) + ∑ i ∈ s, f (w i • x i) := add_le_add_right ih _
        _ = ∑ i ∈ Finset.cons a s ha, f (w i • x i) := by
          simp
  have hsmul :
      ∀ i ∈ t, f (w i • x i) = w i • f (x i) := by
    intro i hi
    simpa using hf_hom.map_smul (hw i hi) (x i)
  calc
    f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, f (w i • x i) := hsum
    _ = ∑ i ∈ t, w i • f (x i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hsmul i hi

end SubadditiveSum

section ConvexCorollary

variable {𝕜 : Type u} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜] [PosMulMono 𝕜]
variable {E : Type v} [AddCommMonoid E] [Module 𝕜 E]
variable {ι : Type w}

/-- Helper for Corollary 4.7.1: Theorem 4.7 transported to the `WithBotTop` owner by swapping the
boundary convention exactly once. -/
theorem isConvex_iff_subadditive_of_positivelyHomogeneous_withBotTop
    [PosMulReflectLT 𝕜]
    {f : E → WithBotTop 𝕜} (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_ne_bot : ∀ y : E, f y ≠ ⊥) :
    f.IsConvex 𝕜 ↔ ∀ x y : E, f (x + y) ≤ f x + f y := by
  let g : E → WithTopBot 𝕜 := withBotTopToWithTopBot ∘ f
  have hg_hom : g.PositivelyHomogeneous 𝕜 := by
    intro a x
    -- Positive homogeneity is preserved by the boundary-convention change.
    calc
      g (a • x) = withBotTopToWithTopBot (f (a • x)) := rfl
      _ = withBotTopToWithTopBot (a • f x) := by
        simpa using congrArg withBotTopToWithTopBot (hf_hom a x)
      _ = a • g x := by
        simpa [g] using withBotTopToWithTopBot_smul (c := a) (z := f x)
  have hg_ne_bot : ∀ y : E, g y ≠ ⊥ := by
    intro y
    -- The imported theorem only needs the pointwise non-`⊥` hypothesis, which transports directly.
    simpa [g] using (withBotTopToWithTopBot_ne_bot_iff (z := f y)).2 (hf_ne_bot y)
  have hg_eq : (g : E → WithTopBot 𝕜) = (show E → WithTopBot 𝕜 from f) := by
    funext x
    -- As raw terms, `g` is just `f` read in the `WithTopBot` owner.
    simpa [g] using withBotTopToWithTopBot_eq_cast (z := f x)
  constructor
  · intro hf_conv
    have hg_conv : g.IsConvex 𝕜 := by
      -- The statement hypothesis already records convexity on the transported `WithTopBot` owner.
      simpa [hg_eq] using hf_conv
    have hsub_g :
        ∀ x y : E, g (x + y) ≤ g x + g y :=
      (isConvex_iff_subadditive_of_positivelyHomogeneous hg_hom hg_ne_bot).mp hg_conv
    intro x y
    have hxy :
        withBotTopToWithTopBot (f (x + y)) ≤
          withBotTopToWithTopBot (f x) + withBotTopToWithTopBot (f y) := by
      -- Apply Theorem 4.7 on the transported owner and rewrite back to `f`.
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
      -- Rewrite the right-hand side back into the `WithTopBot` addition used by Theorem 4.7.
      rw [withBotTopToWithTopBot_add_of_ne_bot (hf_ne_bot x) (hf_ne_bot y)] at hxy
      simpa [g] using hxy
    have hg_conv : g.IsConvex 𝕜 :=
      (isConvex_iff_subadditive_of_positivelyHomogeneous hg_hom hg_ne_bot).mpr hsub_g
    -- Pull convexity back along the owner-identification `g = f`.
    simpa [hg_eq] using hg_conv

-- Proof sketch for the source-facing corollary: recover two-point subadditivity from Theorem 4.7
-- and invoke the primitive owner theorem above.
/-- Corollary 4.7.1, stated coordinate-free: a positively homogeneous convex function satisfies the
finite positive-weight subadditivity inequality for every nonempty finite family of points.
-/
theorem PositivelyHomogeneous.map_sum_le
    [PosMulReflectLT 𝕜]
    {f : E → WithBotTop 𝕜} (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_ne_bot : ∀ y : E, f y ≠ ⊥) (hf_conv : f.IsConvex 𝕜)
    (t : Finset ι) (w : ι → 𝕜) (x : ι → E)
    (ht : t.Nonempty) (hw : ∀ i ∈ t, 0 < w i) :
    f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i • f (x i) := by
  -- Route correction: the direct Theorem 4.7 specialization reads `⊥`/`⊤` in the wrong owner.
  -- First transport convexity to subadditivity on `WithBotTop`, then use the primitive sum lemma.
  have hsub :
      ∀ u v : E, f (u + v) ≤ f u + f v :=
    (isConvex_iff_subadditive_of_positivelyHomogeneous_withBotTop hf_hom hf_ne_bot).mp hf_conv
  -- Once two-point subadditivity is available on the current owner, the finite-sum theorem closes.
  exact hf_hom.map_sum_le_of_subadditive hsub t w x ht hw

end ConvexCorollary

end Function

/-! ### Corollary_4_7_2 (from Chap01) -/
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

/-! ### Example_4_7_2 (from Chap01) -/
noncomputable section

open scoped Rockafellar

section

variable {𝕜 : Type*} [LinearOrder 𝕜]

section RingLayer

variable [Ring 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item gives an explicit `[-∞, +∞]`-valued function on a one-dimensional
  ordered scalar line.
- `core/canonical`: the owner abstractions are `indicator` for the `0/+∞` boundary term,
  `Function.IsConvex` from `Theorem_4_2`, with properness governed by `Function.IsProper` from
  Definition 4.6.
- `bridge/view`: the source-facing example keeps the genuinely new `-∞` interior branch explicit,
  while the boundary/outside behavior is expressed through the chapter owner
  `δ[𝕜](· | {x : 𝕜 | |x| = 1})`; convexity remains owner-level API, while improperness is
  expressed directly as failure of `Function.IsProper`.
- Primitive data vs derived API: the primitive datum is the source-facing interior `-∞` branch
  together with the owner-side boundary indicator. Regionwise evaluation on `|x| < 1`, `|x| = 1`,
  and `1 < |x|` is derived theorem-level API, and convexity/properness stay at the chapter owner
  level rather than being repackaged locally.

Domain-style sampling used here:
- the project declaration `indicator` from `Defintion_4_8_1`;
- the project declaration `Function.IsConvex` from `Theorem_4_2`;
- the project declaration `Function.IsProper` from `Definition_4_6`, whose negation gives the
  source meaning of improperness;
- the chapter codomain owner layer `WithBotTop 𝕜` for `[-∞, +∞]`-valued functions.
-/

/-- Example 4.7.2 in canonical owner form: the function on a one-dimensional ordered scalar line
that equals `-∞` on `|x| < 1`, equals `0` on `|x| = 1`, and equals `+∞` on `|x| > 1`.
Specializing `𝕜 = ℝ` recovers the textbook statement. -/
def example_4_7_2 : 𝕜 → WithBotTop 𝕜 :=
  fun x ↦
    if |x| < 1 then
      ⊥
    else
      δ[𝕜](x | {y : 𝕜 | |y| = 1})

/-- On the open interval `(-1, 1)`, `example_4_7_2` takes the value `-∞`. -/
@[simp] theorem example_4_7_2_apply_of_abs_lt_one {x : 𝕜} (hx : |x| < 1) :
    example_4_7_2 x = ⊥ := by
  simp [example_4_7_2, hx]

/-- On the boundary points `|x| = 1`, `example_4_7_2` takes the value `0`. -/
@[simp] theorem example_4_7_2_apply_of_abs_eq_one {x : 𝕜} (hx : |x| = 1) :
    example_4_7_2 x = 0 := by
  rw [example_4_7_2, if_neg (by simp [hx])]
  simp [hx]

/-- Outside the closed interval `[-1, 1]`, `example_4_7_2` takes the value `+∞`. -/
@[simp] theorem example_4_7_2_apply_of_one_lt_abs {x : 𝕜} (hx : 1 < |x|) :
    example_4_7_2 x = ⊤ := by
  have hlt : ¬ |x| < 1 := not_lt_of_ge hx.le
  have hne : |x| ≠ 1 := ne_of_gt hx
  rw [example_4_7_2, if_neg hlt]
  simp [hne]

private theorem abs_le_one_of_example_4_7_2_lt {x α : 𝕜} (hx : example_4_7_2 x < α) :
    |x| ≤ 1 := by
  by_contra h
  have h' : 1 < |x| := lt_of_not_ge h
  simp [example_4_7_2_apply_of_one_lt_abs h'] at hx

private theorem example_4_7_2_apply_one [IsOrderedRing 𝕜] :
    example_4_7_2 (1 : 𝕜) = (0 : WithBotTop 𝕜) := by
  exact example_4_7_2_apply_of_abs_eq_one (x := (1 : 𝕜)) (abs_one : |(1 : 𝕜)| = 1)

section Strict

variable [IsStrictOrderedRing 𝕜]

-- Proof sketch: use the explicit values of `example_4_7_2`. It takes the value `⊥` on every
-- `x` with `|x| < 1`, so it fails `Function.IsProper`.
/-- The function from Example 4.7.2 is improper. -/
theorem example_4_7_2_isImproper :
    ¬ (example_4_7_2 : 𝕜 → WithBotTop 𝕜).IsProper := by
  intro hproper
  have hzero : example_4_7_2 (0 : 𝕜) = ⊥ := by
    have hlt : |(0 : 𝕜)| < 1 := by simp
    exact example_4_7_2_apply_of_abs_lt_one hlt
  have hbot : (⊥ : WithBotTop 𝕜) < example_4_7_2 (0 : 𝕜) :=
    Function.IsProper.bot_lt hproper (0 : 𝕜)
  rw [hzero] at hbot
  exact lt_irrefl _ hbot

end Strict

-- Proof sketch: evaluate at `x = 1`, where the defining middle branch gives the finite value `0`,
-- so the function cannot coincide with the constant `⊤` function.
/-- The function from Example 4.7.2 is not identically `+∞`. -/
theorem example_4_7_2_ne_top [IsOrderedRing 𝕜] :
    example_4_7_2 ≠ (⊤ : 𝕜 → WithBotTop 𝕜) := by
  intro h
  have hval : example_4_7_2 (1 : 𝕜) = (0 : WithBotTop 𝕜) := example_4_7_2_apply_one
  have htop : (0 : WithBotTop 𝕜) = ⊤ := by
    simpa [hval] using congrFun h (1 : 𝕜)
  exact (WithBotTop.coe_ne_top (0 : 𝕜)) htop

-- Proof sketch: evaluate at `x = 1`, where the defining middle branch gives `0`, or at `x = 2`,
-- where the outer branch gives `⊤`; either value differs from `⊥`, so the function is not
-- constantly `⊥`.
/-- The function from Example 4.7.2 is not identically `-∞`. -/
theorem example_4_7_2_ne_bot [IsOrderedRing 𝕜] :
    example_4_7_2 ≠ (⊥ : 𝕜 → WithBotTop 𝕜) := by
  intro h
  have hval : example_4_7_2 (1 : 𝕜) = (0 : WithBotTop 𝕜) := example_4_7_2_apply_one
  have hbot : (0 : WithBotTop 𝕜) = ⊥ := by
    simpa [hval] using congrFun h (1 : 𝕜)
  exact (WithBotTop.coe_ne_bot (0 : 𝕜)) hbot

end RingLayer

section ConvexLayer

variable [CommRing 𝕜] [IsStrictOrderedRing 𝕜]

private theorem affine_upper_bound_pos_of_example_4_7_2_boundary
    {x y α β t : 𝕜} (hx : example_4_7_2 x < α) (hy : example_4_7_2 y < β)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hz : |(1 - t) * x + t * y| = 1) :
    0 < (1 - t) * α + t * β := by
  have hx_bounds : -1 ≤ x ∧ x ≤ 1 := abs_le.mp <| abs_le_one_of_example_4_7_2_lt hx
  have hy_bounds : -1 ≤ y ∧ y ≤ 1 := abs_le.mp <| abs_le_one_of_example_4_7_2_lt hy
  rcases (abs_eq (show 0 ≤ (1 : 𝕜) by positivity)).mp hz with hz1 | hz1
  · have hx_eq : x = 1 := by
      nlinarith [hx_bounds.2, hy_bounds.2, ht0, ht1, hz1]
    have hy_eq : y = 1 := by
      nlinarith [hx_bounds.2, hy_bounds.2, ht0, ht1, hz1]
    have hx_pos : 0 < α := by
      exact WithBotTop.coe_pos.mp (by simpa [hx_eq] using hx)
    have hy_pos : 0 < β := by
      exact WithBotTop.coe_pos.mp (by simpa [hy_eq] using hy)
    nlinarith
  · have hx_eq : x = -1 := by
      nlinarith [hx_bounds.1, hy_bounds.1, ht0, ht1, hz1]
    have hy_eq : y = -1 := by
      nlinarith [hx_bounds.1, hy_bounds.1, ht0, ht1, hz1]
    have hx_pos : 0 < α := by
      exact WithBotTop.coe_pos.mp (by simpa [hx_eq] using hx)
    have hy_pos : 0 < β := by
      exact WithBotTop.coe_pos.mp (by simpa [hy_eq] using hy)
    nlinarith

-- Proof sketch: apply the owner theorem `Function.isConvex_iff_lt_affine_upper_bound`. If the
-- interpolated point stays in `|x| < 1`, the value is `⊥`. If it lands on `|x| = 1`, positivity
-- of the affine upper bound forces both endpoints to lie at the same boundary point `±1`, so the
-- interpolated value is `0` and still lies strictly below the target real height.
/-- The function from Example 4.7.2 is convex. -/
theorem example_4_7_2_isConvex [DenselyOrdered 𝕜] :
    Function.IsConvex 𝕜 (example_4_7_2 : 𝕜 → WithBotTop 𝕜) := by
  rw [Function.isConvex_iff_lt_affine_upper_bound (f := (example_4_7_2 : 𝕜 → WithBotTop 𝕜))]
  intro x y α β t hx hy ht0 ht1
  let z : 𝕜 := (1 - t) • x + t • y
  have hz_le : |z| ≤ 1 := by
    have hx_le : |x| ≤ 1 := abs_le_one_of_example_4_7_2_lt hx
    have hy_le : |y| ≤ 1 := abs_le_one_of_example_4_7_2_lt hy
    have ht_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht1.le
    dsimp [z]
    calc
      |(1 - t) * x + t * y| ≤ |(1 - t) * x| + |t * y| := abs_add_le _ _
      _ = (1 - t) * |x| + t * |y| := by
        rw [abs_mul, abs_of_nonneg ht_nonneg, abs_mul, abs_of_nonneg ht0.le]
      _ ≤ (1 - t) * 1 + t * 1 := by
        gcongr
      _ = 1 := by ring
  rcases lt_or_eq_of_le hz_le with hz_lt | hz_eq
  · rw [show example_4_7_2 z = ⊥ from example_4_7_2_apply_of_abs_lt_one hz_lt]
    simpa only [z, smul_eq_mul] using
      (show (⊥ : WithBotTop 𝕜) < (((1 - t) * α + t * β : 𝕜) : WithBotTop 𝕜) from
        WithBot.bot_lt_coe _)
  · have hpos : 0 < (1 - t) * α + t * β :=
      affine_upper_bound_pos_of_example_4_7_2_boundary hx hy ht0 ht1 <| by
        simpa [z, smul_eq_mul] using hz_eq
    rw [show example_4_7_2 z = 0 from example_4_7_2_apply_of_abs_eq_one hz_eq]
    simpa only using (WithBotTop.coe_pos.2 hpos)

end ConvexLayer

end

/-! ### Definition_4_7 (from Chap01) -/
universe u v

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item introduces the adjective "improper" for a convex function that fails to
  be proper.
- `core/canonical`: the owner predicate is `Function.IsProper` on functions `f : E → β`, with only
  the codomain order/top/bottom data required by the owner and its domain notation.
- `bridge/view`: the source adjective carries no new owner data; downstream statements should use
  the direct negation `¬ f.IsProper` rather than a parallel alias.
- Layer target: `bridge/view`, since this item only names the negation of the owner predicate from
  Definition 4.6 and should not introduce a second public owner.

Mathlib/project sampling used here:
- `Function.IsProper` from the immediately preceding item `Definition_4_6`;
- the specification theorem `Function.isProper_iff` for that owner;
- the consequence `Function.IsProper.bot_lt`, used as a derived strict-lower-bound bridge when the
  codomain has an order bottom.
- Primitive data vs derived API: there is no new primitive owner here. The source-facing adjective
  "improper" is only the direct negation of the existing properness owner.
-/

namespace Function

variable {E : Type u} {β : Type v}

/-- Canonical bridge for Definition 4.7: a function is improper exactly when it fails either
primitive clause in `Function.IsProper` (nonempty effective domain and nowhere `⊥`). -/
theorem not_isProper_iff [LT β] [Top β] [Bot β] (f : E → β) :
    (¬ f.IsProper) ↔ ¬ dom(f).Nonempty ∨ ∃ x, f x = ⊥ := by
  rw [isProper_iff, not_and_or, not_forall]
  simp

/-- Bridge form of Definition 4.7 using `dom(f) = ∅`. -/
theorem not_isProper_iff_dom_eq_empty_or_exists_eq_bot
    [LT β] [Top β] [Bot β] (f : E → β) :
    (¬ f.IsProper) ↔ dom(f) = ∅ ∨ ∃ x, f x = ⊥ := by
  simpa [Set.not_nonempty_iff_eq_empty] using (not_isProper_iff f)

/-- Logical form of Definition 4.7 using failure of domain nonemptiness. -/
theorem not_isProper_iff_not_nonempty_dom_or_exists_eq_bot
    [LT β] [Top β] [Bot β] (f : E → β) :
    (¬ f.IsProper) ↔ ¬ dom(f).Nonempty ∨ ∃ x, f x = ⊥ := by
  simpa using (not_isProper_iff f)

/-- Bridge form of improperness phrased by failure of strict lower bound and `dom(f) = ∅`. -/
theorem not_isProper_iff_dom_eq_empty_or_exists_not_bot_lt
    [PartialOrder β] [Top β] [OrderBot β] (f : E → β) :
    (¬ f.IsProper) ↔ dom(f) = ∅ ∨ ∃ x, ¬ ⊥ < f x := by
  simpa [bot_lt_iff_ne_bot] using
    (not_isProper_iff_dom_eq_empty_or_exists_eq_bot (f := f))

end Function

/-! ### Theorem_4_7 (from Chap01) -/
noncomputable section

open scoped Pointwise

universe u v w

section

namespace Function

variable {𝕜 : Type v} {α : Type w}

/-- Helper for Theorem 4.7: the canonical scalar action on `WithTopBot α` acts on finite values
and fixes the two boundary points. -/
local instance instSMulWithTopBot [SMul 𝕜 α] : SMul 𝕜 (WithTopBot α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

/-- Helper for Theorem 4.7: the chapter owner `Function.IsConvex` is convexity of the finite-height
epigraph. This local file keeps the owner surface available without routing through the broken
`Theorem_4_2` module. -/
abbrev IsConvex (𝕜 : Type v) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {α : Type w} [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

/-- Helper for Theorem 4.7: a `WithTopBot α` value that is neither `⊤` nor `⊥` is represented by
some finite height `a : α`. -/
private theorem exists_coe_of_ne_top_ne_bot
    {α : Type w} {z : WithTopBot α} (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥) :
    ∃ a : α, (a : WithTopBot α) = z := by
  cases hz : z using WithTop.recTopCoe with
  | top =>
      exact False.elim (hz_top hz)
  | coe z' =>
      cases hz' : z' using WithBot.recBotCoe with
      | bot =>
          exact False.elim (hz_bot (by simp [hz, hz']))
      | coe a =>
          exact ⟨a, rfl⟩

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 4.7 says that for a positively homogeneous function
  `f : E → [-∞, +∞]`, convexity is equivalent to subadditivity.
- `core/canonical`: the governing object is the finite-height epigraph `epi f`; the owner
  predicate `Function.IsConvex` is just `Convex 𝕜 (epi f)`.
- `bridge/view`: positive homogeneity makes `epi f` a cone, and subadditivity is equivalent to
  closure of `epi f` under addition. Theorem 2.6 then identifies convexity of that cone with
  additive closure.
- Primitive data vs derived API: the primitive datum is the function `f`; positive homogeneity and
  the non-`⊥` side condition are source-facing hypotheses, while convexity and subadditivity are
  derived viewpoints on the same epigraph geometry.
-/

section Cone

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type w} [PartialOrder α] [SMul 𝕜 α]
variable [PosSMulMono 𝕜 α]

/-- Helper for Theorem 4.7: the finite-height epigraph of a positively homogeneous function is a
cone. -/
theorem isCone_epi_of_positivelyHomogeneous
    {f : E → WithTopBot α} (hf_hom : f.PositivelyHomogeneous 𝕜) :
    Set.IsCone 𝕜 (epi f) := by
  intro c hc p hp
  rcases p with ⟨x, μ⟩
  rw [mem_epi_iff] at hp ⊢
  -- Positive homogeneity rewrites the function value, then scalar monotonicity lifts the height
  -- inequality to the scaled point.
  calc
    f (c • x) = c • f x := by simpa using hf_hom.map_smul hc x
    _ ≤ c • μ := by
      match hfx : f x with
      | ⊥ =>
          have hfx_bot : f x = ⊥ := by
            simpa using hfx
          change (⊥ : WithTopBot α) ≤ ((c • μ : α) : WithTopBot α)
          exact bot_le
      | (a : α) =>
          have hfx_coe : f x = (a : WithTopBot α) := by
            simpa using hfx
          have hle' : (a : WithTopBot α) ≤ (μ : WithTopBot α) := by
            simpa [hfx_coe] using hp
          have hle : a ≤ μ := by
            exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp hle')
          have hsmul : c • ((a : α) : WithTopBot α) ≤ c • ((μ : α) : WithTopBot α) := by
            change ((c • a : α) : WithTopBot α) ≤ ((c • μ : α) : WithTopBot α)
            exact WithTop.coe_le_coe.mpr
              (WithBot.coe_le_coe.mpr (smul_le_smul_of_nonneg_left hle hc.le))
          simpa [hfx_coe] using hsmul
      | ⊤ =>
          have hfx_top : f x = ⊤ := by
            simpa using hfx
          rw [hfx_top] at hp
          have hnot : ¬ ((⊤ : WithTopBot α) ≤ (μ : WithTopBot α)) := by
            simp
          exact False.elim (hnot hp)

end Cone

section Subadditivity

variable {𝕜 : Type v} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type w} [AddCommMonoid α] [PartialOrder α] [Module 𝕜 α]
variable [AddLeftMono α] [PosSMulMono 𝕜 α]

/-- Helper for Theorem 4.7: a pointwise subadditivity inequality makes the finite-height epigraph
closed under set addition. -/
theorem epi_add_subset_of_subadditive
    {f : E → WithTopBot α}
    (hsub : ∀ x y : E, f (x + y) ≤ f x + f y) :
    epi f + epi f ⊆ epi f := by
  rintro _ ⟨⟨x, μ⟩, hx_epi, ⟨y, ν⟩, hy_epi, rfl⟩
  rw [mem_epi_iff] at hx_epi hy_epi ⊢
  -- The source inequality closes the function value, and the epigraph bounds close the height.
  exact (hsub x y).trans <| add_le_add hx_epi hy_epi

section

variable {𝕜 : Type v} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type w} [AddCommMonoid α] [PartialOrder α] [Module 𝕜 α]
variable [PosSMulMono 𝕜 α]

/-- Helper for Theorem 4.7: additive closure of the finite-height epigraph recovers the pointwise
subadditivity inequality, provided `f` never takes the value `⊥`. -/
theorem subadditive_of_epi_add_subset
    {f : E → WithTopBot α} (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hadd : epi f + epi f ⊆ epi f) :
    ∀ x y : E, f (x + y) ≤ f x + f y := by
  intro x y
  by_cases hxtop : f x = ⊤
  · -- If `f x = ⊤`, then the right-hand side is already `⊤`.
    rw [hxtop]
    exact le_top
  by_cases hytop : f y = ⊤
  · -- The symmetric `⊤` branch is again immediate.
    rcases exists_coe_of_ne_top_ne_bot hxtop (hf_ne_bot x) with ⟨μ, hμ⟩
    have hsum_top : f x + f y = (⊤ : WithTopBot α) := by
      rw [hytop]
      simp
    rw [hsum_top]
    exact le_top
  have hxbot : f x ≠ ⊥ := hf_ne_bot x
  have hybot : f y ≠ ⊥ := hf_ne_bot y
  rcases exists_coe_of_ne_top_ne_bot hxtop hxbot with ⟨μ, hμ⟩
  rcases exists_coe_of_ne_top_ne_bot hytop hybot with ⟨ν, hν⟩
  have hx_epi : (x, μ) ∈ epi f := by
    rw [mem_epi_iff]
    simp [hμ]
  have hy_epi : (y, ν) ∈ epi f := by
    rw [mem_epi_iff]
    simp [hν]
  have hxy_epi : (x + y, μ + ν) ∈ epi f := by
    -- Closure of `epi f` under addition turns the canonical points above `x` and `y`
    -- into the canonical point above `x + y`.
    exact hadd ⟨(x, μ), hx_epi, (y, ν), hy_epi, rfl⟩
  have hxy_le : f (x + y) ≤ μ + ν := by
    exact mem_epi_iff.mp hxy_epi
  simpa [hμ, hν] using hxy_le

end

-- Route correction: the file originally routed through a mixed `ConvexOn`/finite-height epigraph
-- argument. The source proof works directly on the finite-height epigraph `epi f`, so the final
-- theorem now stays entirely on that owner and applies Theorem 2.6 exactly as in Rockafellar.
/-- Theorem 4.7: a positively homogeneous function `f : E → (-∞, +∞]` is convex if and only if
it is subadditive, i.e. `f (x + y) ≤ f x + f y` for all `x, y ∈ E`. -/
theorem isConvex_iff_subadditive_of_positivelyHomogeneous
    [PosMulReflectLT 𝕜]
    {f : E → WithTopBot α} (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥) :
    f.IsConvex 𝕜 ↔ ∀ x y : E, f (x + y) ≤ f x + f y := by
  -- Theorem 2.6 applies to the cone `epi f`; the remaining bridge is exactly the source
  -- equivalence between additive closure of the epigraph and subadditivity of `f`.
  refine (isCone_epi_of_positivelyHomogeneous hf_hom).convex_iff_add_subset.trans ?_
  constructor
  · exact subadditive_of_epi_add_subset hf_ne_bot
  · exact epi_add_subset_of_subadditive

end Subadditivity

end Function
end
