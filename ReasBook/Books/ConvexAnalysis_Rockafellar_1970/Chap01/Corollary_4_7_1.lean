import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_7

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

-- Proof sketch for the source-facing corollary: recover two-point subadditivity from Theorem 4.7
-- and invoke the primitive owner theorem above.
/-- Corollary 4.7.1, stated coordinate-free: a positively homogeneous convex function satisfies the
finite positive-weight subadditivity inequality for every nonempty finite family of points.
-/
theorem PositivelyHomogeneous.map_sum_le
    [PosMulReflectLT 𝕜]
    {f : E → WithTopBot 𝕜} (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_ne_bot : ∀ y : E, f y ≠ ⊥) (hf_conv : f.IsConvex 𝕜)
    (t : Finset ι) (w : ι → 𝕜) (x : ι → E)
    (ht : t.Nonempty) (hw : ∀ i ∈ t, 0 < w i) :
    f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i • f (x i) := by
  have hsub :
      ∀ u v : E, f (u + v) ≤ f u + f v :=
    (isConvex_iff_subadditive_of_positivelyHomogeneous hf_hom hf_ne_bot).mp hf_conv
  -- Once two-point subadditivity is available on the current owner, the finite-sum theorem closes.
  exact hf_hom.map_sum_le_of_subadditive hsub t w x ht hw

end ConvexCorollary

end Function
