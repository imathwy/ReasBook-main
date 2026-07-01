import Mathlib
import Mathlib.Algebra.Order.Ring.Defs
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {𝕜 : Type w}
variable {E : Type u}
variable {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]

namespace Function

/-- Chapter owner alias: convexity of an extended-valued function on a set is convexity of its
finite-height epigraph over that set. -/
abbrev IsConvexOn (𝕜 : Type w) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {α : Type v} [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    (s : Set E) (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi[s] f)

/-- Chapter owner alias: global convexity of an extended-valued function is convexity of its
finite-height epigraph on `Set.univ`. -/
abbrev IsConvex (𝕜 : Type w) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {α : Type v} [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

/-- Epigraph bridge for `Function.IsConvexOn`: this owner is definitionally the convexity of the
finite-height epigraph set `{(x, μ) | x ∈ s ∧ f x ≤ μ}`. -/
theorem isConvexOn_iff_convex_epigraph {s : Set E} {f : E → WithTopBot α} :
    Function.IsConvexOn 𝕜 s f ↔
      Convex 𝕜 {p : E × α | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  simp [Function.IsConvexOn, epi_eq_setOf_mem_and_le]

/-- Epigraph bridge for `Function.IsConvex`: this owner is equivalent to convexity of the
full finite-height epigraph set `{(x, μ) | f x ≤ μ}`. -/
theorem isConvex_iff_convex_epigraph {f : E → WithTopBot α} :
    Function.IsConvex 𝕜 f ↔
      Convex 𝕜 {p : E × α | f p.1 ≤ p.2} := by
  simp [Function.IsConvex, epi_univ_eq_setOf_le]

namespace IsConvexOn

/-- The `Function.IsConvexOn` owner yields convexity of the set-form epigraph bridge. -/
theorem convex_epigraph {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) :
    Convex 𝕜 {p : E × α | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
  (Function.isConvexOn_iff_convex_epigraph (𝕜 := 𝕜) (s := s) (f := f)).1 hf

end IsConvexOn

namespace IsConvex

/-- The `Function.IsConvex` owner yields convexity of the set-form full epigraph bridge. -/
theorem convex_epigraph {f : E → WithTopBot α}
    (hf : Function.IsConvex 𝕜 f) :
    Convex 𝕜 {p : E × α | f p.1 ≤ p.2} :=
  (Function.isConvex_iff_convex_epigraph (𝕜 := 𝕜) (f := f)).1 hf

end IsConvex

end Function

/-
Source/core/bridge triage:
- `source-facing`: the file checks that the canonical `ConvexOn` surface is available for
  extended-order-valued functions and then specializes Theorem 4.2 to the strict
  affine-upper-bound criterion over an ordered scalar ring.
- `core/canonical`: the reusable owner is the existing `ConvexOn` predicate; the chapter epigraph
  `epi f` remains the finite-height view used by the later strict interpolation theorem.
- `bridge/view`: the raw-set reformulation `{p : E × α | f p.1 ≤ p.2}` is the minimal bridge for
  that owner; the later scalar-codomain sections connect it to mathlib's `ConvexOn` API for
  finite-valued functions on `Set.univ`, while the strict interpolation criterion stays in a
  stronger densely ordered ordered-ring layer.
- Primitive data vs derived API: the primitive datum is the function `f`; no new convexity owner is
  introduced here.
- Domain-style sampling used here: `Convex`, the intrinsic epigraph notation `epi f`, and the
  chapter-facing codomain `WithTopBot α`.
- Textual repair note: the transcript's first hypothesis `f(x) < x` is type-invalid in `R^n`; the
  symmetric strict-height hypothesis `f(x) < α` is the intended source meaning and is formalized
  below.
- Layer target: the first section is `core/canonical`, keeping only the global owner and its
  minimal epigraph bridge; the later ordered-ring section is `source-facing`.
-/

section ScalarCodomainOwner

variable {𝕜 : Type w}
variable {E : Type u}
variable {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [Module 𝕜 β]

/-- Owner-first whole-space constant convexity on finite codomain values. -/
theorem Function.convexOn_univ_const (c : β) :
    ConvexOn 𝕜 (Set.univ : Set E) (fun _ : E ↦ c) :=
  convexOn_const c convex_univ

end ScalarCodomainOwner

section ScalarCodomainOwnerLifted

variable {𝕜 : Type w}
variable {E : Type u}
variable {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]

/-- If the codomain lift carries the canonical convexity structure, constants are convex on
`Set.univ` at the owner level. -/
theorem Function.convexOn_univ_const_withTopBot (c : WithTopBot β)
    [AddCommMonoid (WithTopBot β)] [PartialOrder (WithTopBot β)]
    [IsOrderedAddMonoid (WithTopBot β)]
    [Module 𝕜 (WithTopBot β)] [PosSMulMono 𝕜 (WithTopBot β)] :
    ConvexOn 𝕜 (Set.univ : Set E) (fun _ : E ↦ c) :=
  convexOn_const c convex_univ

end ScalarCodomainOwnerLifted

section ScalarCodomain

variable {𝕜 : Type w}
variable {E : Type u}
variable {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

/-- A `β`-valued function that is convex on all of `E` becomes globally convex after the canonical
codomain lift to `WithTopBot β`. -/
theorem Function.isConvex_coe_of_convexOn_univ {f : E → β}
    (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 (epi (fun x ↦ (f x : WithTopBot β))) := by
  simpa [epi_univ_eq_setOf_le] using hf.convex_epigraph

/-- A finite constant `WithTopBot β`-valued function is convex. -/
private theorem Function.isConvex_const_coe (c : β) :
    Convex 𝕜 (epi (fun _ : E ↦ (c : WithTopBot β))) :=
  Function.isConvex_coe_of_convexOn_univ
    (f := fun _ : E ↦ c)
    (Function.convexOn_univ_const (𝕜 := 𝕜) (E := E) c)

/-- A constant `WithTopBot β`-valued function is convex. -/
private theorem Function.isConvex_const (c : WithTopBot β) :
    Convex 𝕜 (epi (fun _ : E ↦ c)) := by
  cases c with
  | none =>
      intro p hp q hq a b ha hb hab
      rw [mem_epi_iff] at hp
      have hp_lt : (p.2 : WithTopBot β) < ⊤ := by
        change (((p.2 : WithBot β) : WithTop (WithBot β)) < (⊤ : WithTop (WithBot β)))
        exact WithTop.coe_lt_top _
      exact (not_lt_of_ge hp hp_lt).elim
  | some c =>
      cases c with
      | bot =>
        intro p hp q hq a b ha hb hab
        rw [mem_epi_iff]
        change (((⊥ : WithBot β) : WithTop (WithBot β)) ≤
          ((((a • p + b • q).2 : β) : WithBot β) : WithTop (WithBot β)))
        exact WithTop.coe_le_coe.mpr bot_le
      | coe c =>
        simpa using Function.isConvex_const_coe (𝕜 := 𝕜) (E := E) (β := β) c

/-!
The direct `WithTopBot` abbreviation has no dedicated namespace API in this mathlib snapshot.
These local bridges keep the order/coercion manipulations explicit and isolated.
-/
private theorem withTopBot_bot_lt_coe {𝕜 : Type w} [LT 𝕜] (a : 𝕜) :
    (⊥ : WithTopBot 𝕜) < (a : WithTopBot 𝕜) := by
  change (((⊥ : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
    (((a : WithBot 𝕜) : WithTop (WithBot 𝕜))))
  exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)

private theorem withTopBot_coe_lt_top {𝕜 : Type w} [LT 𝕜] (a : 𝕜) :
    (a : WithTopBot 𝕜) < (⊤ : WithTopBot 𝕜) := by
  change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) < (⊤ : WithTop (WithBot 𝕜)))
  exact WithTop.coe_lt_top _

private theorem withTopBot_coe_lt_coe_iff {𝕜 : Type w} [LT 𝕜] {a b : 𝕜} :
    (a : WithTopBot 𝕜) < (b : WithTopBot 𝕜) ↔ a < b := by
  constructor
  · intro h
    change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
      (((b : WithBot 𝕜) : WithTop (WithBot 𝕜)))) at h
    exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp h)
  · intro h
    change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
      (((b : WithBot 𝕜) : WithTop (WithBot 𝕜))))
    exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr h)

private theorem withTopBot_coe_lt_coe {𝕜 : Type w} [LT 𝕜] {a b : 𝕜} (h : a < b) :
    (a : WithTopBot 𝕜) < (b : WithTopBot 𝕜) :=
  withTopBot_coe_lt_coe_iff.mpr h

/-- The zero `WithTopBot β`-valued function is convex. -/
theorem Function.isConvex_zero : Convex 𝕜 (epi (fun _ : E ↦ (0 : WithTopBot β))) := by
  simpa using (Function.isConvex_const (𝕜 := 𝕜) (E := E) (β := β) (c := (0 : WithTopBot β)))

end ScalarCodomain

section StrictScalarCodomain

variable {𝕜 : Type w}
variable {E : Type u}
variable [Ring 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]

section Dense

variable [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]

private theorem exists_between_coe_of_lt {x y : WithTopBot 𝕜} (h : x < y) :
    ∃ a : 𝕜, x < (a : WithTopBot 𝕜) ∧ (a : WithTopBot 𝕜) < y := by
  cases x with
  | none =>
      have hyle : y ≤ (⊤ : WithTopBot 𝕜) := le_top
      exact (not_lt_of_ge hyle h).elim
  | some x' =>
      cases x' with
      | bot =>
          cases y with
          | none =>
              exact ⟨0, withTopBot_bot_lt_coe 0, withTopBot_coe_lt_top 0⟩
          | some y' =>
              cases y' with
              | bot =>
                  exact (lt_irrefl _ h).elim
              | coe b =>
                  obtain ⟨a, ha⟩ := exists_lt b
                  exact ⟨a, withTopBot_bot_lt_coe a, withTopBot_coe_lt_coe ha⟩
      | coe x =>
          cases y with
          | none =>
              obtain ⟨a, hxa⟩ := exists_gt x
              exact ⟨a, withTopBot_coe_lt_coe hxa, withTopBot_coe_lt_top a⟩
          | some y' =>
              cases y' with
              | bot =>
                  exact (not_lt_of_ge (bot_le : (⊥ : WithTopBot 𝕜) ≤ (x : WithTopBot 𝕜)) h).elim
              | coe y =>
                  have hxy : x < y := withTopBot_coe_lt_coe_iff.mp h
                  obtain ⟨a, hxa, hay⟩ := exists_between hxy
                  exact ⟨a, withTopBot_coe_lt_coe hxa, withTopBot_coe_lt_coe hay⟩

/-- A function with convex finite-height epigraph satisfies the strict affine upper-bound
interpolation property from Theorem 4.2. -/
private theorem convex_epi_lt_affine_upper_bound {f : E → WithTopBot 𝕜}
    (hf : Convex 𝕜 (epi f))
    (x y : E) (α β t : 𝕜) (hx : f x < α) (hy : f y < β) (ht0 : 0 < t) (ht1 : t < 1) :
    f ((1 - t) • x + t • y) < ((1 - t) * α + t * β : 𝕜) := by
  have hconv : Convex 𝕜 {p : E × 𝕜 | f p.1 ≤ p.2} :=
    by simpa [epi_univ_eq_setOf_le] using hf
  rcases exists_between_coe_of_lt hx with ⟨α', hx', hα'⟩
  rcases exists_between_coe_of_lt hy with ⟨β', hy', hβ'⟩
  have hα'r : α' < α := withTopBot_coe_lt_coe_iff.mp hα'
  have hβ'r : β' < β := withTopBot_coe_lt_coe_iff.mp hβ'
  have hp : (x, α') ∈ {p : E × 𝕜 | f p.1 ≤ p.2} := hx'.le
  have hq : (y, β') ∈ {p : E × 𝕜 | f p.1 ≤ p.2} := hy'.le
  have hmem :
      f ((1 - t) • x + t • y) ≤ ((1 - t) * α' + t * β' : 𝕜) := by
    have hpair :
        (1 - t) • (x, α') + t • (y, β') ∈ {p : E × 𝕜 | f p.1 ≤ p.2} :=
      hconv hp hq (sub_nonneg.mpr ht1.le) ht0.le (by simp)
    simpa [smul_eq_mul] using hpair
  have hαβ : (1 - t) * α' + t * β' < (1 - t) * α + t * β := by
    have h1t : 0 < 1 - t := sub_pos.mpr ht1
    exact add_lt_add
      (mul_lt_mul_of_pos_left hα'r h1t)
      (mul_lt_mul_of_pos_left hβ'r ht0)
  exact lt_of_le_of_lt hmem (withTopBot_coe_lt_coe hαβ)

end Dense

section DenseLinear

variable [Module 𝕜 E]
variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
/-- Helper for Theorem 4.2: adding the same finite slack to both endpoint heights raises the
interpolated affine upper bound by exactly that slack. -/
private theorem affine_upper_bound_add_common
    (a b r s d : 𝕜) (hab : a + b = 1) :
    ((a * (r + d) + b * (s + d) : 𝕜)) = ((a * r + b * s : 𝕜) + d) := by
  -- Reassociate the two shifted terms so the common `d` factors through `a + b = 1`.
  calc
    ((a * (r + d) + b * (s + d) : 𝕜))
        = ((a * r + a * d) + (b * s + b * d) : 𝕜) := by
            rw [mul_add, mul_add]
    _ = ((a * r + b * s) + (a * d + b * d) : 𝕜) := by
          ac_rfl
    _ = ((a * r + b * s) + ((a + b) * d) : 𝕜) := by
          rw [← add_mul]
    _ = ((a * r + b * s) + d : 𝕜) := by
          rw [hab, one_mul]

/-- Helper for Theorem 4.2: the strict interpolation hypothesis forces convexity of the
finite-height epigraph `epi f`. -/
private theorem convex_epi_of_lt_affine_upper_bound {f : E → WithTopBot 𝕜}
    [Module 𝕜 E]
    (hf :
      ∀ x y : E, ∀ α β t : 𝕜,
        f x < α →
        f y < β →
        0 < t →
        t < 1 →
        f ((1 - t) • x + t • y) < ((1 - t) * α + t * β : 𝕜)) :
    Convex 𝕜 (epi f) := by
  -- Work directly from the definition of convexity so the proof stays on the ambient `SMul`.
  intro p hp q hq a b ha hb hab
  obtain rfl | ha_pos := ha.eq_or_lt
  · -- If `a = 0`, the convex combination is just the second endpoint.
    rw [zero_add] at hab
    have hcomb : (0 : 𝕜) • p + b • q = q := by
      -- Substitute the forced endpoint coefficient and let scalar-action simp finish.
      subst hab
      rcases p with ⟨px, pr⟩
      rcases q with ⟨qx, qr⟩
      apply Prod.ext
      · change 0 • px + 1 • qx = qx
        rw [zero_smul, one_smul, zero_add]
      · change 0 * pr + 1 * qr = qr
        ring
    rw [hcomb]
    exact hq
  obtain rfl | hb_pos := hb.eq_or_lt
  · -- If `b = 0`, the convex combination is just the first endpoint.
    rw [add_zero] at hab
    have hcomb : a • p + (0 : 𝕜) • q = p := by
      -- Substitute the forced endpoint coefficient and let scalar-action simp finish.
      subst hab
      rcases p with ⟨px, pr⟩
      rcases q with ⟨qx, qr⟩
      apply Prod.ext
      · change 1 • px + 0 • qx = px
        rw [one_smul, zero_smul, add_zero]
      · change 1 * pr + 0 * qr = pr
        ring
    rw [hcomb]
    exact hp
  rcases p with ⟨x, r⟩
  rcases q with ⟨y, s⟩
  rw [mem_epi_iff] at hp hq ⊢
  by_contra hmem
  -- If the affine height fails, insert a finite scalar `γ` strictly between the affine bound and
  -- the function value at the convex-combination point.
  have hlt : (((a * r + b * s : 𝕜) : WithTopBot 𝕜) < f (a • x + b • y)) := by
    simpa [smul_eq_mul] using (lt_of_not_ge hmem)
  rcases exists_between_coe_of_lt hlt with ⟨γ, hγ_left, hγ_right⟩
  let d : 𝕜 := γ - (a * r + b * s)
  have hd_pos : 0 < d := by
    -- The intermediate height `γ` lies strictly above the failed affine bound.
    have hγ_left' : a * r + b * s < γ := withTopBot_coe_lt_coe_iff.mp hγ_left
    exact sub_pos.mpr hγ_left'
  have hx_strict : f x < ((r + d : 𝕜) : WithTopBot 𝕜) := by
    -- Raise the endpoint height by the same positive slack `d`.
    exact lt_of_le_of_lt hp (withTopBot_coe_lt_coe (lt_add_of_pos_right r hd_pos))
  have hy_strict : f y < ((s + d : 𝕜) : WithTopBot 𝕜) := by
    -- The same common slack works for the second endpoint.
    exact lt_of_le_of_lt hq (withTopBot_coe_lt_coe (lt_add_of_pos_right s hd_pos))
  have hb_lt_one : b < 1 := by
    -- Positive coefficients summing to `1` force `b` into the open interval `(0, 1)`.
    have hba : b < b + a := lt_add_of_pos_right b ha_pos
    simpa [add_comm, hab] using hba
  have h_one_sub_b : 1 - b = a := by
    -- This rewrites the interpolation point back to the original coefficient `a`.
    calc
      1 - b = (a + b) - b := by rw [hab]
      _ = a := by abel
  have hz_strict :
      f ((1 - b) • x + b • y) < (((1 - b) * (r + d) + b * (s + d) : 𝕜) : WithTopBot 𝕜) :=
    hf x y (r + d) (s + d) b hx_strict hy_strict hb_pos hb_lt_one
  have h_shift_eq_gamma : (a * (r + d) + b * (s + d) : 𝕜) = γ := by
    -- The common-shift normalization collapses the new affine bound to the chosen midpoint `γ`.
    calc
      (a * (r + d) + b * (s + d) : 𝕜) = ((a * r + b * s : 𝕜) + d) :=
        affine_upper_bound_add_common a b r s d hab
      _ = γ := by
        calc
          ((a * r + b * s : 𝕜) + d) = d + (a * r + b * s) := by ac_rfl
          _ = γ := by
            dsimp [d]
            exact (sub_eq_iff_eq_add.mp rfl).symm
  have hz_lt_gamma : f (a • x + b • y) < ((γ : 𝕜) : WithTopBot 𝕜) := by
    -- Rewriting both the point and the height produces the contradiction with `γ < f z`.
    have hz_strict' :
        f (a • x + b • y) < (((a * (r + d) + b * (s + d) : 𝕜) : WithTopBot 𝕜)) := by
      simpa [h_one_sub_b] using hz_strict
    exact lt_of_lt_of_eq hz_strict' (congrArg (fun t : 𝕜 ↦ ((t : WithTopBot 𝕜))) h_shift_eq_gamma)
  exact (not_lt_of_ge hz_lt_gamma.le hγ_right).elim

-- Proof sketch: for the forward direction, replace the strict endpoint heights `α, β` by smaller
-- finite scalar values still above `f x` and `f y`, then apply convexity of the closed epigraph.
-- For the reverse direction, if a convex combination of two epigraph points failed to stay in the
-- epigraph, choose an intermediate finite height `r` strictly between the violated target height
-- and the function value there; enlarging the endpoint heights by the same positive gap
-- then violates
-- the assumed strict affine upper-bound property.
/-- Theorem 4.2 on the source owner surface: an extended-valued function is convex iff every
pair of strict finite upper bounds `f x < α` and `f y < β` interpolates to the strict affine upper
bound `f ((1 - t) • x + t • y) < (1 - t) * α + t * β` for all `0 < t < 1`.

The statement is intentionally phrased through `Function.IsConvex`, i.e. convexity of the finite
height epigraph, rather than through `ConvexOn` for `WithTopBot 𝕜`.  The source theorem is about
finite scalar heights above the epigraph; it should not depend on an arbitrary scalar action on the
extended codomain. -/
theorem Function.isConvex_iff_lt_affine_upper_bound (f : E → WithTopBot 𝕜) :
    Function.IsConvex 𝕜 f ↔
      ∀ x y : E, ∀ α β t : 𝕜,
        f x < (α : WithTopBot 𝕜) →
        f y < (β : WithTopBot 𝕜) →
        0 < t →
        t < 1 →
        f ((1 - t) • x + t • y) < (((1 - t) * α + t * β : 𝕜) : WithTopBot 𝕜) := by
  constructor
  · intro hf
    exact convex_epi_lt_affine_upper_bound (f := f) hf
  · intro hf
    exact convex_epi_of_lt_affine_upper_bound (f := f) hf

end DenseLinear

end StrictScalarCodomain

end
