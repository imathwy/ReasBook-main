import Mathlib.Algebra.Group.Pointwise.Set.Lattice
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_3_1_1 (from Chap01) -/
open scoped Pointwise
open scoped Rockafellar

universe u v

section OrderedPositiveCone

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.1 says the order-upper closure of a convex set remains convex.
- `core/canonical`: the owner data are `upperClosure`, `mem_upperClosure`, and the positive-cone
  owner `orthant[R](E)` in an ordered additive module.
- `bridge/view`: the set-builder surface `{x | ∃ x₁ ∈ C, x ≥ x₁}` is a thin restatement of
  `upperClosure C`.
- Primitive data vs derived API: convexity of `C` is primitive; the Minkowski-sum and set-builder
  views are bridge restatements of the owner statement on `upperClosure C`.
- Layer target: `core/canonical`.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no extended-value codomain appears; no codomain lift is needed.
- Scalar/ambient check: the raw upper-closure/Minkowski identity is scalar-free; we expose a
  primitive noncommutative ordered-group statement first (`Set.Ici 0 + C`) and keep the
  commutative orientation (`C + Set.Ici 0`) as a bridge theorem.
- Owner check: keep `orthant[R](E)` as the chapter bridge owner, derived from the primitive
  `Set.Ici (0 : E)` layer.
- Topology check: this source item is not topology-facing.
- Notation check: reuse existing owners/notation (`upperClosure`, `orthant[𝕜](M)`); no new notation
  layer is introduced.
-/

/-- Helper for Text 3.1.1: at the weakest ordered-additive layer, the upper closure is the left
Minkowski sum with `Set.Ici 0`. -/
theorem upperClosure_eq_Ici_add
    {E : Type u} [AddGroup E] [Preorder E] [AddRightMono E]
    (C : Set E) :
    {x : E | x ∈ upperClosure C} = Set.Ici (0 : E) + C := by
  ext x
  constructor
  · rintro ⟨x₁, hx₁, hx₁x⟩
    -- Rewrite an upper-closure witness as a sum of a nonnegative displacement and a base point.
    refine ⟨x - x₁, sub_nonneg.mpr hx₁x, x₁, hx₁, by simp⟩
  · rintro ⟨z, hz, x₁, hx₁, rfl⟩
    -- A point in `Set.Ici 0 + C` dominates its `C`-component.
    refine ⟨x₁, hx₁, ?_⟩
    simpa using add_le_add_left (show (0 : E) ≤ z from hz) x₁

/-- Helper for Text 3.1.1: in the commutative setting, the upper closure is the right Minkowski
sum with `Set.Ici 0`. -/
theorem upperClosure_eq_add_Ici
    {E : Type u} [AddCommGroup E] [Preorder E] [AddRightMono E]
    (C : Set E) :
    {x : E | x ∈ upperClosure C} = C + Set.Ici (0 : E) := by
  -- Commute the primitive Minkowski-sum presentation into the textbook orientation.
  simpa [add_comm] using (upperClosure_eq_Ici_add (C := C))

/-- Helper for Text 3.1.1: in an ordered additive module, the upper closure is the Minkowski sum
with the nonnegative orthant. -/
theorem upperClosure_eq_add_orthant
    {R : Type v} [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    (C : Set E) :
    {x : E | x ∈ upperClosure C} = C + orthant[R](E) := by
  -- Replace `Set.Ici 0` with the chapter's orthant owner.
  simpa [orthant_eq_Ici] using
    (upperClosure_eq_add_Ici C)

/-- Helper for Text 3.1.1: the upper closure of a convex set is convex at the owner level. -/
theorem Convex.upperClosure
    {R : Type v} [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommMonoid E] [Preorder E]
    [IsOrderedAddMonoid E] [SMul R E] [PosSMulMono R E]
    {C : Set E} (hC : Convex R C) :
    Convex R {x : E | x ∈ upperClosure C} := by
  intro x hx y hy a b ha hb hab
  rcases (mem_upperClosure.mp hx) with ⟨x₁, hx₁, hx₁x⟩
  rcases (mem_upperClosure.mp hy) with ⟨y₁, hy₁, hy₁y⟩
  -- Combine the original witnesses using convexity inside `C`.
  refine mem_upperClosure.mpr ?_
  refine ⟨a • x₁ + b • y₁, hC hx₁ hy₁ ha hb hab, ?_⟩
  -- Monotonicity of positive scalar multiplication preserves the witness inequalities.
  exact add_le_add (smul_le_smul_of_nonneg_left hx₁x ha)
    (smul_le_smul_of_nonneg_left hy₁y hb)

/-- Text 3.1.1: the order-upper closure of a convex set is convex. -/
theorem convex_setOf_exists_mem_ge
    {R : Type v} [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommMonoid E] [Preorder E]
    [IsOrderedAddMonoid E] [SMul R E] [PosSMulMono R E]
    (C : Set E) (hC : Convex R C) :
    Convex R {x : E | ∃ x₁ ∈ C, x ≥ x₁} := by
  -- Move to the owner theorem on `upperClosure`.
  have hUpper : Convex R {x : E | x ∈ upperClosure C} := hC.upperClosure
  -- Translate back to the textbook set-builder surface.
  simpa [mem_upperClosure, ge_iff_le] using hUpper

end OrderedPositiveCone

/-! ### Theorem_3_1 (from Chap01) -/
open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.1 states that the sum of two convex subsets is again convex.
- `core/canonical`: the owner abstraction is the intrinsic predicate `Convex 𝕜 s` on sets. The
  chapter owner theorem should live at the primitive additive scalar-action layer.
- `bridge/view`: the textbook sum
  `C₁ + C₂ = {x₁ + x₂ | x₁ ∈ C₁, x₂ ∈ C₂}`
  is exactly mathlib's pointwise set addition notation `C₁ + C₂`.
- Primitive data vs derived API: the sets `C₁` and `C₂` are primitive; the convexity of their
  pointwise sum is the whole statement.
- Domain-style sampling: Chapter 1 already fixes the owner notion in `Definition_2_0_1` by
  recalling `Convex`; this file provides the weak-layer additive closure bridge used directly by
  downstream finite-sum items.
- Layer target: `core/canonical`; expose the binary closure owner at the primitive layer
  `[DistribSMul 𝕜 E]`, with mathlib's `Convex.add` as a stronger specialization.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: this item is codomain-free.
- Scalar/ambient structure stronger than needed? `Yes` in the old `Convex.add`-only surface:
  binary convex-sum closure does not require a full module structure.
- Owner tied to a concrete model? `No`: owner is the intrinsic set predicate `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this is a convexity-closure theorem,
  not a topological closure/interior statement.
- Owner name/notation too heavy or too concrete? `No`: the theorem stays on the short owner
  namespace `Convex` and pointwise sum notation `A + B`.
- Upstream over-specialization to repair first? `Yes`: provide the weak binary bridge here and
  reuse it downstream instead of duplicating local private replacements.
-/

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [DistribSMul 𝕜 E]

/- Theorem 3.1 at the canonical mathlib owner layer (module specialization). -/
recall Convex.add

/-- Theorem 3.1 at the primitive additive scalar-action layer: if `A` and `B` are convex, then
their pointwise sum `A + B` is convex. This is the chapter-level owner bridge; mathlib's
`Convex.add` is the stronger `[Module 𝕜 E]` specialization. -/
theorem Convex.add_set {A B : Set E} (hA : Convex 𝕜 A) (hB : Convex 𝕜 B) :
    Convex 𝕜 (A + B) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨xA, hxA, xB, hxB, rfl⟩
  rcases hy with ⟨yA, hyA, yB, hyB, rfl⟩
  refine ⟨a • xA + b • yA, hA hxA hyA ha hb hab, a • xB + b • yB, hB hxB hyB ha hb hab, ?_⟩
  simp [smul_add, add_assoc, add_left_comm]

end

/-! ### Text_3_1_2 (from Chap01) -/
open scoped Pointwise

universe u v

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.2 characterizes convex cones through the short source owner
  `Set.IsConvexCone R K` by positive-scalar closure and closure under set addition.
  Coordinate-model textbook statements are obtained as downstream specializations.
- `core/canonical`: the owner-side criteria already live upstream as
  `Set.isCone_iff_pos_smul_subset` (canonical setwise form) together with
  `Set.isCone_iff_forall_pos_smul_subset` (pointwise bridge form) for the cone part, and
  `Set.IsCone.convex_iff_add_subset` for the convexity part under a cone hypothesis.
- `bridge/view`: the source-facing pointwise closure statement
  `(∀ c > 0, c • K ⊆ K)` is a bridge restatement of the owner predicate `Set.IsCone R K`.
- Primitive data vs derived API: the primitive source predicate is `Set.IsCone R K`; pointwise
  scalar-closure inclusion is derived via `Set.isCone_iff_forall_pos_smul_subset`.
- Domain-style sampling: this refinement reuses `Set.IsCone`,
  `Set.isCone_iff_forall_pos_smul_subset`, and `Set.IsCone.convex_iff_add_subset`.
- Layer target: `source-facing` with a primitive bridge theorem at the weaker
  `Set.IsConvexCone`-definition layer and Text 3.1.2 as the stronger additive bridge.
-/

/- Canonicalization audit (this pass):
- Codomain/ambient layer check: no `EReal`/`ℝ`-specific codomain appears; keep the semiring layer.
- Scalar/ambient structure check: the positive-scalar/convex bridge stays at the weak
  `Semiring`/`SMul` layer; additive-closure equivalence keeps the division layer required by
  `Set.IsCone.convex_iff_add_subset`.
- Owner check: keep the short source owner `Set.IsConvexCone` and expose owner-prefixed bridge
  constructors/projections.
- Topology check: not applicable in this item.
- Notation check: reuse existing pointwise notation `c • K` and `K + K`; no new notation layer.
-/

section PrimitiveBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set

namespace IsConvexCone

/-- A source-facing convex cone is closed under every positive scalar action on its carrier set. -/
theorem pos_smul_subset {K : Set E} (hK : IsConvexCone R K) :
    ∀ c : R, 0 < c → c • K ⊆ K := by
  intro c hc
  exact hK.isCone.smul_set_subset hc

/-- Constructor bridge from positive-scalar set closure and convexity to the source owner
`Set.IsConvexCone`. -/
theorem of_pos_smul_subset_and_convex {K : Set E}
    (hsmul : ∀ c : R, 0 < c → c • K ⊆ K) (hconv : Convex R K) :
    IsConvexCone R K := by
  exact ⟨(isCone_iff_forall_pos_smul_subset K).2 hsmul, hconv⟩

end IsConvexCone

/-- Primitive owner-level bridge: a subset is a convex cone iff it is closed under positive scalar
set multiplication and is convex. This theorem stays at the weak structure layer of
`Set.IsConvexCone` and `Set.isCone_iff_forall_pos_smul_subset`. -/
theorem IsConvexCone.iff_pos_smul_subset_and_convex (K : Set E) :
    IsConvexCone R K ↔ (∀ c : R, 0 < c → c • K ⊆ K) ∧ Convex R K := by
  constructor
  · intro hK
    exact ⟨hK.pos_smul_subset, hK.convex⟩
  · rintro ⟨hsmul, hconv⟩
    exact IsConvexCone.of_pos_smul_subset_and_convex hsmul hconv

end Set

end PrimitiveBridge

section WeakAdditiveConstructor

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

namespace Set

namespace IsConvexCone

/-- Weak-layer constructor bridge from conehood and additive closure to the source owner
`Set.IsConvexCone`. -/
theorem of_isCone_and_add_subset {K : Set E} (hcone : IsCone R K)
    (hadd : K + K ⊆ K) : IsConvexCone R K := by
  refine ⟨hcone, convex_iff_add_mem.2 ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by simpa [ha0] using hab
    simpa [ha0, hb1] using hy
  · by_cases hb0 : b = 0
    · have ha1 : a = 1 := by simpa [hb0] using hab
      simpa [hb0, ha1] using hx
    · have ha_pos : (0 : R) < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : (0 : R) < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact hadd (Set.add_mem_add (hcone.smul_mem ha_pos hx) (hcone.smul_mem hb_pos hy))

end IsConvexCone

end Set

end WeakAdditiveConstructor

section AdditiveBridge

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R] [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Set

/-- Owner-level canonical form of Text 3.1.2: a subset is a convex cone iff it is a cone and is
closed under set addition. -/
theorem IsConvexCone.iff_isCone_and_add_subset (K : Set E) :
    IsConvexCone R K ↔ IsCone R K ∧ K + K ⊆ K := by
  constructor
  · intro hK
    exact ⟨hK.isCone, hK.add_subset⟩
  · rintro ⟨hcone, hadd⟩
    exact IsConvexCone.of_isCone_and_add_subset hcone hadd

/-- Text 3.1.2 in source-facing pointwise form: a subset of a module over a partially ordered
division semiring is a convex cone iff every positive scalar multiple `c • K` is contained in `K`
and the sum set `K + K` is contained in `K`. -/
theorem IsConvexCone.iff_pos_smul_subset_and_add_subset (K : Set E) :
    IsConvexCone R K ↔ (∀ c : R, 0 < c → c • K ⊆ K) ∧ K + K ⊆ K := by
  simpa [isCone_iff_forall_pos_smul_subset K] using
    (IsConvexCone.iff_isCone_and_add_subset (K := K))

end Set

end AdditiveBridge

/-! ### Text_3_1_3 (from Chap01) -/
open scoped BigOperators Pointwise

universe u v w

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.3 says that a finite linear combination of convex sets is convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜` on sets. Mathlib's finite-sum theorem
  `convex_sum` is canonical but currently requires the stronger `[Module 𝕜 E]` layer.
- `bridge/view`: the textbook expression `∑ i ∈ s, w i • C i` is already the weighted
  Minkowski-sum expression in the pointwise additive structure on sets.
- Primitive data vs derived API: primitive data are a finite family of sets and coefficients;
  scalar-image convexity and binary-sum convexity come from upstream chapter bridges
  (`Convex.smul_set` in `Theorem_3_0_2` and `Convex.add_set` in
  `Theorem_3_1`); finite-sum convexity is then rebuilt below.
- Domain-style sampling: this item aligns with finite pointwise set sums and
  `Set.addCommMonoid`.
- Layer target: `core/canonical` with a source-facing theorem surface by direct owner reuse.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: this item is codomain-free and lives at set convexity.
- Scalar/ambient structure stronger than needed? `Yes` in the old version: requiring
  `[Module 𝕜 E]` came from `convex_sum`, but the finite weighted-set-sum argument only needs
  `[DistribSMul 𝕜 E]` plus commuting scalar actions.
- Owner tied to a concrete model? `No`: owner remains intrinsic `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`.
- Owner name/notation too heavy or too concrete? `No`: theorem surface stays in the textbook
  notation `∑ i ∈ s, w i • C i`.
- Upstream over-specialization to repair first? `Yes`: reuse the upstream weak scalar-image and
  binary-sum bridges, then expose finite-sum closure at the same weak layer.
-/

section

variable {ι : Type u} {𝕜 : Type v} {E : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [DistribSMul 𝕜 E]

/-- Finite Minkowski-sum closure for convex sets at the same primitive scalar-action layer as
scalar-image convexity at this weak action layer, reusing the upstream binary closure theorem
`Convex.add_set` from `Theorem_3_1`. This owner theorem avoids exposing
`[Module 𝕜 E]` on downstream theorem surfaces. -/
theorem Convex.sum_set (s : Finset ι) (t : ι → Set E)
    (h : ∀ i ∈ s, Convex 𝕜 (t i)) :
    Convex 𝕜 (∑ i ∈ s, t i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h x hx y hy a b ha hb hab
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    subst hx0
    subst hy0
    simp [smul_zero]
  · intro i s hi hs h
    have hiConv : Convex 𝕜 (t i) := h i (by simp [hi])
    have hsConv : Convex 𝕜 (∑ j ∈ s, t j) := hs (by
      intro j hj
      exact h j (by simp [hj]))
    simpa [Finset.sum_insert, hi] using hiConv.add_set hsConv

variable [SMulCommClass 𝕜 𝕜 E]

/-- Text 3.1.3 in source-facing weighted-set notation: a finite weighted Minkowski sum of convex
sets is convex. The theorem surface is now at the primitive scalar-action layer
`[DistribSMul 𝕜 E]`, using the weak scalar-image convexity bridge and `Convex.sum_set`
rather than the stronger `[Module 𝕜 E]`-based `convex_sum`. -/
theorem Convex.sum_smul (s : Finset ι) (w : ι → 𝕜) (C : ι → Set E)
    (hC : ∀ i ∈ s, Convex 𝕜 (C i)) :
    Convex 𝕜 (∑ i ∈ s, w i • C i) := by
  refine Convex.sum_set (s := s) (t := fun i ↦ w i • C i) ?_
  intro i hi
  exact (hC i hi).smul_set

end

/-! ### Text_3_1_4 (from Chap01) -/
open scoped BigOperators Pointwise

universe u v

section

variable {ι : Type u} {𝕜 : Type*}
variable [LE 𝕜] [AddCommMonoid 𝕜] [One 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.4 introduces a finite convex combination of sets with nonnegative
  coefficients summing to `1`.
- `core/canonical`: the coefficient owner was already fixed in Definition 2.2.10 as
  `StdSimplex 𝕜 ι`; the resulting weighted combination is the owner-side finite sum
  `w.sum` applied to the set-valued summands `fun i a ↦ a • C i`, with
  `Set.addCommMonoid` supplying the ambient pointwise additive structure on sets.
- `bridge/view`: the textbook coefficient conditions are exactly `w.nonneg` and `w.total`, and
  the source display `∑ i : ι, w.weights i • C i` (for finite `ι`) is a bridge view of that
  owner-side sum once the zero-coefficient branches contribute the additive identity in `Set E`.
  No separate weighted-set owner or wrapper is needed.
- Primitive data vs derived API: the primitive data are the family `C : ι → Set E` and simplex
  weights `w : StdSimplex 𝕜 ι`; a `Fintype` instance is only needed for the derived full-index
  display `∑ i, ...`, not for the owner-side sum.
- Domain-style sampling: this item aligns with `StdSimplex`, `Finsupp.sum_fintype`,
  and `Set.addCommMonoid`.
- Layer target: `source-facing`, expressed directly through the canonical owner operations rather
  than a parallel local alias.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the coefficient owner at canonical `StdSimplex 𝕜 ι`; no concrete
  codomain such as `ℝ`/`EReal` appears in this item.
- Scalar/ambient-structure check: retain only the primitive simplex assumptions
  `[LE 𝕜] [AddCommMonoid 𝕜] [One 𝕜]`; set- and scalar-action assumptions are moved to the
  set-valued bridge specialization.
- Owner check: expose a generic owner-side bridge from `w.sum` to `Fintype` full-index sums for
  any additive codomain, then derive the set-valued textbook surface from it.
- Topology check: not applicable (item is algebraic, not topological).
- Notation/surface check: theorem surfaces keep textbook finite-sum notation `∑ i, ...` and
  simplex-owner notation `w.sum`.
-/

/- Text 3.1.4 uses the chapter's canonical owner for convex-combination coefficients. -/
recall StdSimplex

/- The finite convex combination of sets is then the ordinary finite sum in the additive
commutative monoid of sets. -/
recall Set.addCommMonoid

namespace StdSimplex

variable {β : Type*}

/-- Generic owner-side form: `StdSimplex.sum` is the support-indexed finite sum. -/
theorem sum_eq_sum_support [AddCommMonoid β]
    (w : StdSimplex 𝕜 ι) (f : ι → 𝕜 → β) :
    w.sum f = Finset.sum w.weights.support (fun i ↦ f i (w.weights i)) := by
  rfl

-- Bridge from support-indexed owner sums to full-index sums on finite index types.
theorem sum_eq_sum_weights [Fintype ι] [AddCommMonoid β]
    (w : StdSimplex 𝕜 ι) (f : ι → 𝕜 → β)
    (hzero : ∀ i : ι, f i 0 = 0) :
    w.sum f = ∑ i : ι, f i (w.weights i) := by
  classical
  simpa [Finsupp.sum_fintype] using
    (Finsupp.sum_fintype w.weights f hzero)

-- Canonical weighted-family owner surface (`z : ι → β`) over additive codomains.
theorem sum_smul_eq_sum_support [AddCommMonoid β] [SMul 𝕜 β]
    (w : StdSimplex 𝕜 ι) (z : ι → β) :
    w.sum (fun i a ↦ a • z i) =
      Finset.sum w.weights.support (fun i ↦ w.weights i • z i) := by
  simpa using (sum_eq_sum_support (w := w) (f := fun i a ↦ a • z i))

-- Finite-index bridge for weighted families; `hzero` discharges dropped zero-weight branches.
theorem sum_smul_eq_sum_weights [Fintype ι] [AddCommMonoid β] [SMul 𝕜 β]
    (w : StdSimplex 𝕜 ι) (z : ι → β)
    (hzero : ∀ i : ι, (0 : 𝕜) • z i = 0) :
    w.sum (fun i a ↦ a • z i) = ∑ i : ι, w.weights i • z i := by
  simpa using
    (sum_eq_sum_weights (w := w) (f := fun i a ↦ a • z i)
      (hzero := hzero))

section SetValued

variable {E : Type v} [AddCommMonoid E]

/-- The primitive owner-side form of Text 3.1.4 is the support-indexed simplex sum. -/
theorem sum_smul_set_eq_sum_support [SMul 𝕜 E]
    (w : StdSimplex 𝕜 ι) (C : ι → Set E) :
    w.sum (fun i a ↦ a • C i) =
      Finset.sum w.weights.support (fun i ↦ w.weights i • C i) := by
  simpa using (sum_smul_eq_sum_support (w := w) (z := C))

/-- Primitive finite-index bridge: the textbook full-index display follows once each
zero-coefficient branch is additive identity in `Set E`. -/
theorem sum_smul_set_eq_sum_weights [Fintype ι]
    [SMul 𝕜 E]
    (w : StdSimplex 𝕜 ι) (C : ι → Set E)
    (hzero : ∀ i : ι, (0 : 𝕜) • C i = 0) :
    w.sum (fun i a ↦ a • C i) = ∑ i : ι, w.weights i • C i := by
  simpa using
    (sum_smul_eq_sum_weights (w := w) (z := C)
      (hzero := hzero))

/-- Derived finite-index bridge for nonempty families, using `Set.zero_smul_set`. -/
theorem sum_smul_set_eq_sum_weights_of_nonempty [Fintype ι]
    [SMulWithZero 𝕜 E]
    (w : StdSimplex 𝕜 ι) (C : ι → Set E)
    (hnonempty : ∀ i : ι, (C i).Nonempty) :
    w.sum (fun i a ↦ a • C i) = ∑ i : ι, w.weights i • C i := by
  exact sum_smul_set_eq_sum_weights (w := w) (C := C)
    (hzero := fun i ↦ by simpa using Set.zero_smul_set (α := 𝕜) (hnonempty i))

end SetValued

end StdSimplex

variable {E : Type v}
variable [AddCommMonoid E]
variable [SMul 𝕜 E]
variable (C : ι → Set E) (w : StdSimplex 𝕜 ι)

/- Text 3.1.4: once the coefficient data are taken in the canonical owner `StdSimplex 𝕜 ι`, the
finite convex combination of the family `C` is the owner-side simplex sum
`w.sum (fun i a ↦ a • C i)`. -/
/- Owner-side finite convex-combination form from the simplex-owner sum operation. -/
#check (w.sum fun i a ↦ a • C i)

section

variable [Fintype ι]

/- Companion source-facing display form for finite index types. -/
#check ∑ i : ι, w.weights i • C i

end

end

/-! ### Text_3_1_5 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.5 expresses a Minkowski sum as a union of translates of one set by
  points of the other.
- `core/canonical`: the intrinsic translation owner is pointwise set `vadd` on `Set α` and `Set β`
  via `Set.iUnion_vadd_left_image`; additive Minkowski sum is its self-action specialization.
- `bridge/view`: the translate of `C₂` by `x₁` is the singleton left action
  `({x₁} : Set α) +ᵥ C₂`, and `Set.singleton_vadd` identifies this with the direct translate
  `x₁ +ᵥ C₂`. In the additive specialization, `Set.singleton_add` gives the textbook
  `{x₁} + C₂` form.
- Primitive data vs derived API: the primitive data are a left action and the two sets; the
  additive Minkowski surface is a specialization theorem.
- Domain-style sampling: this item aligns with `Set.iUnion_vadd_left_image`,
  `Set.singleton_vadd`, `Set.iUnion_add_left_image`, and `Set.singleton_add`.
- Layer target: `core/canonical`; reuse the intrinsic `+ᵥ` owner directly, then give only the
  non-duplicate textbook additive singleton bridge as a specialization.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the codomain at intrinsic `Set` translation owners (`+ᵥ` / `+`);
  no concrete codomain such as `ℝ` or `EReal` is mathematically needed.
- Scalar/ambient-structure check: keep only primitive action/additive assumptions (`[VAdd α β]`,
  `[Add γ]`) required by the reused canonical owners.
- Owner check: use canonical owners `Set.iUnion_vadd_left_image` and
  `Set.iUnion_add_left_image`; expose the source-facing theorem first at the intrinsic `+ᵥ`
  owner surface, then add the additive theorem as a specialization bridge.
- Topology check: this item is algebraic (translation of sets), so no ambient-vs-intrinsic
  topology migration applies.
- Owner-name check: keep short theorem names for the source-facing bridge surfaces only.
- Notation check: keep the intrinsic `x +ᵥ C` owner surface for `vadd`, and use textbook-primary
  singleton notation `{x} + C` on the additive theorem surface.
-/

/- Intrinsic translation owner used by Text 3.1.5: pointwise set `vadd` is the union of left
translates. -/
recall Set.iUnion_vadd_left_image

/- Singleton-left translate bridge for the intrinsic `vadd` owner. -/
recall Set.singleton_vadd

/- Additive specialization used for Minkowski sum in the textbook surface. -/
recall Set.iUnion_add_left_image

/- Singleton-left translate bridge for additive Minkowski sum. -/
recall Set.singleton_add

open scoped Pointwise

namespace Set

section VAddSurface

variable {α β : Type*} [VAdd α β] (D₁ : Set α) (D₂ : Set β)

/-- Primitive intrinsic translation-union owner surface for Text 3.1.5. -/
theorem iUnion_mem_vadd : (⋃ x₁ ∈ D₁, x₁ +ᵥ D₂) = D₁ +ᵥ D₂ :=
  Set.iUnion_vadd_left_image (s := D₁)

/-- Source-facing singleton-translate bridge for Text 3.1.5. -/
theorem iUnion_singleton_vadd : (⋃ x₁ ∈ D₁, ({x₁} : Set α) +ᵥ D₂) = D₁ +ᵥ D₂ := by
  -- Rewrite singleton translates to point translates, then invoke the canonical owner theorem.
  calc
    (⋃ x₁ ∈ D₁, ({x₁} : Set α) +ᵥ D₂) = (⋃ x₁ ∈ D₁, x₁ +ᵥ D₂) := by
      simp [Set.singleton_vadd]
    _ = D₁ +ᵥ D₂ := iUnion_mem_vadd (D₁ := D₁) (D₂ := D₂)

end VAddSurface

section AdditiveSurface

variable {γ : Type*} [Add γ] (D₁ D₂ : Set γ)

/-- Primitive additive translation-union owner surface for the additive specialization. -/
theorem iUnion_mem_add : (⋃ x₁ ∈ D₁, (fun x₂ : γ ↦ x₁ + x₂) '' D₂) = D₁ + D₂ :=
  Set.iUnion_add_left_image (s := D₁) (t := D₂)

/-- Text 3.1.5: the Minkowski sum is the union of singleton left translates. -/
theorem iUnion_singleton_add : (⋃ x₁ ∈ D₁, {x₁} + D₂) = D₁ + D₂ := by
  -- Convert the textbook singleton-translate notation to the additive image surface.
  simpa [Set.singleton_add] using (iUnion_mem_add (D₁ := D₁) (D₂ := D₂))

end AdditiveSurface

end Set

/-! ### Text_3_1_6 (from Chap01) -/
open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.6 records the basic algebraic identities for pointwise addition of
  sets and for pointwise scalar multiplication of sets.
- `core/canonical`: the owner abstractions are the pointwise additive semigroup/commutative
  semigroup structures on sets, the pointwise scalar-tower owner on sets for iterated scaling, and
  the pointwise distributive scalar action on sets.
- `bridge/view`: the textbook equalities are exactly the generic algebraic laws `add_comm`,
  `add_assoc`, `smul_assoc`, and `smul_add` read through the owner declarations
  `Set.addCommSemigroup`, `Set.addSemigroup`, `Set.isScalarTower`, and
  `Set.distribSMulSet`.
- Primitive data vs derived API: the primitive data are just the underlying sets and scalars; the
  displayed equalities are derived consequences of the owner structures and should reuse those
  owners directly.
- Domain-style sampling: this item aligns with `Set.addCommSemigroup`, `Set.addSemigroup`,
  `Set.isScalarTower`, and `Set.distribSMulSet`.
- Layer target: `core/canonical`; each clause is exact owner reuse, so the public surface keeps
  direct `recall` of the pointwise-set owner declarations.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the codomain at generic `Set` owners; the identities are pure
  pointwise-set algebra and do not need concrete codomains like `ℝ` or `EReal`.
- Scalar/ambient-structure check: keep only the weak canonical layers already used by the owners:
  `AddSemigroup`/`AddCommSemigroup`, `SMul`/`IsScalarTower`, and `DistribSMul` with
  `AddZeroClass`.
- Owner check: keep intrinsic pointwise owners `Set.addCommSemigroup`, `Set.addSemigroup`,
  `Set.isScalarTower`, and `Set.distribSMulSet`, not local wrapper owners.
- Topology check: this item has no ambient/intrinsic topology content, so no topology-layer change.
- Owner-name/notation check: keep short canonical `Set` owners and use textbook-primary notation
  `+` and `•` on source-facing surfaces.
-/

/- Text 3.1.6 (1): pointwise addition of sets is commutative; this is the commutativity field of
the canonical owner declaration `Set.addCommSemigroup`. -/
recall Set.addCommSemigroup

/- Text 3.1.6 (2): pointwise addition of sets is associative; this is already present at the
weaker canonical owner declaration `Set.addSemigroup`. -/
recall Set.addSemigroup

/- Text 3.1.6 (3): scaling a set first by `λ₂` and then by `λ₁` is the same as
scaling it once by `λ₁ * λ₂`; this is the scalar-associativity field of the weaker
owner declaration `Set.isScalarTower`. -/
recall Set.isScalarTower

/- Text 3.1.6 (4): scalar multiplication distributes over pointwise addition of sets; this is the
distributivity field of the owner declaration `Set.distribSMulSet`. -/
recall Set.distribSMulSet
