import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Restrict
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_3_5_1 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.1 introduces the direct sum of two convex sets as the set of ordered
  pairs with first coordinate in `C` and second coordinate in `D`.
- `core/canonical`: this is exactly the Cartesian product of sets, namely `Set.prod` with notation
  `×ˢ`.
- `bridge/view`: convexity of the product belongs to the later owner theorem `Convex.prod`, not to
  the present definition itself.
- Primitive data vs derived API: the sets `C` and `D` are primitive; the direct sum itself is the
  canonical set product, so this item contributes no extra wrapper data and no derived API beyond
  recalling that owner.
- Domain-style sampling: the relevant owner-side declarations are `Set.prod`,
  `Set.mem_prod`, `Convex.prod`, and the downstream chapter use in `Text_3_5_2`. These confirm
  that the correct public surface is the ambient set-product owner, not a parallel chapter-local
  `directSum` alias.
- Layer target: `core/canonical`; this numbered text is exact owner recall, so the main entry
  should remain a direct `recall` rather than a local compatibility definition.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this owner is codomain-free set
  structure (`Set.prod`) and already sits at the intrinsic set layer.
- Scalar/ambient structure stronger than needed? `No`: this item uses no scalar assumptions.
- Owner tied to a concrete model? `No`: the owner is intrinsic set product, not a coordinate model.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is set construction, not a
  topological closure/interior statement.
- Owner name too concrete/long? `No`: `Set.prod` with notation `×ˢ` is short and canonical.
- Missing notation surface? `No`: the canonical notation `×ˢ` is already primary and is used
  directly in the source-facing comment.
-/

/- Text 3.5.1: the direct sum of sets `C` and `D` is canonically their Cartesian product
`C ×ˢ D` (`Set.prod`), with canonical pair constructor/eliminator
`Set.mk_mem_prod` and `Set.mem_prod`. -/
recall Set.prod
recall Set.mk_mem_prod
recall Set.mem_prod

/-! ### Text_3_5_2 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.2 says that the direct sum of two convex sets is convex.
- `core/canonical`: by Text 3.5.1, the direct sum is exactly the Cartesian product `C ×ˢ D`,
  and the canonical closure theorem is `Convex.prod`.
- `bridge/view`: the set-product bridge (`Set.prod`, `Set.mem_prod`) is upstream in Text 3.5.1;
  this item should expose only the convexity owner theorem.
- Primitive data vs derived API: convexity of the factors is primitive; convexity of the direct
  sum/product is the derived owner-level conclusion.
- Domain-style sampling: this follows the chapter owner-first pattern (for example Text 3.6.4 and
  Theorem 3.5 as direct recalls of `Convex.inter` and `Convex.prod`).
- Layer target: `core/canonical`; keep this file as direct owner reuse with no duplicated bridge
  recalls.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: `Convex.prod` is already at the generic
  semiring/module convexity layer.
- Scalar/ambient structure stronger than needed? `No`: this uses the owner assumptions of
  `Convex.prod`, not an `ℝ`-specific specialization.
- Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜` on `Set`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is convexity closure, not a
  topology statement.
- Owner name too concrete/long? `No`: `Convex.prod` is the short canonical owner theorem.
- Missing notation surface? `No`: the primary notation `C ×ˢ D` is already provided upstream in
  Text 3.5.1.
-/

/- Text 3.5.2: once Text 3.5.1 identifies direct sum with the set product `C ×ˢ D`, convexity is
exactly the canonical owner theorem `Convex.prod`. -/
recall Convex.prod

/-! ### Text_3_5_3 (from Chap01) -/
section

open Set
open scoped Pointwise

variable {E : Type*} [AddCommGroup E]

/-
Source/core/bridge triage:
- `source-facing`: the item states an equivalence between unique decomposition in the pointwise
  sum `C + D` and the trivial intersection of the difference sets `C - C` and `D - D`.
  The mathematics uses only additive commutative group structure.
- `core/canonical`: the owner abstraction for uniqueness is injectivity of the canonical owner map
  `Set.addOnProd C D`; the ambient set operations are the standard pointwise sum and difference
  on `Set E`.
- `bridge/view`: the textbook `∀ x ∈ C + D, ∃! ...` wording is a companion reformulation of this
  injectivity statement, since existence in `C + D` is already built into pointwise set addition.
- Primitive data vs derived API: the sets `C` and `D` are primitive; injectivity of the addition
  map on `C ×ˢ D` is the core proposition, while the `ExistsUnique` decomposition statement is
  derived API.
- Domain-style sampling: the relevant owner-side declarations are `Set.prod` from `Text_3_5_1`,
  `Set.mem_add`, `Set.mem_sub`, `Set.add_image_prod`, `Set.range_restrict`,
  `Set.injOn_iff_injective`, and `Function.Injective.mem_range_iff_existsUnique`; this item adds
  the specific geometric equivalence
  relating those canonical notions to the textbook criterion that the common part of `C - C` and
  `D - D` is trivial. In this additive-group generality, the empty-set-safe canonical form of
  that criterion is `(C - C) ∩ (D - D) ⊆ {0}`.
- Layer target: `core/canonical` for the injectivity theorem, with a thin `bridge/view`
  companion for the textbook unique-decomposition wording.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: this item is set-valued over one ambient additive
  commutative group and has no extra codomain layer to weaken.
- Scalar/ambient structure over-concrete? `No`: there is no scalar parameter here, and the proof
  uses additive commutative-group algebra exactly.
- Owner tied to a concrete model? `No`: owners are intrinsic set/function owners
  (`Function.Injective`, pointwise set operations).
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topology primitives appear.
- Owner-name/noise issue? `Yes`: restricted-map/subtype bridge lemmas are technical and should be
  internal, leaving public theorems at canonical and source-facing layers.
-/

namespace Set

/-- Canonical addition map on the direct-sum owner `C ×ˢ D`. -/
def addOnProd (C D : Set E) : C ×ˢ D → E :=
  (C ×ˢ D).restrict (fun p : E × E ↦ p.1 + p.2)

@[simp] theorem addOnProd_apply (C D : Set E) (p : C ×ˢ D) :
    addOnProd C D p = p.1.1 + p.1.2 := rfl

/-- Internal `Set.InjOn` bridge used to prove the canonical `Function.Injective` theorem.

This keeps ambient-product injectivity algebra private while exposing public statements through
`addOnProd`. The addition map on the direct sum `C ×ˢ D` is injective on `C ×ˢ D` exactly when the
difference sets `C - C` and `D - D` intersect only in `0`, i.e. their intersection is contained
in `{0}`. This is equivalent to unique decomposition in `C + D`, since existence is already
encoded by membership in the pointwise sum. -/
-- Proof sketch: for `(→)`, if `v ∈ (C - C) ∩ (D - D)`, write `v = c₁ - c₂ = d₁ - d₂`; then
-- `c₂ + d₁ = c₁ + d₂`, so uniqueness of decomposition forces `c₁ = c₂` and hence `v = 0`. For
-- `(←)`, two decompositions `x = y₁ + z₁ = y₂ + z₂` give `y₁ - y₂ = z₂ - z₁`, an element of
-- both difference sets; the intersection criterion implies this difference is `0`, so the two
-- decompositions coincide.
private theorem injOn_add_iff_sub_inter_subset_zero (C D : Set E) :
    InjOn (fun p ↦ p.1 + p.2) (C ×ˢ D) ↔
      (C - C) ∩ (D - D) ⊆ ({0} : Set E) := by
  constructor
  · intro hInj v hv
    rcases hv with ⟨hvC, hvD⟩
    rcases mem_sub.mp hvC with ⟨c₁, hc₁, c₂, hc₂, rfl⟩
    rcases mem_sub.mp hvD with ⟨d₁, hd₁, d₂, hd₂, hdiff⟩
    have hsum : c₁ + d₂ = c₂ + d₁ := by
      have := congrArg (fun x ↦ x + c₂ + d₂) hdiff.symm
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hp : (c₁, d₂) = (c₂, d₁) := hInj (mk_mem_prod hc₁ hd₂) (mk_mem_prod hc₂ hd₁) hsum
    have hc : c₁ = c₂ := congrArg Prod.fst hp
    simp [hc]
  · intro hSubset p hp q hq hsum
    rcases mem_prod.mp hp with ⟨hpC, hpD⟩
    rcases mem_prod.mp hq with ⟨hqC, hqD⟩
    have hdiff : p.1 - q.1 = q.2 - p.2 := by
      have := congrArg (fun x ↦ x - q.1 - p.2) hsum
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hpq0 : p.1 - q.1 = 0 := by
      have : p.1 - q.1 ∈ ({0} : Set E) := hSubset ⟨
        mem_sub.mpr ⟨p.1, hpC, q.1, hqC, rfl⟩,
        mem_sub.mpr ⟨q.2, hqD, p.2, hpD, hdiff.symm⟩⟩
      simpa using this
    have hp1 : p.1 = q.1 := sub_eq_zero.mp hpq0
    have hp2 : p.2 = q.2 := by
      have : p.1 + p.2 = p.1 + q.2 := by simpa [hp1] using hsum
      exact add_left_cancel this
    ext <;> assumption

/-- Text 3.5.3, in canonical owner form: `addOnProd C D` is injective exactly when the
difference sets `C - C` and `D - D` intersect only in `0`, i.e. their intersection is contained
in `{0}`. -/
theorem injective_addOnProd_iff_sub_inter_subset_zero (C D : Set E) :
    Function.Injective (addOnProd C D) ↔
      (C - C) ∩ (D - D) ⊆ ({0} : Set E) := by
  simpa [injOn_iff_injective] using injOn_add_iff_sub_inter_subset_zero C D

/-- The textbook unique-decomposition wording is equivalent to injectivity of the addition map on
`C ×ˢ D` when decompositions are viewed intrinsically as elements of the direct-sum owner
`C ×ˢ D` itself.

This is the canonical subtype-owner bridge: injectivity of `addOnProd C D` is equivalent to
uniqueness of subtype decompositions over the sum set `C + D`. -/
theorem existsUnique_subtype_eq_addOnProd_iff_injective_addOnProd (C D : Set E) :
    (∀ x ∈ C + D, ∃! p : C ×ˢ D,
      x = addOnProd C D p) ↔
      Function.Injective (addOnProd C D) := by
  let f : C ×ˢ D → E := addOnProd C D
  have hRange : Set.range f = C + D := by
    dsimp [f, addOnProd]
    calc
      Set.range ((C ×ˢ D).restrict (fun p ↦ p.1 + p.2)) =
          (fun p ↦ p.1 + p.2) '' (C ×ˢ D) := Set.range_restrict _ _
      _ = C + D := Set.add_image_prod
  constructor
  · intro h p q hpq
    have hx : f p ∈ C + D := hRange ▸ ⟨p, rfl⟩
    rcases h (f p) hx with ⟨r, _, huniq⟩
    have hpEq : p = r := huniq p rfl
    have hqEq : q = r := huniq q hpq
    exact hpEq.trans hqEq.symm
  · intro h x hx
    have hxRange : x ∈ Set.range f := hRange.symm ▸ hx
    rcases (Function.Injective.mem_range_iff_existsUnique h).1 hxRange with ⟨p, hp, huniq⟩
    refine ⟨p, hp.symm, ?_⟩
    intro q hq
    exact huniq q hq.symm

/-- Bridge between the textbook ambient-pair wording and the intrinsic subtype-owner wording for
unique decomposition in `C + D`. -/
private theorem existsUnique_mem_prod_eq_add_iff_existsUnique_subtype_eq_addOnProd
    (C D : Set E) :
    (∀ x ∈ C + D, ∃! p ∈ C ×ˢ D, x = p.1 + p.2) ↔
      (∀ x ∈ C + D, ∃! p : C ×ˢ D,
        x = addOnProd C D p) := by
  constructor
  · intro hUnique x hx
    rcases hUnique x hx with ⟨p, hp, hpUnique⟩
    refine ⟨⟨p, hp.1⟩, ?_, ?_⟩
    · simpa [addOnProd] using hp.2
    · intro q hq
      apply Subtype.ext
      exact hpUnique q.1 ⟨q.2, by simpa [addOnProd] using hq⟩
  · intro hUnique x hx
    rcases hUnique x hx with ⟨p, hp, hpUnique⟩
    refine ⟨p.1, ⟨p.2, ?_⟩, ?_⟩
    · simpa [addOnProd] using hp
    · intro q hq
      have hqSubtype : (⟨q, hq.1⟩ : C ×ˢ D) = p :=
        hpUnique ⟨q, hq.1⟩ (by simpa [addOnProd] using hq.2)
      exact congrArg Subtype.val hqSubtype

/-- Source-facing bridge from textbook ambient-pair unique decomposition wording to canonical
owner-level injectivity of `addOnProd C D`. -/
theorem existsUnique_mem_prod_eq_add_iff_injective_addOnProd (C D : Set E) :
    (∀ x ∈ C + D, ∃! p ∈ C ×ˢ D, x = p.1 + p.2) ↔
      Function.Injective (addOnProd C D) := by
  exact (existsUnique_mem_prod_eq_add_iff_existsUnique_subtype_eq_addOnProd C D).trans
    (existsUnique_subtype_eq_addOnProd_iff_injective_addOnProd C D)

/-- Text 3.5.3 in intrinsic subtype-owner form: every `x ∈ C + D` has a unique decomposition as
an element of the direct-sum owner `C ×ˢ D` if and only if
`(C - C) ∩ (D - D) ⊆ ({0} : Set E)`. -/
theorem existsUnique_subtype_eq_addOnProd_iff_sub_inter_subset_zero (C D : Set E) :
    (∀ x ∈ C + D, ∃! p : C ×ˢ D,
      x = addOnProd C D p) ↔
      (C - C) ∩ (D - D) ⊆ ({0} : Set E) := by
  exact (existsUnique_subtype_eq_addOnProd_iff_injective_addOnProd C D).trans
    (injective_addOnProd_iff_sub_inter_subset_zero C D)

/-- Text 3.5.3, source-facing form: every `x ∈ C + D` admits a unique decomposition
`x = y + z` with `y ∈ C` and `z ∈ D` if and only if the difference sets `C - C` and `D - D`
intersect only in `0`, i.e. their intersection is contained in `{0}`. -/
theorem existsUnique_mem_prod_eq_add_iff_sub_inter_subset_zero (C D : Set E) :
  (∀ x ∈ C + D, ∃! p ∈ C ×ˢ D, x = p.1 + p.2) ↔
      (C - C) ∩ (D - D) ⊆ ({0} : Set E) := by
  exact (existsUnique_mem_prod_eq_add_iff_injective_addOnProd C D).trans
    (injective_addOnProd_iff_sub_inter_subset_zero C D)

end Set

end

/-! ### Text_3_5_4 (from Chap01) -/
section

open scoped Pointwise

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [DistribSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.4 asserts that if `C` is convex, then `C - C` is convex.
- `core/canonical`: the theorem surface should stay on the standard owner `Convex 𝕜` with
  pointwise set subtraction notation.
- `bridge/view`: mathlib's canonical subtraction-closure theorem `Convex.sub` is ring-layer; this
  source item needs only semiring scalar assumptions, so we expose the semiring bridge theorem
  `Convex.sub_semiring` via the chapter's weak-layer sum theorem `Convex.add_set` plus a local
  weak-layer negation bridge `Convex.neg_set`, and then
  specialize to `C - C`.
- Primitive data vs derived API: convexity of `C` is primitive; convexity of `C - C` is derived.
- Layer target: expose both the semiring-primitive bridge and the source-facing self-difference
  specialization on the canonical owner surface.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: there is no extra codomain owner here.
- Scalar/ambient structure stronger than needed? `No`: this stays at the weaker semiring action
  layer `[DistribSMul 𝕜 E]`, avoiding both ring assumptions and unnecessary module structure.
- Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜` on sets.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topology in this item.
- Owner name too concrete/long? `No`: public surfaces use short canonical owner names.
- Missing notation surface? `No`: the primary pointwise subtraction notation `C - C` is used.
-/
/-- Helper for Text 3.5.4: negating a convex set preserves convexity at the weak semiring
`DistribSMul` layer. -/
theorem Convex.neg_set {C : Set E} (hC : Convex 𝕜 C) : Convex 𝕜 (-C) := by
  intro x hx y hy a b ha hb hab
  -- Rewrite the target back to membership in `C` so the original convexity hypothesis applies.
  rw [Set.mem_neg] at hx hy ⊢
  -- A convex combination of negatives is the negative of the corresponding convex combination.
  simpa [smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using hC hx hy ha hb hab

/-- Helper for Text 3.5.4: semiring-level subtraction closure for convex sets.

This is the primitive bridge that removes the ring-only restriction of `Convex.sub` on the
canonical owner `Convex 𝕜`. -/
theorem Convex.sub_semiring {C D : Set E} (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    Convex 𝕜 (C - D) := by
  -- Rewrite subtraction as addition with the negated set and reuse the chapter sum theorem.
  simpa [sub_eq_add_neg] using hC.add_set hD.neg_set

/-- Text 3.5.4: if `C` is convex, then the self-difference set `C - C` is convex.

This is the source-facing specialization of the semiring bridge theorem `Convex.sub_semiring`. -/
theorem Convex.sub_self {C : Set E} (hC : Convex 𝕜 C) : Convex 𝕜 (C - C) := by
  -- Specialize the general subtraction-closure lemma to the self-difference case.
  simpa using hC.sub_semiring hC

end

/-! ### Text_3_5_5 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.5 introduces, from a convex set `C ⊆ E`, the subset
  `K_C = {(λ, x) | 0 ≤ λ, x ∈ λ • C}` in one higher dimension and asserts that it is convex.
- `core/canonical`: the public owner is the existing chapter definition
  `homogenizationSet C : Set (R × E)` from Proposition 2.6.12, with its owner-side derived API
  `Convex.homogenizationSet`.
- `bridge/view`: the textbook notation `K_C` is exactly the already named chapter owner
  `homogenizationSet C`, so the convexity assertion here is exact reuse of the owner theorem rather
  than a new bridge construction.
- Primitive data vs derived API: the set `K_C` itself is the already defined source-facing owner
  `homogenizationSet C`; its convexity is derived API on that owner.
- Domain-style sampling: this item aligns with `homogenizationSet`,
  `mem_homogenizationSet_iff`, `Convex.homogenizationSet`, and the chapter pointed-cone bridge
  `pointedConeHull_lift_eq_homogenizationSet`.
- Layer target: `core/canonical`; this numbered text is exact owner reuse, so the main entry should
  be a direct `recall` of `Convex.homogenizationSet` rather than a parallel local theorem.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this item has no function codomain owner;
  it is a set-convexity statement over the existing canonical owner `Convex R`.
- Scalar or ambient structure too concrete? `No` in this file: this item reuses the upstream owner
  theorem `Convex.homogenizationSet` without adding stronger local assumptions.
- Owner tied to a concrete model? `No`: owner surface is intrinsic (`homogenizationSet` / `Convex`)
  and does not introduce model-specific shadow predicates.
- Ambient vs intrinsic topology issue? `Not applicable`: no topology primitives occur here.
- Owner naming too concrete/long? `No`: theorem surface reuses the short canonical owner theorem
  directly via `recall`.
- Notation need on theorem surface? `Already satisfied`: the source-facing notation bridge `K[·|·]`
  is provided upstream, and this item introduces no parallel notation layer.
-/

/- Text 3.5.5: for a convex set `C`, the set
`K_C = {(λ, x) ∈ R × E | 0 ≤ λ, x ∈ λ • C}` is convex. Since `K_C` is exactly
`homogenizationSet C`, this item is exact reuse of the canonical owner theorem
`Convex.homogenizationSet`. -/
recall Convex.homogenizationSet

/-! ### Theorem_3_5 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.5 states that the direct sum of two convex sets is convex.
- `core/canonical`: once Text 3.5.1 identifies that direct sum with `C ×ˢ D`, the canonical owner
  theorem is `Convex.prod` at the scalar-generic `Convex 𝕜` layer.
- `bridge/view`: product-set constructors and pair-membership (`Set.prod`, `Set.mem_prod`) are
  bridge material and belong to the neighboring bridge text item (`Text_3_5_1`).
- Primitive data vs derived API: only convexity of the two factors is primitive for this theorem
  item; the product bridge is upstream and should not be redundantly re-exposed here.
- Domain-style sampling: this matches the chapter pattern where theorem items expose the owner
  closure theorem directly when the mathlib owner is already primitive-layer correct (for example
  `Theorem_3_4` recalling `Convex.linear_image` and `Convex.linear_preimage`).
- Layer target: `core/canonical`; keep the theorem file owner-first, with bridge declarations left
  to the dedicated bridge text files.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: `Convex.prod` is already codomain-free
  and scalar-generic.
- Scalar/ambient structure stronger than needed? `No`: this theorem stays at the native owner
  assumptions of `Convex.prod`, not a concrete-scalar specialization.
- Concrete-model owner instead of intrinsic owner? `No`: owner is the intrinsic set predicate
  `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is convexity closure, not a
  topological interior/closure statement.
- Owner-name/notation mismatch? `No`: the canonical owner name `Convex.prod` and canonical set
  product notation `×ˢ` are the theorem surface.
- Upstream over-specialization to repair first? `No`: the bridge is already upstream in
  `Text_3_5_1`, so this theorem remains a direct owner recall.
-/

/- Theorem 3.5: after identifying the direct sum with the set product `C ×ˢ D`, convexity is the
canonical owner theorem `Convex.prod`. -/
recall Convex.prod
