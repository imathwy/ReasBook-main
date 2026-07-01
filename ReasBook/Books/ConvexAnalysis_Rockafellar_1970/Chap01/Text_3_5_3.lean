import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict

-- Declarations for this item will be appended below by the statement pipeline.

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
