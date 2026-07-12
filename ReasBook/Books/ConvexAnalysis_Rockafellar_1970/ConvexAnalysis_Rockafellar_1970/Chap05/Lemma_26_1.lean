import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_3

open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 26.1 is the graph criterion for when a multivalued mapping and its
  inverse are both single-valued.
- `core/canonical`: Definition 26.0.3 already identifies one-to-one multivalued mappings with the
  canonical `SetRel` owner `ρ.BiUnique`.
- `bridge/view`: the graph-language criterion in this lemma is the coordinate-projection
  reformulation of that owner: `Set.InjOn Prod.fst ρ` and `Set.InjOn Prod.fst ρ⁻¹`.

Domain-style sampling used here:
- `SetRel`, `SetRel.inv`, and graph-membership notation from mathlib's `Data/Rel`;
- `Relator.BiUnique` from `Mathlib/Logic/Relator.lean`;
- `SetRel.biUnique_iff_leftUnique_and_rightUnique` from `Definition_26_0_3`;
- `Relator.RightUnique` and `Relator.LeftUnique` from `Mathlib/Logic/Relator.lean`;
- `Set.InjOn`.

Primitive data vs derived API:
- primitive owner data: a relation `ρ : SetRel α β`;
- primitive owner predicate: `ρ.BiUnique`;
- derived API: first-projection injectivity on `ρ` and `ρ⁻¹` (source-primary inverse wording),
  together with the coordinate-uniqueness graph criterion.

Layer target: `bridge/view`. The public statement stays source-facing, but it is now phrased as a
companion characterization of the canonical owner from Definition 26.0.3 rather than as a parallel
replacement for it.
-/

namespace SetRel

/-- A relation has at most one second-coordinate value over each first-coordinate point exactly
when the first projection is injective on its graph. -/
theorem injOn_fst_iff (ρ : SetRel α β) :
    Set.InjOn Prod.fst ρ ↔
      ∀ ⦃x : α⦄ ⦃xStar1 xStar2 : β⦄, x ~[ρ] xStar1 → x ~[ρ] xStar2 → xStar1 = xStar2 := by
  constructor
  · intro h x xStar1 xStar2 hx1 hx2
    simpa using congrArg Prod.snd (h hx1 hx2 rfl)
  · intro h p hp q hq hpq
    rcases p with ⟨x1, xStar1⟩
    rcases q with ⟨x2, xStar2⟩
    dsimp at hpq
    cases hpq
    simpa [Prod.mk.injEq] using h hp hq

/-- Injectivity of the second projection on the original graph is exactly injectivity of the first
projection on the inverse graph. This is the canonical bridge from the source's inverse-wording to
the owner projection criterion on `ρ` itself. -/
@[simp] theorem injOn_fst_inv_iff_injOn_snd (ρ : SetRel α β) :
    Set.InjOn Prod.fst ρ⁻¹ ↔ Set.InjOn Prod.snd ρ := by
  constructor
  · intro h p hp q hq hpq
    have hp' : p.swap ∈ ρ⁻¹ := hp
    have hq' : q.swap ∈ ρ⁻¹ := hq
    exact congrArg Prod.swap (h hp' hq' hpq)
  · intro h p hp q hq hpq
    have hp' : p.swap ∈ ρ := hp
    have hq' : q.swap ∈ ρ := hq
    exact congrArg Prod.swap (h hp' hq' hpq)

/-- A relation has at most one first-coordinate value over each second-coordinate point exactly
when the second projection is injective on its graph. This is the direct `ρ`-side companion to
`injOn_fst_inv_iff`. -/
theorem injOn_snd_iff (ρ : SetRel α β) :
    Set.InjOn Prod.snd ρ ↔
      ∀ ⦃x1 x2 : α⦄ ⦃xStar : β⦄, x1 ~[ρ] xStar → x2 ~[ρ] xStar → x1 = x2 := by
  rw [← injOn_fst_inv_iff_injOn_snd]
  constructor
  · intro h x1 x2 xStar hx1 hx2
    exact (injOn_fst_iff ρ⁻¹).1 h hx1 hx2
  · intro h
    exact (injOn_fst_iff ρ⁻¹).2 fun {x} {xStar1} {xStar2} hx1 hx2 ↦ h hx1 hx2

/-- Right-uniqueness of the relation owner is exactly injectivity of the first projection on its
graph. -/
theorem rightUnique_iff_injOn_fst (ρ : SetRel α β) :
    ρ.RightUnique ↔ Set.InjOn Prod.fst ρ := by
  simpa [SetRel.RightUnique, Relator.RightUnique] using (injOn_fst_iff ρ).symm

/-- Left-uniqueness of the relation owner is exactly injectivity of the second projection on its
graph. -/
theorem leftUnique_iff_injOn_snd (ρ : SetRel α β) :
    ρ.LeftUnique ↔ Set.InjOn Prod.snd ρ := by
  simpa [SetRel.LeftUnique, Relator.LeftUnique] using (injOn_snd_iff ρ).symm

/-- Left-uniqueness of the original relation is exactly injectivity of the first projection on
the inverse graph. This is the source inverse-single-valuedness bridge at the projection layer. -/
theorem leftUnique_iff_injOn_fst_inv (ρ : SetRel α β) :
    ρ.LeftUnique ↔ Set.InjOn Prod.fst ρ⁻¹ := by
  rw [leftUnique_iff_injOn_snd, ← injOn_fst_inv_iff_injOn_snd]

/-- Companion criterion: the canonical one-to-one owner is equivalent to injectivity of both
coordinate projections on the graph of `ρ`. -/
theorem biUnique_iff_injOn_fst_and_snd (ρ : SetRel α β) :
    ρ.BiUnique ↔
      Set.InjOn Prod.fst ρ ∧ Set.InjOn Prod.snd ρ := by
  constructor
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique] at h
    exact ⟨(rightUnique_iff_injOn_fst ρ).1 h.2, (leftUnique_iff_injOn_snd ρ).1 h.1⟩
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique]
    exact ⟨(leftUnique_iff_injOn_snd ρ).2 h.2, (rightUnique_iff_injOn_fst ρ).2 h.1⟩

/-- Source-inverse companion: the canonical one-to-one owner is equivalent to injectivity of the
first projection on the graph of `ρ` and on the graph of `ρ⁻¹`. -/
theorem biUnique_iff_injOn_fst_and_fst_inv (ρ : SetRel α β) :
    ρ.BiUnique ↔
      Set.InjOn Prod.fst ρ ∧ Set.InjOn Prod.fst ρ⁻¹ := by
  constructor
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique] at h
    exact ⟨(rightUnique_iff_injOn_fst ρ).1 h.2, (leftUnique_iff_injOn_fst_inv ρ).1 h.1⟩
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique]
    exact ⟨(leftUnique_iff_injOn_fst_inv ρ).2 h.2, (rightUnique_iff_injOn_fst ρ).2 h.1⟩

/-- Source-inverse graph criterion: one-to-one-ness is equivalent to first-coordinate uniqueness on
both `ρ` and `ρ⁻¹`. This keeps the source inverse wording while staying at the first-projection
criterion on each graph. -/
theorem biUnique_iff_graph_fst_uniqueness_and_inv_fst_uniqueness (ρ : SetRel α β) :
    ρ.BiUnique ↔
      (∀ ⦃x : α⦄ ⦃xStar1 xStar2 : β⦄, x ~[ρ] xStar1 → x ~[ρ] xStar2 → xStar1 = xStar2) ∧
        ∀ ⦃xStar : β⦄ ⦃x1 x2 : α⦄, xStar ~[ρ⁻¹] x1 → xStar ~[ρ⁻¹] x2 → x1 = x2 := by
  rw [biUnique_iff_injOn_fst_and_fst_inv, injOn_fst_iff, injOn_fst_iff]

/-- Lemma 26.1: a multivalued mapping is one-to-one exactly when its graph contains neither two
distinct pairs with the same first coordinate nor two distinct pairs with the same second
coordinate. This is the graph-side characterization of the canonical owner
`ρ.BiUnique`. -/
theorem biUnique_iff_graph_coordinate_uniqueness (ρ : SetRel α β) :
    ρ.BiUnique ↔
      (∀ ⦃x : α⦄ ⦃xStar1 xStar2 : β⦄, x ~[ρ] xStar1 → x ~[ρ] xStar2 → xStar1 = xStar2) ∧
        ∀ ⦃x1 x2 : α⦄ ⦃xStar : β⦄, x1 ~[ρ] xStar → x2 ~[ρ] xStar → x1 = x2 := by
  constructor
  · intro h
    rcases (biUnique_iff_graph_fst_uniqueness_and_inv_fst_uniqueness ρ).1 h with ⟨hρ, hρinv⟩
    refine ⟨hρ, ?_⟩
    intro x1 x2 xStar hx1 hx2
    exact hρinv (by simpa [SetRel.mem_inv] using hx1) (by simpa [SetRel.mem_inv] using hx2)
  · intro h
    refine (biUnique_iff_graph_fst_uniqueness_and_inv_fst_uniqueness ρ).2 ?_
    refine ⟨h.1, ?_⟩
    intro xStar x1 x2 hx1 hx2
    exact h.2 (by simpa [SetRel.mem_inv] using hx1) (by simpa [SetRel.mem_inv] using hx2)

end SetRel

end
