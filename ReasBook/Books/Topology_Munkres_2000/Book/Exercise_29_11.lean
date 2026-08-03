module

public import Mathlib.Topology.CompactOpen

public section

namespace Topology.IsQuotientMap

/-- Helper for Exercise 29.11: If `p : X → Y` is a quotient map and `Z` is locally
compact Hausdorff, then the product map `Prod.map p (id : Z → Z)`, denoted
`p × i_Z` in the source, is a quotient map. The Hausdorff hypothesis is not
needed for the conclusion. -/
theorem prodMap_id {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyCompactSpace Z] {p : X → Y} (hp : IsQuotientMap p) :
    IsQuotientMap (Prod.map p (id : Z → Z)) := by
  -- Detect openness after pulling back along the product map.
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ ?_,
    hp.surjective.prodMap Function.surjective_id⟩
  constructor
  · intro hs
    -- The quotient lifting property descends the membership predicate through `p`.
    rw [isOpen_iff_continuous_mem] at hs ⊢
    apply hp.continuous_lift_prod_left
    simpa only [Set.mem_preimage, Prod.map_apply', id_eq] using hs
  · intro hs
    -- The reverse implication is ordinary continuity of the product map.
    exact hs.preimage (hp.continuous.prodMap continuous_id)

/-- Exercise 29.11 (2): If `p : A → B` and `q : C → D` are quotient maps and
`B` and `C` are locally compact Hausdorff, then the product map `Prod.map p q`,
denoted `p × q` in the source, is a quotient map. The Hausdorff hypotheses are
not needed for the conclusion. -/
theorem prodMap {A : Type u₁} {B : Type u₂} {C : Type v₁} {D : Type v₂}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    [LocallyCompactSpace B] [LocallyCompactSpace C] {p : A → B} {q : C → D}
    (hp : IsQuotientMap p) (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map p q) := by
  -- Detect openness after pulling back along the product of the quotient maps.
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ ?_, hp.surjective.prodMap hq.surjective⟩
  constructor
  · intro hs
    rw [isOpen_iff_continuous_mem] at hs ⊢
    -- First descend the membership predicate through the left quotient map.
    have hleft : Continuous fun bc : B × C ↦ (bc.1, q bc.2) ∈ s := by
      apply hp.continuous_lift_prod_left
      simpa only [Set.mem_preimage, Prod.map_apply'] using hs
    -- Then descend through the right quotient map to reach `B × D`.
    apply hq.continuous_lift_prod_right
    simpa only using hleft
  · intro hs
    -- The reverse implication follows from continuity of the product map.
    exact hs.preimage (hp.continuous.prodMap hq.continuous)

end Topology.IsQuotientMap
