module

public import Mathlib.Topology.ContinuousMap.Basic

public section

universe u v

namespace ContinuousMap

/-- Glue continuous maps on two closed sets that cover the domain and agree on their
intersection. -/
noncomputable def pasteClosed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩) :
    ContinuousMap X Y := by
  classical
  let h : X → Y := fun x ↦ if hx : x ∈ A then f ⟨x, hx⟩ else g ⟨x, by
    have hxAB : x ∈ A ∪ B := by
      rw [hcover]
      exact Set.mem_univ x
    exact hxAB.resolve_left hx⟩
  refine ⟨h, ?_⟩
  rw [← continuousOn_univ, ← hcover]
  apply ContinuousOn.union_of_isClosed
  · rw [continuousOn_iff_continuous_restrict]
    convert f.continuous using 1
    ext x
    simp [Set.restrict, h, x.property]
  · rw [continuousOn_iff_continuous_restrict]
    convert g.continuous using 1
    ext x
    by_cases hxA : (x : X) ∈ A
    · simpa [Set.restrict, h, hxA] using hfg ⟨x, hxA, x.property⟩
    · simp [Set.restrict, h, hxA]
  · exact hA
  · exact hB

/-- On the left closed set, `pasteClosed` agrees with the left map. -/
@[simp]
theorem pasteClosed_apply_left
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩)
    (x : A) :
    pasteClosed hA hB hcover f g hfg x = f x := by
  simp [pasteClosed, x.property]

/-- On the right closed set, `pasteClosed` agrees with the right map. -/
@[simp]
theorem pasteClosed_apply_right
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩)
    (x : B) :
    pasteClosed hA hB hcover f g hfg x = g x := by
  by_cases hxA : (x : X) ∈ A
  · simpa [pasteClosed, hxA] using hfg ⟨x, hxA, x.property⟩
  · simp [pasteClosed, hxA]

end ContinuousMap
