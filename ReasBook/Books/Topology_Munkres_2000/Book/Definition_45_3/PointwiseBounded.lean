module

public import Mathlib.Topology.Bornology.Constructions

public section

universe u v w

/-- A family of functions is pointwise bounded when its values at each point form a bounded set. -/
def PointwiseBounded {ι : Type w} {X : Type u} {Y : Type v} [Bornology Y]
    (F : ι → X → Y) : Prop :=
  ∀ x, Bornology.IsBounded (Set.range (fun i ↦ F i x))

/-- An indexed family is pointwise bounded exactly when each pointwise range is bounded. -/
theorem pointwiseBounded_iff {ι : Type w} {X : Type u} {Y : Type v} [Bornology Y]
    {F : ι → X → Y} :
    PointwiseBounded F ↔ ∀ x, Bornology.IsBounded (Set.range (fun i ↦ F i x)) :=
  Iff.rfl

/-- A set of function-like maps is pointwise bounded when its values at each point form a bounded
set. -/
protected abbrev Set.PointwiseBounded {F : Type w} {X : Type u} {Y : Type v}
    [CoeFun F (fun _ ↦ X → Y)] [Bornology Y] (𝓕 : Set F) : Prop :=
  PointwiseBounded (fun f : 𝓕 ↦ (f : F))

/-- A set of function-like maps is pointwise bounded exactly when every evaluation image is
bounded. -/
theorem Set.pointwiseBounded_iff {F : Type w} {X : Type u} {Y : Type v}
    [CoeFun F (fun _ ↦ X → Y)] [Bornology Y] {𝓕 : Set F} :
    𝓕.PointwiseBounded ↔ ∀ x, Bornology.IsBounded ((fun f : F ↦ f x) '' 𝓕) := by
  -- Expose the pointwise ranges, then identify each image with its subtype-indexed range.
  simp only [Set.PointwiseBounded, PointwiseBounded, Set.image_eq_range]

/-- The range of an indexed family is pointwise bounded exactly when the family is. -/
theorem pointwiseBounded_range_iff {ι : Type w} {X : Type u} {Y : Type v} [Bornology Y]
    (F : ι → X → Y) :
    PointwiseBounded (fun f : Set.range F ↦ f.1) ↔ PointwiseBounded F := by
  -- Rewrite both families through the common evaluation image of `Set.range F`.
  rw [_root_.pointwiseBounded_iff, _root_.pointwiseBounded_iff]
  constructor
  · intro h x
    have hx := h x
    rw [← Set.image_eq_range (fun f : X → Y ↦ f x) (Set.range F),
      ← Set.range_comp' (fun f : X → Y ↦ f x) F] at hx
    exact hx
  · intro h x
    rw [← Set.image_eq_range (fun f : X → Y ↦ f x) (Set.range F),
      ← Set.range_comp' (fun f : X → Y ↦ f x) F]
    exact h x
