module

public import Mathlib.Topology.MetricSpace.Bounded

public section

universe u v

/-- A bounded function is a function whose range is bounded. -/
structure BoundedFunction (X : Type u) (Y : Type v) [PseudoMetricSpace Y] where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The range of the underlying function is bounded. -/
  isBounded_range : Bornology.IsBounded (Set.range toFun)

namespace BoundedFunction

variable {X : Type u} {Y : Type v} [PseudoMetricSpace Y]

/-- Bounded functions coerce to their underlying functions. -/
instance instFunLike : FunLike (BoundedFunction X Y) X Y where
  coe f := f.toFun
  coe_injective := by
    -- Reduce equality of bounded functions to equality of their underlying functions.
    intro f g h
    cases f with
    | mk f hf =>
      cases g with
      | mk g hg =>
        cases h
        rfl

/-- Evaluation of a bounded function constructed from a raw function. -/
@[simp]
theorem coe_mk (f : X → Y) (hf : Bornology.IsBounded (Set.range f)) :
    ⇑(BoundedFunction.mk f hf) = f := by
  -- The coercion is definitionally the stored function.
  rfl

/-- Two bounded functions are equal when they agree pointwise. -/
@[ext]
theorem ext {f g : BoundedFunction X Y} (h : ∀ x, f x = g x) : f = g := by
  -- Use the standard extensionality principle for function-like structures.
  exact DFunLike.ext f g h

/-- The supremum distance between bounded functions. -/
noncomputable instance instDist : Dist (BoundedFunction X Y) where
  dist f g := sSup (Set.range (fun x ↦ dist (f.toFun x) (g.toFun x)))

/-- Helper for Definition 43.4: the raw distance instance computes as the supremum of pointwise
distances. -/
theorem supDist_apply (f g : BoundedFunction X Y) :
    @dist (BoundedFunction X Y) instDist f g =
      sSup (Set.range (fun x ↦ dist (f x) (g x))) := rfl

/-- Helper for Definition 43.4: the range of pointwise distances between two bounded functions
is bounded above. -/
theorem distRange_bddAbove (f g : BoundedFunction X Y) :
    BddAbove (Set.range (fun x ↦ dist (f x) (g x))) := by
  -- Both values lie in the bounded union of the two function ranges.
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (f.isBounded_range.union g.isBounded_range)
  refine ⟨C, ?_⟩
  intro d hd
  obtain ⟨x, rfl⟩ := hd
  exact hC (Set.mem_union_left _ (Set.mem_range_self x))
    (Set.mem_union_right _ (Set.mem_range_self x))

/-- Helper for Definition 43.4: the raw supremum distance from a bounded function to itself is
zero. -/
theorem supDist_self (f : BoundedFunction X Y) :
    @dist (BoundedFunction X Y) instDist f f = 0 := by
  -- Every pointwise self-distance is zero, so its supremum is zero.
  rw [supDist_apply, sSup_range]
  simp only [dist_self, Real.iSup_const_zero]

/-- Helper for Definition 43.4: the raw supremum distance is symmetric. -/
theorem supDist_comm (f g : BoundedFunction X Y) :
    @dist (BoundedFunction X Y) instDist f g = @dist (BoundedFunction X Y) instDist g f := by
  -- Pointwise symmetry passes directly through the supremum.
  rw [supDist_apply, supDist_apply]
  apply congrArg sSup
  ext d
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, dist_comm (g x) (f x)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, dist_comm (f x) (g x)⟩

/-- Helper for Definition 43.4: the raw supremum distance satisfies the triangle inequality. -/
theorem supDist_triangle (f g h : BoundedFunction X Y) :
    @dist (BoundedFunction X Y) instDist f h ≤
      @dist (BoundedFunction X Y) instDist f g + @dist (BoundedFunction X Y) instDist g h := by
  -- Bound each pointwise distance by the sum of the two suprema.
  rcases isEmpty_or_nonempty X with hX | hX
  · letI : IsEmpty X := hX
    rw [supDist_apply, supDist_apply, supDist_apply]
    rw [sSup_range, sSup_range, sSup_range]
    simp only [Real.iSup_of_isEmpty, add_zero, le_refl]
  · letI : Nonempty X := hX
    rw [supDist_apply, supDist_apply, supDist_apply]
    refine csSup_le (Set.range_nonempty _) ?_
    intro d hd
    obtain ⟨x, rfl⟩ := hd
    calc
      dist (f x) (h x) ≤ dist (f x) (g x) + dist (g x) (h x) := dist_triangle _ _ _
      _ ≤ @dist (BoundedFunction X Y) instDist f g +
          @dist (BoundedFunction X Y) instDist g h := add_le_add
        (le_csSup (distRange_bddAbove f g) (Set.mem_range_self x))
        (le_csSup (distRange_bddAbove g h) (Set.mem_range_self x))

/-- Bounded functions form a pseudometric space under the supremum distance. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (BoundedFunction X Y) where
  toDist := instDist
  dist_self := supDist_self
  dist_comm := supDist_comm
  dist_triangle := supDist_triangle

/-- Helper for Definition 43.4: the pseudometric distance computes as the supremum of pointwise
distances. -/
theorem dist_eq_sSup (f g : BoundedFunction X Y) :
    dist f g = sSup (Set.range (fun x ↦ dist (f x) (g x))) := rfl

/-- Helper for Definition 43.4: bounded functions into a metric space carry the sup metric. -/
noncomputable local instance instMetricSpaceSupport {Y : Type v} [MetricSpace Y] :
    MetricSpace (BoundedFunction X Y) := MetricSpace.mk fun {f g} hfg ↦ by
    -- Zero supremum distance forces zero distance at every point.
    apply ext
    intro x
    apply eq_of_dist_eq_zero
    apply le_antisymm
    · calc
        dist (f x) (g x) ≤ sSup (Set.range (fun x ↦ dist (f x) (g x))) :=
          le_csSup (distRange_bddAbove f g) (Set.mem_range_self x)
        _ = dist f g := (dist_eq_sSup f g).symm
        _ = 0 := hfg
    · exact dist_nonneg

/-- The supremum distance is the indexed supremum of pointwise distances. -/
theorem dist_eq_iSup (f g : BoundedFunction X Y) :
    dist f g = ⨆ x, dist (f x) (g x) := by
  -- Rewrite the supremum of a range as an indexed supremum.
  exact sSup_range

/-- Pointwise distance is bounded by the supremum distance. -/
theorem dist_coe_le_dist (f g : BoundedFunction X Y) (x : X) :
    dist (f x) (g x) ≤ dist f g := by
  -- The value at `x` is a member of the range defining the supremum.
  exact le_csSup (distRange_bddAbove f g) (Set.mem_range_self x)

/-- A nonnegative constant bounds the supremum distance exactly when it bounds every pointwise
distance. -/
theorem dist_le (f g : BoundedFunction X Y) {C : ℝ} (hC : 0 ≤ C) :
    dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  -- One direction follows from the pointwise bound by the supremum.
  constructor
  · intro h x
    exact (dist_coe_le_dist f g x).trans h
  · intro h
    rcases isEmpty_or_nonempty X with hX | hX
    · letI : IsEmpty X := hX
      rw [dist_eq_iSup, Real.iSup_of_isEmpty]
      exact hC
    · letI : Nonempty X := hX
      refine csSup_le (Set.range_nonempty _) ?_
      intro d hd
      obtain ⟨x, rfl⟩ := hd
      exact h x


end BoundedFunction
