module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.ContinuousMap.Basic

public section

open scoped Topology

namespace FourFoldCrosscapPL

universe u v w

variable {ι : Type u} {X : Type v} {Y : Type w}

/-- Helper for Exercise 74.4: the tagged carrier of a family of closed cells. -/
abbrev ClosedCoverCarrier (cell : ι → Set X) := Σ i, cell i

/-- Helper for Exercise 74.4: forget the tag of a point in a finite closed-cell cover. -/
def closedCoverMap (cell : ι → Set X) : ClosedCoverCarrier cell → X :=
  fun point ↦ point.2.1

/-- Helper for Exercise 74.4: the forgetful map from a tagged closed-cell cover is continuous. -/
lemma continuous_closedCoverMap [TopologicalSpace X] (cell : ι → Set X) :
    Continuous (closedCoverMap cell) := by
  -- On each tagged summand the cover map is the canonical subtype inclusion.
  apply continuous_sigma
  intro i
  exact continuous_subtype_val

/-- Helper for Exercise 74.4: bundle the forgetful closed-cover map with its continuity. -/
def closedCoverContinuousMap [TopologicalSpace X] (cell : ι → Set X) :
    C(ClosedCoverCarrier cell, X) :=
  ⟨closedCoverMap cell, continuous_closedCoverMap cell⟩

/-- Helper for Exercise 74.4: a pointwise covering condition makes the tagged cover map
surjective. -/
lemma closedCoverMap_surjective {cell : ι → Set X}
    (hcover : ∀ x, ∃ i, x ∈ cell i) :
    Function.Surjective (closedCoverMap cell) := by
  -- Tag each point by one cell containing it.
  intro x
  obtain ⟨i, hxi⟩ := hcover x
  exact ⟨⟨i, ⟨x, hxi⟩⟩, rfl⟩

/-- Helper for Exercise 74.4: finitely many compact closed cells present their union as a
quotient. -/
lemma isQuotientMap_closedCoverMap [TopologicalSpace X] [T2Space X] [Finite ι]
    {cell : ι → Set X}
    (hcompact : ∀ i, IsCompact (cell i)) (hcover : ∀ x, ∃ i, x ∈ cell i) :
    Topology.IsQuotientMap (closedCoverContinuousMap cell) := by
  -- The finite tagged sum is compact, so its continuous surjection to a Hausdorff space is
  -- quotient. The Hausdorff hypothesis is supplied by the standard compact-to-Hausdorff API.
  letI (i : ι) : CompactSpace (cell i) :=
    isCompact_iff_compactSpace.mp (hcompact i)
  exact Topology.IsQuotientMap.of_surjective_continuous
    (closedCoverMap_surjective hcover) (continuous_closedCoverMap cell)

/-- Helper for Exercise 74.4: cellwise continuous target maps combine continuously on the
tagged cover. -/
lemma continuous_closedCoverTarget [TopologicalSpace X] [TopologicalSpace Y]
    {cell : ι → Set X}
    (target : ∀ i, C(cell i, Y)) :
    Continuous (fun point : ClosedCoverCarrier cell ↦ target point.1 point.2) := by
  -- Continuity out of the sigma type is checked independently on each cell.
  apply continuous_sigma
  intro i
  exact (target i).continuous

/-- Helper for Exercise 74.4: assemble cellwise target maps before descending across overlaps. -/
def closedCoverTarget [TopologicalSpace X] [TopologicalSpace Y] {cell : ι → Set X}
    (target : ∀ i, C(cell i, Y)) : C(ClosedCoverCarrier cell, Y) :=
  ⟨fun point ↦ target point.1 point.2, continuous_closedCoverTarget target⟩

/-- Helper for Exercise 74.4: agreement of cell maps over every overlap is exactly the fiber
compatibility needed to descend the assembled target map. -/
lemma closedCoverTarget_factorsThrough [TopologicalSpace X] [TopologicalSpace Y]
    {cell : ι → Set X}
    (target : ∀ i, C(cell i, Y))
    (hoverlap : ∀ (i j) (x : cell i) (y : cell j), x.1 = y.1 → target i x = target j y) :
    Function.FactorsThrough (closedCoverTarget target) (closedCoverContinuousMap cell) := by
  -- Equality under the cover map exposes two representatives of the same overlap point.
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  exact hoverlap i j x y hxy

/-- Helper for Exercise 74.4: lift compatible maps on a finite compact cell cover to a
continuous map on the covered Hausdorff space. -/
noncomputable def closedCoverLift [TopologicalSpace X] [TopologicalSpace Y]
    [Finite ι] [T2Space X] {cell : ι → Set X}
    (hcompact : ∀ i, IsCompact (cell i)) (hcover : ∀ x, ∃ i, x ∈ cell i)
    (target : ∀ i, C(cell i, Y))
    (hoverlap : ∀ (i j) (x : cell i) (y : cell j), x.1 = y.1 → target i x = target j y) :
    C(X, Y) :=
  (isQuotientMap_closedCoverMap hcompact hcover).lift
    (closedCoverTarget target) (closedCoverTarget_factorsThrough target hoverlap)

/-- Helper for Exercise 74.4: the lifted closed-cover map evaluates by the selected cell map. -/
lemma closedCoverLift_apply [TopologicalSpace X] [TopologicalSpace Y]
    [Finite ι] [T2Space X] {cell : ι → Set X}
    (hcompact : ∀ i, IsCompact (cell i)) (hcover : ∀ x, ∃ i, x ∈ cell i)
    (target : ∀ i, C(cell i, Y))
    (hoverlap : ∀ (i j) (x : cell i) (y : cell j), x.1 = y.1 → target i x = target j y)
    (i : ι) (x : cell i) :
    closedCoverLift hcompact hcover target hoverlap x = target i x := by
  -- Apply the quotient-lift computation rule to the tagged representative `x`.
  have hcomp := (isQuotientMap_closedCoverMap hcompact hcover).lift_comp
    (closedCoverTarget target) (closedCoverTarget_factorsThrough target hoverlap)
  exact congrArg (fun f : C(ClosedCoverCarrier cell, Y) ↦ f ⟨i, x⟩) hcomp

end FourFoldCrosscapPL
