module

public import Topology_Munkres_2000.Book.Theorem_63_1

public section

open Set

namespace FundamentalGroup

/-- Crossing-cover data for the images of two composable source paths. -/
structure CrossingCoverData
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {a b : X} (α : Path a b) (β : Path b a) where
  U : Set Y
  V : Set Y
  A : Set Y
  B : Set Y
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isOpen_A : IsOpen A
  isOpen_B : IsOpen B
  cover : U ∪ V = Set.univ
  overlap : U ∩ V = A ∪ B
  disjoint : Disjoint A B
  source_mem : f a ∈ A
  target_mem : f b ∈ B
  map_first_mem : ∀ t, f (α t) ∈ U
  map_second_mem : ∀ t, f (β t) ∈ V

/-- Mapping a concatenated loop maps each of its two constituent paths. -/
lemma map_fromPath_trans
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {a b : X} (α : Path a b) (β : Path b a) :
    map f a (fromPath (Path.Homotopic.Quotient.mk (α.trans β))) =
      fromPath
        (Path.Homotopic.Quotient.mk
          ((α.map f.continuous).trans (β.map f.continuous))) := by
  -- Expose quotient mapping, then use functoriality of path concatenation.
  rw [map_apply, ← Path.Homotopic.Quotient.mk_map, Path.map_trans]

/-- Crossing-cover data makes the image of a source loop generate the target
fundamental group. -/
lemma CrossingCoverData.existsGeneratorImage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {a b : X} (α : Path a b) (β : Path b a)
    (data : CrossingCoverData f α β)
    [Infinite (FundamentalGroup Y (f a))]
    [IsCyclic (FundamentalGroup Y (f a))] :
    ∃ g : FundamentalGroup X a, Subgroup.zpowers (map f a g) = ⊤ := by
  -- Theorem 63.1 applies to the two mapped paths and supplies the target generator.
  have mappedLoopGenerates :
      Subgroup.zpowers
          (fromPath
            (Path.Homotopic.Quotient.mk
              ((α.map f.continuous).trans (β.map f.continuous)))) = ⊤ := by
    exact crossingLoopClass_zpowers_eq_top data.U data.V data.A data.B
      (α.map f.continuous) (β.map f.continuous) data.isOpen_U data.isOpen_V
      data.isOpen_A data.isOpen_B data.cover data.overlap data.disjoint
      data.source_mem data.target_mem data.map_first_mem data.map_second_mem
  -- Choose the original concatenated loop and identify its image propositionally.
  refine ⟨fromPath (Path.Homotopic.Quotient.mk (α.trans β)), ?_⟩
  rw [map_fromPath_trans]
  exact mappedLoopGenerates

/-- A crossing-cover generator certificate makes the induced fundamental-group
map surjective. -/
lemma CrossingCoverData.mapSurjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {a b : X} (α : Path a b) (β : Path b a)
    (data : CrossingCoverData f α β)
    [Infinite (FundamentalGroup Y (f a))]
    [IsCyclic (FundamentalGroup Y (f a))] :
    Function.Surjective (map f a) := by
  -- First obtain one source loop whose image generates the cyclic target.
  obtain ⟨g, hg⟩ := data.existsGeneratorImage f α β
  intro y
  have hy : y ∈ Subgroup.zpowers (map f a g) := by
    rw [hg]
    exact Subgroup.mem_top y
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  -- The matching integral power of the source loop maps to the given element.
  refine ⟨g ^ n, ?_⟩
  rw [map_zpow, hn]

namespace CrossingCoverData

/-- Helper for Remark 65.1: two distinct endpoint components exhaust an open
overlap having exactly two connected components. -/
lemma ofTwoOverlapComponents
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace Y]
    (f : C(X, Y)) {a b : X} (alpha : Path a b) (beta : Path b a)
    (U V : Set Y) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (ha : f a ∈ U ∩ V) (hb : f b ∈ U ∩ V)
    (hdifferent : connectedComponentIn (U ∩ V) (f a) ≠
      connectedComponentIn (U ∩ V) (f b))
    (hcomponents : Cardinal.mk (ConnectedComponents (U ∩ V : Set Y)) = 2)
    (halpha : ∀ t, f (alpha t) ∈ U) (hbeta : ∀ t, f (beta t) ∈ V) :
    Nonempty (CrossingCoverData f alpha beta) := by
  classical
  let aOverlap : (U ∩ V : Set Y) := ⟨f a, ha⟩
  let bOverlap : (U ∩ V : Set Y) := ⟨f b, hb⟩
  have endpointClasses_ne :
      (aOverlap : ConnectedComponents (U ∩ V : Set Y)) ≠ bOverlap := by
    -- Equality in the component quotient would identify the two ambient components.
    intro hclasses
    apply hdifferent
    rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb]
    exact congrArg (fun S : Set (U ∩ V : Set Y) ↦ Subtype.val '' S)
      (ConnectedComponents.coe_eq_coe.mp hclasses)
  have componentCases (y : (U ∩ V : Set Y)) :
      (y : ConnectedComponents (U ∩ V : Set Y)) = aOverlap ∨
        (y : ConnectedComponents (U ∩ V : Set Y)) = bOverlap := by
    -- Cardinality two says the class distinct from the first endpoint is unique.
    obtain ⟨other, hother, hotherUnique⟩ :=
      (Cardinal.mk_eq_two_iff'
        (aOverlap : ConnectedComponents (U ∩ V : Set Y))).mp hcomponents
    have b_eq_other :
        (bOverlap : ConnectedComponents (U ∩ V : Set Y)) = other :=
      hotherUnique bOverlap endpointClasses_ne.symm
    by_cases hy : (y : ConnectedComponents (U ∩ V : Set Y)) = aOverlap
    · exact Or.inl hy
    · exact Or.inr ((hotherUnique y hy).trans b_eq_other.symm)
  let A : Set Y := connectedComponentIn (U ∩ V) (f a)
  let B : Set Y := connectedComponentIn (U ∩ V) (f b)
  have overlap_eq : U ∩ V = A ∪ B := by
    -- Lift an overlap point to the subtype and use the two quotient-class cases.
    apply Set.Subset.antisymm
    · intro y hy
      rcases componentCases ⟨y, hy⟩ with hyA | hyB
      · apply Or.inl
        simp only [A, connectedComponentIn_eq_image ha]
        exact ⟨⟨y, hy⟩, ConnectedComponents.coe_eq_coe'.mp hyA, rfl⟩
      · apply Or.inr
        simp only [B, connectedComponentIn_eq_image hb]
        exact ⟨⟨y, hy⟩, ConnectedComponents.coe_eq_coe'.mp hyB, rfl⟩
    · exact Set.union_subset
        (connectedComponentIn_subset (U ∩ V) (f a))
        (connectedComponentIn_subset (U ∩ V) (f b))
  have components_disjoint : Disjoint A B := by
    -- Intersecting canonical components would make them equal.
    rw [Set.disjoint_left]
    intro y hyA hyB
    apply hdifferent
    exact (connectedComponentIn_eq hyA).trans (connectedComponentIn_eq hyB).symm
  -- The two canonical components now supply all fields of the crossing certificate.
  exact ⟨
    { U := U
      V := V
      A := A
      B := B
      isOpen_U := hUopen
      isOpen_V := hVopen
      isOpen_A := (hUopen.inter hVopen).connectedComponentIn
      isOpen_B := (hUopen.inter hVopen).connectedComponentIn
      cover := hcover
      overlap := overlap_eq
      disjoint := components_disjoint
      source_mem := mem_connectedComponentIn ha
      target_mem := mem_connectedComponentIn hb
      map_first_mem := halpha
      map_second_mem := hbeta }⟩

end CrossingCoverData

end FundamentalGroup
