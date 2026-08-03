module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.DerivedSet

public section

universe u

/-- Helper for Exercise 30.3: a point of `A` outside `derivedSet A` is isolated in
`A` by an element of the canonical countable basis. -/
private lemma Set.exists_countableBasis_inter_eq_singleton {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] {A : Set X} {x : X} (hxA : x ∈ A)
    (hx : x ∉ derivedSet A) :
    ∃ B ∈ TopologicalSpace.countableBasis X, x ∈ B ∧ B ∩ A = {x} := by
  -- Negating the accumulation-point criterion gives a neighborhood containing
  -- no point of `A` other than `x`.
  rw [mem_derivedSet, accPt_iff_nhds] at hx
  push Not at hx
  obtain ⟨U, hU, hU_unique⟩ := hx
  -- Refine that neighborhood to an element of the canonical countable basis.
  obtain ⟨B, ⟨hB_basis, hxB⟩, hBU⟩ :=
    (TopologicalSpace.isBasis_countableBasis X).nhds_hasBasis.mem_iff.mp hU
  refine ⟨B, hB_basis, hxB, ?_⟩
  -- The refined basis element meets `A` exactly at the isolated point.
  ext y
  constructor
  · intro hy
    have hyx : y = x := hU_unique y ⟨hBU hy.1, hy.2⟩
    simp [hyx]
  · intro hy
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨hxB, hxA⟩

/-- In a second-countable space, a set has only countably many points that are
not limit points of the set. -/
theorem Set.countable_sdiff_derivedSet {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (A : Set X) : (A \ derivedSet A).Countable := by
  classical
  -- Select one isolating countable-basis element for each non-limit point.
  choose B hB_basis hxB hB_inter using fun x : {x : X // x ∈ A \ derivedSet A} ↦
    Set.exists_countableBasis_inter_eq_singleton x.property.1 x.property.2
  let selectedBasis : {x : X // x ∈ A \ derivedSet A} →
      TopologicalSpace.countableBasis X :=
    fun x ↦ ⟨B x, hB_basis x⟩
  -- Equality of selected basis elements forces equality of their unique points in `A`.
  have selectedBasis_injective : Function.Injective selectedBasis := by
    intro x y hxy
    have hBxy : B x = B y := congrArg Subtype.val hxy
    have hyB : y.1 ∈ B x := by
      rw [hBxy]
      exact hxB y
    have hy_singleton : y.1 ∈ ({x.1} : Set X) := by
      rw [← hB_inter x]
      exact ⟨hyB, y.property.1⟩
    have hyx : y.1 = x.1 := by simpa using hy_singleton
    exact Subtype.ext hyx.symm
  -- The domain is countable because it injects into the countable basis subtype.
  exact selectedBasis_injective.countable

/-- Exercise 30.3. In a second-countable space, an uncountable set has
uncountably many points that are limit points of the set. -/
theorem Set.uncountable_inter_derivedSet {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] {A : Set X} (hA : ¬ A.Countable) :
    ¬ (A ∩ derivedSet A).Countable := by
  -- If the limit points in `A` were countable, the two-piece decomposition of
  -- `A` would contradict its assumed uncountability.
  intro h
  apply hA
  rw [← sdiff_union_inter A (derivedSet A)]
  exact (countable_sdiff_derivedSet A).union h
