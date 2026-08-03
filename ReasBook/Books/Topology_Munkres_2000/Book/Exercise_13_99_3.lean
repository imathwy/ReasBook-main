module

public import Topology_Munkres_2000.Book.Exercise_53_6
public import Topology_Munkres_2000.Book.Exercise_53_3
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.Discrete

import Topology_Munkres_2000.Book.Theorem_54_4

public section

universe u v

/- Exercise 13.99.3, regularity assertion. The total space of a covering map over
a regular space is regular, where Munkres's regularity is represented by
`T3Space`. -/
#check IsCoveringMap.t3Space

namespace IsCoveringMap

/-- Helper for Exercise 13.99.3: a surjective covering with path-connected total space has
countable fibers when one fundamental group of the base is countable. -/
private lemma countable_fiber_of_countable_fundamentalGroup
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (x₀ b : X)
    [PathConnectedSpace E] [Countable (FundamentalGroup X x₀)] :
    Countable (p ⁻¹' {b}) := by
  -- Surjectivity transfers path-connectedness to the base, so all fibers are equivalent.
  letI : PathConnectedSpace X := hsurj.pathConnectedSpace hp.continuous
  obtain ⟨e₀, he₀⟩ := hsurj x₀
  have he₀Fiber : e₀ ∈ p ⁻¹' {x₀} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using he₀
  let e₀Fiber : p ⁻¹' {x₀} := ⟨e₀, he₀Fiber⟩
  have hCountable₀ : Countable (p ⁻¹' {x₀}) :=
    (hp.liftingCorrespondence_surjective e₀Fiber).countable
  -- Normalize the two fiber presentations once, then transport countability by equivalence.
  have hSource : p ⁻¹' {x₀} = {e : E | p e = x₀} := by
    ext e
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  have hTarget : p ⁻¹' {b} = {e : E | p e = b} := by
    ext e
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  obtain ⟨e⟩ := hp.fiberEquiv x₀ b
  let fiberEquiv : (p ⁻¹' {x₀}) ≃ (p ⁻¹' {b}) :=
    (Equiv.setCongr hSource).trans (e.trans (Equiv.setCongr hTarget.symm))
  exact fiberEquiv.countable_iff.mp hCountable₀

/-- Helper for Exercise 13.99.3: a covering of a second-countable space with countable
fibers has second-countable total space. -/
private lemma secondCountableTopology_of_countable_fibers
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) [SecondCountableTopology X]
    [∀ b : X, Countable (p ⁻¹' {b})] : SecondCountableTopology E := by
  classical
  -- Choose one open product chart around every base point.
  choose hDiscrete U hbU hUOpen hpUOpen H hH using hp
  have hUNhds : ∀ b : X, U b ∈ nhds b :=
    fun b ↦ (hUOpen b).mem_nhds (hbU b)
  obtain ⟨s, hsCountable, hsCover⟩ :=
    TopologicalSpace.countable_cover_nhds hUNhds
  letI : Countable s := hsCountable.to_subtype
  -- Each selected preimage is homeomorphic to a product of second-countable spaces.
  have hChartSecondCountable (b : X) : SecondCountableTopology (p ⁻¹' U b) := by
    letI : DiscreteTopology (p ⁻¹' {b}) := hDiscrete b
    letI : SecondCountableTopology (p ⁻¹' {b}) := inferInstance
    letI : SecondCountableTopology (U b) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    exact (H b).secondCountableTopology
  letI : ∀ i : s, SecondCountableTopology (p ⁻¹' U i.1) :=
    fun i ↦ hChartSecondCountable i.1
  -- Pull the countable neighborhood cover back to the total space.
  have hPreimageCover : ⋃ i : s, p ⁻¹' U i.1 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    have hpe : p e ∈ ⋃ b ∈ s, U b := by
      rw [hsCover]
      exact Set.mem_univ (p e)
    obtain ⟨b, hpe⟩ := Set.mem_iUnion.mp hpe
    obtain ⟨hb, hpe⟩ := Set.mem_iUnion.mp hpe
    exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hpe⟩
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun i : s ↦ hpUOpen i.1) hPreimageCover

/-- Exercise 13.99.3, countable-basis assertion. Let `p : E → X` be a surjective
covering map with path-connected total space and locally path-connected base. If
`X` has a countable basis and `FundamentalGroup X x₀` is countable, then `E` has
a countable basis. -/
theorem secondCountableTopology_of_countable_fundamentalGroup
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (x₀ : X)
    [PathConnectedSpace E] [LocallyPathConnectedSpace X] [SecondCountableTopology X]
    [Countable (FundamentalGroup X x₀)] : SecondCountableTopology E := by
  -- The fundamental group bounds every sheet set, and the chart-cover helper assembles them.
  letI : ∀ b : X, Countable (p ⁻¹' {b}) :=
    fun b ↦ countable_fiber_of_countable_fundamentalGroup hp hsurj x₀ b
  exact secondCountableTopology_of_countable_fibers hp

end IsCoveringMap

end
