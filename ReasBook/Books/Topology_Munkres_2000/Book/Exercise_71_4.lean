module

public import Topology_Munkres_2000.Book.Definition_71_4.WedgeOfCircles
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Perfect

public section

universe u v

namespace Topology.IsWedgeOfCircles

/-- Helper for Exercise 71.4: the unit circle has at least two distinct points. -/
lemma circleNontrivial : Nontrivial Circle := by
  -- The antipode of any circle point is a distinct second point.
  exact ⟨⟨1, -1, (Circle.neg_ne_self 1).symm⟩⟩

/-- Helper for Exercise 71.4: the wedge point is an accumulation point of every
constituent circle. -/
lemma accPt_basepoint {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} [Topology.IsWedgeOfCircles S p] (α : J) :
    AccPt p (Filter.principal (S α)) := by
  -- Transfer the separation, connectedness, and nontriviality needed for
  -- perfectness from the unit circle to this constituent circle.
  obtain ⟨e⟩ := IsWedgeOfCircles.homeomorphic_circle (S := S) (p := p) α
  letI : Nontrivial Circle := circleNontrivial
  letI : T1Space (S α) := e.symm.t1Space
  letI : ConnectedSpace (S α) := e.connectedSpace_iff.mpr inferInstance
  letI : Nontrivial (S α) := e.toEquiv.nontrivial
  let q : S α := ⟨p, mem_basepoint α⟩
  have hq : AccPt q (Filter.principal (Set.univ : Set (S α))) :=
    PerfectSpace.univ_preperfect q (Set.mem_univ q)
  rw [accPt_iff_nhds] at hq ⊢
  intro U hU
  -- Pull the ambient neighborhood back to the subtype and then forget the
  -- subtype wrapper on the resulting point.
  obtain ⟨y, hy, hyq⟩ := hq (Subtype.val ⁻¹' U) (continuous_subtype_val.continuousAt hU)
  refine ⟨y, ⟨hy.1, y.property⟩, ?_⟩
  intro hyp
  exact hyq (Subtype.ext hyp)

/-- Helper for Exercise 71.4: points chosen on injectively indexed distinct circles
meet each constituent circle in at most one point. -/
lemma circlePointRange_inter_subsingleton {J : Type v} {X : Type u}
    [TopologicalSpace X] {S : J → Set X} {p : X}
    [Topology.IsWedgeOfCircles S p] {ι : Type*} (e : ι ↪ J) (x : ι → X)
    (hxS : ∀ i, x i ∈ S (e i)) (hxp : ∀ i, x i ≠ p) (α : J) :
    (Set.range x ∩ S α).Subsingleton := by
  -- A selected point lying on `S α` forces its assigned index to be `α`,
  -- since every intersection of two distinct circles is just the wedge point.
  rintro _ ⟨⟨i, rfl⟩, hxiα⟩ _ ⟨⟨j, rfl⟩, hxjα⟩
  have hei : e i = α := by
    by_contra hne
    have hxinter : x i ∈ S (e i) ∩ S α := ⟨hxS i, hxiα⟩
    rw [IsWedgeOfCircles.inter_eq (S := S) (p := p) hne] at hxinter
    exact hxp i (Set.mem_singleton_iff.mp hxinter)
  have hej : e j = α := by
    by_contra hne
    have hxinter : x j ∈ S (e j) ∩ S α := ⟨hxS j, hxjα⟩
    rw [IsWedgeOfCircles.inter_eq (S := S) (p := p) hne] at hxinter
    exact hxp j (Set.mem_singleton_iff.mp hxinter)
  exact congrArg x (e.injective (hei.trans hej.symm))

/-- Helper for Exercise 71.4: an injectively indexed choice of non-basepoints,
one from each selected circle, has closed range. -/
lemma isClosed_range_of_circlePoints {J : Type v} {X : Type u}
    [TopologicalSpace X] {S : J → Set X} {p : X}
    [Topology.IsWedgeOfCircles S p] {ι : Type*} (e : ι ↪ J) (x : ι → X)
    (hxS : ∀ i, x i ∈ S (e i)) (hxp : ∀ i, x i ≠ p) :
    IsClosed (Set.range x) := by
  -- Coherence reduces global closedness to closedness on each circle.
  rw [(IsWedgeOfCircles.isCoherentWith (S := S) (p := p)).isClosed_iff]
  rintro _ ⟨α, rfl⟩
  obtain ⟨hcircle⟩ := IsWedgeOfCircles.homeomorphic_circle (S := S) (p := p) α
  letI : T1Space (S α) := hcircle.symm.t1Space
  have hsubsingleton : (Subtype.val ⁻¹' Set.range x : Set (S α)).Subsingleton := by
    intro y hy z hz
    apply Subtype.ext
    exact circlePointRange_inter_subsingleton e x hxS hxp α
      ⟨hy, y.property⟩ ⟨hz, z.property⟩
  -- A subsingleton set is finite, and finite sets are closed in a T1 space.
  exact hsubsingleton.finite.isClosed

/-- Exercise 71.4: An infinite wedge of circles does not satisfy the first
countability axiom. -/
theorem not_firstCountable_of_infinite {J : Type v} {X : Type u}
    [Infinite J] [TopologicalSpace X] (S : J → Set X) (p : X)
    [Topology.IsWedgeOfCircles S p] : ¬ FirstCountableTopology X := by
  -- Assume a countable decreasing neighborhood basis and assign its `n`th
  -- member to a distinct constituent circle.
  intro hfirst
  letI : FirstCountableTopology X := hfirst
  classical
  let e : ℕ ↪ J := Infinite.natEmbedding J
  obtain ⟨U, hUbasis⟩ := Filter.exists_antitone_basis (𝓝 p)
  have hchosen : ∀ n, ∃ y ∈ U n ∩ S (e n), y ≠ p := by
    intro n
    exact accPt_iff_nhds.mp (accPt_basepoint (S := S) (p := p) (e n))
      (U n) (hUbasis.mem n)
  choose x hxU hxne using hchosen
  have hxS : ∀ n, x n ∈ S (e n) := fun n ↦ (hxU n).2
  have hclosed : IsClosed (Set.range x) :=
    isClosed_range_of_circlePoints e x hxS hxne
  have hpRange : p ∉ Set.range x := by
    rintro ⟨n, hn⟩
    exact hxne n hn
  -- The complement is therefore a neighborhood of the wedge point, so some
  -- basis member lies inside it; its chosen point gives the contradiction.
  have hcomplement : (Set.range x)ᶜ ∈ 𝓝 p := hclosed.isOpen_compl.mem_nhds hpRange
  obtain ⟨n, hUn⟩ := hUbasis.mem_iff.mp hcomplement
  exact hUn (hxU n).1 ⟨n, rfl⟩

end Topology.IsWedgeOfCircles
