module

public import Mathlib.Topology.Order.Basic

public section

universe u

open scoped Topology

namespace OrderTopology

/-- The open intervals used in the interval basis for an order topology. -/
def openIntervals (α : Type u) [LinearOrder α] : Set (Set α) :=
  {s | ∃ a b, a < b ∧ s = Set.Ioo a b}

/-- Membership in the open-interval family. -/
@[simp]
theorem mem_openIntervals {α : Type u} [LinearOrder α] {s : Set α} :
    s ∈ openIntervals α ↔ ∃ a b, a < b ∧ s = Set.Ioo a b := by
  simp [openIntervals]

/-- The half-open intervals adjoining a least element, when one exists. -/
def leftEndpointIntervals (α : Type u) [LinearOrder α] : Set (Set α) :=
  {s | ∃ a₀ b, IsLeast Set.univ a₀ ∧ a₀ < b ∧ s = Set.Ico a₀ b}

/-- Membership in the family of intervals adjoining a least element. -/
@[simp]
theorem mem_leftEndpointIntervals {α : Type u} [LinearOrder α] {s : Set α} :
    s ∈ leftEndpointIntervals α ↔
      ∃ a₀ b, IsLeast Set.univ a₀ ∧ a₀ < b ∧ s = Set.Ico a₀ b := by
  simp [leftEndpointIntervals]

/-- The half-open intervals adjoining a greatest element, when one exists. -/
def rightEndpointIntervals (α : Type u) [LinearOrder α] : Set (Set α) :=
  {s | ∃ a b₀, IsGreatest Set.univ b₀ ∧ a < b₀ ∧ s = Set.Ioc a b₀}

/-- Membership in the family of intervals adjoining a greatest element. -/
@[simp]
theorem mem_rightEndpointIntervals {α : Type u} [LinearOrder α] {s : Set α} :
    s ∈ rightEndpointIntervals α ↔
      ∃ a b₀, IsGreatest Set.univ b₀ ∧ a < b₀ ∧ s = Set.Ioc a b₀ := by
  simp [rightEndpointIntervals]

/-- The endpoint-aware interval family used to define the order topology on a linear order. -/
def basis (α : Type u) [LinearOrder α] : Set (Set α) :=
  openIntervals α ∪ leftEndpointIntervals α ∪ rightEndpointIntervals α

/-- The interval basis is the union of its open-interval and endpoint-interval families. -/
theorem basis_eq_union (α : Type u) [LinearOrder α] :
    basis α = openIntervals α ∪ leftEndpointIntervals α ∪ rightEndpointIntervals α := by
  simp [basis]

/-- Helper for Definition 14.3: every endpoint-aware basis interval is open. -/
private lemma isOpen_of_mem_basis {α : Type u} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {s : Set α} (hs : s ∈ basis α) : IsOpen s := by
  -- Split a basis member into its open, left-endpoint, or right-endpoint form.
  simp only [basis, Set.mem_union, mem_openIntervals, mem_leftEndpointIntervals,
    mem_rightEndpointIntervals] at hs
  rcases hs with (⟨a, b, hab, rfl⟩ | ⟨a₀, b, ha₀, hab, rfl⟩) |
    ⟨a, b₀, hb₀, hab, rfl⟩
  · exact isOpen_Ioo
  · -- A half-open interval at a least element is the corresponding open lower ray.
    have hIco : Set.Ico a₀ b = Set.Iio b := by
      ext x
      simp [ha₀.2 (Set.mem_univ x)]
    rw [hIco]
    exact isOpen_Iio
  · -- Dually, a half-open interval at a greatest element is an open upper ray.
    have hIoc : Set.Ioc a b₀ = Set.Ioi a := by
      ext x
      simp [hb₀.2 (Set.mem_univ x)]
    rw [hIoc]
    exact isOpen_Ioi

/-- Helper for Definition 14.3: every neighborhood contains an endpoint-aware basis interval. -/
private lemma exists_basis_subset_of_mem_nhds {α : Type u} [LinearOrder α] [Nontrivial α]
    [TopologicalSpace α] [OrderTopology α] (x : α) {s : Set α} (hs : s ∈ 𝓝 x) :
    ∃ v ∈ basis α, x ∈ v ∧ v ⊆ s := by
  -- Classify the point by whether it is a global endpoint or has neighbors on both sides.
  rcases isBot_or_exists_lt x with hxbot | hxlower
  · rcases isTop_or_exists_gt x with hxtop | hxupper
    · -- A point cannot be both endpoints in a nontrivial linear order.
      obtain ⟨y, hy⟩ := exists_ne x
      exact (hy (le_antisymm (hxbot y) (hxtop y)).symm).elim
    · -- At the least point, refine the neighborhood by an interval `[x, b)`.
      obtain ⟨b, hxb, hb⟩ := exists_Ico_subset_of_mem_nhds hs hxupper
      have hxleast : IsLeast Set.univ x := ⟨Set.mem_univ x, fun y _ ↦ hxbot y⟩
      refine ⟨Set.Ico x b, ?_, ?_, hb⟩
      · simp only [basis, Set.mem_union, mem_openIntervals, mem_leftEndpointIntervals,
          mem_rightEndpointIntervals]
        exact Or.inl (Or.inr ⟨x, b, hxleast, hxb, rfl⟩)
      · exact ⟨le_rfl, hxb⟩
  · rcases isTop_or_exists_gt x with hxtop | hxupper
    · -- At the greatest point, refine the neighborhood by an interval `(a, x]`.
      obtain ⟨a, hax, ha⟩ := exists_Ioc_subset_of_mem_nhds hs hxlower
      have hxgreatest : IsGreatest Set.univ x := ⟨Set.mem_univ x, fun y _ ↦ hxtop y⟩
      refine ⟨Set.Ioc a x, ?_, ?_, ha⟩
      · simp only [basis, Set.mem_union, mem_openIntervals, mem_leftEndpointIntervals,
          mem_rightEndpointIntervals]
        exact Or.inr ⟨a, x, hxgreatest, hax, rfl⟩
      · exact ⟨hax, le_rfl⟩
    · -- At an interior point, use the standard two-sided interval neighborhood lemma.
      obtain ⟨a, b, hxab, hab⟩ :=
        (mem_nhds_iff_exists_Ioo_subset' hxlower hxupper).mp hs
      refine ⟨Set.Ioo a b, ?_, hxab, hab⟩
      simp only [basis, Set.mem_union, mem_openIntervals, mem_leftEndpointIntervals,
        mem_rightEndpointIntervals]
      exact Or.inl (Or.inl ⟨a, b, hxab.1.trans hxab.2, rfl⟩)

/-- Definition 14.3: the endpoint-aware interval family is a basis for an order topology. -/
theorem isTopologicalBasis_basis {α : Type u} [LinearOrder α] [Nontrivial α]
    [TopologicalSpace α] [OrderTopology α] :
    TopologicalSpace.IsTopologicalBasis (basis α) := by
  -- Apply the standard criterion using openness and neighborhood refinement.
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    (fun s hs ↦ isOpen_of_mem_basis hs) ?_
  intro x s hxs hs
  exact exists_basis_subset_of_mem_nhds x (hs.mem_nhds hxs)

/-- The topology generated by the endpoint-aware interval basis is the canonical order topology. -/
theorem generateFrom_basis (α : Type u) [LinearOrder α] :
    TopologicalSpace.generateFrom (basis α) = Preorder.topology α := by
  -- Separate the degenerate orders from the nontrivial order-topology case.
  rcases subsingleton_or_nontrivial α with hα | hα
  · letI := hα
    apply TopologicalSpace.ext
    funext s
    apply propext
    refine Subsingleton.set_cases ?_ ?_ s
    · simp
    · simp
  · letI := hα
    letI : TopologicalSpace α := Preorder.topology α
    letI : OrderTopology α := ⟨rfl⟩
    exact isTopologicalBasis_basis.eq_generateFrom.symm

end OrderTopology
