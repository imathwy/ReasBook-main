module

public import Topology_Munkres_2000.Book.Lemma_37_2
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.WithTopology

public section

open Filter Set Topology

universe u

namespace Set.FiniteIntersectionProperty

/-- Helper for Exercise 37.1: two members of a family with the finite intersection
property have nonempty intersection. -/
theorem inter_nonempty_of_mem {X : Type u} {𝒟 : Set (Set X)}
    (h𝒟 : 𝒟.FiniteIntersectionProperty) {A B : Set X}
    (hA : A ∈ 𝒟) (hB : B ∈ 𝒟) : (A ∩ B).Nonempty := by
  classical
  -- Apply the finite intersection property to the two-set subfamily.
  have hpair_mem : ∀ C ∈ ({A, B} : Finset (Set X)), C ∈ 𝒟 := by
    intro C hC
    rw [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact hA
    · exact hB
  have hpairs := Set.FiniteIntersectionProperty.finset_iff.mp h𝒟
    ({A, B} : Finset (Set X)) hpair_mem
  simpa only [Finset.set_biInter_insert, Finset.set_biInter_singleton] using hpairs

end Set.FiniteIntersectionProperty

namespace Ultrafilter

/-- Helper for Exercise 37.1: the sets belonging to an ultrafilter form a family
maximal with respect to the finite intersection property. -/
theorem isMaximalFiniteIntersection {X : Type u} (f : Ultrafilter X) :
    IsMaximalFiniteIntersection f.sets := by
  change Maximal Set.FiniteIntersectionProperty f.sets
  rw [maximal_subset_iff']
  constructor
  · -- A finite intersection of ultrafilter members remains in the proper filter.
    rw [Set.FiniteIntersectionProperty.finset_iff]
    intro s hs
    exact f.nonempty_of_mem ((Filter.biInter_finset_mem s).mpr hs)
  · intro 𝒞 h𝒞 hsets A hA
    -- A proper FIP extension cannot contain both `A` and its ultrafilter-selected complement.
    by_contra hA_not_mem
    have hA_compl : Aᶜ ∈ f := f.compl_mem_iff_notMem.mpr hA_not_mem
    obtain ⟨x, hxA, hxA_compl⟩ :=
      h𝒞.inter_nonempty_of_mem hA (hsets hA_compl)
    exact hxA_compl hxA

end Ultrafilter

namespace CofiniteTopology

/-- Helper for Exercise 37.1: an infinite subset of a cofinite space is dense. -/
theorem closure_eq_univ_of_infinite {X : Type u} {s : Set (CofiniteTopology X)}
    (hs : s.Infinite) : closure s = Set.univ := by
  -- A closed set in the cofinite topology is either universal or finite.
  rcases CofiniteTopology.isClosed_iff.mp isClosed_closure with hclosure | hclosure_finite
  · exact hclosure
  · exact (hs (hclosure_finite.subset subset_closure)).elim

end CofiniteTopology

namespace IsMaximalFiniteIntersection

/-- Exercise 37.1 (1). For a family `𝒟` maximal with respect to the finite
intersection property, `x ∈ closure D` for every `D ∈ 𝒟` if and only if every
neighborhood of `x` belongs to `𝒟`. Only the forward implication uses maximality. -/
theorem mem_closure_iff_nhds_mem {X : Type u} [TopologicalSpace X]
    {𝒟 : Set (Set X)} (h𝒟 : IsMaximalFiniteIntersection 𝒟) (x : X) :
    (∀ D ∈ 𝒟, x ∈ closure D) ↔ ∀ U ∈ 𝓝 x, U ∈ 𝒟 := by
  constructor
  · intro hx U hU
    -- Every family member meets `U`; maximality then forces `U` into the family.
    apply h𝒟.mem_of_intersects
    intro D hD
    have hfrequent := mem_closure_iff_frequently.mp (hx D hD)
    obtain ⟨y, hyU, hyD⟩ := Filter.frequently_iff.mp hfrequent hU
    exact ⟨y, hyU, hyD⟩
  · intro hnhds D hD
    -- Pairwise FIP intersections witness that `D` occurs frequently near `x`.
    rw [mem_closure_iff_frequently, Filter.frequently_iff]
    intro U hU
    exact h𝒟.prop.inter_nonempty_of_mem (hnhds U hU) hD

/-- Exercise 37.1 (2). A family maximal with respect to the finite intersection
property is upward closed under inclusion. -/
theorem mem_of_superset {X : Type u} {𝒟 : Set (Set X)}
    (h𝒟 : IsMaximalFiniteIntersection 𝒟)
    {D A : Set X} (hD : D ∈ 𝒟) (hDA : D ⊆ A) :
    A ∈ 𝒟 := by
  -- Each member meets `D`, hence also its superset `A`; maximality gives membership.
  apply h𝒟.mem_of_intersects
  intro E hE
  obtain ⟨x, hxD, hxE⟩ := h𝒟.prop.inter_nonempty_of_mem hD hE
  exact ⟨x, hDA hxD, hxE⟩

/-- Exercise 37.1 (3). The printed `T₁` claim is false: in the cofinite topology
on `ℕ`, some family maximal with respect to the finite intersection property has
more than one point in the intersection of the closures of all its members. -/
theorem t1_iInter_closure_not_subsingleton_counterexample :
    ∃ 𝒟 : Set (Set (CofiniteTopology ℕ)),
      IsMaximalFiniteIntersection 𝒟 ∧
        ¬ (⋂ D ∈ 𝒟, closure D).Subsingleton := by
  refine ⟨(Filter.hyperfilter (CofiniteTopology ℕ)).sets,
    Ultrafilter.isMaximalFiniteIntersection _, ?_⟩
  -- Every hyperfilter member is infinite, hence dense in the cofinite topology.
  have hclosure (D : Set (CofiniteTopology ℕ))
      (hD : D ∈ Filter.hyperfilter (CofiniteTopology ℕ)) : closure D = Set.univ := by
    apply CofiniteTopology.closure_eq_univ_of_infinite
    intro hD_finite
    exact hD_finite.notMem_hyperfilter hD
  have hall_closures :
      (⋂ D ∈ (Filter.hyperfilter (CofiniteTopology ℕ)).sets, closure D) = Set.univ := by
    rw [Set.iInter_eq_univ]
    intro D
    rw [Set.iInter_eq_univ]
    intro hD
    exact hclosure D hD
  -- Thus the intersection is the whole nontrivial carrier.
  rw [hall_closures, Set.subsingleton_univ_iff]
  exact not_subsingleton (CofiniteTopology ℕ)

end IsMaximalFiniteIntersection

namespace Set.FiniteIntersectionProperty

/-- If a family has the finite intersection property and contains every neighborhood
of `x`, then `x` belongs to the closure of every member of the family. -/
theorem mem_closure_of_nhds_mem {X : Type u} [TopologicalSpace X]
    {𝒟 : Set (Set X)} (h𝒟 : 𝒟.FiniteIntersectionProperty) {x : X}
    (hx : ∀ U ∈ 𝓝 x, U ∈ 𝒟) :
    ∀ D ∈ 𝒟, x ∈ _root_.closure D := by
  intro D hD
  -- Pairwise FIP intersections verify the neighborhood characterization of closure.
  rw [mem_closure_iff_frequently, Filter.frequently_iff]
  intro U hU
  exact h𝒟.inter_nonempty_of_mem (hx U hU) hD

end Set.FiniteIntersectionProperty
