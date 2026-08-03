module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Topology.Closure

public section

open Set

universe u

namespace Set

/-- A collection of subsets has the finite intersection property if every finite
subcollection has nonempty intersection. -/
def FiniteIntersectionProperty {X : Type u} (𝒜 : Set (Set X)) : Prop :=
  ∀ ⦃𝒞 : Set (Set X)⦄, 𝒞 ⊆ 𝒜 → 𝒞.Finite → (⋂₀ 𝒞).Nonempty

namespace FiniteIntersectionProperty

/-- The finite intersection property is equivalent to nonemptiness of every
intersection indexed by a finite list without repetitions. -/
theorem finset_iff {X : Type u} {𝒜 : Set (Set X)} :
    𝒜.FiniteIntersectionProperty ↔
      ∀ s : Finset (Set X), (∀ A ∈ s, A ∈ 𝒜) → (⋂ A ∈ s, A).Nonempty := by
  constructor
  · -- Regard a finset as the finite subcollection in the defining property.
    intro h𝒜 s hs
    have hnonempty := h𝒜 (𝒞 := (s : Set (Set X))) hs s.finite_toSet
    simpa only [sInter_eq_biInter, Finset.set_biInter_coe] using hnonempty
  · -- Enumerate an arbitrary finite subcollection by its canonical finset.
    intro hfinset 𝒞 h𝒞 h𝒞finite
    have hnonempty := hfinset h𝒞finite.toFinset fun A hA ↦
      h𝒞 (h𝒞finite.mem_toFinset.mp hA)
    simpa only [← Finset.set_biInter_coe, h𝒞finite.coe_toFinset,
      sInter_eq_biInter] using hnonempty

/-- The finite intersection property passes to subcollections. -/
theorem mono {X : Type u} {𝒜 𝓑 : Set (Set X)}
    (h𝒜 : 𝒜.FiniteIntersectionProperty) (h𝓑 : 𝓑 ⊆ 𝒜) :
    𝓑.FiniteIntersectionProperty := by
  -- Any finite subcollection of `𝓑` is also a finite subcollection of `𝒜`.
  intro 𝒞 h𝒞 h𝒞finite
  exact h𝒜 (h𝒞.trans h𝓑) h𝒞finite

/-- Helper for Definition 26.5: a pointwise map compatible with a transformation of
sets preserves the finite intersection property of the transformed family. -/
theorem image_of_mapsTo {X : Type u} {Y : Type v} {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.FiniteIntersectionProperty) (g : Set X → Set Y) (φ : X → Y)
    (hφ : ∀ A, MapsTo φ A (g A)) :
    (g '' 𝒜).FiniteIntersectionProperty := by
  classical
  rw [finset_iff] at h𝒜 ⊢
  intro s hs
  -- Choose one source set for every transformed set in the finite family.
  have hexists : ∀ B ∈ s, ∃ A ∈ 𝒜, g A = B := by
    intro B hB
    exact hs B hB
  choose rep hrep_mem hrep_eq using hexists
  let t := s.attach.image fun B ↦ rep B.1 B.2
  have ht : ∀ A ∈ t, A ∈ 𝒜 := by
    intro A hA
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.mp hA
    exact hrep_mem B.1 B.2
  obtain ⟨x, hx⟩ := h𝒜 t ht
  refine ⟨φ x, ?_⟩
  -- Map the common source point into each chosen transformed set.
  simp only [mem_iInter] at hx ⊢
  intro B hB
  have hrep_t : rep B hB ∈ t := by
    exact Finset.mem_image.mpr ⟨⟨B, hB⟩, Finset.mem_attach s ⟨B, hB⟩, rfl⟩
  rw [← hrep_eq B hB]
  exact hφ (rep B hB) (hx (rep B hB) hrep_t)

/-- Direct images of a family with the finite intersection property have the finite
intersection property. -/
theorem image {X : Type u} {Y : Type v} {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.FiniteIntersectionProperty) (f : X → Y) :
    ((fun A ↦ f '' A) '' 𝒜).FiniteIntersectionProperty := by
  -- Direct image membership supplies the pointwise compatibility hypothesis.
  refine image_of_mapsTo h𝒜 (fun A ↦ f '' A) f ?_
  intro A x hx
  exact ⟨x, hx, rfl⟩

/-- The closures of a family with the finite intersection property have the finite
intersection property. -/
theorem closure {X : Type u} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.FiniteIntersectionProperty) :
    (closure '' 𝒜).FiniteIntersectionProperty := by
  -- The identity map sends every set into its closure.
  refine image_of_mapsTo h𝒜 _root_.closure id ?_
  intro A x hx
  exact subset_closure hx

end FiniteIntersectionProperty

end Set
