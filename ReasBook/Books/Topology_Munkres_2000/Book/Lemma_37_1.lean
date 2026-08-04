module

public import Topology_Munkres_2000.Book.Definition_26_5
public import Mathlib.Order.TeichmullerTukey

public section

open Set

universe u

/-- Helper for Lemma 37.1: a family has the finite intersection property exactly when
each of its finite subfamilies has the finite intersection property. -/
lemma finiteIntersectionProperty_iff_finiteSubfamilies {X : Type u} {𝒜 : Set (Set X)} :
    𝒜.FiniteIntersectionProperty ↔
      ∀ 𝒞 ⊆ 𝒜, 𝒞.Finite → 𝒞.FiniteIntersectionProperty := by
  constructor
  · -- Monotonicity passes the property to every finite subfamily.
    intro h𝒜 𝒞 h𝒞 _
    exact h𝒜.mono h𝒞
  · -- Apply the property of a finite subfamily to that subfamily itself.
    intro hfinite
    rw [Set.FiniteIntersectionProperty.finset_iff]
    intro s hs
    have hsFIP := hfinite (s : Set (Set X)) hs s.finite_toSet
    rw [Set.FiniteIntersectionProperty.finset_iff] at hsFIP
    exact hsFIP s fun A hA ↦ hA

/-- Helper for Lemma 37.1: families with the finite intersection property form a
class of finite character. -/
private lemma finiteIntersectionPropertyIsOfFiniteCharacter {X : Type u} :
    Order.IsOfFiniteCharacter
      {𝒜 : Set (Set X) | 𝒜.FiniteIntersectionProperty} := by
  -- Normalize membership and use the finite-subfamily characterization.
  intro 𝒜
  simpa only [Set.mem_setOf_eq] using
    (finiteIntersectionProperty_iff_finiteSubfamilies (𝒜 := 𝒜))

/-- Lemma 37.1. Every family of subsets with the finite intersection property is
contained in a family maximal among those with the finite intersection property. -/
theorem existsMaximalFiniteIntersection {X : Type u} {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.FiniteIntersectionProperty) :
    ∃ 𝒟 : Set (Set X), 𝒜 ⊆ 𝒟 ∧ Maximal Set.FiniteIntersectionProperty 𝒟 := by
  -- Teichmüller–Tukey extends the given member to a maximal member of the class.
  simpa only [Set.mem_setOf_eq] using
    finiteIntersectionPropertyIsOfFiniteCharacter.exists_maximal h𝒜
