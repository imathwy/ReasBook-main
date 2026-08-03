module

public import Mathlib.Topology.Compactness.CountablyCompact

public section

open Set

universe u

/-- Helper for Exercise 28.5: an antitone sequence of nonempty closed sets in a
countably compact space has nonempty intersection. -/
private lemma iInter_nonempty_of_antitone_isClosed {X : Type u} [TopologicalSpace X]
    [CountablyCompactSpace X] (C : ℕ → Set X) (hAntitone : Antitone C)
    (hClosed : ∀ n, IsClosed (C n)) (hNonempty : ∀ n, (C n).Nonempty) :
    (⋂ n, C n).Nonempty := by
  -- If the intersection were empty, the open complements would cover the space.
  by_contra hIntersection
  have hCover : (Set.univ : Set X) ⊆ ⋃ n, (C n)ᶜ := by
    intro x hx
    by_contra hxComplement
    apply hIntersection
    refine ⟨x, ?_⟩
    rw [Set.mem_iInter]
    intro n
    have hxNotComplement : x ∉ (C n)ᶜ := by
      intro hx
      exact hxComplement (Set.mem_iUnion.mpr ⟨n, hx⟩)
    simpa only [Set.mem_compl_iff, not_not] using hxNotComplement
  have hMonotone : Monotone (fun n ↦ (C n)ᶜ) := by
    intro m n hmn
    exact Set.compl_subset_compl.mpr (hAntitone hmn)
  -- Countable compactness collapses this directed cover to one complement.
  obtain ⟨n, hn⟩ := CountablyCompactSpace.isCountablyCompact_univ.elim_directed_cover
    (fun k ↦ (C k)ᶜ) (fun k ↦ (hClosed k).isOpen_compl) hCover hMonotone.directed_le
  obtain ⟨x, hx⟩ := hNonempty n
  exact hn (Set.mem_univ x) hx

/-- Helper for Exercise 28.5: complements of finite initial unions form an
antitone sequence. -/
private lemma antitone_compl_partial_iUnion {X : Type u} (U : ℕ → Set X) :
    Antitone (fun n ↦ (⋃ i ≤ n, U i)ᶜ) := by
  -- Enlarging the initial segment enlarges its union and reverses complements.
  intro m n hmn
  apply Set.compl_subset_compl.mpr
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨i, hi.trans hmn, hxi⟩

/-- Helper for Exercise 28.5: if no finite subfamily covers the space, every
finite initial union has nonempty complement. -/
private lemma compl_partial_iUnion_nonempty_of_no_finite_subcover {X : Type u}
    (U : ℕ → Set X) (hNoFinite : ∀ t : Finset ℕ, ¬ (Set.univ : Set X) ⊆ ⋃ i ∈ t, U i) :
    ∀ n, ((⋃ i ≤ n, U i)ᶜ).Nonempty := by
  classical
  intro n
  -- An empty complement would make `Finset.Iic n` a finite subcover.
  rw [Set.nonempty_iff_ne_empty]
  intro hEmpty
  apply hNoFinite (Finset.Iic n)
  intro x hx
  have hxPrefix : x ∈ ⋃ i ≤ n, U i := by
    by_contra hxUnion
    have hxComplement : x ∈ (⋃ i ≤ n, U i)ᶜ := hxUnion
    rw [hEmpty] at hxComplement
    exact hxComplement
  simpa only [Finset.mem_Iic] using hxPrefix

/-- Exercise 28.5: A topological space is countably compact if and only if every
antitone sequence of nonempty closed sets has nonempty intersection. -/
theorem countablyCompactSpace_iff_nested_closed_iInter {X : Type u} [TopologicalSpace X] :
    CountablyCompactSpace X ↔
      ∀ C : ℕ → Set X, Antitone C → (∀ n, IsClosed (C n)) →
        (∀ n, (C n).Nonempty) → (⋂ n, C n).Nonempty := by
  constructor
  · -- The forward implication is the directed-complement-cover argument.
    intro hCompact C hAntitone hClosed hNonempty
    letI : CountablyCompactSpace X := hCompact
    exact iInter_nonempty_of_antitone_isClosed C hAntitone hClosed hNonempty
  · -- For an open cover, apply the nested-set hypothesis to complements of prefixes.
    intro hNested
    rw [← isCountablyCompact_univ_iff, isCountablyCompact_iff_countable_open_cover]
    intro U hOpen hCover
    classical
    by_contra hFinite
    push Not at hFinite
    have hPrefixClosed : ∀ n, IsClosed ((⋃ i ≤ n, U i)ᶜ) := by
      intro n
      apply IsOpen.isClosed_compl
      exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hOpen i
    obtain ⟨x, hxPrefixes⟩ := hNested (fun n ↦ (⋃ i ≤ n, U i)ᶜ)
      (antitone_compl_partial_iUnion U) hPrefixClosed
      (compl_partial_iUnion_nonempty_of_no_finite_subcover U hFinite)
    -- A cover member containing `x` already occurs in its matching prefix.
    obtain ⟨k, hxUk⟩ := Set.mem_iUnion.mp (hCover (Set.mem_univ x))
    have hxPrefixComplement : x ∈ (⋃ i ≤ k, U i)ᶜ := Set.mem_iInter.mp hxPrefixes k
    exact hxPrefixComplement (Set.mem_iUnion₂.mpr ⟨k, le_rfl, hxUk⟩)
