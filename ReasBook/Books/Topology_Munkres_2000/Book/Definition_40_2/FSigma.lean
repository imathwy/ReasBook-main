module

public import Mathlib.Topology.GDelta.Basic

public section

open Set

universe u

/-- A subset is an `Fσ` set if it is the union of a countable collection of closed subsets. -/
def IsFσ {X : Type u} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

/-- A set is `Fσ` exactly when it is the union of a sequence of closed sets. -/
theorem isFσ_iff_eq_iUnion_nat {X : Type u} [TopologicalSpace X] {s : Set X} :
    IsFσ s ↔ ∃ f : ℕ → Set X, (∀ n, IsClosed (f n)) ∧ s = ⋃ n, f n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, hTc, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hTn
    · exact ⟨fun _ ↦ ∅, fun _ ↦ isClosed_empty, by simp⟩
    · obtain ⟨f, rfl⟩ := Countable.exists_eq_range hTc hTn
      exact ⟨f, by simpa using hT, by simp⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨range f, by simpa using hf, countable_range f, by simp⟩

alias ⟨IsFσ.eq_iUnion_nat, _⟩ := isFσ_iff_eq_iUnion_nat

/-- An `Fσ` set is equivalently a set whose complement is a `Gδ` set. -/
theorem isFσ_iff_compl_isGδ {X : Type u} [TopologicalSpace X] {s : Set X} :
    IsFσ s ↔ IsGδ sᶜ := by
  rw [isFσ_iff_eq_iUnion_nat, isGδ_iff_eq_iInter_nat]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun n ↦ (f n)ᶜ, fun n ↦ (hf n).isOpen_compl, compl_iUnion f⟩
  · rintro ⟨f, hf, hs⟩
    refine ⟨fun n ↦ (f n)ᶜ, fun n ↦ (hf n).isClosed_compl, ?_⟩
    calc
      s = sᶜᶜ := (compl_compl s).symm
      _ = (⋂ n, f n)ᶜ := congrArg compl hs
      _ = ⋃ n, (f n)ᶜ := compl_iInter f
