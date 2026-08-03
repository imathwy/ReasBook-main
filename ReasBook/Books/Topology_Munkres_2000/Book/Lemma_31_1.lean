module

public import Mathlib.Topology.Separation.Regular

public section

open Set Filter Topology

universe u

/-- Lemma 31.1 (a): Regularity is equivalent to every neighborhood containing
the closure of a smaller neighborhood. This applies in particular under the
book's standing `T1Space` assumption. -/
theorem regularSpace_iff_exists_nhds_closure_subset
    {X : Type u} [TopologicalSpace X] :
    RegularSpace X ↔ ∀ (x : X) (U : Set X) (hU : U ∈ 𝓝 x),
      ∃ V : Set X, V ∈ 𝓝 x ∧ closure V ⊆ U := by
  constructor
  · intro hRegular x U hU
    -- A regular space has a closed neighborhood inside every prescribed neighborhood.
    have hClosedNhds : ∀ (x : X) (U : Set X), U ∈ 𝓝 x →
        ∃ V ∈ 𝓝 x, IsClosed V ∧ V ⊆ U :=
      ((regularSpace_TFAE X).out 0 3).mp hRegular
    obtain ⟨V, hV, hVclosed, hVU⟩ := hClosedNhds x U hU
    refine ⟨V, hV, ?_⟩
    rwa [hVclosed.closure_eq]
  · intro hShrink
    -- The closure of a shrinking neighborhood supplies the closed-neighborhood criterion.
    refine RegularSpace.of_exists_mem_nhds_isClosed_subset ?_
    intro x U hU
    obtain ⟨V, hV, hVU⟩ := hShrink x U hU
    exact ⟨closure V, mem_of_superset hV subset_closure, isClosed_closure, hVU⟩

/-- Helper for Lemma 31.1: an open set whose closure avoids `t` gives separated
neighborhoods of every subset of that open set and `t`. -/
private lemma separatedNhds_of_isOpen_closure_subset_compl
    {X : Type u} [TopologicalSpace X] {s t V : Set X}
    (hVopen : IsOpen V) (hsV : s ⊆ V) (hclosure : closure V ⊆ tᶜ) :
    SeparatedNhds s t := by
  -- Use `V` and the open complement of its closure as the separating neighborhoods.
  refine ⟨V, (closure V)ᶜ, hVopen, isClosed_closure.isOpen_compl, hsV, ?_, ?_⟩
  · exact subset_compl_comm.mp hclosure
  · exact disjoint_compl_right.mono_left subset_closure

/-- Lemma 31.1 (b): Normality is equivalent to every open neighborhood of a
closed set containing the closure of a smaller open neighborhood of that set.
This applies in particular under the book's standing `T1Space` assumption. -/
theorem normalSpace_iff_exists_isOpen_closure_subset
    {X : Type u} [TopologicalSpace X] :
    NormalSpace X ↔ ∀ (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U),
      ∃ V : Set X, IsOpen V ∧ A ⊆ V ∧ closure V ⊆ U := by
  constructor
  · intro hNormal A U hA hU hAU
    -- Install normality so the standard closure-shrinking theorem applies directly.
    letI : NormalSpace X := hNormal
    exact normal_exists_closure_subset hA hU hAU
  · intro hShrink
    -- Shrink around one closed set inside the complement of the other.
    refine ⟨?_⟩
    intro s t hs ht hst
    have hstCompl : s ⊆ tᶜ :=
      fun x hxs hxt ↦ Set.disjoint_left.mp hst hxs hxt
    obtain ⟨V, hVopen, hsV, hclosure⟩ :=
      hShrink s tᶜ hs ht.isOpen_compl hstCompl
    exact separatedNhds_of_isOpen_closure_subset_compl hVopen hsV hclosure
