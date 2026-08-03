module

public import Mathlib.Topology.Baire.Lemmas

public section

open scoped Topology

universe u

/-- Helper for Exercise 48.4: an open subset of a Baire subspace is a Baire space. -/
lemma BaireSpace.of_isOpen_subset {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : BaireSpace U) (hV : IsOpen V) (hVU : V ⊆ U) : BaireSpace V := by
  -- Regard the inclusion `V → U` as an open embedding and transport the Baire property.
  letI : BaireSpace U := hU
  have hVopenInU : IsOpen (Subtype.val ⁻¹' V : Set U) :=
    hV.preimage continuous_subtype_val
  exact (Topology.IsOpenEmbedding.inclusion hVU hVopenInU).baireSpace

/-- Helper for Exercise 48.4: a nonempty open Baire subspace meets every countable
intersection of open dense subsets of the ambient space. -/
lemma IsOpen.nonempty_inter_iInter_of_baireSpace {X : Type u} [TopologicalSpace X]
    {V : Set X} (hVopen : IsOpen V) (hVne : V.Nonempty) (hVBaire : BaireSpace V)
    {f : ℕ → Set X} (hfOpen : ∀ n, IsOpen (f n)) (hfDense : ∀ n, Dense (f n)) :
    (V ∩ ⋂ n, f n).Nonempty := by
  -- Restrict the open dense family to the open subspace `V`.
  letI : BaireSpace V := hVBaire
  have hRestrictedOpen : ∀ n, IsOpen ((fun y : V ↦ (y : X)) ⁻¹' f n) := fun n ↦
    (hfOpen n).preimage continuous_subtype_val
  have hRestrictedDense : ∀ n, Dense ((fun y : V ↦ (y : X)) ⁻¹' f n) := fun n ↦
    Dense.preimage (hfDense n) hVopen.isOpenEmbedding_subtypeVal.isOpenMap
  have hInterDense : Dense (⋂ n, (fun y : V ↦ (y : X)) ⁻¹' f n) :=
    BaireSpace.baire_property _ hRestrictedOpen hRestrictedDense
  have hVnonempty : Nonempty V := hVne.to_subtype
  obtain ⟨y, hy⟩ := hInterDense.nonempty_iff.2 hVnonempty
  -- Return the subtype witness to the ambient space.
  refine ⟨y, y.property, ?_⟩
  rw [Set.mem_iInter]
  intro n
  exact Set.mem_iInter.mp hy n

/-- Exercise 48.4. If every point of a topological space has a neighborhood
that is a Baire space, then the whole space is a Baire space. -/
theorem BaireSpace.of_baire_neighborhoods {X : Type u} [TopologicalSpace X]
    (h : ∀ x : X, ∃ U : Set X, U ∈ 𝓝 x ∧ BaireSpace U) : BaireSpace X := by
  -- Test density of a countable intersection against an arbitrary nonempty open set.
  constructor
  intro f hfOpen hfDense
  rw [dense_iff_inter_open]
  intro W hWopen hWne
  obtain ⟨x, hxW⟩ := hWne
  obtain ⟨U, hUnhds, hUBaire⟩ := h x
  obtain ⟨N, hNU, hNopen, hxN⟩ := mem_nhds_iff.mp hUnhds
  let V := W ∩ N
  have hVopen : IsOpen V := hWopen.inter hNopen
  have hVne : V.Nonempty := ⟨x, hxW, hxN⟩
  have hVU : V ⊆ U := fun _ hy ↦ hNU hy.2
  have hVBaire : BaireSpace V := BaireSpace.of_isOpen_subset hUBaire hVopen hVU
  -- The open Baire set `V ⊆ W` meets the restricted dense intersection.
  obtain ⟨y, hyV, hyInter⟩ :=
    hVopen.nonempty_inter_iInter_of_baireSpace hVne hVBaire hfOpen hfDense
  exact ⟨y, hyV.1, hyInter⟩
