module

public import Topology_Munkres_2000.Book.Definition_43_9.Evaluation
public import Mathlib.Topology.CompactOpen

public section

open scoped Topology

universe u v

namespace ContinuousMap

/-- Helper for Exercise 46.8: continuity of evaluation gives an open neighborhood on which
all maps send a fixed compact set into a fixed open set. -/
lemma exists_isOpen_mem_subset_setOf_mapsTo {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace C(X, Y)]
    (h_eval : Continuous (evaluation X Y)) {K : Set X} {U : Set Y} {f : C(X, Y)}
    (hK : IsCompact K) (hU : IsOpen U) (hf : Set.MapsTo f K U) :
    ∃ W : Set C(X, Y), IsOpen W ∧ f ∈ W ∧ W ⊆ {g : C(X, Y) | Set.MapsTo g K U} := by
  -- The open evaluation preimage contains the compact rectangle `K × {f}`.
  have hpreimage : IsOpen ((evaluation X Y) ⁻¹' U) := hU.preimage h_eval
  have hrectangle : K ×ˢ ({f} : Set C(X, Y)) ⊆ (evaluation X Y) ⁻¹' U := by
    rintro ⟨x, g⟩ ⟨hx, hg⟩
    rw [Set.mem_singleton_iff] at hg
    have hgf : g = f := hg
    simpa only [Set.mem_preimage, evaluation_apply, hgf] using hf hx
  -- The tube lemma supplies a uniform neighborhood of `f` over all of `K`.
  obtain ⟨V, W, hV, hW, hKV, hfW, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hpreimage hrectangle
  refine ⟨W, hW, hfW (Set.mem_singleton f), ?_⟩
  intro g hg x hx
  exact hVW (show (x, g) ∈ V ×ˢ W from ⟨hKV hx, hg⟩)

/-- Helper for Exercise 46.8: compact-open subbasic sets are open whenever evaluation is
continuous. -/
lemma isOpen_setOf_mapsTo_of_continuous_evaluation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace C(X, Y)]
    (h_eval : Continuous (evaluation X Y)) {K : Set X} {U : Set Y}
    (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | Set.MapsTo f K U} := by
  -- Every map in the subbasic set has the neighborhood constructed above.
  rw [isOpen_iff_forall_mem_open]
  intro f hf
  obtain ⟨W, hW, hfW, hWsub⟩ :=
    exists_isOpen_mem_subset_setOf_mapsTo h_eval hK hU hf
  exact ⟨W, hWsub, hW, hfW⟩

/-- Exercise 46.8. If evaluation is continuous for a topology `T` on `C(X, Y)`,
then `T` is finer than the compact-open topology. -/
theorem le_compactOpen_of_continuous_evaluation {X : Type u} {Y : Type v}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (T : TopologicalSpace C(X, Y))
    (h_eval : Continuous[TopologicalSpace.induced Prod.fst tX ⊓
      TopologicalSpace.induced Prod.snd T, tY] (evaluation X Y)) :
    T ≤ compactOpen := by
  -- Install `T` locally so the explicit continuity hypothesis becomes ordinary continuity.
  letI : TopologicalSpace C(X, Y) := T
  have h_eval' : Continuous (evaluation X Y) := h_eval
  -- It suffices to prove that every compact-open generator is open in `T`.
  rw [compactOpen_eq]
  refine le_generateFrom ?_
  exact Set.forall_mem_image2.2 fun K hK U hU ↦
    isOpen_setOf_mapsTo_of_continuous_evaluation h_eval' hK hU

end ContinuousMap
