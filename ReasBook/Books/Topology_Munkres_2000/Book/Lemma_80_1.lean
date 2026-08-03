module

public import Topology_Munkres_2000.Book.Lemma_80_1.PathComponent

public section

universe u v

/-- Lemma 80.1. If `B` is path connected and locally path connected, then the
restriction of a covering map in Munkres's surjective sense to any path component
of its domain is again a covering map in that sense. -/
theorem coveringMap_restrictPathComponent {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B] {p : E → B} (hp : IsCoveringMap p)
    (e₀ : E) :
    IsCoveringMap (fun x : pathComponent e₀ ↦ p x) ∧
      Function.Surjective (fun x : pathComponent e₀ ↦ p x) :=
  ⟨hp.restrictPathComponent e₀, hp.surjective_restrictPathComponent e₀⟩
