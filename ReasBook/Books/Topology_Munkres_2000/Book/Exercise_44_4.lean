module

public import Topology_Munkres_2000.Book.Exercise_44_4.PerfectImage
public import Topology_Munkres_2000.Book.Exercise_44_4.HilbertCube

public section

open TopologicalSpace

universe u

/-- Part (a) of Exercise 44.4: A Hausdorff continuous image of the closed unit interval is
compact, connected, weakly locally connected, and metrizable. -/
theorem continuousSurjectiveUnitInterval_properties
    (X : Type u) [TopologicalSpace X] [T2Space X] (f : C(unitInterval, X))
    (hf : Function.Surjective f) :
    CompactSpace X ∧ ConnectedSpace X ∧ WeaklyLocallyConnectedSpace X ∧ MetrizableSpace X := by
  have hPeano : PeanoSpace X := { toT2Space := inferInstance, exists_surjective := ⟨f, hf⟩ }
  exact ⟨hPeano.compactSpace, hPeano.connectedSpace,
    hPeano.weaklyLocallyConnectedSpace, hPeano.metrizableSpace⟩

/-- Exercise 44.4 (b): Assuming the Hahn--Mazurkiewicz theorem, the countable
product `ℕ → unitInterval` is a continuous image of the closed unit interval. -/
theorem existsContinuousSurjectiveHilbertCube
    (hahnMazurkiewicz :
      ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
        [ConnectedSpace Y] [WeaklyLocallyConnectedSpace Y] [MetrizableSpace Y],
        ∃ f : C(unitInterval, Y), Function.Surjective f) :
    ∃ f : C(unitInterval, ℕ → unitInterval), Function.Surjective f := by
  -- Specialization assembles the Hilbert cube's canonical product-space instances.
  exact hahnMazurkiewicz (ℕ → unitInterval)
