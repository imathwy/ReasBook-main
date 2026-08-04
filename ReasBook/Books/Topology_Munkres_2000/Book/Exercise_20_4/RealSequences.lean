module

public import Topology_Munkres_2000.Book.Definition_20_9
public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology

public section

/-- Real sequences equipped with the uniform topology. -/
abbrev UniformRealSequence :=
  WithTopology (ℕ → ℝ) (UniformMetric.topology ℕ)

/-- Real sequences equipped with the box topology. -/
abbrev BoxRealSequence :=
  WithTopology (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))

namespace UniformRealSequence

/-- Regard an ordinary real sequence as a point of real sequence space with the uniform topology. -/
def ofSequence (x : ℕ → ℝ) : UniformRealSequence :=
  .toTopology (UniformMetric.topology ℕ) x

/-- Helper for Exercise 20.4: `ofSequence` is the canonical uniform-topology wrapper. -/
theorem ofSequence_eq_toTopology (x : ℕ → ℝ) :
    ofSequence x = WithTopology.toTopology (UniformMetric.topology ℕ) x := by
  -- The owner module can expose the defining computation directly.
  rfl

end UniformRealSequence

namespace BoxRealSequence

/-- Regard an ordinary real sequence as a point of real sequence space with the box topology. -/
def ofSequence (x : ℕ → ℝ) : BoxRealSequence :=
  .toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) x

/-- Helper for Exercise 20.4: `ofSequence` is the canonical box-topology wrapper. -/
theorem ofSequence_eq_toTopology (x : ℕ → ℝ) :
    ofSequence x =
      WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) x := by
  -- The owner module can expose the defining computation directly.
  rfl

end BoxRealSequence
