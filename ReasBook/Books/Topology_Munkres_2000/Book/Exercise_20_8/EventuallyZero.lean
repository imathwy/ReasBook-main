module

public import Topology_Munkres_2000.Book.Exercise_19_7.EventuallyZero
public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Topology_Munkres_2000.Book.Definition_20_9.UniformMetric
public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.WithTopology

public section

open scoped lp

/-- A finitely supported real sequence is square-summable. -/
theorem hasFiniteSupport_memL2 (x : ℕ → ℝ) (hx : x.HasFiniteSupport) :
    Memℓp x 2 := by
  -- Finite support is preserved by taking the squared coordinate norms.
  apply memℓp_gen
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  exact hx.subset fun n hn hzero ↦ hn (by simpa [hzero])

/-- The canonical inclusion of eventually-zero real sequences into `ℓ²(ℕ, ℝ)`. -/
@[expose]
def eventuallyZeroToL2 (x : eventuallyZeroRealSequences) : ℓ²(ℕ, ℝ) :=
  ⟨fun n ↦ x.1 n, hasFiniteSupport_memL2 x.1 (mem_eventuallyZeroRealSequences.mp x.property)⟩

/-- The inclusion into `ℓ²(ℕ, ℝ)` preserves every coordinate. -/
@[simp]
theorem eventuallyZeroToL2_apply (x : eventuallyZeroRealSequences) (n : ℕ) :
    eventuallyZeroToL2 x n = x.1 n := rfl

/-- The canonical inclusion of eventually-zero sequences into `ℓ²(ℕ, ℝ)` is injective. -/
theorem eventuallyZeroToL2_injective : Function.Injective eventuallyZeroToL2 := by
  intro x y h
  apply Subtype.ext
  funext n
  exact congrArg (fun z : ℓ²(ℕ, ℝ) ↦ z n) h

/-- The topology on eventually-zero real sequences induced by the box topology. -/
@[reducible, expose]
def eventuallyZeroRealBoxTopology : TopologicalSpace eventuallyZeroRealSequences :=
  TopologicalSpace.induced Subtype.val (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))

/-- The named box topology is the topology induced by the coordinate inclusion. -/
theorem eventuallyZeroRealBoxTopology_def :
    eventuallyZeroRealBoxTopology =
      TopologicalSpace.induced Subtype.val (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) := rfl

/-- The topology on eventually-zero real sequences induced by their inclusion into `ℓ²`. -/
@[reducible, expose]
noncomputable def eventuallyZeroRealL2Topology : TopologicalSpace eventuallyZeroRealSequences :=
  TopologicalSpace.induced eventuallyZeroToL2 inferInstance

/-- The named `ℓ²` topology is the topology induced by `eventuallyZeroToL2`. -/
theorem eventuallyZeroRealL2Topology_def :
    eventuallyZeroRealL2Topology =
      TopologicalSpace.induced eventuallyZeroToL2 inferInstance := rfl

/-- The topology on eventually-zero real sequences induced by the uniform topology. -/
@[reducible, expose]
noncomputable def eventuallyZeroRealUniformTopology :
    TopologicalSpace eventuallyZeroRealSequences :=
  TopologicalSpace.induced Subtype.val (UniformMetric.topology ℕ)

/-- The named uniform topology is the topology induced by the coordinate inclusion. -/
theorem eventuallyZeroRealUniformTopology_def :
    eventuallyZeroRealUniformTopology =
      TopologicalSpace.induced Subtype.val (UniformMetric.topology ℕ) := rfl

/-- Helper for Exercise 20.8: convergence in the named eventually-zero box topology is
convergence of the underlying sequences in the canonical box wrapper. -/
lemma tendsto_eventuallyZeroBox_iff {γ : Type*} (u : γ → eventuallyZeroRealSequences)
    (l : Filter γ) (x : eventuallyZeroRealSequences) :
    @Filter.Tendsto γ eventuallyZeroRealSequences u l
        (@nhds eventuallyZeroRealSequences eventuallyZeroRealBoxTopology x) ↔
      Filter.Tendsto (BoxRealSequence.ofSequence ∘ Subtype.val ∘ u) l
        (nhds (BoxRealSequence.ofSequence x.1)) := by
  -- First expose the induced topology, then pass through the wrapper homeomorphism.
  rw [eventuallyZeroRealBoxTopology_def]
  rw [@nhds_induced (ℕ → ℝ) eventuallyZeroRealSequences
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) Subtype.val x]
  rw [Filter.tendsto_comap_iff]
  constructor
  · intro h
    simpa only [Function.comp_def, BoxRealSequence.ofSequence_eq_toTopology] using
      (@Continuous.tendsto (ℕ → ℝ) BoxRealSequence
        (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) inferInstance
        (WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
        (WithTopology.continuous_toTopology
          (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))) x.1).comp h
  · intro h
    simpa only [Function.comp_def, BoxRealSequence.ofSequence_eq_toTopology] using
      (@Continuous.tendsto BoxRealSequence (ℕ → ℝ) inferInstance
        (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
        (WithTopology.ofTopology (t := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
        (WithTopology.continuous_ofTopology
          (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
        (BoxRealSequence.ofSequence x.1)).comp h

/-- Helper for Exercise 20.8: convergence in the named eventually-zero uniform topology is
convergence of the underlying sequences in the canonical uniform wrapper. -/
lemma tendsto_eventuallyZeroUniform_iff {γ : Type*} (u : γ → eventuallyZeroRealSequences)
    (l : Filter γ) (x : eventuallyZeroRealSequences) :
    @Filter.Tendsto γ eventuallyZeroRealSequences u l
        (@nhds eventuallyZeroRealSequences eventuallyZeroRealUniformTopology x) ↔
      Filter.Tendsto (UniformRealSequence.ofSequence ∘ Subtype.val ∘ u) l
        (nhds (UniformRealSequence.ofSequence x.1)) := by
  -- First expose the induced topology, then pass through the wrapper homeomorphism.
  rw [eventuallyZeroRealUniformTopology_def]
  rw [@nhds_induced (ℕ → ℝ) eventuallyZeroRealSequences
    (UniformMetric.topology ℕ) Subtype.val x]
  rw [Filter.tendsto_comap_iff]
  constructor
  · intro h
    simpa only [Function.comp_def, UniformRealSequence.ofSequence_eq_toTopology] using
      (@Continuous.tendsto (ℕ → ℝ) UniformRealSequence (UniformMetric.topology ℕ)
        inferInstance (WithTopology.toTopology (UniformMetric.topology ℕ))
        (WithTopology.continuous_toTopology (UniformMetric.topology ℕ)) x.1).comp h
  · intro h
    simpa only [Function.comp_def, UniformRealSequence.ofSequence_eq_toTopology] using
      (@Continuous.tendsto UniformRealSequence (ℕ → ℝ) inferInstance
        (UniformMetric.topology ℕ)
        (WithTopology.ofTopology (t := UniformMetric.topology ℕ))
        (WithTopology.continuous_ofTopology (UniformMetric.topology ℕ))
        (UniformRealSequence.ofSequence x.1)).comp h

end
