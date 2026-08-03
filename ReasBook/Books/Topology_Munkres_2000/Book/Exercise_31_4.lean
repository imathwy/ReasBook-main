module

public import Topology_Munkres_2000.Book.Example_31_1
public import Topology_Munkres_2000.Book.Lemma_13_4
public import Mathlib.Topology.WithTopology

public section

/-- Helper for Exercise 31.4: `WithTopology X t` is canonically homeomorphic to `X` with topology
`t`. -/
def withTopologyHomeomorph {X : Type u} (t : TopologicalSpace X) :
    @Homeomorph X (WithTopology X t) t (WithTopology.instTopologicalSpace X t) :=
  Homeomorph.mk (WithTopology.equiv X t).symm (WithTopology.continuous_toTopology t)
    (WithTopology.continuous_ofTopology t)

/-- Helper for Exercise 31.4: Hausdorffness of a topology is equivalent to Hausdorffness of its
`WithTopology` copy. -/
lemma t2Space_withTopology_iff {X : Type u} (t : TopologicalSpace X) :
    T2Space (WithTopology X t) ↔ @T2Space X t := by
  -- Transport the separation class in both directions along the canonical homeomorphism.
  constructor
  · intro hT2
    letI : T2Space (WithTopology X t) := hT2
    letI : TopologicalSpace X := t
    exact (withTopologyHomeomorph t).symm.t2Space
  · intro hT2
    letI : TopologicalSpace X := t
    letI : T2Space X := hT2
    exact (withTopologyHomeomorph t).t2Space

/-- Helper for Exercise 31.4: regular Hausdorffness of a topology is equivalent to that of its
`WithTopology` copy. -/
lemma t3Space_withTopology_iff {X : Type u} (t : TopologicalSpace X) :
    T3Space (WithTopology X t) ↔ @T3Space X t := by
  -- Transport the separation class in both directions along the canonical homeomorphism.
  constructor
  · intro hT3
    letI : T3Space (WithTopology X t) := hT3
    letI : TopologicalSpace X := t
    exact (withTopologyHomeomorph t).symm.t3Space
  · intro hT3
    letI : TopologicalSpace X := t
    letI : T3Space X := hT3
    exact (withTopologyHomeomorph t).t3Space

/-- Helper for Exercise 31.4: normal Hausdorffness of a topology is equivalent to that of its
`WithTopology` copy. -/
lemma t4Space_withTopology_iff {X : Type u} (t : TopologicalSpace X) :
    T4Space (WithTopology X t) ↔ @T4Space X t := by
  -- Transport the separation class in both directions along the canonical homeomorphism.
  constructor
  · intro hT4
    letI : T4Space (WithTopology X t) := hT4
    letI : TopologicalSpace X := t
    exact (withTopologyHomeomorph t).symm.t4Space
  · intro hT4
    letI : TopologicalSpace X := t
    letI : T4Space X := hT4
    exact (withTopologyHomeomorph t).t4Space

/-- Helper for Exercise 31.4: refining a topology preserves Hausdorffness on the same carrier. -/
lemma t2Space_of_finer_topology {X : Type u} {t t' : TopologicalSpace X} (h_finer : t' ≤ t)
    (hT2 : @T2Space X t) : @T2Space X t' := by
  -- Reuse the coarser separating neighborhoods, promoting only their openness.
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := hT2.t2 hxy
  exact ⟨u, v, hu.mono h_finer, hv.mono h_finer, hxu, hyv, huv⟩

/-- The first conclusion of Exercise 31.4: if `t'` is finer than `t`, Hausdorffness of the coarser
topology `t` implies Hausdorffness of the finer topology `t'`. -/
theorem t2Space_of_finer {X : Type u} (t t' : TopologicalSpace X) (h_finer : t' ≤ t)
    (hT2 : T2Space (WithTopology X t)) : T2Space (WithTopology X t') := by
  -- Move to the shared carrier, refine its topology, and transport back to `WithTopology`.
  apply (t2Space_withTopology_iff t').2
  exact t2Space_of_finer_topology h_finer ((t2Space_withTopology_iff t).1 hT2)

namespace RealTopology

/-- Helper for Exercise 31.4: the `K`-topology on `ℝ` refines the standard topology. -/
lemma standard_le_k :
    k ≤ (inferInstance : TopologicalSpace ℝ) := by
  -- Use the previously established strict comparison of these two topologies.
  exact k_lt_standard.le

end RealTopology

/-- Helper for Exercise 31.4: the indiscrete topology on `Bool` is not Hausdorff. -/
lemma notT2Space_indiscrete_bool :
    ¬ T2Space (WithTopology Bool (⊤ : TopologicalSpace Bool)) := by
  -- Two distinct points cannot have disjoint nonempty indiscrete-open neighborhoods.
  intro hT2With
  have hT2 : @T2Space Bool ⊤ := (t2Space_withTopology_iff ⊤).1 hT2With
  obtain ⟨u, v, hu, hv, hfu, htv, huv⟩ := hT2.t2 Bool.false_ne_true
  rw [TopologicalSpace.isOpen_top_iff] at hu hv
  rcases hu with rfl | rfl
  · exact hfu
  · rcases hv with rfl | rfl
    · exact htv
    · exact Set.disjoint_left.mp huv (Set.mem_univ false) (Set.mem_univ false)

/-- Helper for Exercise 31.4: the indiscrete topology on `Bool` is not regular Hausdorff. -/
lemma notT3Space_indiscrete_bool :
    ¬ T3Space (WithTopology Bool (⊤ : TopologicalSpace Bool)) := by
  -- A `T₃` instance canonically supplies the already impossible `T₂` instance.
  intro hT3
  letI : T3Space (WithTopology Bool (⊤ : TopologicalSpace Bool)) := hT3
  exact notT2Space_indiscrete_bool inferInstance

/-- Helper for Exercise 31.4: the indiscrete topology on `Bool` is not normal Hausdorff. -/
lemma notT4Space_indiscrete_bool :
    ¬ T4Space (WithTopology Bool (⊤ : TopologicalSpace Bool)) := by
  -- A `T₄` instance canonically supplies the already impossible `T₃` instance.
  intro hT4
  letI : T4Space (WithTopology Bool (⊤ : TopologicalSpace Bool)) := hT4
  exact notT3Space_indiscrete_bool inferInstance

/-- The second conclusion of Exercise 31.4: Hausdorffness of a finer topology need not imply
Hausdorffness of a coarser topology. -/
theorem exists_finer_t2Space_not_coarser :
    ∃ (X : Type) (t t' : TopologicalSpace X),
      t' ≤ t ∧ T2Space (WithTopology X t') ∧ ¬ T2Space (WithTopology X t) := by
  -- The discrete topology on `Bool` refines its indiscrete topology.
  refine ⟨Bool, ⊤, ⊥, bot_le, ?_, notT2Space_indiscrete_bool⟩
  infer_instance

/-- The third conclusion of Exercise 31.4: regularity of a coarser topology need not imply
regularity of a finer topology. -/
theorem exists_coarser_t3Space_not_finer :
    ∃ (X : Type) (t t' : TopologicalSpace X),
      t' ≤ t ∧ T3Space (WithTopology X t) ∧ ¬ T3Space (WithTopology X t') := by
  -- The standard real topology is `T₃`, while its finer `K`-topology is not.
  refine ⟨ℝ, inferInstance, RealTopology.k, RealTopology.standard_le_k, ?_, ?_⟩
  · apply (t3Space_withTopology_iff _).2
    infer_instance
  · intro hT3
    exact RealTopology.kNotT3Space ((t3Space_withTopology_iff RealTopology.k).1 hT3)

/-- The fourth conclusion of Exercise 31.4: regularity of a finer topology need not imply
regularity of a coarser topology. -/
theorem exists_finer_t3Space_not_coarser :
    ∃ (X : Type) (t t' : TopologicalSpace X),
      t' ≤ t ∧ T3Space (WithTopology X t') ∧ ¬ T3Space (WithTopology X t) := by
  -- Again use discrete `Bool` over its indiscrete coarsening.
  refine ⟨Bool, ⊤, ⊥, bot_le, ?_, notT3Space_indiscrete_bool⟩
  infer_instance

/-- The fifth conclusion of Exercise 31.4: normality of a coarser topology need not imply
normality of a finer topology. -/
theorem exists_coarser_t4Space_not_finer :
    ∃ (X : Type) (t t' : TopologicalSpace X),
      t' ≤ t ∧ T4Space (WithTopology X t) ∧ ¬ T4Space (WithTopology X t') := by
  -- The standard real topology is `T₄`; a `T₄` `K`-topology would contradict its failure of `T₃`.
  refine ⟨ℝ, inferInstance, RealTopology.k, RealTopology.standard_le_k, ?_, ?_⟩
  · apply (t4Space_withTopology_iff _).2
    infer_instance
  · intro hT4
    have hK4 : @T4Space ℝ RealTopology.k := (t4Space_withTopology_iff RealTopology.k).1 hT4
    letI : TopologicalSpace ℝ := RealTopology.k
    letI : T4Space ℝ := hK4
    exact RealTopology.kNotT3Space inferInstance

/-- The sixth conclusion of Exercise 31.4: normality of a finer topology need not imply
normality of a coarser topology. -/
theorem exists_finer_t4Space_not_coarser :
    ∃ (X : Type) (t t' : TopologicalSpace X),
      t' ≤ t ∧ T4Space (WithTopology X t') ∧ ¬ T4Space (WithTopology X t) := by
  -- Discrete `Bool` is `T₄`, whereas the indiscrete topology is not even Hausdorff.
  refine ⟨Bool, ⊤, ⊥, bot_le, ?_, notT4Space_indiscrete_bool⟩
  apply (t4Space_withTopology_iff _).2
  infer_instance

/-- Exercise 31.4: the six conclusions about separation axioms under refinement. -/
theorem separationAxiomsUnderRefinement :
    (∀ {X : Type u} (t t' : TopologicalSpace X),
      t' ≤ t → T2Space (WithTopology X t) → T2Space (WithTopology X t')) ∧
      (∃ (X : Type) (t t' : TopologicalSpace X),
        t' ≤ t ∧ T2Space (WithTopology X t') ∧ ¬ T2Space (WithTopology X t)) ∧
      (∃ (X : Type) (t t' : TopologicalSpace X),
        t' ≤ t ∧ T3Space (WithTopology X t) ∧ ¬ T3Space (WithTopology X t')) ∧
      (∃ (X : Type) (t t' : TopologicalSpace X),
        t' ≤ t ∧ T3Space (WithTopology X t') ∧ ¬ T3Space (WithTopology X t)) ∧
      (∃ (X : Type) (t t' : TopologicalSpace X),
        t' ≤ t ∧ T4Space (WithTopology X t) ∧ ¬ T4Space (WithTopology X t')) ∧
      (∃ (X : Type) (t t' : TopologicalSpace X),
        t' ≤ t ∧ T4Space (WithTopology X t') ∧ ¬ T4Space (WithTopology X t)) := by
  -- Package the six atomic conclusions into the single source-facing exercise result.
  exact ⟨t2Space_of_finer, exists_finer_t2Space_not_coarser,
    exists_coarser_t3Space_not_finer, exists_finer_t3Space_not_coarser,
    exists_coarser_t4Space_not_finer, exists_finer_t4Space_not_coarser⟩
