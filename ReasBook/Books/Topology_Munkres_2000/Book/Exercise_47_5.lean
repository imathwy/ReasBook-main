module

public import Mathlib.Topology.UniformSpace.Ascoli

public section

open Filter Set

universe u v

/-- Exercise 47.5 (1): A pointwise limit of an equicontinuous sequence of functions into a
uniform space is continuous. -/
theorem continuous_limit_of_equicontinuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [UniformSpace Y] (F : ℕ → X → Y) (f : X → Y)
    (h_pointwise : Tendsto F atTop (nhds f)) (h_equicontinuous : Equicontinuous F) :
    Continuous f := by
  have h_range : (range F).Equicontinuous := by
    rwa [equicontinuous_iff_range] at h_equicontinuous
  have h_mem : f ∈ closure (range F) :=
    mem_closure_of_tendsto h_pointwise range_mem_map
  exact h_range.closure.continuous ⟨f, h_mem⟩

/-- Exercise 47.5 (2): A pointwise-convergent equicontinuous sequence of functions into a uniform
space converges uniformly on every compact subset. -/
theorem tendsto_compactConvergence_of_equicontinuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [UniformSpace Y] (F : ℕ → X → Y) (f : X → Y)
    (h_pointwise : Tendsto F atTop (nhds f)) (h_equicontinuous : Equicontinuous F) :
    Tendsto (fun n ↦ UniformOnFun.ofFun {K : Set X | IsCompact K} (F n)) atTop
      (nhds (UniformOnFun.ofFun {K : Set X | IsCompact K} f)) := by
  have h_compact : ∀ K ∈ {K : Set X | IsCompact K}, IsCompact K := fun _ hK ↦ hK
  have h_cover : ⋃₀ {K : Set X | IsCompact K} = univ := by
    rw [sUnion_eq_univ_iff]
    intro x
    exact ⟨{x}, isCompact_singleton, mem_singleton x⟩
  have h_equicontinuousOn : ∀ K ∈ {K : Set X | IsCompact K}, EquicontinuousOn F K :=
    fun K _ ↦ h_equicontinuous.equicontinuousOn K
  exact (EquicontinuousOn.tendsto_uniformOnFun_iff_pi
    h_compact h_cover h_equicontinuousOn atTop f).2 h_pointwise

end
