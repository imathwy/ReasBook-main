module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.UniformSpace.UniformConvergence

public section

universe u v w

open Filter

/-- A family of functions vanishes uniformly at infinity when it converges uniformly to zero
along the cocompact filter. -/
def UniformlyVanishesAtInfinity {ι : Type w} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [UniformSpace Y] [Zero Y] (F : ι → X → Y) : Prop :=
  TendstoUniformlyOnFilter F 0 ⊤ (cocompact X)

/-- Helper for Exercise 45.5: uniform vanishing is uniform convergence to zero along the
cocompact filter. -/
theorem uniformlyVanishesAtInfinity_iff_tendstoUniformlyOnFilter
    {ι : Type w} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [UniformSpace Y] [Zero Y] (F : ι → X → Y) :
    UniformlyVanishesAtInfinity F ↔
      TendstoUniformlyOnFilter F 0 ⊤ (cocompact X) := by
  -- Expose the defining filter formulation at its canonical owner.
  rfl

/-- A set of functions vanishes uniformly at infinity when its subtype-indexed family does. -/
protected abbrev Set.UniformlyVanishesAtInfinity {X : Type u} {Y : Type v}
    [TopologicalSpace X] [UniformSpace Y] [Zero Y] (𝓕 : Set (X → Y)) : Prop :=
  UniformlyVanishesAtInfinity ((↑) : 𝓕 → X → Y)

/-- A singleton family vanishes uniformly at infinity exactly when its function tends to zero
along the cocompact filter. -/
theorem uniformlyVanishesAtInfinity_singleton_iff {X : Type u} {Y : Type v}
    [TopologicalSpace X] [UniformSpace Y] [Zero Y] (f : X → Y) :
    ({f} : Set (X → Y)).UniformlyVanishesAtInfinity ↔
      Tendsto f (cocompact X) (nhds 0) := by
  -- Expose uniform convergence and compare its singleton-indexed product filter directly.
  rw [Set.UniformlyVanishesAtInfinity,
    uniformlyVanishesAtInfinity_iff_tendstoUniformlyOnFilter]
  constructor
  · intro h
    rw [Uniform.tendsto_nhds_right, tendsto_def]
    intro s hs
    obtain ⟨si, hsi, sx, hsx, hprod⟩ := eventually_prod_iff.mp (h s hs)
    rw [eventually_top] at hsi
    filter_upwards [hsx] with x hx
    exact hprod (hsi ⟨f, Set.mem_singleton f⟩) hx
  · intro h
    intro s hs
    have h_event : ∀ᶠ x in cocompact X, (0, f x) ∈ s :=
      (Uniform.tendsto_nhds_right.mp h) hs
    apply eventually_prod_iff.mpr
    refine ⟨fun _ ↦ True, Filter.Eventually.of_forall fun _ ↦ trivial,
      fun x ↦ (0, f x) ∈ s, h_event, ?_⟩
    intro i _ x hx
    simpa only [Pi.zero_apply, Set.mem_singleton_iff.mp i.property] using hx
