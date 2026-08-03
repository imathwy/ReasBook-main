module

public import Mathlib.Topology.UniformSpace.CompactConvergence

public section

open Filter Set
open scoped UniformConvergence

universe u v

/-- Theorem 46.2: A sequence of functions converges in the topology of compact
convergence exactly when its restrictions to every compact subset converge uniformly. -/
theorem tendsto_compactConvergence_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    [UniformSpace Y] (F : ℕ → X → Y) (f : X → Y) :
    Tendsto
        (fun n ↦ UniformOnFun.ofFun {K : Set X | IsCompact K} (F n)) atTop
        (nhds (UniformOnFun.ofFun {K : Set X | IsCompact K} f)) ↔
      ∀ K : Set X, IsCompact K →
        TendstoUniformly (fun n ↦ K.restrict (F n)) (K.restrict f) atTop := by
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  simp only [mem_setOf_eq, Function.comp_apply, UniformOnFun.toFun_ofFun,
    tendstoUniformlyOn_iff_restrict]

end
