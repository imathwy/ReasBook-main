module

public import Topology_Munkres_2000.Book.Theorem_18_6

public section

universe u v

/-- Exercise 21.8: If continuous functions `f n : X → Y` converge uniformly to `g`
and `x n` converges to `a`, then `f n (x n)` converges to `g a`. -/
theorem tendsto_apply_of_tendstoUniformly {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] {f : ℕ → X → Y} {g : X → Y}
    {x : ℕ → X} {a : X} (hf : ∀ n, Continuous (f n))
    (hfg : TendstoUniformly f g Filter.atTop)
    (hx : Filter.Tendsto x Filter.atTop (nhds a)) :
    Filter.Tendsto (fun n ↦ f n (x n)) Filter.atTop (nhds (g a)) :=
  hfg.tendsto_comp (continuous_of_tendstoUniformly hf hfg).continuousAt hx
