module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Covering.Basic

public section

universe u v

namespace IsCoveringMap

/-- Exercise 79.7: the domain of a covering homomorphism to an abelian topological group is
abelian. -/
theorem mul_comm {G' : Type u} {G : Type v}
    [TopologicalSpace G'] [Group G'] [IsTopologicalGroup G']
    [PathConnectedSpace G']
    [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G]
    {p : G' →* G} (hp : IsCoveringMap p) (x y : G') :
    x * y = y * x := by
  have h := hp.eq_of_comp_eq
    (continuous_mul.comp <| continuous_fst.prodMk continuous_snd)
    (continuous_mul.comp <| continuous_snd.prodMk continuous_fst)
    (by
      funext z
      simp only [Function.comp_apply, map_mul]
      exact _root_.mul_comm _ _)
    (1, 1) (by simp)
  exact congr_fun h (x, y)

end IsCoveringMap
