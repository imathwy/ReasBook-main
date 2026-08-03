module

public import Topology_Munkres_2000.Book.Lemma_80_2

public section

universe u v w

namespace IsCoveringMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- If `r ∘ q` and `r` are covering maps in the surjective sense, then so is `q`. -/
theorem of_comp_right_surjective {q : X → Y} {r : Y → Z}
    [PreconnectedSpace Y] [LocallyConnectedSpace Z]
    (hq_continuous : Continuous q) (hcomp : IsCoveringMap (r ∘ q))
    (hcomp_surjective : Function.Surjective (r ∘ q)) (hr : IsCoveringMap r) :
    IsCoveringMap q ∧ Function.Surjective q := by
  -- Apply the canonical cancellation theorem with the composite itself as `p`.
  exact _root_.coveringMap_of_comp_right hq_continuous rfl hcomp hcomp_surjective hr

/-- If `r ∘ q` and `q` are covering maps in the surjective sense, then so is `r`. -/
theorem of_comp_left_surjective {q : X → Y} {r : Y → Z}
    [LocallyConnectedSpace Y] [LocallyConnectedSpace Z]
    (hr_continuous : Continuous r) (hcomp : IsCoveringMap (r ∘ q))
    (hcomp_surjective : Function.Surjective (r ∘ q)) (hq : IsCoveringMap q)
    (hq_surjective : Function.Surjective q) :
    IsCoveringMap r ∧ Function.Surjective r := by
  -- Apply the canonical cancellation theorem with the composite itself as `p`.
  exact _root_.coveringMap_of_comp_left hr_continuous rfl hcomp hcomp_surjective hq
    hq_surjective

end IsCoveringMap
