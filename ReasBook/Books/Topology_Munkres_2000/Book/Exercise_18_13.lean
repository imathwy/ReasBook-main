module

public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.DenseEmbedding

public section

/-- Exercise 18.13: Any two continuous maps from `closure A` to a Hausdorff space
that agree with `f` on `A` are equal. -/
theorem Continuous.extensionToClosure_unique {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X}
    {f : A → Y} {g h : closure A → Y} (hg : Continuous g) (hh : Continuous h)
    (hg_extends : ∀ x : A, g ⟨x, subset_closure x.property⟩ = f x)
    (hh_extends : ∀ x : A, h ⟨x, subset_closure x.property⟩ = f x) :
    g = h := by
  apply ((denseRange_inclusion_iff subset_closure).2 subset_rfl).equalizer hg hh
  funext x
  exact (hg_extends x).trans (hh_extends x).symm
