module

public import Topology_Munkres_2000.Book.Example_38_4.Extension

public section

universe u v w

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- The canonical continuous extension determined by limits along a compactification. -/
noncomputable def continuousExtension (C : Compactification.{u, v} X)
    {Y : Type w} [TopologicalSpace Y] [T3Space Y] (f : ContinuousMap X Y)
    (hf : ∀ y : C, ∃ z : Y, Filter.Tendsto f (Filter.comap C (nhds y)) (nhds z)) :
    ContinuousMap C Y where
  toFun := C.isDenseEmbedding.isDenseInducing.extend f
  continuous_toFun := C.isDenseEmbedding.isDenseInducing.continuous_extend hf

/-- The canonical extension agrees with the original function on the embedded copy of `X`. -/
theorem continuousExtension_apply (C : Compactification.{u, v} X)
    {Y : Type w} [TopologicalSpace Y] [T3Space Y] (f : ContinuousMap X Y)
    (hf : ∀ y : C, ∃ z : Y, Filter.Tendsto f (Filter.comap C (nhds y)) (nhds z)) (x : X) :
    continuousExtension C f hf (C x) = f x :=
  C.isDenseEmbedding.isDenseInducing.extend_eq' hf x

/-- A continuous extension from the dense copy of `X` is uniquely determined. -/
theorem continuousExtension_unique (C : Compactification.{u, v} X)
    {Y : Type w} [TopologicalSpace Y] [T3Space Y] (f : ContinuousMap X Y)
    (hf : ∀ y : C, ∃ z : Y, Filter.Tendsto f (Filter.comap C (nhds y)) (nhds z))
    (g : ContinuousMap C Y) (hg : ∀ x : X, g (C x) = f x) :
    g = continuousExtension C f hf := by
  ext y
  exact congrFun (C.isDenseEmbedding.isDenseInducing.extend_unique hg g.continuous).symm y


end Compactification
