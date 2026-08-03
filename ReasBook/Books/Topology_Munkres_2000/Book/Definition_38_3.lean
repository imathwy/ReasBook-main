module

public import Topology_Munkres_2000.Book.Theorem_38_4

public section

universe u w

namespace Compactification

/- Definition 38.3. For a completely regular space `X`, `stoneCech X` is its chosen
Stone–Čech compactification. -/
#check stoneCech

/-- The Stone–Čech compactification uniquely extends every continuous map from a completely
regular space into a compact Hausdorff space. -/
theorem stoneCech_extendsContinuousMap (X : Type u) [TopologicalSpace X] [T35Space X]
    {C : Type w} [TopologicalSpace C] [CompactSpace C] [T2Space C]
    (f : ContinuousMap X C) :
    ∃! g : ContinuousMap (stoneCech X) C, ∀ x : X, g (stoneCech X x) = f x :=
  extendsContinuousMap (stoneCech X) (stoneCech_extendsBoundedContinuousReal X) f

end Compactification
