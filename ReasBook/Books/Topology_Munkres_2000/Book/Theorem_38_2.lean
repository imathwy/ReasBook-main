module

public import Topology_Munkres_2000.Book.Theorem_38_2.RealExtension

public section

universe u

namespace Compactification

/-- Theorem 38.2: Every completely regular space in Munkres's sense has a compactification to
which every bounded continuous real-valued function extends uniquely and continuously. -/
theorem exists_extendsBoundedContinuousReal (X : Type u) [TopologicalSpace X] [T35Space X] :
    ∃ C : Compactification.{u, u} X, C.ExtendsBoundedContinuousReal :=
  ⟨stoneCech X, stoneCech_extendsBoundedContinuousReal X⟩

end Compactification
