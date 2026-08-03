module

public import Topology_Munkres_2000.Book.Proposition_81_2.Covering
public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

universe u v

namespace ConnectedCovering

variable {B : Type v} [TopologicalSpace B]

/-- A connected covering is regular when every induced fundamental-group subgroup is normal. -/
class IsRegular (C : ConnectedCovering.{u} B) : Prop where
  normal (b₀ : B) (e₀ : C.Total) (h₀ : C.proj e₀ = b₀) :
    (C.isCoveringMap.fundamentalGroupMapRange h₀).Normal

/-- Regularity supplies normality of the induced subgroup at every chosen point. -/
instance instNormalFundamentalGroupMapRange (C : ConnectedCovering.{u} B) [C.IsRegular]
    (b₀ : B) (e₀ : C.Total) (h₀ : C.proj e₀ = b₀) :
    (C.isCoveringMap.fundamentalGroupMapRange h₀).Normal :=
  IsRegular.normal b₀ e₀ h₀

end ConnectedCovering
