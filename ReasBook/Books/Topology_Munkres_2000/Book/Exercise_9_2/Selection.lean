module

public import Topology_Munkres_2000.Book.Remark_9_4.ChoiceFunction
public import Mathlib.Order.WellFounded
public import Mathlib.Logic.Encodable.Basic

universe u

public section

namespace SetChoice

/-- The choice function on an encodable type obtained by minimizing `Encodable.encode`. -/
noncomputable def ofEncodable {α : Type u} [Encodable α] : SetChoice α :=
  SetChoice.ofFun
    (fun s hs ↦ Function.argminOn Encodable.encode s hs)
    (Function.argminOn_mem Encodable.encode)

/-- The choice function obtained by taking minima under a well-founded relation. -/
noncomputable def ofWellFounded {α : Type u} (r : α → α → Prop) [IsWellFounded α r] :
    SetChoice α :=
  SetChoice.ofFun
    (fun s hs ↦ WellFounded.min (IsWellFounded.wf : WellFounded r) s hs)
    (WellFounded.min_mem (IsWellFounded.wf : WellFounded r))

end SetChoice
