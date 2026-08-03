module

public import Topology_Munkres_2000.Book.Definition_81_4
public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup

public section

namespace Circle

/-- Helper for Example 81.1: every fundamental group of the circle is multiplicatively
commutative. -/
noncomputable instance instIsMulCommutativeFundamentalGroup (x : Circle) :
    IsMulCommutative (FundamentalGroup Circle x) :=
  IsMulCommutative.of_comm fun a b ↦ by
    -- Transport multiplication to the standard integer coordinate group.
    let e := (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x 1).trans
      fundamentalGroupEquivInt
    apply e.injective
    simpa only [map_mul] using mul_comm (e a) (e b)

end Circle

namespace ConnectedCovering

/-- Every connected covering of the circle is regular. -/
instance instIsRegularCircle (C : ConnectedCovering Circle) : C.IsRegular := by
  -- Every subgroup of the now-commutative circle fundamental group is normal.
  constructor
  intro b₀ e₀ h₀
  infer_instance

end ConnectedCovering
