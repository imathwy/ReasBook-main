module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Module.Torsion.Free

public section

universe u

namespace Module.Free

/-- The underlying additive group of a free `ℤ`-module is torsion-free. -/
instance instIsAddTorsionFree {G : Type u} [AddCommGroup G] [Module.Free ℤ G] :
    IsAddTorsionFree G :=
  Module.isTorsionFree_int_iff_isAddTorsionFree.mp inferInstance

end Module.Free
