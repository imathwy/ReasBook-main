module

public import Mathlib.GroupTheory.FiniteAbelian.Basic

public section

universe u

namespace AddCommGroup

variable {G : Type u} [AddCommGroup G] [AddGroup.FG G]

/-- The torsion subgroup of a finitely generated abelian group is finitely generated as a
`ℤ`-module. -/
instance moduleFiniteTorsion : Module.Finite ℤ (torsion G) := by
  change Module.Finite ℤ (torsion G).toIntSubmodule
  exact Module.Finite.of_fg (IsNoetherian.noetherian (torsion G).toIntSubmodule)

/-- The torsion subgroup of a finitely generated abelian group is finite. -/
instance finiteTorsion : Finite (torsion G) :=
  Module.finite_of_fg_torsion _ <|
    AddMonoid.isTorsion_iff_isTorsion_int.mp AddCommMonoid.addTorsion.isTorsion

end AddCommGroup
