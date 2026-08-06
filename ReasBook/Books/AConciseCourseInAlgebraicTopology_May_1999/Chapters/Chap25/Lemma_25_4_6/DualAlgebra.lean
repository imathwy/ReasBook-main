module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_5.AdmissibleMonomials

public section

noncomputable section

universe u

open scoped TensorProduct

/-- The restricted (equivalently, graded) dual of the Steenrod algebra: the linear functionals
whose support on the admissible monomial basis is finite.  Since each graded piece of `A` is
finite-dimensional, this is the direct sum of the duals of the graded pieces, as in May's `A_*`.
It is deliberately smaller than the full algebraic dual `Module.Dual (ZMod 2) A`. -/
def modTwoSteenrodAlgebraGradedDualSubmodule :
    Submodule (ZMod 2) (Module.Dual (ZMod 2) ModTwoSteenrodAlgebra) where
  carrier := { φ | Set.Finite {I : AdmissibleSteenrodMonomialIndex |
    φ (admissibleSteenrodMonomial I) ≠ 0} }
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ
    sorry
  smul_mem' := by
    intro c φ hφ
    sorry

/-- May's dual Steenrod algebra carrier `A_*`, realized as the graded/restricted dual of `A`. -/
abbrev modTwoSteenrodAlgebraGradedDual : Type :=
  modTwoSteenrodAlgebraGradedDualSubmodule

/-- The canonical inclusion of the graded dual into the full linear dual, used for the evaluation
pairing with the Steenrod algebra. -/
abbrev modTwoSteenrodAlgebraGradedDual.inclusion :
    modTwoSteenrodAlgebraGradedDual →ₗ[ZMod 2]
      Module.Dual (ZMod 2) ModTwoSteenrodAlgebra :=
  modTwoSteenrodAlgebraGradedDualSubmodule.subtype

/-- Evaluate an element of the graded dual on an element of the Steenrod algebra. -/
abbrev modTwoSteenrodAlgebraGradedDual.eval
    (f : modTwoSteenrodAlgebraGradedDual) (a : ModTwoSteenrodAlgebra) : ZMod 2 :=
  f.1 a

/-- The canonical inclusion of `A_* ⊗ M` into `Aᵛ ⊗ M`, induced by the inclusion of
the graded dual into the full linear dual. -/
abbrev modTwoSteenrodAlgebraGradedDual.tensorInclusion
    (M : Type u) [AddCommMonoid M] [Module (ZMod 2) M] :
    (modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)] M) →ₗ[(ZMod 2)]
      (Module.Dual (ZMod 2) ModTwoSteenrodAlgebra ⊗[(ZMod 2)] M) :=
  TensorProduct.map modTwoSteenrodAlgebraGradedDual.inclusion LinearMap.id

/-- The preexisting additive commutative group structure on the graded dual of
`ModTwoSteenrodAlgebra`. -/
noncomputable abbrev modTwoSteenrodAlgebraGradedDualAddCommGroup :
    AddCommGroup modTwoSteenrodAlgebraGradedDual :=
  inferInstance

/-- The `ZMod 2`-algebra structures on the graded dual `A_*` whose semiring structure comes
from a chosen ring structure. -/
abbrev modTwoSteenrodAlgebraGradedDualAlgebraStructure
    (toRing : Ring modTwoSteenrodAlgebraGradedDual) : Type :=
  let _ : Ring modTwoSteenrodAlgebraGradedDual := toRing
  Algebra (ZMod 2) modTwoSteenrodAlgebraGradedDual

/-- A chosen source-facing algebra structure on the graded dual `A_*`. -/
class ModTwoSteenrodAlgebraDualAlgebra where
  /-- The ring structure on the graded dual `A_*`. -/
  toRing : Ring modTwoSteenrodAlgebraGradedDual
  /-- The additive commutative group underlying the ring structure on `A_*` agrees with the
  preexisting additive structure on the linear dual. -/
  addCommGroup_eq :
    toRing.toAddCommGroup = modTwoSteenrodAlgebraGradedDualAddCommGroup
  /-- The `ZMod 2`-algebra structure on the graded dual `A_*`. -/
  toAlgebra : modTwoSteenrodAlgebraGradedDualAlgebraStructure toRing

/-- The data carried by `ModTwoSteenrodAlgebraDualAlgebra` is a ring and `ZMod 2`-algebra
structure on the graded dual `A_*`, compatible with its preexisting additive commutative
group on the linear dual. -/
theorem modTwoSteenrodAlgebraDualAlgebra_spec
    (AStar : ModTwoSteenrodAlgebraDualAlgebra) :
    AStar.toRing.toAddCommGroup = modTwoSteenrodAlgebraGradedDualAddCommGroup :=
  AStar.addCommGroup_eq

/-- A chosen dual Steenrod algebra owner supplies the ambient ring structure on `A_*`. -/
instance (AStar : ModTwoSteenrodAlgebraDualAlgebra) :
    Ring modTwoSteenrodAlgebraGradedDual :=
  AStar.toRing

/-- A chosen dual Steenrod algebra owner supplies the ambient `ZMod 2`-algebra structure on
`A_*`. -/
instance (AStar : ModTwoSteenrodAlgebraDualAlgebra) :
    modTwoSteenrodAlgebraGradedDualAlgebraStructure AStar.toRing :=
  AStar.toAlgebra

namespace ModTwoSteenrodAlgebraDualAlgebra

/-- The unit element of the chosen dual Steenrod algebra owner on the graded dual `A_*`. -/
abbrev one (AStar : ModTwoSteenrodAlgebraDualAlgebra) : modTwoSteenrodAlgebraGradedDual :=
  let _ : Ring modTwoSteenrodAlgebraGradedDual := AStar.toRing
  (1 : modTwoSteenrodAlgebraGradedDual)

end ModTwoSteenrodAlgebraDualAlgebra
