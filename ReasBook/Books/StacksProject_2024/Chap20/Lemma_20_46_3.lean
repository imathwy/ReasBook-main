import StacksProject_2024.Chap20.Lemma_20_47_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace CochainComplex

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
variable {K L : CochainComplex (SheafOfModules R) ℤ}

-- Proof sketch: boundedness of the total tensor complex follows from boundedness of the two
-- strictly perfect inputs. In each degree, the total tensor term is a finite direct sum of tensor
-- products of retracts of finite free module sheaves, hence again a retract of a finite free
-- module sheaf.
/-- The tensor product of two strictly perfect complexes of modules over a sheaf of rings is
strictly perfect. In Lean, this totalized tensor product is the monoidal tensor on
`CochainComplex (SheafOfModules R) ℤ`. -/
theorem isStrictlyPerfect_tensor
    [MonoidalCategory (CochainComplex (SheafOfModules R) ℤ)]
    (hK : IsStrictlyPerfect K)
    (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (K ⊗ L) := sorry

end CochainComplex

variable {X : RingedSpace.{u}}
variable {K L : CochainComplex (RingedSpace.Modules X) ℤ}

variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]

/-- Lemma 20.46.3: the totalized tensor product of two strictly perfect complexes of
`\mathcal O_X`-modules on a ringed space is strictly perfect. In Lean, this totalized tensor
product is the monoidal tensor on `CochainComplex (RingedSpace.Modules X) ℤ`. -/
theorem tensor_isStrictlyPerfect_of_isStrictlyPerfect
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (K ⊗ L) :=
  CochainComplex.isStrictlyPerfect_tensor hK hL

end AlgebraicGeometry.RingedSpace
