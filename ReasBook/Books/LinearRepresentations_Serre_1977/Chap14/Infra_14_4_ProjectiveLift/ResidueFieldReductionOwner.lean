import Mathlib
import Mathlib.RepresentationTheory.Intertwining
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_6.Index

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u w w₁ x

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G]

local notation "kA" => IsLocalRing.ResidueField A

variable {P : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]

variable {B : Type w₁} [Ring B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
variable {Bbar : Type x} [Ring Bbar] [Algebra A Bbar] [Algebra (IsLocalRing.ResidueField A) Bbar]
variable [IsScalarTower A (IsLocalRing.ResidueField A) Bbar]

namespace FiniteProjectiveGroupAlgebraModule

section Henselian

variable [HenselianLocalRing A]

/-- Helper owner for `Infra_14_4_ProjectiveLift`: every finite projective `k[G]`-module is the
reduction of a finite projective `A[G]`-module, proved from the split Exercise 14-14.4-6 support
files without importing the broken omnibus file. -/
theorem exists_residueFieldReduction_iso
    [Finite G]
    (F : FiniteProjectiveGroupAlgebraModule kA G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction ≅ F) := by
  -- Route correction: keep the Chapter `14` public owner on the split support layer instead of
  -- importing the broken omnibus `Exercise_14_14_4_6.lean`.
  -- TODO: finish the nilpotent-kernel projector lift on this owner surface by re-exposing the
  -- lifted-projector range equivalence from the split support files, then remove this placeholder.
  sorry

end Henselian

end FiniteProjectiveGroupAlgebraModule
