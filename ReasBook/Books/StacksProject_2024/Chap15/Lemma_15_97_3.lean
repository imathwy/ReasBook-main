import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Basis
import StacksProject_2024.Chap15.Lemma_15_8_4
import StacksProject_2024.Chap15.Lemma_15_97_1

noncomputable section

open CategoryTheory
open ComplexShape
open scoped FittingIdeal
open scoped TensorProduct

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

open scoped EtaDeterminantalIdeal

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTermLinearEquiv (M : CpxA) (i : ℤ) :
    ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M).X i :
      ModuleCat B) ≃ₗ[B] (B ⊗[A] (M.X i)) := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A (M.X i)))

noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFree
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] :
    Module.Free B
      ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M).X i :
        ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Free.of_basis (b.map (extendScalarsTermLinearEquiv M i).symm)

noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFinite
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] [Module.Finite A (M.X i)] :
    Module.Finite B
      ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M).X i :
        ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Finite.of_basis
    (b.map (extendScalarsTermLinearEquiv M i).symm)

/-
Domain-style sampling:
- primary domain: determinantal ideals for the Berthelot-Ogus presentation map `(f, d^i)` under
  tensor-product base change;
- sampled owner declarations:
  `etaDeterminantalIdeal`,
  `etaPresentationQuotient`,
  `(ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)`,
  `fittingIdeal_eq_of_linearEquiv`,
  `fittingIdeal_baseChange`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the intrinsic Fitting ideal together with the chapter base-change owner
    `fittingIdeal_baseChange`;
  `bridge/view`: the scalar-extended cochain complex
    `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M`;
- primitive data vs. derived API: the primitive source-facing data are the presentation map
  `etaPresentationLinearMap f M i` and its quotient; the base-changed complex itself is derived
  bridge data, and the equality below is the source-facing statement. -/

-- Proof sketch: `etaDeterminantalIdeal` is the intrinsic Fitting ideal of
-- `etaPresentationQuotient f M i`. After scalar extension, the degree terms remain finite free by
-- the canonical tensor-product instances.
-- Comparing the scalar-extended quotient with the quotient attached to the canonical scalar
-- extension `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M`
-- reduces the statement to the chapter owner
-- `fittingIdeal_baseChange`.
/-- Lemma 15.97.3: the degree-`i` determinantal ideal attached to `(f, d^i)` commutes with base
change along `A → B`. The primitive data are only the finite free terms in degrees `i` and
`i + 1`; boundedness and nonzerodivisor hypotheses are not needed for this base-change identity
itself. -/
theorem etaDeterminantalIdeal_baseChange
    (f : A) (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    I[algebraMap A B f]_(i)(
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M)) =
      Ideal.map (algebraMap A B)
        (I[f]_(i)(M)) := sorry

end
