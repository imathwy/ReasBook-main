import Mathlib
import stacks_proof.stacks_project.Chap15.«15_60_1_1»
import stacks_proof.stacks_project.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
/-- Helper for Lemma 15.75.9: the cochain-level scalar-extension functor along `A → B`. -/
private abbrev ExtCpx :
    CochainComplex (ModuleCat A) ℤ ⥤ CochainComplex (ModuleCat B) ℤ :=
  (ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)

/- Domain-style sampling for Lemma 15.75.9:
- primary domain: preservation of perfect objects in derived categories under derived scalar
  extension;
- sampled owner declarations:
  `K.IsPerfect`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebra_isPseudoCoherent`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: the theorem is source-facing, while the core/canonical owners are
  `K.IsPerfect` and the derived base-change object `K ⊗[A]^L[B]`;
- primitive vs. derived:
  primitive data are the perfect object `K` and the algebra map `A → B`;
  the preservation statement is derived API over those existing owners, so the public surface
  should use the owner notation rather than a raw functor application term;
- source/core/bridge triage:
  `source-facing`: perfectness is preserved by derived base change;
  `core/canonical`: `K.IsPerfect` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to `K`. -/

/-- Helper for Lemma 15.75.9: after restricting scalars, the regular `B`-module is canonically
itself. -/
private noncomputable abbrev restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.75.9: the restricted scalar action on `B` still forms the expected scalar
tower over `A`. -/
private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Lemma 15.75.9: a bounded finite-projective strict complex should compute derived
scalar extension by ordinary termwise scalar extension. -/
private noncomputable def derivedTensorWithAlgebra_Q_obj_iso_of_isBoundedFiniteProjective
    (L : CochainComplex (ModuleCat A) ℤ)
    (hL : CochainComplex.IsBoundedFiniteProjective L) :
    ((DerivedCategory.Q.obj L) ⊗[A]^L[B]) ≅
      DerivedCategory.Q.obj ((ExtCpx (A := A) (B := B)).obj L) :=
  sorry

/-- Helper for Lemma 15.75.9: scalar extension of a bounded finite-projective complex is again
bounded finite-projective. -/
private theorem isBoundedFiniteProjective_mapExtendScalars
    (L : CochainComplex (ModuleCat A) ℤ)
    [hL : CochainComplex.IsBoundedFiniteProjective L] :
    CochainComplex.IsBoundedFiniteProjective ((ExtCpx (A := A) (B := B)).obj L) := by
  rcases hL.bounded with ⟨a, b, hGE, hLE⟩
  refine ⟨⟨a, b, ?_, ?_⟩, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff] at hGE ⊢
    intro i hi
    change IsZero (((ModuleCat.extendScalars (algebraMap A B)).obj (L.X i) : ModuleCat B))
    simpa [ExtCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (ModuleCat.extendScalars (algebraMap A B)).map_isZero (hGE i hi)
  · rw [CochainComplex.isStrictlyLE_iff] at hLE ⊢
    intro i hi
    change IsZero (((ModuleCat.extendScalars (algebraMap A B)).obj (L.X i) : ModuleCat B))
    simpa [ExtCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (ModuleCat.extendScalars (algebraMap A B)).map_isZero (hLE i hi)
  · intro i
    let e :
        ((ModuleCat.extendScalars (algebraMap A B)).obj (L.X i)) ≅
          ModuleCat.of B (TensorProduct A B (L.X i : Type _)) := by
      simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          restrictScalarsSelfEquiv
          (LinearEquiv.refl A (L.X i : Type _))).toModuleIso
    letI : Module.Finite B (TensorProduct A B (L.X i : Type _)) :=
      Module.Finite.base_change (R := A) (A := B) (M := (L.X i : Type _))
    exact Module.Finite.equiv e.toLinearEquiv.symm
  · intro i
    let e :
        ((ModuleCat.extendScalars (algebraMap A B)).obj (L.X i)) ≅
          ModuleCat.of B (TensorProduct A B (L.X i : Type _)) := by
      simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          restrictScalarsSelfEquiv
          (LinearEquiv.refl A (L.X i : Type _))).toModuleIso
    letI : Module.Projective B (TensorProduct A B (L.X i : Type _)) :=
      Module.Projective.tensorProduct
    exact Module.Projective.of_equiv e.toLinearEquiv.symm

/-- Lemma 15.75.9: if `K^•` is a perfect complex of `A`-modules, then its derived base change
`K^• \otimes_A^{\mathbf L} B` is a perfect complex of `B`-modules. -/
@[stacks 066W]
theorem derivedTensorWithAlgebra_isPerfect
    (K : DModA) (hK : K.IsPerfect) :
    (K ⊗[A]^L[B]).IsPerfect := by
  rcases hK with ⟨L, e, hL⟩
  let Lbase : CochainComplex (ModuleCat B) ℤ := (ExtCpx (A := A) (B := B)).obj L
  have hLbase : CochainComplex.IsBoundedFiniteProjective Lbase := by
    -- Proof comment: termwise scalar extension preserves the bounded support and finite
    -- projective terms of the chosen strict perfect representative.
    simpa [Lbase] using
      (isBoundedFiniteProjective_mapExtendScalars (A := A) (B := B) L)
  refine ⟨Lbase, ?_, hLbase⟩
  -- Proof comment: the derived base change of `K` is computed by termwise scalar extension on the
  -- bounded-above flat representative `L`.
  exact
    (derivedTensorWithAlgebra (algebraMap A B)).mapIso e ≪≫
      (derivedTensorWithAlgebra_Q_obj_iso_of_isBoundedFiniteProjective
        (A := A) (B := B) L hL)

end

end CategoryTheory
