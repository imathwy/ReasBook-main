import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_65_6
import StacksProject_2024.Chap15.Lemma_15_75_3
import StacksProject_2024.Chap15.Definition_15_82_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u

attribute [local instance] HasDerivedCategory.standard

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/- Domain-style sampling:
* primary domain: commutative algebra of pseudo-coherent and perfect ring maps;
* sampled owner declarations:
  `RingHom.FiniteType`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `ModuleHasFiniteTorDimension`,
  `RingHom.IsRegularRingMap`;
* best owner abstraction: this file is the `source-facing` owner for predicates on an actual ring
  hom `f : A →+* B`, matching the chapter owner style of `RingHom.IsRegularRingMap`; the
  module-level owners above provide the canonical primitive data;
* primitive vs. derived:
  primitive data are finite type, relative pseudo-coherence of the target ring over the base, and
  finite tor dimension of the target as a base module;
  derived API is any later polynomial-presentation or perfect-module characterization.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsPseudoCoherentRingMap` and `RingHom.IsPerfectRingMap`;
* `core/canonical`: `RingHom.FiniteType`, `ModuleCat.IsPseudoCoherentRelativeTo`, and
  `ModuleHasFiniteTorDimension`;
* `bridge/view`: for `f = algebraMap A B`, the target ring regarded as the canonical module
  objects `ModuleCat.of B B` and `ModuleCat.of A B`.
-/

/-- Definition 15.83.1 (1): a ring map `f : A →+* B` is pseudo-coherent if it is of finite type
and `B`, viewed as a `B`-module, is pseudo-coherent relative to `A`. -/
@[stacks 067H, mk_iff isPseudoCoherentRingMap_iff_finiteType_and_isPseudoCoherentRelativeTo]
class IsPseudoCoherentRingMap : Prop where
  /-- A pseudo-coherent ring map is of finite type. -/
  finiteType : f.FiniteType
  /-- The target ring, viewed as a module over itself, is pseudo-coherent relative to the base. -/
  isPseudoCoherentRelativeTo :
    let _ := f.toAlgebra
    let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp finiteType
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A

/-- Definition 15.83.1 (2): a ring map `f : A →+* B` is perfect if it is pseudo-coherent and `B`,
viewed as an `A`-module, has finite tor dimension. -/
@[stacks 067H, mk_iff isPerfectRingMap_iff_isPseudoCoherentRingMap_and_hasFiniteTorDimension]
class IsPerfectRingMap : Prop extends IsPseudoCoherentRingMap f where
  /-- The target ring has finite tor dimension as a module over the base ring. -/
  hasFiniteTorDimension :
    let _ := f.toAlgebra
    ModuleHasFiniteTorDimension (ModuleCat.of A B)

attribute [instance] IsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
attribute [instance] IsPerfectRingMap.hasFiniteTorDimension

section

variable (A : Type u) [CommRing A]

/-- Helper for Definition 15.83.1: the empty polynomial algebra over `A` is canonically `A`
itself. -/
noncomputable def emptyPolynomialPresentation : MvPolynomial (Fin 0) A ≃ₐ[A] A :=
  (MvPolynomial.renameEquiv A (_root_.finZeroEquiv' : Fin 0 ≃ PEmpty.{u + 1})).trans
    (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1})

/-- Helper for Definition 15.83.1: restricting the regular module along a ring equivalence keeps
it perfect. -/
lemma restrictScalars_regularModule_isPerfect_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S)).IsPerfect := by
  -- The restricted regular module is linearly equivalent to `R`, so it is finite projective.
  rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
  refine ⟨0, ?_⟩
  rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
  let eₗ :
      ModuleCat.of R R ≃ₗ[R]
        ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S)) :=
    { __ := e.toAddEquiv
      map_smul' := fun r s ↦ e.map_mul r s }
  constructor
  · exact Module.Projective.of_equiv eₗ
  · exact Module.Finite.equiv eₗ

/-- Helper for Definition 15.83.1: the regular module of a commutative ring is perfect. -/
lemma regularModule_isPerfect : (ModuleCat.of A A).IsPerfect := by
  -- Specialize the restriction-of-scalars argument to the identity equivalence.
  simpa using
    restrictScalars_regularModule_isPerfect_of_ringEquiv (R := A) (S := A) (RingEquiv.refl A)

/-- Helper for Definition 15.83.1: the restricted degree-zero complex for the empty polynomial
presentation is pseudo-coherent. -/
lemma empty_presentation_regularModule_isPseudoCoherent :
    (CochainComplex.polynomialPresentationRestriction
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj (ModuleCat.of A A))
      ((emptyPolynomialPresentation A).toAlgHom)).IsPseudoCoherent := by
  -- Route correction: compare the restricted single complex with the degree-zero derived object
  -- of the restricted regular module, then transport pseudo-coherence across that isomorphism.
  let F := ModuleCat.restrictScalars (emptyPolynomialPresentation A).toAlgHom.toRingHom
  let M : ModuleCat A := ModuleCat.of A A
  let P : ObjectProperty (DerivedCategory (ModuleCat (MvPolynomial (Fin 0) A))) :=
    fun K ↦ DerivedCategory.IsPseudoCoherent K
  have hPerfect : (F.obj M).IsPerfect := by
    simpa [F, M] using
      restrictScalars_regularModule_isPerfect_of_ringEquiv
        ((emptyPolynomialPresentation A).toRingEquiv)
  have hPseudo : (F.obj M).IsPseudoCoherent :=
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (F.obj M)).1 hPerfect |>.1
  let e :
      (ModuleCat.single0Functor.obj (F.obj M)) ≅
        DerivedCategory.Q.obj
          (CochainComplex.polynomialPresentationRestriction
            ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)
            ((emptyPolynomialPresentation A).toAlgHom)) :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (MvPolynomial (Fin 0) A)) (0 : ℤ)).app
      (F.obj M)) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor F (0 : ℤ)).app M).symm
  exact P.prop_of_iso e hPseudo

/-- The identity map of a commutative ring is pseudo-coherent. -/
instance : (RingHom.id A).IsPseudoCoherentRingMap where
  finiteType := RingHom.FiniteType.id A
  isPseudoCoherentRelativeTo := by
    let _ : Algebra A A := (RingHom.id A).toAlgebra
    let _ : Algebra.FiniteType A A := RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.id A)
    -- Use the empty polynomial presentation of `A` over itself and the pseudo-coherent witness
    -- for the restricted regular module.
    rw [ModuleCat.IsPseudoCoherentRelativeTo]
    rw [CochainComplex.isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation]
    refine ⟨0, (emptyPolynomialPresentation A).toAlgHom, ?_, ?_⟩
    · exact (emptyPolynomialPresentation A).surjective
    · simpa using empty_presentation_regularModule_isPseudoCoherent (A := A)

/-- The identity map of a commutative ring is perfect. -/
instance : (RingHom.id A).IsPerfectRingMap where
  toIsPseudoCoherentRingMap := inferInstance
  hasFiniteTorDimension := by
    -- The regular module is perfect, hence has finite tor dimension.
    exact
      (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (ModuleCat.of A A)).1
        (regularModule_isPerfect A) |>.2

end

end RingHom

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

instance finiteType_of_isPseudoCoherentRingMap : Algebra.FiniteType A B := by
  exact
    RingHom.finiteType_algebraMap.mp
      (inferInstance : (algebraMap A B).IsPseudoCoherentRingMap).finiteType

attribute [instance 100] finiteType_of_isPseudoCoherentRingMap

end

end Algebra
