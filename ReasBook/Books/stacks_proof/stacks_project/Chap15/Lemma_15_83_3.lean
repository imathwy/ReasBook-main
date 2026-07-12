import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open ComplexShape

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

/-- Restrict a cochain complex of `A`-modules along a polynomial presentation of `A` over `R`. -/
abbrev polynomialPresentationRestriction
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : CochainComplex (ModuleCat A) ℤ) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
  ((ModuleCat.restrictScalars α.toRingHom).mapHomologicalComplex (up ℤ)).obj K

/-- Definition 15.82.4 (1): a cochain complex of `A`-modules is `m`-pseudo-coherent relative to
`R` if every surjective polynomial presentation yields an `m`-pseudo-coherent restriction. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
    CategoryTheory.CochainComplex.IsMPseudoCoherent (K.polynomialPresentationRestriction α) m

/-- Definition 15.82.4 (2): a cochain complex of `A`-modules is pseudo-coherent relative to `R`
if it is `m`-pseudo-coherent relative to `R` for every integer `m`. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

end CochainComplex

namespace ModuleCat

/-- Definition 15.82.4 (4): an `A`-module is pseudo-coherent relative to `R` if its degree-zero
cochain complex is pseudo-coherent relative to `R`. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherentRelativeTo R

end ModuleCat

namespace RingHom

/-- Definition 15.83.1 (1): a ring map `f : A →+* B` is pseudo-coherent if it is of finite type
and `B`, viewed as a `B`-module, is pseudo-coherent relative to `A`. -/
class IsPseudoCoherentRingMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop where
  /-- A pseudo-coherent ring map is of finite type. -/
  finiteType : f.FiniteType
  /-- The target ring, viewed as a module over itself, is pseudo-coherent relative to the base. -/
  isPseudoCoherentRelativeTo :
    let _ := f.toAlgebra
    let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp finiteType
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A

attribute [instance] IsPseudoCoherentRingMap.isPseudoCoherentRelativeTo

end RingHom

namespace Algebra

section

variable {R : Type u} {A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

/- Domain-style sampling for Lemma 15.83.3:
- primary domain: pseudo-coherent ring maps and relative pseudo-coherent modules over finite type
  algebras above a Noetherian base;
- sampled owner declarations:
  `RingHom.IsPseudoCoherentRingMap`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `Module.isPseudoCoherentRelativeTo_iff_finite`;
- best owner abstraction: `RingHom.IsPseudoCoherentRingMap` on the structure map `algebraMap R A`;
- primitive vs. derived:
  primitive data are the finite type map `R → A` and the owner field
  `(ModuleCat.of A A).IsPseudoCoherentRelativeTo R`;
  the derived API is the Noetherian finite-type criterion
  `Module.isPseudoCoherentRelativeTo_iff_finite`, specialized to the regular module `A`;
- source/core/bridge triage:
  `source-facing`: the numbered lemma asserting the Noetherian finite-type criterion;
  `core/canonical`: `RingHom.IsPseudoCoherentRingMap` and
    `Module.IsPseudoCoherentRelativeTo`;
  `bridge/view`: the bundled/unbundled module identification for `A` viewed as an `A`-module.
-/
/-- Helper for Lemma 15.83.3: the regular `A`-module is pseudo-coherent relative to the
Noetherian base `R` in the structure-map algebra context required by
`RingHom.IsPseudoCoherentRingMap`. -/
  theorem regularModule_isPseudoCoherentRelativeTo
    (hfiniteType : (algebraMap R A).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance) :
    let _ : Algebra R A := (algebraMap R A).toAlgebra
    let _ : Algebra.FiniteType R A :=
      RingHom.finiteType_algebraMap.mp hfiniteType
    (ModuleCat.of A A).IsPseudoCoherentRelativeTo R := by
  let _ : Algebra R A := (algebraMap R A).toAlgebra
  let _ : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hfiniteType
  -- Check relative pseudo-coherence presentationwise and use that every quotient of a Noetherian
  -- polynomial ring is finite as a module over the presentation ring.
  rw [ModuleCat.IsPseudoCoherentRelativeTo, CochainComplex.IsPseudoCoherentRelativeTo]
  intro m n α hα
  let P : Type u := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Module.Finite P A := by
    simpa [P, AlgHom.Finite, RingHom.Finite] using AlgHom.Finite.of_surjective α hα
  let F : ModuleCat A ⥤ ModuleCat P := ModuleCat.restrictScalars α.toRingHom
  let M : ModuleCat P := F.obj (ModuleCat.of A A)
  have hPseudoModule : (ModuleCat.of P A).IsPseudoCoherent := by
    exact (Module.isPseudoCoherent_iff_finite : (ModuleCat.of P A).IsPseudoCoherent ↔
      Module.Finite P A).2 inferInstance
  have hPseudoRestricted : M.IsPseudoCoherent := by
    simpa [F, M] using hPseudoModule
  have hMPseudoRestricted : M.IsMPseudoCoherent m := by
    rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent] at hPseudoRestricted
    exact hPseudoRestricted m
  let e :
      (ModuleCat.single0Functor.obj M) ≅
        DerivedCategory.Q.obj
          (((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
            (ModuleCat.of A A)).polynomialPresentationRestriction α) :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat P) (0 : ℤ)).app M) ≪≫
      DerivedCategory.Q.mapIso
        (((Functor.mapCochainComplexSingleFunctor F (0 : ℤ)).app
          (ModuleCat.of A A)).symm)
  let Qprop : CategoryTheory.ObjectProperty (DerivedCategory (ModuleCat P)) :=
    fun K ↦ DerivedCategory.IsMPseudoCoherent K m
  exact Qprop.prop_of_iso e hMPseudoRestricted

/-- Lemma 15.83.3: a finite type ring map out of a Noetherian ring is pseudo-coherent. -/
@[stacks 067I]
instance isPseudoCoherentRingMap_of_finiteType_of_isNoetherianRing :
    (algebraMap R A).IsPseudoCoherentRingMap where
  -- The structure map is finite type by the ambient finite-type algebra hypothesis.
  finiteType := RingHom.finiteType_algebraMap.mpr inferInstance
  -- The second field is exactly the regular-module criterion packaged in the required context.
  isPseudoCoherentRelativeTo := regularModule_isPseudoCoherentRelativeTo (R := R) (A := A)

end

end Algebra
