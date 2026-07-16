import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16

-- Auxiliary owner declarations split from `Lemma_15_60_1`.

noncomputable section

open CategoryTheory
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A]

/- Domain-style sampling for the derived scalar-extension owner:
- primary domain: derived extension of scalars for module derived categories over a commutative
  ring map;
- sampled owner declarations:
  `ModuleCat.extendScalars`,
  `Functor.totalLeftDerived`,
  `Functor.totalLeftDerivedCounit`,
  `Functor.mapHomotopyCategoryCompIso`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension functor
  `derivedTensorWithAlgebra σ : D(R) ⥤ D(A)` attached to an explicit ring map `σ : R →+* A`;
- primitive vs. derived:
  primitive data are the ring map `σ` and the exact module-category functor
  `ModuleCat.extendScalars σ`;
  the derived scalar-extension functor and its comparison isomorphisms are derived API over that
  owner;
- source/core/bridge triage:
  `core/canonical`: `derivedTensorWithAlgebra σ`;
  `bridge/view`: the textbook object notation `K ⊗[R]^L[A]` and the iterated-vs-direct comparison
  isomorphism. -/

local notation "KModR" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "QisR" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
local notation "QhR" => (DerivedCategory.Qh : KModR ⥤ DModR)

/-- Helper for 15.60.1.1: the additive functor on homotopy categories induced by a functor
to the derived category. -/
private abbrev mapHomotopyCategoryToDerived
    {C : Type u} {E : Type u} [Category C] [Category E] [Preadditive C] [Abelian E]
    [HasDerivedCategory E] (F : C ⥤ E) [F.Additive] :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory E :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-category scalar-extension functor to the derived category. This internal bridge
packages the additive instance needed by `mapHomotopyCategoryToDerived`. -/
private noncomputable abbrev extendScalarsHomotopyToDerived
    {S T : Type u} [CommRing S] [CommRing T] (σ : S →+* T) :
    HomotopyCategory (ModuleCat S) (up ℤ) ⥤ DerivedCategory (ModuleCat T) :=
  let F : ModuleCat S ⥤ ModuleCat T := ModuleCat.extendScalars σ
  letI : F.Additive := (ModuleCat.extendRestrictScalarsAdj σ).left_adjoint_additive
  mapHomotopyCategoryToDerived F

-- Proof sketch: use K-flat resolutions of complexes of `R`-modules and the fact that extension
-- of scalars along `R → A` preserves quasi-isomorphisms on K-flat replacements, then apply the
-- abstract existence criterion for total left derived functors.
/-- The canonical homotopy-to-derived scalar-extension bridge
`extendScalarsHomotopyToDerived σ : K(R) ⟶ D(A)` admits a total left derived functor
`D(R) ⟶ D(A)`. -/
theorem extendScalarsToDerived_hasLeftDerivedFunctor (σ : R →+* A) :
    (extendScalarsHomotopyToDerived σ : KModR ⥤ DModA).HasLeftDerivedFunctor QisR := by
  sorry

/-- The unbounded derived scalar-extension functor `- \otimes_R^{\mathbf L} A : D(R) ⟶ D(A)`. -/
noncomputable def derivedTensorWithAlgebra
    (σ : R →+* A) :
    DModR ⥤ DModA :=
  let F : KModR ⥤ DModA :=
    extendScalarsHomotopyToDerived σ
  letI : F.HasLeftDerivedFunctor QisR :=
    extendScalarsToDerived_hasLeftDerivedFunctor σ
  F.totalLeftDerived QhR QisR

/-- The derived scalar-extension functor commutes with the triangulated shift. -/
noncomputable instance derivedTensorWithAlgebra_commShift (σ : R →+* A) :
    (derivedTensorWithAlgebra σ).CommShift ℤ := sorry

-- Proof sketch: extension of scalars on homotopy categories is triangulated, and exactness
-- passes to its total left derived functor on the derived category.
/-- The derived scalar-extension functor is exact in the triangulated sense. -/
theorem derivedTensorWithAlgebra_isTriangulated (σ : R →+* A) :
    (derivedTensorWithAlgebra σ).IsTriangulated := sorry

/-- The canonical comparison morphism from iterated derived scalar extension
`- \otimes_R^{\mathbf L} A \otimes_A^{\mathbf L} B` to direct derived scalar extension
`- \otimes_R^{\mathbf L} B`, attached to ring maps `σ : R → A`, `τ : A → B`,
`ρ : R → B` with `τ.comp σ = ρ`. -/
private noncomputable def derivedTensorWithAlgebraCompComparison
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B) (hcomp : τ.comp σ = ρ) :
    derivedTensorWithAlgebra σ ⋙ derivedTensorWithAlgebra τ ⟶
      derivedTensorWithAlgebra ρ :=
  let kModR := HomotopyCategory (ModuleCat R) (up ℤ)
  let kModA := HomotopyCategory (ModuleCat A) (up ℤ)
  let dModR := DerivedCategory (ModuleCat R)
  let dModA := DerivedCategory (ModuleCat A)
  let dModB := DerivedCategory (ModuleCat B)
  let qhR : kModR ⥤ dModR := DerivedCategory.Qh
  let qhA : kModA ⥤ dModA := DerivedCategory.Qh
  let qisR := HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
  let qisA := HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
  letI : (ModuleCat.extendScalars σ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} σ).left_adjoint_additive
  letI : (ModuleCat.extendScalars τ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} τ).left_adjoint_additive
  letI : (ModuleCat.extendScalars ρ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ρ).left_adjoint_additive
  let F₁ : kModR ⥤ kModA := (ModuleCat.extendScalars σ).mapHomotopyCategory (up ℤ)
  let G₁ : kModA ⥤ dModB := extendScalarsHomotopyToDerived τ
  let H₁ : kModR ⥤ dModB := F₁ ⋙ G₁
  let G : kModR ⥤ dModB := extendScalarsHomotopyToDerived ρ
  let compIsoOnHomotopy :
      ((ModuleCat.extendScalars σ).mapHomotopyCategory (up ℤ)) ⋙
          (ModuleCat.extendScalars τ).mapHomotopyCategory (up ℤ) ≅
        (ModuleCat.extendScalars ρ).mapHomotopyCategory (up ℤ) :=
    (Functor.mapHomotopyCategoryCompIso
        (ModuleCat.extendScalars σ)
        (ModuleCat.extendScalars τ)).symm ≪≫
      Functor.mapHomotopyCategoryIso
        ((ModuleCat.extendScalarsComp σ τ).symm ≪≫
          eqToIso (congrArg (fun f ↦ ModuleCat.extendScalars f) hcomp))
  let compIsoToDerived :
      F₁ ⋙ extendScalarsHomotopyToDerived τ ≅
        extendScalarsHomotopyToDerived ρ :=
    (Functor.associator
        ((ModuleCat.extendScalars σ).mapHomotopyCategory (up ℤ))
        ((ModuleCat.extendScalars τ).mapHomotopyCategory (up ℤ))
        DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerRight compIsoOnHomotopy DerivedCategory.Qh
  letI :
      (extendScalarsHomotopyToDerived σ : kModR ⥤ dModA).HasLeftDerivedFunctor qisR :=
    extendScalarsToDerived_hasLeftDerivedFunctor σ
  letI : (F₁ ⋙ qhA).HasLeftDerivedFunctor qisR := by
    change (extendScalarsHomotopyToDerived σ : kModR ⥤ dModA).HasLeftDerivedFunctor qisR
    simpa [F₁, qhA, extendScalarsHomotopyToDerived, mapHomotopyCategoryToDerived] using
      (extendScalarsToDerived_hasLeftDerivedFunctor σ :
        (extendScalarsHomotopyToDerived σ : kModR ⥤ dModA).HasLeftDerivedFunctor qisR)
  letI : G₁.HasLeftDerivedFunctor qisA :=
    extendScalarsToDerived_hasLeftDerivedFunctor τ
  letI : G.HasLeftDerivedFunctor qisR :=
    extendScalarsToDerived_hasLeftDerivedFunctor ρ
  have hHasLeftDerived :
      H₁.HasLeftDerivedFunctor qisR ↔ G.HasLeftDerivedFunctor qisR :=
    Functor.hasLeftDerivedFunctor_iff_of_iso compIsoToDerived qisR
  letI : H₁.HasLeftDerivedFunctor qisR :=
    hHasLeftDerived.2 inferInstance
  letI :
      (derivedTensorWithAlgebra ρ).IsLeftDerivedFunctor
        (Functor.totalLeftDerivedCounit G qhR qisR)
        qisR := by
    simpa [G, derivedTensorWithAlgebra, extendScalarsHomotopyToDerived,
      mapHomotopyCategoryToDerived] using
      (inferInstance :
        (Functor.totalLeftDerived G qhR qisR).IsLeftDerivedFunctor
          (Functor.totalLeftDerivedCounit G qhR qisR)
          qisR)
  let leftCompCounit :
      qhR ⋙ (derivedTensorWithAlgebra σ ⋙ derivedTensorWithAlgebra τ) ⟶ H₁ := by
    change
      qhR ⋙ (((F₁ ⋙ qhA).totalLeftDerived qhR qisR) ⋙ G₁.totalLeftDerived qhA qisA) ⟶ H₁
    exact
      (Functor.associator qhR ((F₁ ⋙ qhA).totalLeftDerived qhR qisR)
          (G₁.totalLeftDerived qhA qisA)).hom ≫
        Functor.whiskerRight
          (Functor.totalLeftDerivedCounit (F₁ ⋙ qhA) qhR qisR)
          (G₁.totalLeftDerived qhA qisA) ≫
        (Functor.associator F₁ qhA (G₁.totalLeftDerived qhA qisA)).hom ≫
        Functor.whiskerLeft F₁
          (Functor.totalLeftDerivedCounit G₁ qhA qisA)
  let leftComp :
      derivedTensorWithAlgebra σ ⋙ derivedTensorWithAlgebra τ ⟶
        Functor.totalLeftDerived H₁ qhR qisR :=
    (Functor.totalLeftDerived H₁ qhR qisR).leftDerivedLift
      (Functor.totalLeftDerivedCounit H₁ qhR qisR)
      qisR
      (derivedTensorWithAlgebra σ ⋙ derivedTensorWithAlgebra τ)
      leftCompCounit
  leftComp ≫
    (Functor.leftDerivedNatIso
      (Functor.totalLeftDerived H₁ qhR qisR)
      (derivedTensorWithAlgebra ρ)
      (Functor.totalLeftDerivedCounit H₁ qhR qisR)
      (Functor.totalLeftDerivedCounit G qhR qisR)
      qisR
      compIsoToDerived).hom

/-- The canonical iterated-vs-direct derived scalar-extension comparison is an isomorphism. -/
private theorem derivedTensorWithAlgebraCompComparison_isIso
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B) (hcomp : τ.comp σ = ρ) :
    IsIso (derivedTensorWithAlgebraCompComparison σ τ ρ hcomp) := by
  sorry

/-- The canonical comparison between iterated derived scalar extension
`- \otimes_R^{\mathbf L} A \otimes_A^{\mathbf L} B` and direct derived scalar extension
`- \otimes_R^{\mathbf L} B`. -/
noncomputable def derivedTensorWithAlgebraCompIso
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B) (hcomp : τ.comp σ = ρ) :
    derivedTensorWithAlgebra σ ⋙ derivedTensorWithAlgebra τ ≅
      derivedTensorWithAlgebra ρ :=
  letI : IsIso (derivedTensorWithAlgebraCompComparison σ τ ρ hcomp) :=
    derivedTensorWithAlgebraCompComparison_isIso σ τ ρ hcomp
  asIso (derivedTensorWithAlgebraCompComparison σ τ ρ hcomp)

end

end CategoryTheory

namespace DerivedTensorWithAlgebra

/- Textbook notation for the derived scalar-extension object `K ⊗_R^{\mathbf L} A` in `D(A)`. -/
set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗[" R:70 "]^L[" A:70 "]" =>
  (CategoryTheory.derivedTensorWithAlgebra (algebraMap R A)).obj K

end DerivedTensorWithAlgebra
