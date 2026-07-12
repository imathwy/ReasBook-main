import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA uB vA vB

/- Semantic search note: `lean_leansearch` is unavailable in this environment, so the owner/API
choice was checked against the local derived-functor recall files `21_3_0_1`, `21_3_0_2`, and the
Chapter 20 derived-pushforward owner `moduleDerivedPushforward`. -/

namespace DifferentialGradedModule

section

section

variable {C : Type*} {D : Type*}
variable [Category C] [Abelian C]
variable [Category D] [Abelian D]

local notation "DC" => DerivedCategory C
local notation "DD" => DerivedCategory D
local notation "QC" => (DerivedCategory.Q : CochainComplex C ℤ ⥤ DC)
local notation "QD" => (DerivedCategory.Q : CochainComplex D ℤ ⥤ DD)
local notation "QisC" => HomologicalComplex.quasiIso C (up ℤ)

/-- Private canonical core: the cochain-level functor induced by `F`, landing in the target
derived category. The public Chapter 24 owners remain thin source-facing specializations. -/
private abbrev cochainFunctorToDerived (F : C ⥤ D) [F.Additive] :
    CochainComplex C ℤ ⥤ DD :=
  F.mapHomologicalComplex (up ℤ) ⋙ QD

/-- Private bridge: a right-derived-functor instance for the raw cochain-level functor also serves
for its private core abbreviation. -/
private instance cochainFunctorToDerived_hasRightDerivedFunctor
    (F : C ⥤ D) [F.Additive]
    [Functor.HasRightDerivedFunctor (F.mapHomologicalComplex (up ℤ) ⋙ QD) QisC] :
    Functor.HasRightDerivedFunctor (cochainFunctorToDerived F) QisC := by
  simpa [cochainFunctorToDerived] using
    (inferInstance :
      Functor.HasRightDerivedFunctor (F.mapHomologicalComplex (up ℤ) ⋙ QD) QisC)

/-- Private canonical core: the total right derived functor of `cochainFunctorToDerived F`. -/
private abbrev derivedCochainFunctor
    (F : C ⥤ D) [F.Additive]
    [Functor.HasRightDerivedFunctor (cochainFunctorToDerived F) QisC] :
    DC ⥤ DD :=
  (cochainFunctorToDerived F).totalRightDerived QC QisC

/-- Private canonical comparison morphism for `derivedCochainFunctor F`. -/
private abbrev derivedCochainFunctorUnit
    (F : C ⥤ D) [F.Additive]
    [Functor.HasRightDerivedFunctor (cochainFunctorToDerived F) QisC] :
    cochainFunctorToDerived F ⟶ QC ⋙ derivedCochainFunctor F :=
  (cochainFunctorToDerived F).totalRightDerivedUnit QC QisC

/-- Private core companion: `derivedCochainFunctor F` is the canonical total right derived
functor of `cochainFunctorToDerived F`. -/
private theorem derivedCochainFunctor_isRightDerivedFunctor
    (F : C ⥤ D) [F.Additive]
    [Functor.HasRightDerivedFunctor (cochainFunctorToDerived F) QisC] :
    (derivedCochainFunctor F).IsRightDerivedFunctor
      (derivedCochainFunctorUnit F)
      QisC := by
  simpa [derivedCochainFunctor, derivedCochainFunctorUnit] using
    (inferInstance :
      Functor.IsRightDerivedFunctor
        ((cochainFunctorToDerived F).totalRightDerived QC QisC)
        ((cochainFunctorToDerived F).totalRightDerivedUnit QC QisC)
        QisC)

end

variable {DGModA : Type uA} {DGModB : Type uB}
variable [Category.{vA} DGModA] [Abelian DGModA]
variable [Category.{vB} DGModB] [Abelian DGModB]

local notation "DA" => DerivedCategory DGModA
local notation "DB" => DerivedCategory DGModB
local notation "QA" => (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DA)
local notation "QB" => (DerivedCategory.Q : CochainComplex DGModB ℤ ⥤ DB)
local notation "QisA" => HomologicalComplex.quasiIso DGModA (up ℤ)
local notation "QisB" => HomologicalComplex.quasiIso DGModB (up ℤ)

/-- Definition 24.29.2 (1): for the chosen internal-Hom functor
`\mathcal{H}\!\mathit{om}^{dg}_{\mathcal B}(\mathcal N, -)` from differential graded
`\mathcal B`-modules to differential graded `\mathcal A`-modules, the derived internal hom is its
total right derived functor. -/
abbrev derivedInternalHom
    (internalHom : DGModB ⥤ DGModA) [internalHom.Additive]
    [Functor.HasRightDerivedFunctor (internalHom.mapHomologicalComplex (up ℤ) ⋙ QA) QisB] :
    DB ⥤ DA :=
  derivedCochainFunctor internalHom

/-- The canonical comparison morphism from the cochain-level internal-Hom functor to its chosen
derived internal-Hom. -/
abbrev derivedInternalHomUnit
    (internalHom : DGModB ⥤ DGModA) [internalHom.Additive]
    [Functor.HasRightDerivedFunctor (internalHom.mapHomologicalComplex (up ℤ) ⋙ QA) QisB] :
    internalHom.mapHomologicalComplex (up ℤ) ⋙ QA ⟶ QB ⋙ derivedInternalHom internalHom :=
  derivedCochainFunctorUnit internalHom

/-- The chosen owner `derivedInternalHom internalHom` is the canonical total right derived functor
of the cochain-level internal-Hom functor. -/
theorem derivedInternalHom_isRightDerivedFunctor
    (internalHom : DGModB ⥤ DGModA) [internalHom.Additive]
    [Functor.HasRightDerivedFunctor (internalHom.mapHomologicalComplex (up ℤ) ⋙ QA) QisB] :
    (derivedInternalHom internalHom).IsRightDerivedFunctor
      (derivedInternalHomUnit internalHom)
      QisB := by
  exact derivedCochainFunctor_isRightDerivedFunctor internalHom

/-- Definition 24.29.2 (2): for the chosen pushforward functor on differential graded modules
attached to a morphism of ringed topoi together with a differential graded algebra map
`\varphi : \mathcal B \to f_*\mathcal A`, the derived pushforward is its total right derived
functor. -/
abbrev derivedPushforward
    (pushforward : DGModA ⥤ DGModB) [pushforward.Additive]
    [Functor.HasRightDerivedFunctor (pushforward.mapHomologicalComplex (up ℤ) ⋙ QB) QisA] :
    DA ⥤ DB :=
  derivedCochainFunctor pushforward

/-- The canonical comparison morphism from the cochain-level pushforward functor to its chosen
derived pushforward. -/
abbrev derivedPushforwardUnit
    (pushforward : DGModA ⥤ DGModB) [pushforward.Additive]
    [Functor.HasRightDerivedFunctor (pushforward.mapHomologicalComplex (up ℤ) ⋙ QB) QisA] :
    pushforward.mapHomologicalComplex (up ℤ) ⋙ QB ⟶ QA ⋙ derivedPushforward pushforward :=
  derivedCochainFunctorUnit pushforward

/-- The chosen owner `derivedPushforward pushforward` is the canonical total right derived functor
of the cochain-level pushforward functor. -/
theorem derivedPushforward_isRightDerivedFunctor
    (pushforward : DGModA ⥤ DGModB) [pushforward.Additive]
    [Functor.HasRightDerivedFunctor (pushforward.mapHomologicalComplex (up ℤ) ⋙ QB) QisA] :
    (derivedPushforward pushforward).IsRightDerivedFunctor
      (derivedPushforwardUnit pushforward)
      QisA := by
  exact derivedCochainFunctor_isRightDerivedFunctor pushforward

end

end DifferentialGradedModule
