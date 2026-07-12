import Mathlib
import StacksProject_2024.Chap10.Lemma_10_75_5
import StacksProject_2024.Chap13.Lemma_13_16_1
import StacksProject_2024.Chap13.Definition_13_16_2
import StacksProject_2024.Chap15.Definition_15_59_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace ModuleCat

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat R)
private abbrev single0 : ModuleCat R ⥤ DMod :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "Q" => (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
private abbrev torOne (M : ModuleCat R) : ModuleCat R ⥤ ModuleCat R :=
  ((Tor (ModuleCat R) 1).obj M)

private noncomputable instance tensorRight_preservesFiniteColimits (M : ModuleCat R) :
    PreservesFiniteColimits (tensorRight M) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

/- Domain-style sampling:
- primary domain: the low-degree long exact Tor/tensor sequence for a short exact sequence of
  `R`-modules with fixed left tensor factor `M`;
- sampled owner declarations:
  `CategoryTheory.Tor`,
  `CategoryTheory.tor_flip_iso`,
  `CategoryTheory.Functor.leftDerivedZeroIsoSelf`,
  `CategoryTheory.Functor.leftDerivedNatIso`,
  `Functor.homologySequenceComposableArrows₅_exact`;
- best owner abstraction: the public owner in this domain is the bifunctor
  `CategoryTheory.Tor (ModuleCat R)`, specialized in degree `1` to the functor
  `((Tor (ModuleCat R) 1).obj M)`; the degree-`0` terms should be presented through the canonical
  owner `tensorLeft M` rather than a parallel right-derived-functor surrogate;
- primitive data vs derived API: the primitive data are only the fixed module `M` and the short
  exact sequence `hS`. The connecting morphism is derived API, computed from the canonical
  long exact sequence for `derivedTensorProduct (M[0])`, but the public theorem surface should use
  `((Tor (ModuleCat R) 1).obj M)` and `tensorLeft M` directly.

Source/core/bridge triage:
- `source-facing`: the textbook six-term sequence
  `Tor₁^R(M, X₁) ⟶ Tor₁^R(M, X₂) ⟶ Tor₁^R(M, X₃) ⟶ M ⊗[R] X₁ ⟶ M ⊗[R] X₂ ⟶ M ⊗[R] X₃ ⟶ 0`;
- `core/canonical`: `CategoryTheory.Tor (ModuleCat R)` and `tensorLeft M`;
- `bridge/view`: the internal comparison between low-degree homology of
  `derivedTensorProduct (M[0])` and the canonical `Tor₁`/tensor owners.
-/

private instance tensorRight_mapHomotopyCategoryToDerived_hasLeftDerivedFunctor (M : ModuleCat R) :
    Functor.HasLeftDerivedFunctor
      (CategoryTheory.mapHomotopyCategoryToDerived (tensorRight M) : KMod ⥤ DMod)
      Qis := by
  sorry

private noncomputable abbrev unboundedTensorRightDerived (M : ModuleCat R) : DMod ⥤ DMod :=
  Functor.totalLeftDerived
    (CategoryTheory.mapHomotopyCategoryToDerived (tensorRight M) : KMod ⥤ DMod)
    Qh
    Qis

private noncomputable instance unboundedTensorRightDerived_commShift (M : ModuleCat R) :
    (unboundedTensorRightDerived M).CommShift ℤ := by
  sorry

private instance unboundedTensorRightDerived_isTriangulated (M : ModuleCat R) :
    (unboundedTensorRightDerived M).IsTriangulated := by
  sorry

private abbrev derivedTensorIthRightDerivedFunctor (M : ModuleCat R) (i : ℤ) :
    ModuleCat R ⥤ ModuleCat R :=
  single0 ⋙ unboundedTensorRightDerived M ⋙ DerivedCategory.homologyFunctor (ModuleCat R) i

private noncomputable def projectiveResolutionSingle0Iso (X : ModuleCat R) :
    Functor.obj Q (CategoryTheory.projectiveResolution X).cochainComplex ≅ single0.obj X :=
  let f :
      Functor.obj Q (CategoryTheory.projectiveResolution X).cochainComplex ⟶
        Functor.obj Q ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj X) :=
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod).map
      (CategoryTheory.ProjectiveResolution.π' (CategoryTheory.projectiveResolution X))
  let _ : IsIso
      ((DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod).map
        (CategoryTheory.ProjectiveResolution.π' (CategoryTheory.projectiveResolution X))) := by
    infer_instance
  let _ : IsIso f := by simpa [f]
  let e :
      Functor.obj Q (CategoryTheory.projectiveResolution X).cochainComplex ≅
        Functor.obj Q ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj X) :=
    asIso f
  e ≪≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app X).symm

private noncomputable def unboundedTensorRightResolutionComparison (M X : ModuleCat R) :
    (unboundedTensorRightDerived M).obj (single0.obj X) ⟶
      Functor.obj Q (((tensorRight M).mapHomologicalComplex (up ℤ)).obj
        (CategoryTheory.ProjectiveResolution.cochainComplex
          (CategoryTheory.projectiveResolution X))) :=
  let P := CategoryTheory.ProjectiveResolution.cochainComplex (CategoryTheory.projectiveResolution X)
  let β :
      (CategoryTheory.mapHomotopyCategoryToDerived (tensorRight M) : KMod ⥤ DMod).obj
          ((HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj P) ⟶
        (HomotopyCategory.quotient (ModuleCat R) (up ℤ) ⋙ Qh).obj
          (((tensorRight M).mapHomologicalComplex (up ℤ)).obj P) := by
    simpa [CategoryTheory.mapHomotopyCategoryToDerived] using
      ((DerivedCategory.Qh : KMod ⥤ DMod).map
        ((Functor.mapHomotopyCategoryFactors (tensorRight M) (up ℤ)).inv.app P))
  let γ :
      (HomotopyCategory.quotient (ModuleCat R) (up ℤ) ⋙ Qh).obj
          (((tensorRight M).mapHomologicalComplex (up ℤ)).obj P) ⟶
        Functor.obj Q (((tensorRight M).mapHomologicalComplex (up ℤ)).obj P) :=
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app
      (((tensorRight M).mapHomologicalComplex (up ℤ)).obj P)
  (unboundedTensorRightDerived M).map
      (projectiveResolutionSingle0Iso X).inv ≫
    (Functor.totalLeftDerivedCounit
      (CategoryTheory.mapHomotopyCategoryToDerived (tensorRight M) : KMod ⥤ DMod)
      Qh
      Qis).app
        ((HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj P) ≫
    β ≫
    γ

private theorem tensorRight_projectiveResolutionCochainEq
    (M X : ModuleCat R) :
    ((tensorRight M).mapHomologicalComplex (up ℤ)).obj
        (CategoryTheory.ProjectiveResolution.cochainComplex
          (CategoryTheory.projectiveResolution X)) =
      ((((tensorRight M).mapHomologicalComplex (down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution X))).extend
        ComplexShape.embeddingDownNat) := by
  sorry

private noncomputable def tensorRight_projectiveResolutionCochainIso
    (M X : ModuleCat R) :
    ((tensorRight M).mapHomologicalComplex (up ℤ)).obj
        (CategoryTheory.ProjectiveResolution.cochainComplex
          (CategoryTheory.projectiveResolution X)) ≅
      ((((tensorRight M).mapHomologicalComplex (down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution X))).extend
        ComplexShape.embeddingDownNat) :=
  eqToIso (tensorRight_projectiveResolutionCochainEq M X)

private noncomputable def tensorRight_projectiveResolutionHomologyIso
    (M X : ModuleCat R) (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat R) (up ℤ) (-(n : ℤ))).obj
        (((tensorRight M).mapHomologicalComplex (up ℤ)).obj
          (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution X))) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (down ℕ) n).obj
        (((tensorRight M).mapHomologicalComplex (down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution X))) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (up ℤ) (-(n : ℤ))).mapIso
      (tensorRight_projectiveResolutionCochainIso M X) ≪≫
    ((((tensorRight M).mapHomologicalComplex (down ℕ)).obj
        (CategoryTheory.ProjectiveResolution.complex
          (CategoryTheory.projectiveResolution X))).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp))

private noncomputable def derivedTensorTensorRightComparison (M : ModuleCat R) :
    derivedTensorIthRightDerivedFunctor M 0 ⟶ tensorRight M where
  app X :=
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (unboundedTensorRightResolutionComparison M X) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).hom.app
        (((tensorRight M).mapHomologicalComplex (up ℤ)).obj
          (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution X))) ≫
      (tensorRight_projectiveResolutionHomologyIso M X 0).hom ≫
      ((CategoryTheory.projectiveResolution X).isoLeftDerivedObj (tensorRight M) 0).inv ≫
      (tensorRight M).leftDerivedZeroIsoSelf.hom.app X
  naturality {X Y} f := by
    sorry

private theorem derivedTensorTensorRightComparison_isIso
    (M : ModuleCat R) (X : ModuleCat R) :
    IsIso ((derivedTensorTensorRightComparison M).app X) := by
  sorry

private theorem derivedTensorTensorRightComparison_natIso
    (M : ModuleCat R) :
    IsIso (derivedTensorTensorRightComparison M) := by
  letI (X : ModuleCat R) := derivedTensorTensorRightComparison_isIso M X
  exact NatIso.isIso_of_isIso_app (derivedTensorTensorRightComparison M)

private instance derivedTensorTensorRightComparison_isIso' (M : ModuleCat R) :
    IsIso (derivedTensorTensorRightComparison M) :=
  derivedTensorTensorRightComparison_natIso M

private noncomputable def derivedTensorTorOneRightComparison (M : ModuleCat R) :
    derivedTensorIthRightDerivedFunctor M (-1) ⟶
      ((Functor.flip (Tor' (ModuleCat R) 1)).obj M) where
  app X :=
    (DerivedCategory.homologyFunctor (ModuleCat R) (-1)).map
        (unboundedTensorRightResolutionComparison M X) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-1)).hom.app
        (((tensorRight M).mapHomologicalComplex (up ℤ)).obj
          (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution X))) ≫
      (tensorRight_projectiveResolutionHomologyIso M X 1).hom ≫
      ((CategoryTheory.projectiveResolution X).isoLeftDerivedObj (tensorRight M) 1).inv
  naturality {X Y} f := by
    sorry

private theorem derivedTensorTorOneRightComparison_isIso
    (M : ModuleCat R) (X : ModuleCat R) :
    IsIso ((derivedTensorTorOneRightComparison M).app X) := by
  sorry

private theorem derivedTensorTorOneRightComparison_natIso
    (M : ModuleCat R) :
    IsIso (derivedTensorTorOneRightComparison M) := by
  letI (X : ModuleCat R) := derivedTensorTorOneRightComparison_isIso M X
  exact NatIso.isIso_of_isIso_app (derivedTensorTorOneRightComparison M)

private instance derivedTensorTorOneRightComparison_isIso' (M : ModuleCat R) :
    IsIso (derivedTensorTorOneRightComparison M) :=
  derivedTensorTorOneRightComparison_natIso M

private noncomputable def derivedTensorTorOneIso (M : ModuleCat R) :
    derivedTensorIthRightDerivedFunctor M (-1) ≅ torOne M := by
  exact
    asIso
      (derivedTensorTorOneRightComparison M ≫
        ((tor_flip_iso (ModuleCat R) 1).app M).inv)

private noncomputable def derivedTensorTensorIso (M : ModuleCat R) :
    derivedTensorIthRightDerivedFunctor M 0 ≅ tensorLeft M := by
  exact
    asIso
      (derivedTensorTensorRightComparison M ≫
        (BraidedCategory.tensorLeftIsoTensorRight M).inv)

private abbrev derivedTensorConnectingHom (M : ModuleCat R)
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ((derivedTensorIthRightDerivedFunctor M (-1)).obj S.X₃) ⟶
      ((derivedTensorIthRightDerivedFunctor M 0).obj S.X₁) :=
  let T := (unboundedTensorRightDerived M).mapTriangle.obj hS.singleTriangle
  (DerivedCategory.homologyFunctor (ModuleCat R) 0).homologySequenceδ T (-1) 0 (by simp)

/-- The canonical six-term `Tor₁`/tensor row attached to a short exact sequence `hS`.
Internally the connecting morphism is computed from the long exact sequence of
`derivedTensorProduct (M[0])`, but the public terms are the canonical owners
`((Tor (ModuleCat R) 1).obj M)` and `tensorLeft M`. -/
def torTensorSixTermSequence (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) : ComposableArrows (ModuleCat R) 6 :=
  (ComposableArrows.mk₅
      ((torOne M).map S.g)
      ((derivedTensorTorOneIso M).inv.app S.X₃ ≫
        derivedTensorConnectingHom M hS ≫
        (derivedTensorTensorIso M).hom.app S.X₁)
      ((tensorLeft M).map S.f)
      ((tensorLeft M).map S.g)
      (0 : (M ⊗ S.X₃) ⟶ ⊤_ (ModuleCat R))).precomp ((torOne M).map S.f)

/-- Lemma 10.75.2: for a short exact sequence `hS`, the canonical six-term sequence
`Tor₁^R(M, S.X₁) ⟶ Tor₁^R(M, S.X₂) ⟶ Tor₁^R(M, S.X₃) ⟶
M ⊗[R] S.X₁ ⟶ M ⊗[R] S.X₂ ⟶ M ⊗[R] S.X₃ ⟶ 0`
is exact. In Lean the tensor terms are the monoidal products `M ⊗ S.Xᵢ` in `ModuleCat R`. -/
theorem torTensorSixTermSequence_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) :
    (torTensorSixTermSequence M hS).Exact := by
  sorry

end ModuleCat

/- Lemma 10.75.2: for a short exact sequence `0 → N' → N → N'' → 0` of `R`-modules, the canonical
six-term row
`Tor₁^R(M, N') → Tor₁^R(M, N) → Tor₁^R(M, N'') → M ⊗[R] N' → M ⊗[R] N → M ⊗[R] N'' → 0`
is exact. In Lean, this source-facing sequence is formalized by
`ModuleCat.torTensorSixTermSequence_exact`. -/
recall ModuleCat.torTensorSixTermSequence_exact
