import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap15.Lemma_15_60_3

noncomputable section

open Algebra
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra
open scoped NaiveCotangent

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S']
variable {ι σ : Type u}

local notation "CpxS" => CochainComplex (ModuleCat S) ℤ
local notation "CpxS'" => CochainComplex (ModuleCat S') ℤ
local notation "KModS" => HomotopyCategory (ModuleCat S) (up ℤ)
local notation "QhS" => (DerivedCategory.Qh : KModS ⥤ DerivedCategory (ModuleCat S))
local notation "QisS" => HomotopyCategory.quasiIso (ModuleCat S) (up ℤ)
private abbrev extCpx : CpxS ⥤ CpxS' :=
  (ModuleCat.extendScalars (algebraMap S S')).mapHomologicalComplex (up ℤ)
local notation "ExtCpx" => (extCpx : CpxS ⥤ CpxS')

private local instance extendScalars_additive :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap S S')).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap S S')).left_adjoint_additive

/- Domain-style sampling for Lemma 15.86.1:
- primary domain: derived base change for naive cotangent complexes in `D(S)`;
- sampled owner declarations of the same kind:
  `Algebra.naiveCotangent`,
  `Presentation.toExtension`,
  `Algebra.Extension.naiveCotangentChainComplex`,
  `derivedTensorWithAlgebra`,
  `Functor.totalLeftDerivedCounit`;
- best owner abstraction: the source-facing owner for the canonical self-presentation
  `NL_{S/R}` is `NL_{S⁄R}.extend embeddingDownNat`,
  and for a chosen presentation it is
  `(P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat`;
- primitive data: the chosen presentation itself, namely `Generators.self R S` in part `(1)` and
  a general `P : Presentation R S ι σ` in part `(2)`;
- derived API: the canonical counit comparison
  `NL_{S/R} ⊗[S]^{\mathbf L} S' ⟶ NL_{S/R} ⊗[S] S'`
  and its truncation in degrees `≥ -1`.

Source/core/bridge triage:
- `source-facing`: the self-presentation and chosen-presentation comparison morphisms and their
  truncation-isomorphism statements below;
- `core/canonical`: the cochain owners
  `E.naiveCotangentChainComplex.extend embeddingDownNat`,
  the derived scalar-extension functor `derivedTensorWithAlgebra`,
  and the counit `Functor.totalLeftDerivedCounit`;
- `bridge/view`: the passage from a concrete cochain complex to its derived object through `Q`,
  together with the standard `Q`/`Qh` comparison isomorphisms.

Accordingly, this file should reuse the chapter owner coming from `Generators.self` or
`Presentation.toExtension`, and should state the canonical base-change morphism explicitly rather
than only asserting existence of some isomorphism between source and target objects. -/

private theorem naiveCotangentChainComplex_X_succ_succ_isZero
    (E : Algebra.Extension R S) (n : ℕ) :
    IsZero (E.naiveCotangentChainComplex.X (n + 2)) := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat S} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat S) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of S PUnit, 0, by simp⟩
  let C := E.naiveCotangentChainComplex
  have hs : (succZero (C.d (n + 1) n)).1 = ModuleCat.of S PUnit := rfl
  have hX : C.X (n + 2) ≅ (succZero (C.d (n + 1) n)).1 := by
    simpa [C, Algebra.Extension.naiveCotangentChainComplex] using
      (ChainComplex.mk'XIso
        (ModuleCat.of S E.CotangentSpace)
        (ModuleCat.of S (ULift E.Cotangent))
        (ModuleCat.ofHom (E.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
        succZero n)
  exact
    IsZero.of_iso
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of S PUnit))
      (hX ≪≫ eqToIso hs)

private theorem naiveCotangentCochain_isStrictlyGE
    (E : Algebra.Extension R S) :
    CochainComplex.IsStrictlyGE (E.naiveCotangentChainComplex.extend embeddingDownNat) (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hnonneg : 0 ≤ -i - 2 := by omega
  have hexists : ∃ n : ℕ, i = -((n + 2 : ℕ) : ℤ) := by
    refine ⟨Int.toNat (-i - 2), ?_⟩
    have htoNat : ((Int.toNat (-i - 2) : ℕ) : ℤ) = -i - 2 := by
      exact Int.toNat_of_nonneg hnonneg
    omega
  rcases hexists with ⟨n, rfl⟩
  exact
    (naiveCotangentChainComplex_X_succ_succ_isZero E n).of_iso
      (E.naiveCotangentChainComplex.extendXIso
        embeddingDownNat
        (show embeddingDownNat.f (n + 2) = -((n + 2 : ℕ) : ℤ) by rfl))

private theorem selfNaiveCotangent_isStrictlyGE :
    CochainComplex.IsStrictlyGE
      (show CpxS from (Algebra.naiveCotangent R S).extend embeddingDownNat)
      (-1) := by
  simpa [Algebra.naiveCotangent] using
    naiveCotangentCochain_isStrictlyGE (Generators.self R S).toExtension

private theorem presentationNaiveCotangent_isStrictlyGE
    (P : Presentation R S ι σ) :
    CochainComplex.IsStrictlyGE
      ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)
      (-1) := by
  simpa using
    naiveCotangentCochain_isStrictlyGE P.toExtension

private theorem extendScalarsComplex_isStrictlyGE
    (P : CpxS) [CochainComplex.IsStrictlyGE P (-1)] :
    CochainComplex.IsStrictlyGE
      (Functor.obj ExtCpx P)
      (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  simpa using
    (ModuleCat.extendScalars (algebraMap S S')).map_isZero
      (P.isZero_of_isStrictlyGE (-1) i hi)

private noncomputable def derivedTensorWithAlgebraComplexComparison
    (P : CpxS) :
    (DerivedCategory.Q.obj P ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj (Functor.obj ExtCpx P) :=
  let F : KModS ⥤ DerivedCategory (ModuleCat S') :=
    mapHomotopyCategoryToDerived (ModuleCat.extendScalars (algebraMap S S'))
  letI : F.HasLeftDerivedFunctor QisS := by
    change
      (mapHomotopyCategoryToDerived
        (ModuleCat.extendScalars (algebraMap S S'))).HasLeftDerivedFunctor QisS
    simpa using extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap S S')
  (derivedTensorWithAlgebra (algebraMap S S')).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat S)).app P).inv ≫
    (F.totalLeftDerivedCounit QhS QisS).app
      ((HomotopyCategory.quotient (ModuleCat S) (up ℤ)).obj P) ≫
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat S') (up ℤ) ⥤
        DerivedCategory (ModuleCat S')).map
      ((Functor.mapHomotopyCategoryFactors
        (ModuleCat.extendScalars (algebraMap S S')) (up ℤ)).inv.app P) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat S')).app
      (Functor.obj ExtCpx P)).hom

private noncomputable def derivedTensorWithAlgebraTruncGEComparison
    (P : CpxS) [CochainComplex.IsStrictlyGE P (-1)] :
    (t.truncGE (-1)).obj
        ((derivedTensorWithAlgebra (algebraMap S S')).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj
        (Functor.obj ExtCpx P) :=
  letI :
      CochainComplex.IsStrictlyGE (Functor.obj ExtCpx P) (-1) :=
    extendScalarsComplex_isStrictlyGE P
  letI :
      DerivedCategory.IsGE (DerivedCategory.Q.obj (Functor.obj ExtCpx P)) (-1) := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  t.descTruncGE (derivedTensorWithAlgebraComplexComparison P) (-1)

-- Proof sketch: this is the canonical counit comparison for the left-derived scalar-extension
-- functor `- ⊗[S]^L[S']`, evaluated on the canonical self-presentation cochain model of
-- `NL_{S/R}` and transported along the standard `Q`/`Qh` comparison isomorphisms.
/-- The canonical comparison morphism
`NL_{S/R} \otimes_S^{\mathbf L} S' \to NL_{S/R} \otimes_S S'`
for the canonical cochain model `NL_{S⁄R}.extend embeddingDownNat`. -/
noncomputable def selfNaiveCotangentBaseChangeComparison :
    (naiveCotangentObject R S ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj
        (Functor.obj ExtCpx ((NL_{S⁄R}).extend embeddingDownNat : CpxS)) :=
  derivedTensorWithAlgebraComplexComparison
    ((NL_{S⁄R}).extend embeddingDownNat : CpxS)

-- Proof sketch: the ordinary base-change target is represented by a two-term cochain complex,
-- hence lies in `D^{≥ -1}(S')`; factor the canonical counit comparison through `τ_{\ge -1}` via
-- `t.descTruncGE`.
/-- The induced canonical morphism
`τ_{\ge -1}(NL_{S/R} \otimes_S^{\mathbf L} S') \to NL_{S/R} \otimes_S S'`
to the ordinary base-change target for the self-presentation model. -/
noncomputable def selfNaiveCotangentBaseChangeTruncGEComparison :
    (t.truncGE (-1)).obj (naiveCotangentObject R S ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj
        (Functor.obj ExtCpx ((NL_{S⁄R}).extend embeddingDownNat : CpxS)) :=
  letI :
      CochainComplex.IsStrictlyGE (((NL_{S⁄R}).extend embeddingDownNat : CpxS)) (-1) :=
    selfNaiveCotangent_isStrictlyGE
  derivedTensorWithAlgebraTruncGEComparison (((NL_{S⁄R}).extend embeddingDownNat : CpxS))

-- Proof sketch: the same counit construction evaluated on the chosen presentationwise naive
-- cotangent cochain complex.
/-- The canonical comparison morphism
`NL_{P/R} \otimes_S^{\mathbf L} S' \to NL_{P/R} \otimes_S S'`
for the presentationwise naive cotangent complex attached to `P`. -/
noncomputable def presentationNaiveCotangentBaseChangeComparison
    (P : Presentation R S ι σ) :
    (DerivedCategory.Q.obj
        ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat) ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj
        (Functor.obj ExtCpx ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)) :=
  derivedTensorWithAlgebraComplexComparison
    ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)

-- Proof sketch: as in the self-presentation case, the ordinary base-change target already lies in
-- `D^{≥ -1}(S')`, so the canonical counit comparison factors uniquely through `τ_{\ge -1}`.
/-- The induced canonical morphism
`τ_{\ge -1}(NL_{P/R} \otimes_S^{\mathbf L} S') \to NL_{P/R} \otimes_S S'`
to the ordinary base-change target for the presentationwise naive cotangent complex attached to
`P`. -/
noncomputable def presentationNaiveCotangentBaseChangeTruncGEComparison
    (P : Presentation R S ι σ) :
    (t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat) ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj
        (Functor.obj ExtCpx ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)) :=
  letI :
      CochainComplex.IsStrictlyGE
        ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)
        (-1) :=
    presentationNaiveCotangent_isStrictlyGE P
  derivedTensorWithAlgebraTruncGEComparison
    ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)

-- Proof sketch: apply Lemma `15.85.6` to the canonical self-presentation complex
-- `((Generators.self R S).toExtension.naiveCotangentChainComplex).extend embeddingDownNat`.
-- That complex is concentrated in degrees `-1` and `0`, and the comparison above is the
-- canonical counit map from derived scalar extension to ordinary scalar extension. Since the
-- ordinary base-change target is already in `D^{≥ -1}(S')`, the induced morphism out of
-- `τ_{\ge -1}` is therefore an isomorphism.
/-- Lemma 15.86.1 (1), canonical-map form: for the canonical self-presentation of `S` over `R`,
the induced canonical morphism
`τ_{\ge -1}(NL_{S/R} \otimes_S^{\mathbf L} S') \to NL_{S/R} \otimes_S S'`
is an isomorphism in `D(S')`. -/
theorem selfNaiveCotangentBaseChangeComparison_truncGE_isIso :
    IsIso
      (selfNaiveCotangentBaseChangeTruncGEComparison :
        (t.truncGE (-1)).obj (naiveCotangentObject R S ⊗[S]^L[S']) ⟶
          DerivedCategory.Q.obj
            (Functor.obj ExtCpx (((NL_{S⁄R}).extend embeddingDownNat : CpxS)))) := sorry

-- Proof sketch: package the preceding canonical-map statement as the corresponding
-- object-level `IsIsomorphic` claim.
/-- Lemma 15.86.1 (1), object form: for the canonical self-presentation of `S` over `R`, the
derived base change of the naive cotangent complex becomes, after truncation in degrees `≥ -1`,
canonically isomorphic in `D(S')` to the ordinary base change of the two-term naive cotangent
complex. -/
theorem truncGE_derivedTensor_self_naiveCotangent_isIsomorphic_baseChange :
    IsIsomorphic
      ((t.truncGE (-1)).obj
        (naiveCotangentObject R S ⊗[S]^L[S']))
      (DerivedCategory.Q.obj
        (Functor.obj ExtCpx (((NL_{S⁄R}).extend embeddingDownNat : CpxS)))) :=
  sorry

-- Proof sketch: apply Lemma `15.85.6` to the two-term complex associated to the cotangent map of
-- the chosen presentation cochain owner
-- `(P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat`. As
-- above, the complex is supported in degrees `-1` and `0`, so the truncation `τ_{\ge -1}` of
-- the canonical counit map factors through the ordinary scalar extension target, which already
-- lies in `D^{≥ -1}(S')`.
/-- Lemma 15.86.1 (2), canonical-map form: for any presentation `P` of `S` over `R`, the
induced canonical morphism
`τ_{\ge -1}(NL_{P/R} \otimes_S^{\mathbf L} S') \to NL_{P/R} \otimes_S S'`
is an isomorphism in `D(S')`. -/
theorem presentationNaiveCotangentBaseChangeComparison_truncGE_isIso
    (P : Presentation R S ι σ) :
    IsIso
      (presentationNaiveCotangentBaseChangeTruncGEComparison P :
        (t.truncGE (-1)).obj
            (DerivedCategory.Q.obj
              ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat) ⊗[S]^L[S']) ⟶
          DerivedCategory.Q.obj
            (Functor.obj ExtCpx
              ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat))) := sorry

-- Proof sketch: package the preceding canonical-map statement as the corresponding
-- object-level `IsIsomorphic` claim.
/-- Lemma 15.86.1 (2), object form: for any presentation `P` of `S` over `R`, the derived base
change of the presentationwise naive cotangent complex becomes, after truncation in degrees
`≥ -1`, canonically isomorphic in `D(S')` to its ordinary base change along `S → S'`. -/
theorem truncGE_derivedTensor_presentation_naiveCotangent_isIsomorphic_baseChange
    (P : Presentation R S ι σ) :
    IsIsomorphic
      ((t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat) ⊗[S]^L[S']))
      (DerivedCategory.Q.obj
        (Functor.obj ExtCpx
          ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat))) := sorry

end

end CategoryTheory
