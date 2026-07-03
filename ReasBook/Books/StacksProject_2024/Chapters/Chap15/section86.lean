import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_86_1 (from Chap15) -/
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

/-! ### Lemma_15_86_2 (from Chap15) -/
open scoped TensorProduct
open Algebra

noncomputable section

universe u x y

/- Domain triage:
* primary domain: underived base change for presentationwise naive cotangent complexes and their
  degree `-1` and `0` homology in commutative algebra;
* sampled owner declarations:
  - `Presentation.baseChange`,
  - `Presentation.baseChangeFromBaseChange`,
  - `Extension.naiveCotangentChainComplex`,
  - `Extension.CotangentSpace.map_comp_cotangentComplex`,
  - `tensor_presentation_cotangent_h1_to_h1_cotangent`,
  - `KaehlerDifferential.tensorKaehlerEquivBase`;
* best owner abstraction: the source-facing owner is the comparison chain map between the
  canonical two-term complexes
  `P.toExtension.baseChange.naiveCotangentChainComplex` and
  `(P.baseChange R').toExtension.naiveCotangentChainComplex`; the owner-level public comparison on
  `H^{-1}` is the canonical composite
  `H1Cotangent.baseChangeComparison R R' S`,
  `S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R' S'`,
  the degree `0` owner is already the canonical equivalence
  `KaehlerDifferential.tensorKaehlerEquivBase R R' S`;
* primitive data: the ring maps `R → S`, `R → R'`, and the chosen presentation `P`;
* derived API: the source-facing surjectivity theorem for the explicit presentation-level
  `H^{-1}` comparison composite, the owner-level comparison
  `H1Cotangent.baseChangeComparison R R' S` and its surjectivity statement, and direct reuse of
  `KaehlerDifferential.tensorKaehlerEquivBase` for degree `0`.

Source/core/bridge triage:
* `source-facing`: the comparison `NL(P/R) ⊗[S] S' → NL(P.baseChange R'/R')` for a chosen
  presentation `P`;
* `core/canonical`: `Presentation.baseChange`, `Presentation.baseChangeFromBaseChange`,
  `Extension.naiveCotangentChainComplex`, `H1Cotangent.baseChangeComparison`, and
  `KaehlerDifferential.tensorKaehlerEquivBase`;
* `bridge/view`: the explicit presentation-level composite of
  `tensor_presentation_cotangent_h1_to_h1_cotangent`,
  `H1Cotangent.map`, and `equivH1Cotangent.symm` used in the surjectivity theorem below.
-/

section

variable {R S R' : Type u}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable {ι : Type x} {σ : Type y}

local notation "S'" => R' ⊗[R] S

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.H1Cotangent

variable (R R' S)

/- The canonical owner-level base-change map
`S' ⊗[S] H¹(L_{S/R}) → H¹(L_{S'/R'})`. -/
noncomputable abbrev baseChangeComparison :
    S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R' S' :=
  (map R R' S' S').comp (LinearMap.liftBaseChange S' (map R R S S'))

/- Lemma 15.86.2 (in particular): the canonical owner-level base-change map
`S' ⊗[S] H¹(L_{S/R}) → H¹(L_{S'/R'})` is surjective. -/
theorem baseChangeComparison_surjective
    :
    Function.Surjective (baseChangeComparison R R' S) := sorry

end Algebra.H1Cotangent

namespace Algebra.Presentation

/-- Lemma 15.86.2: for a chosen presentation `P` of `S` over `R`, the comparison
`NL(P/R) ⊗[S] S' → NL(P.baseChange R'/R')`
is surjective on `H^{-1}`. This is the source-facing presentation-level comparison whose target is
identified with `H1Cotangent R' S'` via the canonical presentation equivalence. -/
theorem naiveCotangentBaseChangeH1Comparison_surjective
    (P : Presentation R S ι σ) :
    Function.Surjective
      (((P.baseChange R').toGenerators.equivH1Cotangent.symm).toLinearMap ∘ₗ
        H1Cotangent.map R R' S' S' ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators) := sorry

end Algebra.Presentation

/- The degree `0` part of Lemma 15.86.2 is the canonical Kähler-differential base-change
equivalence, i.e. the degree-`0` comparison for the owner chain map
`Extension.naiveCotangentChainMap (P.baseChangeFromBaseChange R')`. -/
recall KaehlerDifferential.tensorKaehlerEquivBase

end

/-! ### Lemma_15_86_3 (from Chap15) -/
open Algebra
open CategoryTheory
open ComplexShape
open ULift
open scoped DerivedTensorWithAlgebra NaiveCotangent TensorProduct

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section

variable {A A' B : Type u}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

local notation "B'" => A' ⊗[A] B
local notation "CpxB" => CochainComplex (ModuleCat B) ℤ
local notation "CpxB'" => CochainComplex (ModuleCat B') ℤ
local notation "DModB'" => DerivedCategory (ModuleCat B')

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

private abbrev extCpx : CpxB ⥤ CpxB' :=
  (ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)

private local instance extendScalars_additive_local :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap B B')).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap B B')).left_adjoint_additive

/- Domain-style sampling for Lemma 15.86.3:
- primary domain: pushout/base-change comparison morphisms for naive cotangent complexes in
  `D(B')`;
- sampled owner declarations of the same kind:
  `NL_{B⁄A}`,
  `CategoryTheory.derivedTensorWithAlgebra`,
  `CategoryTheory.selfNaiveCotangentBaseChangeComparison` from `15.86.1`,
  `CategoryTheory.HasTorAmplitudeIn`,
  `Extension.CotangentSpace.map_comp_cotangentComplex`,
  `Generators.defaultHom`,
  `LinearMap.baseChange`;
- best owner abstraction: the source-facing owner is the canonical comparison morphism
  `NL_{B/A} ⊗[B] B' ⟶ NL_{B'/A'}`, together with its derived companion
  `NL_{B/A} ⊗[B]^L[B'] ⟶ NL_{B'/A'}`; the presentation-level tensorized conormal/cotangent-space
  maps are bridge data used only to build those owner morphisms;
- primitive data: only the pushout square `B' = A' ⊗[A] B` and the canonical self-presentations
  `Generators.self A B`, `Generators.self B B'`, `Generators.self A B'`, `Generators.self A' B'`;
- derived API: the underived comparison is a quasi-isomorphism when `A → B` is flat, and the
  derived comparison is an isomorphism under the intrinsic tor-amplitude hypothesis
  `HasTorAmplitudeIn NL_{B/A} (-1) 0`.

Source/core/bridge triage:
- `source-facing`: the two canonical comparison morphisms in `D(B')`;
- `core/canonical`: `NL_{B/A}`, `⊗[B]^L[B']`, and `HasTorAmplitudeIn`;
- `bridge/view`: the tensorized self-presentation complex of `NL_{B/A}` and the presentationwise
  chain maps built from `Extension.CotangentSpace.map_comp_cotangentComplex` and
  `Generators.defaultHom`.
 -/

local notation "PAB" => (Generators.self A B : Generators A B B)
local notation "Ppush" => (Generators.self B B' : Generators B B' B')
local notation "PtargetA" => (Generators.self A B' : Generators A B' B')
local notation "PtargetA'" => (Generators.self A' B' : Generators A' B' B')

private abbrev Pcomp : Generators A B' (B' ⊕ B) :=
  (Generators.self B B' : Generators B B' B').comp PAB

private noncomputable def tensorizedSelfNaiveCotangentChainComplex :
    ChainComplex (ModuleCat B') ℕ :=
  ChainComplex.mk'
    (ModuleCat.of B' (B' ⊗[B] (PAB).toExtension.CotangentSpace))
    (ModuleCat.of B' (B' ⊗[B] ULift ((PAB).toExtension.Cotangent)))
    (ModuleCat.ofHom
      (LinearMap.baseChange B'
        ((PAB).toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap)))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B' PUnit, 0, CategoryTheory.Limits.zero_comp⟩)

private theorem extendScalarsComplex_selfNaiveCotangent_eq_tensorized :
    extCpx.obj (((PAB).toExtension.naiveCotangentChainComplex).extend embeddingDownNat) =
      ((tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ)).extend
        embeddingDownNat := by
  sorry

private noncomputable def tensorizedCompCotangentSpaceMap :
    B' ⊗[B] (PAB).toExtension.CotangentSpace →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).CotangentSpace :=
  let f := ((Ppush).toComp PAB).toExtensionHom
  show B' ⊗[B] (PAB).toExtension.CotangentSpace →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).CotangentSpace from
    (Extension.CotangentSpace.map f).liftBaseChange B'

private noncomputable def tensorizedCompCotangentMap :
    B' ⊗[B] (PAB).toExtension.Cotangent →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent :=
  let f := ((Ppush).toComp PAB).toExtensionHom
  show B' ⊗[B] (PAB).toExtension.Cotangent →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent from
    LinearMap.liftBaseChange B' (Extension.Cotangent.map f)

private noncomputable def tensorizedCompLiftCotangentMap :
    B' ⊗[B] ULift ((PAB).toExtension.Cotangent) →ₗ[B']
      ULift ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent :=
  show B' ⊗[B] ULift ((PAB).toExtension.Cotangent) →ₗ[B']
      ULift ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent from
    ((ULift.moduleEquiv :
        ULift ((((Generators.self B B' : Generators B B' B').comp
          (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent ≃ₗ[B']
          ((((Generators.self B B' : Generators B B' B').comp
            (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent).symm.toLinearMap) ∘ₗ
      (tensorizedCompCotangentMap ∘ₗ
        LinearMap.baseChange B'
          ((ULift.moduleEquiv :
              ULift ((PAB).toExtension.Cotangent) ≃ₗ[B] (PAB).toExtension.Cotangent).toLinearMap))

private theorem tensorizedCompChainMap_comm :
    ModuleCat.ofHom tensorizedCompLiftCotangentMap ≫
      ((((Pcomp).toExtension : Algebra.Extension A B').naiveCotangentChainComplex).d 1 0) =
    tensorizedSelfNaiveCotangentChainComplex.d 1 0 ≫
      ModuleCat.ofHom tensorizedCompCotangentSpaceMap := by
  sorry

private theorem tensorizedSelfNaiveCotangentChainComplex_d_succ_succ (n : ℕ) :
    (tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ).d
      (n + 2) (n + 1) = 0 := by
  rw [tensorizedSelfNaiveCotangentChainComplex, ChainComplex.mk'_d]
  simp

private noncomputable def tensorizedCompChainMap :
    (tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ) ⟶
      (Pcomp).toExtension.naiveCotangentChainComplex :=
  ChainComplex.mkHom
    tensorizedSelfNaiveCotangentChainComplex
    (Pcomp).toExtension.naiveCotangentChainComplex
    (ModuleCat.ofHom tensorizedCompCotangentSpaceMap)
    (ModuleCat.ofHom tensorizedCompLiftCotangentMap)
    tensorizedCompChainMap_comm
    (fun i _ ↦ ⟨0, by
      rw [tensorizedSelfNaiveCotangentChainComplex_d_succ_succ]
      simp⟩)

private noncomputable def naiveCotangentUnderivedPushoutChainMap :
    (tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ) ⟶
      (PtargetA').toExtension.naiveCotangentChainComplex :=
  let f :
      (((Pcomp).toExtension : Algebra.Extension A B').Hom
        (((PtargetA').toExtension : Algebra.Extension A' B'))) :=
    (((PtargetA).defaultHom PtargetA').comp ((Pcomp).defaultHom PtargetA)).toExtensionHom
  tensorizedCompChainMap ≫ Extension.naiveCotangentChainMap f

end

section

variable (A A' B : Type u)
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

local notation "B'" => A' ⊗[A] B
local notation "CpxB" => CochainComplex (ModuleCat B) ℤ
local notation "PAB" => (Generators.self A B : Generators A B B)
local notation "DModB'" => DerivedCategory (ModuleCat B')

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

-- Proof sketch: the source is the ordinary tensorized two-term self-presentation model of
-- `NL_{B/A}` over `B'`, and the target is the canonical self-presentation model of `NL_{B'/A'}`.
-- The map is built from the presentation-level tensorized comparison to the composite
-- presentation of `B'` over `A`, followed by the canonical owner chain map induced by the
-- composite `defaultHom` comparison to the self-model over `A'`.
/-- The ordinary base-changed object `NL_{B/A} ⊗[B] B'` in `D(B')`, represented by extending
scalars on the canonical cochain model `NL_{B⁄A}.extend embeddingDownNat`. This is the
bridge/view source of the pushout comparison, not a second owner parallel to `NL_{B⁄A}`. -/
noncomputable abbrev naiveCotangentBaseChangeObject : DModB' :=
  DerivedCategory.Q.obj
    (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)).obj
      (((NL_{B⁄A}).extend embeddingDownNat : CpxB)))

/-- The canonical underived pushout comparison
`NL_{B/A} ⊗[B] B' ⟶ NL_{B'/A'}`
in `D(B')`, written on the source by the tensorized two-term self-presentation model of
`NL_{B/A}`. -/
noncomputable def naiveCotangentPushoutComparison :
    naiveCotangentBaseChangeObject A A' B ⟶
      naiveCotangentObject A' B' :=
  by
    change
      DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)).obj
            (((PAB).toExtension.naiveCotangentChainComplex).extend embeddingDownNat)) ⟶
        naiveCotangentObject A' B'
    rw [extendScalarsComplex_selfNaiveCotangent_eq_tensorized]
    simpa using
      (DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          naiveCotangentUnderivedPushoutChainMap
          embeddingDownNat))

-- Proof sketch: compose the canonical derived-to-underived comparison from Lemma `15.86.1`
-- for the self-presentation model of `NL_{B/A}` with the canonical underived pushout comparison
-- just defined above.
/-- The canonical derived pushout comparison
`NL_{B/A} ⊗[B]^{\mathbf L} B' ⟶ NL_{B'/A'}`
in `D(B')`. -/
noncomputable def naiveCotangentDerivedPushoutComparison :
    (naiveCotangentObject A B ⊗[B]^L[B']) ⟶
      naiveCotangentObject A' B' :=
  selfNaiveCotangentBaseChangeComparison ≫
    naiveCotangentPushoutComparison A A' B

-- Proof sketch: when `B` is flat over `A`, the tensorized self-presentation computes the
-- underived pushout `NL_{B/A} ⊗[B] B'`, and the source Stacks argument identifies the degree
-- `-1` and `0` maps with the canonical flat-base-change maps on `H1Cotangent` and Kähler
-- differentials. Since both complexes are two-term, those two homology isomorphisms imply the
-- comparison is a quasi-isomorphism.
/-- Lemma 15.86.3 (1): if `B` is flat over `A`, then the canonical underived pushout comparison
`NL_{B/A} ⊗[B] B' ⟶ NL_{B'/A'}`
is a quasi-isomorphism, i.e. an isomorphism in `D(B')`. -/
theorem naiveCotangentPushoutComparison_isIso_of_flat
    [Module.Flat A B] :
    IsIso (naiveCotangentPushoutComparison A A' B) := sorry

-- Proof sketch: the intrinsic hypothesis `HasTorAmplitudeIn NL_{B/A} (-1) 0` upgrades the
-- canonical derived-to-underived comparison for `NL_{B/A}` to a quasi-isomorphism after tensoring
-- with `B'`, and part `(1)` gives the underived pushout comparison as a quasi-isomorphism. Their
-- composite is therefore an isomorphism in `D(B')`.
/-- Lemma 15.86.3 (2): if `B` is flat over `A` and the canonical owner `NL_{B/A}` has
tor-amplitude in `[-1, 0]`, then the canonical derived pushout comparison
`NL_{B/A} ⊗[B]^{\mathbf L} B' ⟶ NL_{B'/A'}`
is a quasi-isomorphism, hence an isomorphism in `D(B')`. -/
theorem naiveCotangentDerivedPushoutComparison_isIso_of_flat_of_hasTorAmplitudeIn
    [Module.Flat A B]
    (hNL : HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0) :
    IsIso (naiveCotangentDerivedPushoutComparison A A' B) := sorry

end CategoryTheory

end

/-! ### Lemma_15_86_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open Algebra
open scoped NaiveCotangent

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [RingHom.IsLocalCompleteIntersection (algebraMap A B)]

/- Domain triage:
- primary domain: local complete intersection ring maps and the derived invariants of the
  canonical naive cotangent complex `NL_{B⁄A}`;
- sampled owner declarations:
  - `RingHom.IsLocalCompleteIntersection`, the chapter owner for the source-facing lci property;
  - `naiveCotangentObject A B`, the Chapter 10 bridge/view object of `NL_{B⁄A}` in `D(B)`;
  - `K.IsPerfect` and `HasTorAmplitudeIn`, the chapter owners for the two target
    derived properties.
- best owner abstraction: the primitive public datum is the lci owner
  `RingHom.IsLocalCompleteIntersection (algebraMap A B)`, while a chosen presentation
  `P : Generators A B (Fin n)` is bridge data supplied by Definition `15.33.2`.
- layer triage:
  - `source-facing`: the lci-facing perfectness and tor-amplitude theorems below;
  - `core/canonical`: `HasTorAmplitudeIn` and `DerivedCategory.IsPerfect` on
    `naiveCotangentObject A B`;
  - `bridge/view`: the chosen finite presentation witness from Definition `15.33.2`, used only
    internally in the proof. -/

/-- Lemma 15.86.4: if `A → B` is a local complete intersection ring map, then the naive
cotangent complex `NL_{B/A}` is perfect and has tor-amplitude in `[-1, 0]`. -/
theorem naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection
    :
    (naiveCotangentObject A B).IsPerfect ∧
      HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0 := by
  sorry

/-- For a local complete intersection ring map, the naive cotangent complex `NL_{B/A}` is
perfect in `D(B)`. -/
theorem naiveCotangent_isPerfect_of_isLocalCompleteIntersection
    :
    (naiveCotangentObject A B).IsPerfect :=
  naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection.1

/-- For a local complete intersection ring map, the naive cotangent complex `NL_{B/A}` has
tor-amplitude in `[-1, 0]`. -/
theorem naiveCotangent_hasTorAmplitude_of_isLocalCompleteIntersection
    :
    HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0 :=
  naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection.2

end

/-! ### Lemma_15_86_5 (from Chap15) -/
open Algebra
open scoped TensorProduct

noncomputable section

universe u

section

variable {A A' B : Type u}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

local notation "B'" => B ⊗[A] A'

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance :
    Module B' ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)) :=
  Submodule.module (LinearMap.ker (H1Cotangent.baseChangeComparison A A' B))

/- Domain-style sampling:
- primary domain: base change for local complete intersection ring maps and the induced
  cotangent-homology comparison kernel;
- sampled owner declarations:
  `RingHom.IsLocalCompleteIntersection`,
  `RingHom.IsLocalCompleteIntersection.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`,
  `H1Cotangent.baseChangeComparison`;
- best owner abstraction: the primitive source-facing input is only
  `RingHom.IsLocalCompleteIntersection (algebraMap A B)`;
  the pushout lci structure on `algebraMap A' B'` is derived bridge data from the complete-
  intersection base-change/locality story and should not remain a second public hypothesis;
- primitive vs. derived: the comparison kernel
  `LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)` is the source-facing object of the
  lemma, while the lci property of `A' → B'` is internal proof data. -/

-- Proof sketch: by Lemma `15.86.4`, the naive cotangent complexes for `A → B` and the derived
-- base-changed local complete intersection map `A' → B'` are perfect of tor-amplitude in
-- `[-1, 0]`. Lemma `15.86.2` and the pushout
-- comparison give a distinguished triangle whose cone has only one nonzero cohomology module,
-- namely this kernel in degree `-1`. The cone is again perfect of tor-amplitude in `[-1, 1]`,
-- so Lemmas `15.65.4` and `15.67.6` make the kernel finitely presented and flat, hence finite
-- projective.
/-- Lemma 15.86.5: for a cocartesian square of commutative rings, written in the owner-facing
tensor order as the pushout `B' = B ⊗[A] A'`, if `A → B` is a local complete intersection, then
the kernel of the canonical comparison
`H^{-1}(NL_{B/A} ⊗[B] B') → H^{-1}(NL_{B'/A'})`, expressed in the library-facing form as the
kernel of `H1Cotangent.baseChangeComparison A A' B`,
is a finite projective `B'`-module.
-/
theorem ker_h1Cotangent_baseChange_comparison_finite_projective_of_isLocalCompleteIntersection
    [RingHom.IsLocalCompleteIntersection (algebraMap A B)] :
    Module.FiniteProjective B'
      ↥(LinearMap.ker (H1Cotangent.baseChangeComparison A A' B)) := by
  have hbase :
      RingHom.IsLocalCompleteIntersection (algebraMap A' B') := by
    -- This pushout local-complete-intersection structure is derived internally from the lci
    -- base-change/locality story, rather than treated as additional public input.
    sorry
  letI := hbase
  sorry

end
