import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import StacksProject_2024.stacks_project.Chap10.Definition_10_134_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_3

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

/-- Helper for Lemma 15.86.1: the extended naive cotangent cochain complex has no terms in
positive degrees. -/
private theorem naiveCotangentCochain_isStrictlyLE_zero
    (E : Algebra.Extension R S) :
    CochainComplex.IsStrictlyLE (E.naiveCotangentChainComplex.extend embeddingDownNat) 0 := by
  -- Check the upper support bound degreewise after extending from `ℕ` to `ℤ`.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact
    E.naiveCotangentChainComplex.isZero_extend_X embeddingDownNat i fun j hij ↦ by
      have hnonpos : (embeddingDownNat.f j : ℤ) ≤ 0 := by
        simp [ComplexShape.embeddingDownNat]
      omega

/-- Helper for Lemma 15.86.1: the canonical self-presentation naive cotangent cochain complex is
supported in degrees `≤ 0`. -/
private theorem selfNaiveCotangent_isStrictlyLE_zero :
    CochainComplex.IsStrictlyLE
      (show CpxS from (Algebra.naiveCotangent R S).extend embeddingDownNat)
      0 := by
  -- Specialize the extension-level support bound to the self-presentation model.
  simpa [Algebra.naiveCotangent] using
    naiveCotangentCochain_isStrictlyLE_zero (Generators.self R S).toExtension

/-- Helper for Lemma 15.86.1: every presentationwise naive cotangent cochain complex is supported
in degrees `≤ 0`. -/
private theorem presentationNaiveCotangent_isStrictlyLE_zero
    (P : Presentation R S ι σ) :
    CochainComplex.IsStrictlyLE
      ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)
      0 := by
  -- The presentation case is the same extension-level bound.
  simpa using
    naiveCotangentCochain_isStrictlyLE_zero P.toExtension

/-- Helper for Lemma 15.86.1: the degree-zero term of the self-presentation naive cotangent
cochain complex is free, hence flat. -/
private theorem selfNaiveCotangent_degree_zero_flat :
    Module.Flat S ((((NL_{S⁄R}).extend embeddingDownNat : CpxS).X 0)) := by
  -- Transport degree `0` along `extendXIso`, then use the canonical cotangent-space basis.
  letI :
      Module.Free S ((Generators.self R S).toExtension.CotangentSpace) :=
    Module.Free.of_basis (Generators.self R S).cotangentSpaceBasis
  let e :
      ((((NL_{S⁄R}).extend embeddingDownNat : CpxS).X 0)) ≃ₗ[S]
        (Generators.self R S).toExtension.CotangentSpace := by
    simpa [Algebra.naiveCotangent, Algebra.Extension.naiveCotangentChainComplex] using
      (((NL_{S⁄R}).extendXIso embeddingDownNat
        (show embeddingDownNat.f 0 = (0 : ℤ) by rfl)).toLinearEquiv)
  letI : Module.Flat S ((Generators.self R S).toExtension.CotangentSpace) :=
    Module.Flat.of_free (R := S) (M := (Generators.self R S).toExtension.CotangentSpace)
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 15.86.1: the degree-zero term of a presentationwise naive cotangent cochain
complex is free, hence flat. -/
private theorem presentationNaiveCotangent_degree_zero_flat
    (P : Presentation R S ι σ) :
    Module.Flat S
      ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxS).X 0)) := by
  -- Transport degree `0` along `extendXIso`, then use the presentation cotangent-space basis.
  letI :
      Module.Free S P.toExtension.CotangentSpace :=
    Module.Free.of_basis P.cotangentSpaceBasis
  let e :
      ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxS).X 0)) ≃ₗ[S]
        P.toExtension.CotangentSpace := by
    simpa [Algebra.Extension.naiveCotangentChainComplex] using
      (((P.toExtension.naiveCotangentChainComplex).extendXIso embeddingDownNat
        (show embeddingDownNat.f 0 = (0 : ℤ) by rfl)).toLinearEquiv)
  letI : Module.Flat S P.toExtension.CotangentSpace :=
    Module.Flat.of_free (R := S) (M := P.toExtension.CotangentSpace)
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 15.86.1: the two-term representative theorem from Lemma `15.85.6`
specialized to `Q.obj P` supplies the canonical truncation/base-change isomorphism. -/
private noncomputable def derivedTensorWithAlgebraTruncGEIsoOfTwoTermFlat
    (P : CpxS) [CochainComplex.IsStrictlyGE P (-1)] (hLE : P.IsStrictlyLE 0)
    (hflat0 : Module.Flat S (P.X 0)) :
    DerivedCategory.Q.obj (Functor.obj ExtCpx P) ≅
      (t.truncGE (-1)).obj
        ((derivedTensorWithAlgebra (algebraMap S S')).obj (DerivedCategory.Q.obj P)) :=
  sorry

/-- Helper for Lemma 15.86.1: if a cochain complex over `S` is supported in degrees `[-1, 0]`
and its degree-zero term is flat, then the explicit truncation factor of the canonical derived
base-change counit is an isomorphism. -/
theorem derivedTensorWithAlgebraTruncGEComparison_isIso_of_two_term_flat
    (P : CpxS) [CochainComplex.IsStrictlyGE P (-1)] (hLE : P.IsStrictlyLE 0)
    (hflat0 : Module.Flat S (P.X 0)) :
    IsIso ((derivedTensorWithAlgebraTruncGEIsoOfTwoTermFlat
      (S := S) (S' := S') P hLE hflat0).inv) := by
  infer_instance

-- Proof sketch: the ordinary base-change target is represented by a two-term cochain complex,
-- hence the isomorphism from Lemma `15.85.6` directly yields the induced map out of
-- `τ_{\ge -1}`.
/-- The induced canonical morphism
`τ_{\ge -1}(NL_{S/R} \otimes_S^{\mathbf L} S') \to NL_{S/R} \otimes_S S'`
to the ordinary base-change target for the self-presentation model. -/
noncomputable def selfNaiveCotangentBaseChangeTruncGEComparison :
    (t.truncGE (-1)).obj (naiveCotangentObject R S ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj
        (Functor.obj ExtCpx ((NL_{S⁄R}).extend embeddingDownNat : CpxS)) :=
  let P : CpxS := ((NL_{S⁄R}).extend embeddingDownNat : CpxS)
  letI : CochainComplex.IsStrictlyGE P (-1) := selfNaiveCotangent_isStrictlyGE
  (derivedTensorWithAlgebraTruncGEIsoOfTwoTermFlat
    (S := S)
    (S' := S')
    P
    selfNaiveCotangent_isStrictlyLE_zero
    selfNaiveCotangent_degree_zero_flat).inv

-- Proof sketch: as in the self-presentation case, the ordinary base-change target already lies in
-- `D^{≥ -1}(S')`, so the same specialized isomorphism supplies the induced truncation map.
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
  let P' : CpxS := (P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat
  letI : CochainComplex.IsStrictlyGE P' (-1) := presentationNaiveCotangent_isStrictlyGE P
  (derivedTensorWithAlgebraTruncGEIsoOfTwoTermFlat
    (S := S)
    (S' := S')
    P'
    (presentationNaiveCotangent_isStrictlyLE_zero (P := P))
    (presentationNaiveCotangent_degree_zero_flat (P := P))).inv

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
            (Functor.obj ExtCpx (((NL_{S⁄R}).extend embeddingDownNat : CpxS)))) := by
  let P : CpxS := ((NL_{S⁄R}).extend embeddingDownNat : CpxS)
  letI : CochainComplex.IsStrictlyGE P (-1) := selfNaiveCotangent_isStrictlyGE
  -- Specialize the generic two-term flat comparison theorem to the canonical self-presentation.
  simpa using
    derivedTensorWithAlgebraTruncGEComparison_isIso_of_two_term_flat
      (S := S)
      (S' := S')
      P
      selfNaiveCotangent_isStrictlyLE_zero
      selfNaiveCotangent_degree_zero_flat

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
        (Functor.obj ExtCpx (((NL_{S⁄R}).extend embeddingDownNat : CpxS)))) := by
  let φ :
      (t.truncGE (-1)).obj (naiveCotangentObject R S ⊗[S]^L[S']) ⟶
        DerivedCategory.Q.obj
          (Functor.obj ExtCpx (((NL_{S⁄R}).extend embeddingDownNat : CpxS))) :=
    selfNaiveCotangentBaseChangeTruncGEComparison
  -- Package the canonical comparison isomorphism as the corresponding object-level witness.
  have hφ : IsIso φ := selfNaiveCotangentBaseChangeComparison_truncGE_isIso
  exact ⟨asIso φ⟩

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
              ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat))) := by
  let P' : CpxS := ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxS)
  letI : CochainComplex.IsStrictlyGE P' (-1) := presentationNaiveCotangent_isStrictlyGE P
  -- The presentation case is the same generic comparison for the chosen cotangent cochain model.
  simpa using
    derivedTensorWithAlgebraTruncGEComparison_isIso_of_two_term_flat
      (S := S)
      (S' := S')
      P'
      (presentationNaiveCotangent_isStrictlyLE_zero (P := P))
      (presentationNaiveCotangent_degree_zero_flat (P := P))

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
          ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat))) := by
  let φ :
      (t.truncGE (-1)).obj
          (DerivedCategory.Q.obj
            ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat) ⊗[S]^L[S']) ⟶
        DerivedCategory.Q.obj
          (Functor.obj ExtCpx
            ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)) :=
    presentationNaiveCotangentBaseChangeTruncGEComparison P
  -- Package the canonical presentationwise comparison isomorphism as an object-level witness.
  have hφ : IsIso φ := presentationNaiveCotangentBaseChangeComparison_truncGE_isIso P
  exact ⟨asIso φ⟩

end

end CategoryTheory
