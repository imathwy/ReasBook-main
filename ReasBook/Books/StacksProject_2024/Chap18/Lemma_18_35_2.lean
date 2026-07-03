import Mathlib
import stacks_project.Chap18.Definition_18_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped RelativeDerivation
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.35.2:
- primary domain: naive cotangent complexes of presentations `\mathcal A[E] \to \mathcal B` of
  sheaves of `\mathcal A`-algebras on a fixed site, compared in the derived category of
  `\mathcal B`-module sheaves;
- sampled owner declarations:
  `Sheaf.composeAndSheafify J CommRingCat.free`,
  `Sheaf.adjunction J CommRingCat.adj`,
  `presentationMapOf`,
  `Under`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `DerivedCategory.Q.obj`;
- best owner abstraction: the source-facing primitive data are a sheaf of sets `E` together with a
  map `α : E ⟶ \mathcal B` of underlying sheaves of sets; this induces the presentation
  morphism `presentationMapOf J 𝒜 𝒝 E α : \mathcal A[E] \to \mathcal B`, whose two-term
  complex is the correct presentationwise input to `presentationNaiveCotangent`;
- derived API: the resulting comparison morphism in `D(\mathcal B)` from the chosen presentation
  to the canonical presentation `\mathcal A[\mathcal B] \to \mathcal B`.

Source/core/bridge triage:
- `source-facing`: the comparison in `D(\mathcal B)` between the naive cotangent complexes of the
  chosen presentation `\mathcal A[E] \to \mathcal B` and the canonical presentation
  `\mathcal A[\mathcal B] \to \mathcal B`;
- `core/canonical`: `presentationMapOf`, `presentationNaiveCotangent`, and `naiveCotangent`;
- `bridge/view`: the localization functor `DerivedCategory.Q`.

This file should therefore keep the source presentation data visible, and expose an actual
comparison morphism in `D(\mathcal B)` rather than only the proposition that two objects are
isomorphic. -/

section

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]
variable {A : Sheaf J CommRingCat.{u}} {B : Under A}

local notation "ModB" => SheafOfModules (ringSheaf J B.right)
local notation "DModB" => DerivedCategory ModB

local instance : HasDerivedCategory ModB :=
  HasDerivedCategory.standard ModB

private abbrev cotangentSingle₀ : CochainComplex ModB ℤ :=
  (HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj (Ω(B.hom))

private abbrev presentationCotangentSingle
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    CochainComplex ModB ℤ :=
  (HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj
    (Ω(presentationBaseOf A E ≫ presentationMapOf A B E α))

private abbrev naiveCotangentSingle : CochainComplex ModB ℤ :=
  (HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj
    (Ω(presentationBase A B ≫ presentationMap A B))

/-- The naive cotangent complex attached to a presentation of `B` by a sheaf of sets
`α : E ⟶ presentationVariables B`, i.e. to the induced presentation morphism
`\mathcal A[E] \to \mathcal B`. -/
abbrev presentationNaiveCotangentOf
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    CochainComplex ModB ℤ :=
  presentationNaiveCotangent
    (presentationBaseOf A E)
    (presentationMapOf A B E α)

omit [HasWeakSheafify J (Type u)] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
private theorem presentationBaseOf_comp_presentationMapOf
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    presentationBaseOf A E ≫ presentationMapOf A B E α = B.hom := by
  simpa [presentationBaseOf, presentationMapOf] using
    ((((Under.costarAdjForget A).homEquiv (presentationFreeSheaf E) B).symm
      (presentationFreeMap B E α))).w.symm

omit [HasWeakSheafify J (Type u)] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
private theorem presentationBase_comp_presentationMap :
    presentationBase A B ≫ presentationMap A B = B.hom := by
  simpa [presentationBase, presentationMap, presentationBaseOf, presentationMapOf] using
    ((((Under.costarAdjForget A).homEquiv
      (presentationFreeSheaf (presentationVariables B)) B).symm
      (presentationFreeMap B (presentationVariables B) (𝟙 _)))).w.symm

omit [HasWeakSheafify J (Type u)] [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
private theorem presentationNaiveCotangent_target_eq
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    Ω(presentationBaseOf A E ≫ presentationMapOf A B E α) = Ω(B.hom) :=
  congrArg (fun φ ↦ Ω(φ))
    (presentationBaseOf_comp_presentationMapOf E α)

omit [HasWeakSheafify J (Type u)] [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
private theorem naiveCotangent_target_eq :
    Ω(presentationBase A B ≫ presentationMap A B) = Ω(B.hom) :=
  congrArg (fun φ ↦ Ω(φ)) presentationBase_comp_presentationMap

omit [HasWeakSheafify J (Type u)] [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
private theorem presentationCotangentSingle_eq
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    presentationCotangentSingle E α = cotangentSingle₀ :=
  congrArg ((HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj)
    (presentationNaiveCotangent_target_eq E α)

omit [HasWeakSheafify J (Type u)] [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
private theorem naiveCotangentSingle_eq :
    (naiveCotangentSingle : CochainComplex ModB ℤ) = cotangentSingle₀ :=
  congrArg ((HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj)
    naiveCotangent_target_eq

-- Proof sketch: compare the chosen presentation `\mathcal A[E] \to \mathcal B` with the
-- canonical one `\mathcal A[\mathcal B] \to \mathcal B` through the refinement
-- `\mathcal A[E \amalg \mathcal B] \to \mathcal B` coming from the map
-- `coprod.desc α (𝟙 _) : E ⨿ presentationVariables B ⟶ presentationVariables B`. The two induced
-- maps to the refinement are
-- quasi-isomorphisms by the same site-level conormal exactness argument as in Lemma `18.33.8`,
-- together with the presentation-independence argument from Chapter `10`. Passing to
-- `DerivedCategory.Q` produces the comparison morphism in `D(B)`.
private noncomputable def presentationNaiveCotangentToCotangent
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    : presentationNaiveCotangentOf E α ⟶ presentationCotangentSingle E α :=
  HomologicalComplex.mkHomToSingle
    (show (presentationNaiveCotangentOf E α).X 0 ⟶
        Ω(presentationBaseOf A E ≫ presentationMapOf A B E α) from by
      rw [presentationNaiveCotangent_X_zero]
      exact conormalToDifferentials (presentationBaseOf A E) (presentationMapOf A B E α))
    (fun i hi ↦ by
      have hi₀ : i + 1 = 0 := by
        simpa [ComplexShape.up, ComplexShape.Rel] using hi
      have hi' : i = -1 := by omega
      subst hi'
      simpa [presentationNaiveCotangentOf] using
        conormal_comp_zero (presentationBaseOf A E) (presentationMapOf A B E α)
    )

private noncomputable def naiveCotangentToCotangent :
    naiveCotangent A B ⟶ naiveCotangentSingle :=
  HomologicalComplex.mkHomToSingle
    (show (naiveCotangent A B).X 0 ⟶ Ω(presentationBase A B ≫ presentationMap A B) from by
      rw [naiveCotangent_X_zero]
      exact conormalToDifferentials (presentationBase A B) (presentationMap A B))
    (fun i hi ↦ by
      have hi₀ : i + 1 = 0 := by
        simpa [ComplexShape.up, ComplexShape.Rel] using hi
      have hi' : i = -1 := by omega
      subst hi'
      simpa [naiveCotangent] using
        conormal_comp_zero (presentationBase A B) (presentationMap A B)
    )

private noncomputable def presentationCotangentSingleIso
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    presentationCotangentSingle E α ≅ cotangentSingle₀ :=
  eqToIso (presentationCotangentSingle_eq E α)

private noncomputable def naiveCotangentSingleIso :
    (naiveCotangentSingle : CochainComplex ModB ℤ) ≅ cotangentSingle₀ :=
  eqToIso naiveCotangentSingle_eq

private instance presentationNaiveCotangentToCotangent_q_isIso
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    IsIso (DerivedCategory.Q.map (presentationNaiveCotangentToCotangent E α)) := by
  sorry

private instance naiveCotangentToCotangent_q_isIso :
    IsIso
      (DerivedCategory.Q.map
        (naiveCotangentToCotangent : naiveCotangent A B ⟶ naiveCotangentSingle)) := by
  sorry

/-- Lemma 18.35.2: let
`α : E ⟶ presentationVariables B`
be a locally surjective map of sheaves of sets, so that the
induced map `\mathcal A[E] \to \mathcal B` is a chosen presentation of `\mathcal B` over
`\mathcal A`. Then there is a canonical comparison morphism in `D(B)` from the naive cotangent
complex of that chosen presentation to the canonical naive cotangent complex
`NL_{\mathcal B/\mathcal A}`. -/
noncomputable abbrev presentationNaiveCotangentComparison
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    ((DerivedCategory.Q.obj (presentationNaiveCotangentOf E α)) : DModB) ⟶
      ((DerivedCategory.Q.obj (naiveCotangent A B)) : DModB) :=
  DerivedCategory.Q.map (presentationNaiveCotangentToCotangent E α) ≫
    DerivedCategory.Q.map (presentationCotangentSingleIso E α).hom ≫
    (asIso
      (DerivedCategory.Q.map
        ((naiveCotangentSingleIso :
          (naiveCotangentSingle : CochainComplex ModB ℤ) ≅ cotangentSingle₀).hom))).inv ≫
    (asIso
      (DerivedCategory.Q.map
        (naiveCotangentToCotangent : naiveCotangent A B ⟶ naiveCotangentSingle))).inv

private instance presentationNaiveCotangentComparison_isIso_inst
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    IsIso (presentationNaiveCotangentComparison E α) := by
  sorry

/-- The comparison morphism of Lemma 18.35.2 is an isomorphism in `D(B)`. -/
theorem presentationNaiveCotangentComparison_isIso
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    IsIso (presentationNaiveCotangentComparison E α) := by
  exact presentationNaiveCotangentComparison_isIso_inst E α hα

/-- The chosen-presentation naive cotangent complex and the canonical naive cotangent complex are
canonically isomorphic in `D(B)`. -/
theorem presentationNaiveCotangent_iso
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    IsIsomorphic
      ((DerivedCategory.Q.obj (presentationNaiveCotangentOf E α)) : DModB)
      ((DerivedCategory.Q.obj (naiveCotangent A B)) : DModB) := by
  letI := presentationNaiveCotangentComparison_isIso E α hα
  exact ⟨asIso (presentationNaiveCotangentComparison E α)⟩

end

end
