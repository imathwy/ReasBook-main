import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_35_1 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ O₃ : Sheaf J CommRingCat.{u}}

private abbrev presentationNaiveCotangentTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    ℤ → SheafOfModules (ringSheaf J O₃)
  | Int.negSucc 0 => conormalSource α
  | Int.ofNat 0 => conormalTensorTerm φ α
  | _ => 0

private noncomputable def presentationNaiveCotangentDifferential
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (n : ℤ) :
    presentationNaiveCotangentTerm φ α n ⟶
      presentationNaiveCotangentTerm φ α (n + 1) :=
  match n with
  | Int.negSucc 0 => by
      simpa [presentationNaiveCotangentTerm] using conormalMap φ α
  | Int.negSucc 1 => by
      change (0 : SheafOfModules (ringSheaf J O₃)) ⟶ conormalSource α
      exact 0
  | Int.negSucc (_ + 2) => by
      change (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0
      exact 0
  | Int.ofNat 0 => by
      change conormalTensorTerm φ α ⟶ (0 : SheafOfModules (ringSheaf J O₃))
      exact 0
  | Int.ofNat (_ + 1) => by
      change (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0
      exact 0

private theorem presentationNaiveCotangent_sq_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (n : ℤ) :
    presentationNaiveCotangentDifferential φ α n ≫
      presentationNaiveCotangentDifferential φ α (n + 1) = 0 :=
  match n with
  | Int.negSucc 0 => by
      change conormalMap φ α ≫
          (0 : conormalTensorTerm φ α ⟶ (0 : SheafOfModules (ringSheaf J O₃))) = 0
      exact comp_zero
  | Int.negSucc 1 => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ conormalSource α) ≫
          conormalMap φ α = 0
      exact zero_comp
  | Int.negSucc 2 => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ conormalSource α) = 0
      rfl
  | Int.negSucc (_ + 3) => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) = 0
      simp
  | Int.ofNat 0 => by
      change (0 : conormalTensorTerm φ α ⟶ (0 : SheafOfModules (ringSheaf J O₃))) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) = 0
      rfl
  | Int.ofNat (_ + 1) => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) = 0
      simp

/-- The naive cotangent complex of a presentation `O₁ ⟶ O₂ ⟶ O₃`, represented as the two-term
cochain complex with `conormalSource α` in degree `-1` and `conormalTensorTerm φ α` in degree
`0`. -/
noncomputable abbrev presentationNaiveCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    CochainComplex (SheafOfModules (ringSheaf J O₃)) ℤ :=
  CochainComplex.of
    (presentationNaiveCotangentTerm φ α)
    (presentationNaiveCotangentDifferential φ α)
    (presentationNaiveCotangent_sq_zero φ α)

/-- The degree `-1` term of the presentationwise naive cotangent complex is the conormal source
term `Ker(α) / Ker(α)^2`. -/
theorem presentationNaiveCotangent_X_negOne
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (presentationNaiveCotangent φ α).X (-1) = conormalSource α := by
  rfl

/-- The degree `0` term of the presentationwise naive cotangent complex is the tensor term
`\Omega_{O₂/O₁} \otimes_{O₂} O₃`. -/
theorem presentationNaiveCotangent_X_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (presentationNaiveCotangent φ α).X 0 = conormalTensorTerm φ α := by
  rfl

variable [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]
variable [HasWeakSheafify J (Type u)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜)

/- Definition 18.35.1: the naive cotangent complex `NL_{\mathcal B/\mathcal A}` is the two-term
cochain complex obtained from the canonical sheaf morphism of `18.35.0.2` by placing
`\mathcal I/\mathcal I^2` in degree `-1` and
`\Omega_{\mathcal A[\mathcal B]/\mathcal A} \otimes_{\mathcal A[\mathcal B]} \mathcal B` in
degree `0`. The canonical owner construction for such a complex is `CochainComplex.of`. -/
noncomputable abbrev naiveCotangent :
    CochainComplex (SheafOfModules (ringSheaf J 𝒝.right)) ℤ :=
  presentationNaiveCotangent (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝)

/-- The degree `-1` term of `NL_{\mathcal B/\mathcal A}` is the scalar-extended conormal source
term of the canonical presentation `\mathcal A[\mathcal B] \to \mathcal B`, namely the owner
`conormalSource (presentationMap 𝒜 𝒝)` from Lemma `18.33.8`. -/
theorem naiveCotangent_X_negOne :
    (naiveCotangent 𝒜 𝒝).X (-1) =
      conormalSource (presentationMap 𝒜 𝒝) := by
  rfl

/-- The degree `0` term of `NL_{\mathcal B/\mathcal A}` is the tensor term
`\Omega_{\mathcal A[\mathcal B]/\mathcal A} \otimes_{\mathcal A[\mathcal B]} \mathcal B`. -/
theorem naiveCotangent_X_zero :
    (naiveCotangent 𝒜 𝒝).X 0 =
      conormalTensorTerm (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝) := by
  rfl

end SheafOfModules.RingedSite

/-! ### Lemma_18_35_2 (from Chap18) -/
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

/-! ### Lemma_18_35_3 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

/-- The additive sheaf underlying the actual inverse image of `Ω(φ)`. -/
abbrev inverseImageNaiveCotangentSheaf
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
          (ringSheaf JC O₂))).IsRightAdjoint] :
    Sheaf JD AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf
      ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))).obj
    (inverseImageRelativeDifferentialsSource F O₁ O₂ φ)

/-- The additive sheaf underlying the pulled-back relative differentials. -/
abbrev pulledBackNaiveCotangentSheaf
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
          (ringSheaf JC O₂))).IsRightAdjoint] :
    Sheaf JD AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf
      ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))).obj
    (pulledBackRelativeDifferentials F O₁ O₂ φ)

-- Proof sketch: Lemma `18.33.5` produces the canonical comparison morphism from the actual
-- inverse image of `Ω_{O₂/O₁}` to the pulled-back owner
-- `pulledBackRelativeDifferentials F O₁ O₂ φ`, and that morphism is an isomorphism. The naive
-- cotangent complex in this site-level formulation is the single-term cochain complex
-- concentrated in degree `0` on the underlying additive sheaf, so applying `CochainComplex.single₀`
-- to the comparison gives the desired identification.
/-- Lemma 18.35.3: for a morphism of topoi presented by a continuous functor
`F : \mathcal D \to \mathcal C` and a morphism `\mathcal O_1 \to \mathcal O_2` of sheaves of
commutative rings on `\mathcal C`, the inverse image of the naive cotangent complex
`NL_{\mathcal O_2/\mathcal O_1}` is canonically isomorphic to the naive cotangent complex of the
pulled-back morphism. In this formalization, both naive cotangent complexes are the degree-`0`
single-term complexes on the corresponding sheaves of relative differentials. -/
theorem inverseImage_naive_cotangent_complex_iso
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
          (ringSheaf JC O₂))).IsRightAdjoint] :
    IsIsomorphic
      ((CochainComplex.single₀ (Sheaf JD AddCommGrpCat.{max u v})).obj
        (inverseImageNaiveCotangentSheaf F O₁ O₂ φ))
      ((CochainComplex.single₀ (Sheaf JD AddCommGrpCat.{max u v})).obj
        (pulledBackNaiveCotangentSheaf F O₁ O₂ φ)) := sorry

/-! ### Definition_18_35_4 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {C : Type u} [SmallCategory C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf JC CommRingCat.{u})]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

local instance (f : X ⟶ Y) : Functor.IsContinuous f.base JD JC :=
  f.isMorphismOfSites.toIsContinuous

/- Domain-style sampling for Definition 18.35.4:
- primary domain: naive cotangent complexes of site-presented morphisms of ringed topoi;
- sampled owner declarations:
  `RingedSite.Hom`,
  `RingedSite.Hom.inverseImageStructureSheafMap`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`;
- best owner abstraction: the source-facing owner is the bundled morphism of ringed sites
  `f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪'`; the inverse-image
  structure-sheaf map is derived data via `inverseImageStructureSheafMap f`, and the naive
  cotangent complex is the Chapter 18 site-level owner `naiveCotangent` applied to that
  inverse-image map;
- primitive data: the bundled morphism `f`;
- derived API: the inverse-image structure-sheaf map, the induced `Under` object
  `Under.mk (inverseImageStructureSheafMap f)`, and the resulting two-term complex concentrated in
  degrees `-1` and `0`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.Hom.naiveCotangentComplex`, written as `NL(f)`;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: `inverseImageStructureSheafMap f`, converting the bundled ringed-site morphism to
  the sheaf morphism to which the site-level naive cotangent owner applies.

This item should therefore be organized around the bundled owner `RingedSite.Hom`, not around the
raw site data `(f.base, 𝒪, 𝒪', fSharp)`. -/

private abbrev sourceSheaf (f : X ⟶ Y) :
    Sheaf JC CommRingCat.{u} :=
  (f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪'

private abbrev sourceUnder (f : X ⟶ Y) :
    Under ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪') :=
  Under.mk (inverseImageStructureSheafMap f)

/-- Definition 18.35.4: for a bundled morphism of ringed sites
`f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪'` presenting a morphism of
ringed topoi, the naive cotangent complex `NL_f` is the site-level naive cotangent complex
`NL_{\mathcal O_X / f^{-1}\mathcal O_Y}` from Definition `18.35.1`, specialized along the
inverse-image structure-sheaf map `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`. -/
abbrev naiveCotangentComplex :
    CochainComplex (ringedSiteModuleCategory JC 𝒪) ℤ :=
  naiveCotangent (sourceSheaf f) (sourceUnder f)

end

/- Source-facing notation for the naive cotangent complex of a morphism of ringed sites. -/
scoped syntax:max "NL(" term ")" : term

scoped macro_rules
  | `(NL($f)) => `(RingedSite.Hom.naiveCotangentComplex $f)

open scoped RingedSite.Hom

section

variable {C : Type u} [SmallCategory C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf JC CommRingCat.{u})]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

local instance (f : X ⟶ Y) : Functor.IsContinuous f.base JD JC :=
  f.isMorphismOfSites.toIsContinuous

/-- The naive cotangent complex of `f` is the Chapter 18 site-level owner applied to the
inverse-image structure-sheaf morphism `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`. -/
theorem naiveCotangentComplex_def :
    NL(f) =
      naiveCotangent
        ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪')
        (Under.mk (inverseImageStructureSheafMap f)) :=
  rfl

end

end RingedSite.Hom
