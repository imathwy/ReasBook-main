import Mathlib
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_134_10 (from Chap10) -/
open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open scoped NaiveCotangent

universe u v

noncomputable section

section

variable {A : Type u} {Aₛ : Type v}
variable [CommRing A] [CommRing Aₛ] [Algebra A Aₛ]

private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  simp [ComplexShape.down]

private noncomputable abbrev liftCotangentEquiv
    (P : Extension.{max u v} A Aₛ) :
    ULift.{v, max u v} P.Cotangent ≃ₗ[Aₛ] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def liftCotangentLinear
    (P : Extension.{max u v} A Aₛ) :
    P.Cotangent →ₗ[Aₛ] ULift.{v, max u v} P.Cotangent where
  toFun x := ⟨x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def liftCotangentSpaceToLiftCotangent
    (P : Extension.{max u v} A Aₛ) (σ : P.CotangentSpace →ₗ[Aₛ] P.Cotangent) :
    P.CotangentSpace →ₗ[Aₛ] ULift.{v, max u v} P.Cotangent where
  toFun x := ULift.up (σ x)
  map_add' x y := by
    change ULift.up (σ (x + y)) = ULift.up (σ x + σ y)
    simp
  map_smul' a x := by
    change ULift.up (σ (a • x)) = ULift.up (a • σ x)
    simp

private noncomputable def naiveCotangentChainComplexXIsoPUnit
    (P : Extension.{max u v} A Aₛ) (i : ℕ) :
    P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{max u v} Aₛ PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{max u v} Aₛ} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{max u v} Aₛ) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{max u v} Aₛ PUnit, 0, by simp⟩
  simpa [Extension.naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of.{max u v} Aₛ P.CotangentSpace)
      (ModuleCat.of.{max u v} Aₛ (ULift.{v, max u v} P.Cotangent))
      (ModuleCat.ofHom (P.cotangentComplex.comp (liftCotangentEquiv P).toLinearMap))
      succZero i)

private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension.{max u v} A Aₛ) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  let e := naiveCotangentChainComplexXIsoPUnit P i
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{max u v} A Aₛ) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

private theorem cotangentComplex_bijective_of_subsingleton_h1_and_kaehler
    (P : Extension.{max u v} A Aₛ)
    [Subsingleton P.H1Cotangent] [Subsingleton Ω[Aₛ⁄A]] :
    Function.Bijective P.cotangentComplex := by
  refine ⟨(Extension.subsingleton_h1Cotangent P).mp inferInstance, ?_⟩
  intro x
  have hx : x ∈ LinearMap.ker P.toKaehler := by
    change P.toKaehler x = 0
    exact Subsingleton.elim _ _
  have hexact := (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
  rw [hexact] at hx
  exact hx

private noncomputable def localization_naiveCotangentComplex_contraction
    (P : Extension.{max u v} A Aₛ)
    (σ : P.CotangentSpace →ₗ[Aₛ] P.Cotangent)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel j i) :
    P.naiveCotangentChainComplex.X i ⟶ P.naiveCotangentChainComplex.X j := by
  rcases i with _ | i
  · rcases j with _ | j
    · exfalso
      simp [ComplexShape.down] at hij
    · cases j with
      | zero =>
          simpa [Extension.naiveCotangentChainComplex] using
            (ModuleCat.ofHom (liftCotangentSpaceToLiftCotangent P σ))
      | succ j =>
          exfalso
          simp [ComplexShape.down] at hij
  · exact 0

private theorem localization_naiveCotangentComplex_contraction_comp_d_apply
    (P : Extension.{max u v} A Aₛ)
    (σ : P.CotangentSpace →ₗ[Aₛ] P.Cotangent)
    (hσ : P.cotangentComplex.comp σ = LinearMap.id) (x : P.CotangentSpace) :
    (ModuleCat.Hom.hom
        (localization_naiveCotangentComplex_contraction P σ 0 1 naiveCotangent_rel10 ≫
          ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))) x =
      x := by
  change P.cotangentComplex (σ x) = x
  simpa [LinearMap.comp_apply] using congrArg (fun f : P.CotangentSpace →ₗ[Aₛ] P.CotangentSpace ↦ f x) hσ

private theorem localization_naiveCotangentComplex_d_comp_contraction_apply
    (P : Extension.{max u v} A Aₛ)
    (σ : P.CotangentSpace →ₗ[Aₛ] P.Cotangent)
    (hσ : σ.comp P.cotangentComplex = LinearMap.id) (x : P.Cotangent) :
    (ModuleCat.Hom.hom
        (ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) ≫
            localization_naiveCotangentComplex_contraction P σ 0 1 naiveCotangent_rel10 +
          localization_naiveCotangentComplex_contraction P σ 1 2 naiveCotangent_rel21 ≫ 0))
      (ULift.up x) =
      ULift.up x := by
  change ULift.up (σ (P.cotangentComplex x)) + 0 = ULift.up x
  rw [add_zero]
  exact congrArg ULift.up <| by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : P.Cotangent →ₗ[Aₛ] P.Cotangent ↦ f x) hσ

private theorem localization_naiveCotangentComplex_id_eq_nullHomotopicMap
    (P : Extension.{max u v} A Aₛ)
    (σ : P.CotangentSpace →ₗ[Aₛ] P.Cotangent)
    (hleft : P.cotangentComplex.comp σ = LinearMap.id)
    (hright : σ.comp P.cotangentComplex = LinearMap.id) :
    𝟙 P.naiveCotangentChainComplex =
      Homotopy.nullHomotopicMap'
        (localization_naiveCotangentComplex_contraction P σ) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left naiveCotangent_rel10
        (by simp [ComplexShape.down]) (localization_naiveCotangentComplex_contraction P σ)]
      rw [Extension.naiveCotangentChainComplex_d_1_0]
      ext x
      simpa [Extension.naiveCotangentChainComplex] using
        (localization_naiveCotangentComplex_contraction_comp_d_apply P σ hleft x).symm
  | succ i =>
      cases i with
      | zero =>
          rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10
            (localization_naiveCotangentComplex_contraction P σ)]
          rw [Extension.naiveCotangentChainComplex_d_succ_succ P 0,
            Extension.naiveCotangentChainComplex_d_1_0 P]
          ext x
          cases x with
          | up x =>
              simpa [Extension.naiveCotangentChainComplex] using
                (localization_naiveCotangentComplex_d_comp_contraction_apply P σ hright x).symm
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ P i
          ext x
          exact Subsingleton.elim _ _

/- Domain-style sampling:
* primary domain: localization of naive cotangent complexes for commutative algebras;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the Chapter 10 owner `NL_{-⁄-}`;
  - `Algebra.Extension.naiveCotangentChainComplex`, the presentation-level two-term model;
  - `naiveCotangent_tensor_homotopyEquiv_of_flat`, the flat base-change owner comparison;
  - `naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv`, the localization-away
    specialization of that comparison.
* best owner abstraction: the public source-facing statement here belongs on the canonical complex
  `NL_{Aₛ⁄A}`. The self-presentation `Extension.self A Aₛ` and any tensor/base-change model are
  bridge/view data, not the owner surface.
* primitive vs. derived:
  - primitive data: the localization algebra `A → Aₛ`, encoded by `S : Submonoid A` and
    `[IsLocalization S Aₛ]`;
  - derived API: the self-presentation chain complex and the comparison with the zero complex.
* layer triage:
  - `source-facing`: the statement that the naive cotangent complex of a localization is
    contractible;
  - `core/canonical`: `NL_{Aₛ⁄A}`;
  - `bridge/view`: presentation-level models such as `(Extension.self A Aₛ).naiveCotangentChainComplex`.
-/
-- Proof sketch: apply flat base change for the naive cotangent complex along `A → Aₛ`, using the
-- localization flatness `Module.Flat A Aₛ`, to identify `NL_{Aₛ/A}` with `NL_{Aₛ/Aₛ}`. Then use
-- the identity-map case of the naive cotangent complex, which is homotopy equivalent to the zero
-- complex.
/-- Lemma 10.134.10: if `S ⊂ A` is a multiplicative subset and `Aₛ = S⁻¹A`, then the naive
cotangent complex `NL_{Aₛ/A}` is homotopy equivalent to the zero complex. -/
noncomputable def localization_naiveCotangentComplex_homotopyEquiv_zero
    (S : Submonoid A) [IsLocalization S Aₛ] :
    HomotopyEquiv (NL_{Aₛ⁄A}) (HomologicalComplex.zero : ChainComplex (ModuleCat Aₛ) ℕ) := by
  let P : Extension.{max u v} A Aₛ := (Generators.self A Aₛ).toExtension
  let Z : ChainComplex (ModuleCat Aₛ) ℕ := HomologicalComplex.zero
  letI : Algebra.FormallyEtale A Aₛ := Algebra.FormallyEtale.of_isLocalization S
  letI : Subsingleton P.H1Cotangent :=
    ((Generators.self A Aₛ).equivH1Cotangent).injective.subsingleton
  let e : P.Cotangent ≃ₗ[Aₛ] P.CotangentSpace :=
    LinearEquiv.ofBijective P.cotangentComplex
      (cotangentComplex_bijective_of_subsingleton_h1_and_kaehler P)
  have hleft : P.cotangentComplex ∘ₗ e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change e (e.symm x) = x
    exact LinearEquiv.apply_symm_apply e x
  have hright : e.symm.toLinearMap ∘ₗ P.cotangentComplex = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change e.symm (e x) = x
    exact LinearEquiv.symm_apply_apply e x
  let hContract :
      Homotopy (𝟙 P.naiveCotangentChainComplex) 0 :=
    (Homotopy.ofEq
      (localization_naiveCotangentComplex_id_eq_nullHomotopicMap P e.symm.toLinearMap hleft hright)).trans
      (Homotopy.nullHomotopy'
        (localization_naiveCotangentComplex_contraction P e.symm.toLinearMap))
  have hZeroId : (0 : Z ⟶ Z) = 𝟙 Z := by
    apply HomologicalComplex.hom_ext
    intro i
    simpa [Z] using
      (Limits.isZero_zero (ModuleCat Aₛ)).eq_of_src
        (0 : Z.X i ⟶ Z.X i) ((𝟙 Z : Z ⟶ Z).f i)
  refine
    { hom := 0
      inv := 0
      homotopyHomInvId := by
        simpa [P, Z, Algebra.naiveCotangent] using hContract.symm
      homotopyInvHomId := by
        exact Homotopy.ofEq hZeroId }

end

/-! ### Lemma_10_134_11 (from Chap10) -/
open Algebra
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {Aₛ : Type v} {B : Type w}
variable [CommRing A] [CommRing Aₛ] [CommRing B]
variable [Algebra A B]

/- Domain triage:
* primary domain: first cotangent homology under base localization and flat base change;
* sampled owner declarations:
  - `Algebra.H1Cotangent.map`, the canonical change-of-base map on first cotangent homology;
  - `Algebra.tensorH1CotangentOfFlat`, the owner flat base-change equivalence for `H¹(L_)`;
  - `Algebra.H1Cotangent.mapEquiv`, the canonical transport along an algebra equivalence;
  - `IsLocalization.algebraLid`, the canonical localization identification
    `Aₛ ⊗[A] B ≃ₐ[Aₛ] B`.
* best owner abstraction: the public object here is the canonical linear map
  `H1Cotangent.map A Aₛ B B`; no extra presentation-level wrapper or local comparison package is
  needed.
* primitive data: localization flatness over `A` and the canonical algebra equivalence
  `IsLocalization.algebraLid S Aₛ B`;
* derived API: the induced `Aₛ`-linear equivalence on `H¹(L_)`, whose underlying linear map is
  `H1Cotangent.map A Aₛ B B`.
* layer triage:
  - `source-facing`: bijectivity of the comparison `H¹(L_{B/A}) → H¹(L_{B/Aₛ})`;
  - `core/canonical`: `H1Cotangent.map A Aₛ B B`;
  - `bridge/view`: the canonical composite
    `moduleLid.symm ≪≫ₗ tensorH1CotangentOfFlat ≪≫ₗ H1Cotangent.mapEquiv (IsLocalization.algebraLid ...)`.
-/
-- Proof sketch: source localization is formally étale, so the Jacobi-Zariski comparison for
-- `A → Aₛ → B` is the owner-level map `H1Cotangent.map A Aₛ B B`; this is the canonical
-- `H¹` consequence of the source homotopy-equivalence statement for naive cotangent complexes.
/-- Lemma 10.134.11: if `S` is a multiplicative subset of `A` and `B` is an `Aₛ = S⁻¹A`-algebra,
then the canonical map from the first homology of the naive cotangent complex over `A` to the one
over `Aₛ` is bijective. This is the library-facing consequence of the source statement that
`NL_{B/A} → NL_{B/Aₛ}` is a homotopy equivalence. -/
theorem h1Cotangent_map_bijective_of_isLocalization_source
    (S : Submonoid A) [Algebra A Aₛ] [IsLocalization S Aₛ] [Algebra Aₛ B]
    [IsScalarTower A Aₛ B] :
    Function.Bijective (H1Cotangent.map A Aₛ B B) := by
  letI : Module.Flat A Aₛ := IsLocalization.flat Aₛ S
  let e : H1Cotangent A B ≃ₗ[Aₛ] H1Cotangent Aₛ B :=
    (IsLocalization.moduleLid S Aₛ (H1Cotangent A B)).symm.trans
      ((Algebra.tensorH1CotangentOfFlat A B Aₛ).trans
        (H1Cotangent.mapEquiv Aₛ (Aₛ ⊗[A] B) B (IsLocalization.algebraLid S Aₛ B)))
  have h : ∀ x, e x = H1Cotangent.map A Aₛ B B x := by
    intro x
    simp only [e, LinearEquiv.trans_apply]
    rw [show (IsLocalization.moduleLid S Aₛ (H1Cotangent A B)).symm x = 1 ⊗ₜ[A] x by rfl]
    rw [Algebra.tensorH1CotangentOfFlat_tmul, one_smul]
    let eB : Aₛ ⊗[A] B ≃ₐ[Aₛ] B := IsLocalization.algebraLid S Aₛ B
    letI : Algebra B (Aₛ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI := eB.toRingHom.toAlgebra
    letI : IsScalarTower Aₛ (Aₛ ⊗[A] B) B :=
      .of_algebraMap_eq' (((eB : Aₛ ⊗[A] B →ₐ[Aₛ] B)).comp_algebraMap).symm
    letI : TensorProduct.CompatibleSMul A Aₛ Aₛ B :=
      IsLocalization.tensorProduct_compatibleSMul S Aₛ Aₛ B
    letI : IsScalarTower B (Aₛ ⊗[A] B) B := .of_algebraMap_eq fun b ↦ by
      change b = eB (1 ⊗ₜ[A] b)
      simpa [IsLocalization.algebraLid] using
        (Algebra.TensorProduct.lidOfCompatibleSMul_tmul A Aₛ B (1 : Aₛ) b).symm
    simp only [H1Cotangent.mapEquiv, LinearEquiv.coe_mk, H1Cotangent.map]
    let f1 := ((Generators.self A B).defaultHom (Generators.self Aₛ (Aₛ ⊗[A] B))).toExtensionHom
    let f2 := ((Generators.self Aₛ (Aₛ ⊗[A] B)).defaultHom (Generators.self Aₛ B)).toExtensionHom
    let f := ((Generators.self A B).defaultHom (Generators.self Aₛ B)).toExtensionHom
    have hcomp := (Extension.H1Cotangent.map_comp_apply f1 f2 x).symm
    have hEq : Extension.H1Cotangent.map (f2.comp f1) = Extension.H1Cotangent.map f :=
      Extension.H1Cotangent.map_eq _ _
    exact hcomp.trans (by simpa using congrArg (fun g ↦ g x) hEq)
  have hmap : (e : H1Cotangent A B → H1Cotangent Aₛ B) = H1Cotangent.map A Aₛ B B := funext h
  simpa [hmap] using e.bijective

end

/-! ### Lemma_10_134_12 (from Chap10) -/
open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent TensorProduct

universe u v

noncomputable section

section

variable (A : Type u) (B : Type v) (Bg : Type v)
variable [CommRing A] [CommRing B] [CommRing Bg]
variable [Algebra A B] [Algebra A Bg] [Algebra B Bg]
variable [IsScalarTower A B Bg]
variable (g : B) [IsLocalization.Away g Bg]

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] TensorProduct.rightAlgebra

private noncomputable abbrev scalarExtendedNaiveCotangent :
    ChainComplex (ModuleCat Bg) ℕ :=
  ((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (NL_{B⁄A})

/- Domain triage:
* primary domain: naive cotangent complexes under localization of the target algebra.
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the Chapter 10 owner `NL_{-⁄-}`;
  - `Algebra.Generators.localizationAway`, the canonical presentation of an arbitrary
    away-localization target;
  - `Algebra.Generators.cotangentCompLocalizationAwayEquiv`, the presentation-level splitting of
    the localized conormal module;
  - `Algebra.Extension.CotangentSpace.compEquiv`, the matching presentation-level splitting of the
    localized cotangent-space term.
* best owner abstraction: the public source-facing statement should still be about the canonical
  comparison map from the literal scalar extension of `NL_{B⁄A}` from `B` to `Bg`, written
  `NL_{B⁄A} ⊗[B] B_g`, to the owner `NL_{Bg⁄A}` for an arbitrary localization target `Bg` with
  `[IsLocalization.Away g Bg]`. The localization presentation obtained by adjoining an inverse of
  `g` is bridge data used only to define that comparison map.
* primitive vs. derived:
  - primitive data: the algebra map `A → B`, the away-localization target `Bg`, and the owner
    complexes `NL_{B⁄A}` and `NL_{Bg⁄A}`;
  - derived API: the private tensor-model bridge and the canonical chain map through the localized
    self-presentation.
* layer triage:
  - `source-facing`: the canonical map `NL_{B⁄A} ⊗[B] Bg → NL_{Bg⁄A}`;
  - `core/canonical`: `NL_{B⁄A}` and `NL_{Bg⁄A}`;
  - `bridge/view`: the localized self-presentation
    `(Generators.localizationAway Bg g).comp (Generators.self A B)`.
-/

private noncomputable abbrev selfExtension :
    Extension A B :=
  (Generators.self A B).toExtension

private abbrev selfLiftCotangent : Type (max u v) :=
  ULift.{v, max u v} (selfExtension A B).Cotangent

private noncomputable abbrev selfLiftCotangentEquiv :
    selfLiftCotangent A B ≃ₗ[B] (selfExtension A B).Cotangent :=
  ULift.moduleEquiv

private noncomputable abbrev localizedSelfGenerators :
    Generators A Bg (Unit ⊕ B) :=
  (Generators.localizationAway Bg g).comp (Generators.self A B)

/-- Private bridge/view model for `NL_{B⁄A} ⊗[B] Bg` with the degree-`1` term normalized from
`Bg ⊗[B] ULift P.Cotangent` to `Bg ⊗[B] P.Cotangent`. -/
private noncomputable def tensorNaiveCotangentAwayModel :
    ChainComplex (ModuleCat Bg) ℕ :=
  let P := selfExtension A B
  ChainComplex.mk'
    (ModuleCat.of Bg (Bg ⊗[B] P.CotangentSpace))
    (ModuleCat.of Bg (Bg ⊗[B] P.Cotangent))
    (ModuleCat.ofHom (LinearMap.baseChange Bg P.cotangentComplex))
    (fun {_ _} _ ↦ ⟨ModuleCat.of Bg PUnit, 0, zero_comp⟩)

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap B Bg)).obj (ModuleCat.of Bg Bg)) ≃ₗ[Bg] Bg :=
  { __ := AddEquiv.refl Bg
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower B Bg ↑((ModuleCat.restrictScalars (algebraMap B Bg)).obj (ModuleCat.of Bg Bg)) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    rfl

private noncomputable def scalarExtendedPUnitIso :
    (ModuleCat.extendScalars (algebraMap B Bg)).obj (ModuleCat.of B PUnit) ≅
      ModuleCat.of Bg PUnit := by
  let e₁ :
      (ModuleCat.extendScalars (algebraMap B Bg)).obj (ModuleCat.of B PUnit) ≅
        ModuleCat.of Bg (Bg ⊗[B] PUnit) := by
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv B Bg)
        (LinearEquiv.refl B PUnit)).toModuleIso
  letI : Subsingleton (Bg ⊗[B] PUnit) := inferInstance
  let e₂ : ModuleCat.of Bg (Bg ⊗[B] PUnit) ≅ ModuleCat.of Bg PUnit :=
    (LinearEquiv.ofSubsingleton _ _).toModuleIso
  exact e₁ ≪≫ e₂

omit [Algebra A Bg] [IsScalarTower A B Bg] in
private theorem tensorNaiveCotangentAwayModel_d_succ_succ
    (n : ℕ) :
    (tensorNaiveCotangentAwayModel A B Bg).d (n + 2) (n + 1) = 0 := by
  rw [tensorNaiveCotangentAwayModel, ChainComplex.mk'_d]
  ext x
  rfl

omit [Algebra A Bg] [IsScalarTower A B Bg] in
private theorem naiveCotangentTensor_d_succ_succ
    (n : ℕ) :
    (scalarExtendedNaiveCotangent A B Bg).d (n + 2) (n + 1) = 0 := by
  rw [scalarExtendedNaiveCotangent, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    Extension.naiveCotangentChainComplex_d_succ_succ (selfExtension A B) n]
  simpa using CategoryTheory.Functor.map_zero (ModuleCat.extendScalars (algebraMap B Bg))
    ((NL_{B⁄A}).X (n + 2)) ((NL_{B⁄A}).X (n + 1))

private noncomputable def naiveCotangentTensorToTensorModelXIso :
    ∀ n : ℕ,
      (scalarExtendedNaiveCotangent A B Bg).X n ≅
        (tensorNaiveCotangentAwayModel A B Bg).X n
  | 0 => by
      let P := selfExtension A B
      simpa [scalarExtendedNaiveCotangent, tensorNaiveCotangentAwayModel, Algebra.naiveCotangent, P,
        Extension.naiveCotangentChainComplex, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv B Bg)
          (LinearEquiv.refl B P.CotangentSpace)).toModuleIso
  | 1 => by
      let P := selfExtension A B
      simpa [scalarExtendedNaiveCotangent, tensorNaiveCotangentAwayModel,
        Algebra.naiveCotangent, P, Extension.naiveCotangentChainComplex, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv B Bg)
          (selfLiftCotangentEquiv A B)).toModuleIso
  | n + 2 => by
      let P := selfExtension A B
      let succZero :
          ∀ {X₀ X₁ : ModuleCat Bg} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat Bg) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of Bg PUnit, 0, zero_comp⟩
      let succZeroB :
          ∀ {X₀ X₁ : ModuleCat B} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, zero_comp⟩
      have hsrc :
          (scalarExtendedNaiveCotangent A B Bg).X (n + 2) ≅
            ModuleCat.of Bg PUnit := by
        let hX :
            (scalarExtendedNaiveCotangent A B Bg).X (n + 2) =
              (ModuleCat.extendScalars (algebraMap B Bg)).obj ((NL_{B⁄A}).X (n + 2)) :=
          CategoryTheory.Functor.mapHomologicalComplex_obj_X
            (ModuleCat.extendScalars (algebraMap B Bg)) (ComplexShape.down ℕ) (NL_{B⁄A}) (n + 2)
        have hmk : (NL_{B⁄A}).X (n + 2) ≅ ModuleCat.of B PUnit := by
          simpa [Algebra.naiveCotangent, P, Extension.naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of B P.CotangentSpace)
              (ModuleCat.of B (selfLiftCotangent A B))
              (ModuleCat.ofHom
                (P.cotangentComplex.comp (selfLiftCotangentEquiv A B).toLinearMap))
              succZeroB n)
        simpa [scalarExtendedNaiveCotangent] using
          eqToIso hX ≪≫ (ModuleCat.extendScalars (algebraMap B Bg)).mapIso hmk ≪≫
            scalarExtendedPUnitIso B Bg
      have htrg :
          (tensorNaiveCotangentAwayModel A B Bg).X (n + 2) ≅
            ModuleCat.of Bg PUnit := by
        simpa [tensorNaiveCotangentAwayModel, P] using
          (ChainComplex.mk'XIso
            (ModuleCat.of Bg (Bg ⊗[B] P.CotangentSpace))
            (ModuleCat.of Bg (Bg ⊗[B] P.Cotangent))
            (ModuleCat.ofHom (LinearMap.baseChange Bg P.cotangentComplex))
            succZero n)
      exact hsrc ≪≫ htrg.symm

omit [Algebra A Bg] [IsScalarTower A B Bg] in
private theorem naiveCotangentTensorToTensorModelXIso_comm :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (naiveCotangentTensorToTensorModelXIso A B Bg i).hom ≫
          (tensorNaiveCotangentAwayModel A B Bg).d i j =
        (scalarExtendedNaiveCotangent A B Bg).d i j ≫
          (naiveCotangentTensorToTensorModelXIso A B Bg j).hom := by
  intro i j hij
  subst i
  cases j with
  | zero =>
      let P := selfExtension A B
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · have hL :
            (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        have hR :
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        exact hL.trans hR.symm
      · intro t x
        rcases x with ⟨x⟩
        change
          (LinearMap.baseChange Bg P.cotangentComplex)
              ((TensorProduct.AlgebraTensorModule.congr
                  (restrictScalarsSelfEquiv B Bg)
                  (selfLiftCotangentEquiv A B))
                (t ⊗ₜ[B] ULift.up x)) =
            (LinearMap.baseChange Bg
              (P.cotangentComplex.comp
                (selfLiftCotangentEquiv A B).toLinearMap))
              (t ⊗ₜ[B] ULift.up x)
        rfl
      · intro x y hx hy
        calc
          (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
              (x + y) =
          (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
                x +
              (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
                y := by
                  simpa using
                    (LinearMap.map_add
                      (ModuleCat.Hom.hom
                        ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                          (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
                      x y)
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
                x +
              (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
                y := by rw [hx, hy]
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
              (x + y) := by
                simpa using
                  (LinearMap.map_add
                    (ModuleCat.Hom.hom
                      ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                        (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
                    x y).symm
  | succ j =>
      rw [show (tensorNaiveCotangentAwayModel A B Bg).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using tensorNaiveCotangentAwayModel_d_succ_succ
              A B Bg j,
        show (scalarExtendedNaiveCotangent A B Bg).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using naiveCotangentTensor_d_succ_succ
              A B Bg j]
      ext x
      have hL :
          (ModuleCat.Hom.hom
              ((naiveCotangentTensorToTensorModelXIso A B Bg (j + 2)).hom ≫
                (0 : (tensorNaiveCotangentAwayModel A B Bg).X (j + 2) ⟶
                  (tensorNaiveCotangentAwayModel A B Bg).X (j + 1))))
            x = 0 := by
        rfl
      have hR :
          (ModuleCat.Hom.hom
              ((0 : (scalarExtendedNaiveCotangent A B Bg).X (j + 2) ⟶
                (scalarExtendedNaiveCotangent A B Bg).X (j + 1)) ≫
                (naiveCotangentTensorToTensorModelXIso A B Bg (j + 1)).hom))
            x = 0 := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
        change (ModuleCat.Hom.hom (naiveCotangentTensorToTensorModelXIso A B Bg (j + 1)).hom) 0 = 0
        simpa using
          (LinearMap.map_zero
            (ModuleCat.Hom.hom (naiveCotangentTensorToTensorModelXIso A B Bg (j + 1)).hom))
      simpa [Nat.add_assoc] using hL.trans hR.symm

private noncomputable def naiveCotangentTensorToTensorModelIso :
    scalarExtendedNaiveCotangent A B Bg ≅
      tensorNaiveCotangentAwayModel A B Bg :=
  HomologicalComplex.Hom.isoOfComponents
    (naiveCotangentTensorToTensorModelXIso A B Bg)
    (naiveCotangentTensorToTensorModelXIso_comm A B Bg)

private theorem tensorToLocalizedSelfPresentation_cotangentComplex_apply
    (x : Bg ⊗[B] (selfExtension A B).Cotangent) :
    ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex)
        (LinearMap.liftBaseChange Bg
          (Extension.Cotangent.map
            ((Generators.localizationAway Bg g).toComp
              (Generators.self A B)).toExtensionHom) x) =
      ((Extension.CotangentSpace.map
          ((Generators.localizationAway Bg g).toComp
            (Generators.self A B)).toExtensionHom).liftBaseChange Bg)
        (LinearMap.baseChange Bg
          ((selfExtension A B).cotangentComplex) x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro t y
    rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.baseChange_tmul,
      LinearMap.liftBaseChange_tmul]
    exact congrArg (fun z ↦ t • z)
      (Extension.CotangentSpace.map_cotangentComplex
        ((Generators.localizationAway Bg g).toComp
          (Generators.self A B)).toExtensionHom y).symm
  · intro x y hx hy
    simp [map_add, hx, hy]

private noncomputable def tensorToLocalizedSelfPresentation :
    tensorNaiveCotangentAwayModel A B Bg ⟶
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex :=
  let P := selfExtension A B
  let Q := Generators.localizationAway Bg g
  let C := (localizedSelfGenerators A B Bg g).toExtension
  ChainComplex.mkHom _ _
    (ModuleCat.ofHom
      (LinearMap.liftBaseChange Bg
        (Extension.CotangentSpace.map (Q.toComp (Generators.self A B)).toExtensionHom)))
    (ModuleCat.ofHom
      (((ULift.moduleEquiv :
            ULift C.Cotangent ≃ₗ[Bg] C.Cotangent).symm.toLinearMap) ∘ₗ
        LinearMap.liftBaseChange Bg
          (Extension.Cotangent.map (Q.toComp (Generators.self A B)).toExtensionHom)))
    (by
      ext x
      change
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex)
            (LinearMap.liftBaseChange Bg
              (Extension.Cotangent.map
                ((Generators.localizationAway Bg g).toComp
                  (Generators.self A B)).toExtensionHom) x) =
          ((Extension.CotangentSpace.map
              ((Generators.localizationAway Bg g).toComp
                (Generators.self A B)).toExtensionHom).liftBaseChange Bg)
            (LinearMap.baseChange Bg
              ((selfExtension A B).cotangentComplex) x)
      simpa [tensorNaiveCotangentAwayModel, selfExtension, localizedSelfGenerators,
        LinearMap.comp_assoc] using
        tensorToLocalizedSelfPresentation_cotangentComplex_apply A B Bg g x)
    (by
      intro n h
      refine ⟨0, ?_⟩
      rw [tensorNaiveCotangentAwayModel_d_succ_succ A B Bg n,
        Extension.naiveCotangentChainComplex_d_succ_succ
          ((localizedSelfGenerators A B Bg g).toExtension) n]
      simp)

/-- The canonical chain map
`NL_{B⁄A} ⊗[B] Bg ⟶ NL_{Bg⁄A}` obtained by localizing the
canonical self-presentation of `B` away from `g` and then comparing that localized presentation
with the owner self-presentation of the chosen away-localization target `Bg`. -/
noncomputable def naiveCotangent_tensor_comparison_of_isLocalizationAway :
    (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NL_{B⁄A})) ⟶
      NL_{Bg⁄A} :=
  let f :
      (localizedSelfGenerators A B Bg g).toExtension.Hom
        (Generators.self A Bg).toExtension :=
    (Generators.defaultHom
      (localizedSelfGenerators A B Bg g)
      (Generators.self A Bg)).toExtensionHom
  (naiveCotangentTensorToTensorModelIso A B Bg).hom ≫
    tensorToLocalizedSelfPresentation A B Bg g ≫
    Extension.naiveCotangentChainMap f

-- Proof sketch: let `P := Generators.self A B`, and let `β` be the localized presentation
-- `(Generators.localizationAway Bg g).comp P` of `Bg` obtained by adjoining an inverse of `g`.
-- Mathlib's `cotangentCompLocalizationAwayEquiv` and `CotangentSpace.compEquiv` identify the
-- conormal and cotangent-space terms of `β` with the tensorized terms of `NL_{B⁄A}` plus the
-- contractible localization-away summand. The resulting comparison
-- `NL_{B⁄A} ⊗[B] Bg → β.naiveCotangentChainComplex` is therefore a homotopy equivalence, and the
-- canonical presentation-independence map from `β.naiveCotangentChainComplex` to the owner
-- `NL_{Bg⁄A}` is a homotopy equivalence as well. Passing to the homotopy category packages the
-- source statement as the claim that the canonical comparison morphism becomes an isomorphism.
private theorem naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso_aux :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map
        (naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g)) := by
  sorry

/-- Lemma 10.134.12: for any away-localization target `Bg` of `B` at `g`, the canonical
comparison map
`NL_{B⁄A} ⊗[B] Bg ⟶ NL_{Bg⁄A}`
is a homotopy equivalence. -/
noncomputable def naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv :
    HomotopyEquiv
      (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (NL_{B⁄A}))
      NL_{Bg⁄A} := by
  let f := naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g
  letI :
      IsIso
        ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map f) :=
    naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso_aux A B Bg g
  let e :
      HomotopyEquiv
        (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (NL_{B⁄A}))
        NL_{Bg⁄A} :=
    HomotopyCategory.homotopyEquivOfIso <|
      asIso ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map f)
  have h : Homotopy e.hom f := by
    simpa [e, f, HomotopyCategory.homotopyEquivOfIso] using
      (HomotopyCategory.homotopyOutMap f)
  exact
    { hom := f
      inv := e.inv
      homotopyHomInvId := (h.symm.compRight e.inv).trans e.homotopyHomInvId
      homotopyInvHomId := (h.compLeft e.inv).symm.trans e.homotopyInvHomId }

/-- Companion: the homotopy-category image of the canonical comparison map from
`Lemma 10.134.12` is an isomorphism. -/
theorem naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map
        (naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g)) := by
  let e := naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv A B Bg g
  change IsIso (HomotopyCategory.isoOfHomotopyEquiv e).hom
  infer_instance

end

/-! ### Lemma_10_134_13 (from Chap10) -/
/- Domain-style sampling:
- primary domain: localization/base change for first cotangent homology of commutative algebras;
- sampled owner declarations:
  `Algebra.H1Cotangent.map`,
  `Algebra.tensorH1CotangentOfFlat`,
  `Algebra.tensorH1CotangentOfIsLocalization`,
  `Algebra.H1Cotangent.isLocalizedModule`;
- best owner abstraction: `Algebra.tensorH1CotangentOfIsLocalization`;
- primitive data: a commutative `A`-algebra `B` together with a multiplicative subset
  `S : Submonoid B`;
- derived API: the canonical localization equivalence on `H¹(L_{B/A})`;
- layer triage:
  - `source-facing`: the quasi-isomorphism
    `NL_{B/A} ⊗_B S⁻¹B → NL_{S⁻¹B/A}`;
  - `core/canonical`: `Algebra.tensorH1CotangentOfIsLocalization`;
  - `bridge/view`: none; this item is a direct owner recall.
-/

/- Lemma 10.134.13: localizing the first cotangent homology along a multiplicative subset
`S ⊂ B` identifies it with the first cotangent homology of the localization `S⁻¹B`. This is the
library-facing consequence of the source statement that the canonical map
`NL_{B/A} ⊗_B S⁻¹B → NL_{S⁻¹B/A}` is a quasi-isomorphism. -/
recall Algebra.tensorH1CotangentOfIsLocalization

/-! ### Lemma_10_134_14 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe u v

noncomputable section

/- Domain-style sampling:
* primary domain: two-term complexes encoded by short complexes with vanishing second
  differential, and transported from chain complexes through `K.sc 0`;
* sampled owner declarations:
  - `HomologicalComplex.shortComplexFunctor` and `HomologicalComplex.sc`,
    which package the degree-`0` two-term view of a chain complex;
  - `ShortComplex.HomotopyEquiv`, the canonical owner for homotopy equivalences of those
    two-term objects;
  - `Homotopy.toShortComplex`, which transports chain homotopies to the associated short
    complexes;
  - `HomologicalComplex.XIsoOfEq`, the owner-level transport used to identify the degree-`0`
    short-complex terms with `A.X 1` and `A.X 0`;
  - `HomologicalComplex.sc`, used only as the bridge from the chain-complex presentation back to
    the short-complex owner.
* best owner abstraction: the stable block morphism and isomorphism belong at the
  `ShortComplex.HomotopyEquiv` level, under the intrinsic two-term hypothesis `g = 0`; the
  chain-complex statement is then only the thin transport along `A.sc 0` and `B.sc 0`.
* layer triage:
  - `source-facing`: the stable block morphism for short complexes with zero second differential;
  - `core/canonical`: `ShortComplex.HomotopyEquiv`;
  - `bridge/view`: the chain-complex morphism `A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0` obtained from
    `(A.sc 0)` and `(B.sc 0)`.
-/

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Helper for Lemma 10.134.14: in degree `0`, the extra `h₀` term produced by
`Homotopy.toShortComplex` factors through degree `2`, so it vanishes as soon as the target is
zero there. -/
private lemma chain_homotopy_toSc0_h₀_eq_zero
    {A B : ChainComplex C ℕ} {f g : A ⟶ B} (ho : Homotopy f g) (hB₂ : IsZero (B.X 2)) :
    (ho.toShortComplex 0).h₀ = 0 := by
  -- At `i = 0`, the defining branch of `toShortComplex` uses the degree-`2` component.
  have hzero : ho.hom 1 2 = 0 := hB₂.eq_of_tgt _ _
  have hcomp : ho.hom 1 2 ≫ B.d 2 1 = 0 := by
    rw [hzero, zero_comp]
  have hprev0 : (ComplexShape.down ℕ).prev 0 = 1 := by
    simp [ChainComplex.prev]
  have hprev1 : (ComplexShape.down ℕ).prev ((ComplexShape.down ℕ).prev 0) = 2 := by
    rw [hprev0]
    simp [ChainComplex.prev]
  have hprev_one : (ComplexShape.down ℕ).prev 1 = 2 := by
    simp [ChainComplex.prev]
  dsimp [Homotopy.toShortComplex]
  rw [if_pos (by simp)]
  have hzero' :
      ho.hom ((ComplexShape.down ℕ).prev 0)
        ((ComplexShape.down ℕ).prev ((ComplexShape.down ℕ).prev 0)) = 0 := by
    rw [hprev0]
    rw [hprev_one]
    exact hzero
  rw [hzero', zero_comp]
  rfl

namespace ShortComplex

variable [HasBinaryBiproducts C]
variable {S T : ShortComplex C}

/-- The stable block morphism attached to a homotopy equivalence of two-term short complexes. -/
noncomputable def stableBiprodHom (e : S.HomotopyEquiv T) :
    S.X₁ ⊞ T.X₂ ⟶ T.X₁ ⊞ S.X₂ :=
  biprod.lift
    (biprod.desc e.hom.τ₁ e.homotopyInvHomId.h₁)
    (biprod.desc S.f e.inv.τ₂)

private noncomputable def stableBiprodInv (e : S.HomotopyEquiv T) :
    T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ :=
  biprod.lift
    (biprod.desc e.inv.τ₁ (-e.homotopyHomInvId.h₁))
    (biprod.desc (-T.f) e.hom.τ₂)

/-- Helper for Lemma 10.134.14: normalize the forward block morphism as a biproduct matrix so
the source proof can be read entrywise. -/
lemma stableBiprodHom_eq_ofComponents (e : S.HomotopyEquiv T) :
    stableBiprodHom e =
      Biprod.ofComponents e.hom.τ₁ S.f e.homotopyInvHomId.h₁ e.inv.τ₂ := by
  -- We freeze the four matrix entries of `stableBiprodHom` once so later calculations can use
  -- the source proof's block notation instead of repeated `biprod.lift`/`biprod.desc` expansion.
  rw [← Biprod.ofComponents_eq (stableBiprodHom e)]
  simp [stableBiprodHom]

/-- Helper for Lemma 10.134.14: normalize the backward block morphism as a biproduct matrix so
the source proof can be compared directly with the Lean block map. -/
lemma stableBiprodInv_eq_ofComponents (e : S.HomotopyEquiv T) :
    stableBiprodInv e =
      Biprod.ofComponents e.inv.τ₁ (-T.f) (-e.homotopyHomInvId.h₁) e.hom.τ₂ := by
  -- As above, we expose the four entries explicitly before attempting the matrix computation.
  rw [← Biprod.ofComponents_eq (stableBiprodInv e)]
  simp [stableBiprodInv]

/-- Helper for Lemma 10.134.14: the forward-then-backward block product is the lower unipotent
automorphism predicted by the source proof once the extra diagonal `h₀` term disappears. -/
lemma stableBiprodHom_comp_stableBiprodInv_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hT : T.g = 0) (h0S : e.homotopyHomInvId.h₀ = 0) :
    stableBiprodHom e ≫ stableBiprodInv e =
      (Biprod.unipotentLower
        (e.homotopyInvHomId.h₁ ≫ e.inv.τ₁ - e.inv.τ₂ ≫ e.homotopyHomInvId.h₁)).hom := by
  -- We translate the composite into a four-entry block matrix before simplifying each entry.
  rw [stableBiprodHom_eq_ofComponents, stableBiprodInv_eq_ofComponents, Biprod.ofComponents_comp]
  -- The off-diagonal zero and diagonal identities come from the morphism and homotopy equations.
  ext <;> simp [Biprod.unipotentLower, e.hom.comm₁₂]
  · -- The `(1,1)` entry is the identity after cancelling the homotopy correction.
    rw [show e.hom.τ₁ ≫ e.inv.τ₁ =
        S.f ≫ e.homotopyHomInvId.h₁ + e.homotopyHomInvId.h₀ + 𝟙 S.X₁ by
          simpa using e.homotopyHomInvId.comm₁, h0S]
    abel
  · abel
  · -- The `(2,2)` entry is the identity because `T.g = 0` kills the extra term in `comm₂`.
    rw [show e.inv.τ₂ ≫ e.hom.τ₂ =
        T.g ≫ e.homotopyInvHomId.h₂ + e.homotopyInvHomId.h₁ ≫ T.f + 𝟙 T.X₂ by
          simpa using e.homotopyInvHomId.comm₂, hT, zero_comp]
    abel

/-- Helper for Lemma 10.134.14: the backward-then-forward block product is the symmetric lower
unipotent automorphism from the source proof after the degree-`2` diagonal term vanishes. -/
lemma stableBiprodInv_comp_stableBiprodHom_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    stableBiprodInv e ≫ stableBiprodHom e =
      (Biprod.unipotentLower
        (e.hom.τ₂ ≫ e.homotopyInvHomId.h₁ - e.homotopyHomInvId.h₁ ≫ e.hom.τ₁)).hom := by
  -- This is the same entrywise block computation with `S` and `T` interchanged.
  rw [stableBiprodInv_eq_ofComponents, stableBiprodHom_eq_ofComponents, Biprod.ofComponents_comp]
  ext <;> simp [Biprod.unipotentLower, e.inv.comm₁₂]
  · -- The `(1,1)` entry is the identity after the target-side homotopy correction cancels.
    rw [show e.inv.τ₁ ≫ e.hom.τ₁ =
        T.f ≫ e.homotopyInvHomId.h₁ + e.homotopyInvHomId.h₀ + 𝟙 T.X₁ by
          simpa using e.homotopyInvHomId.comm₁, h0T]
    abel
  · abel
  · -- The `(2,2)` entry is the identity because `S.g = 0` removes the extra `comm₂` term.
    rw [show e.hom.τ₂ ≫ e.inv.τ₂ =
        S.g ≫ e.homotopyHomInvId.h₂ + e.homotopyHomInvId.h₁ ≫ S.f + 𝟙 S.X₂ by
          simpa using e.homotopyHomInvId.comm₂, hS, zero_comp]
    abel

/-- Helper for Lemma 10.134.14: after correcting the naive backward block map by the inverse
unipotent factors coming from the two block products, the forward block morphism becomes an
isomorphism. -/
theorem stableBiprodHom_isIso_of_h₀_eq_zero
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (hT : T.g = 0)
    (h0S : e.homotopyHomInvId.h₀ = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    IsIso (stableBiprodHom e) := by
  -- The source proof shows that the naive inverse works up to lower-unipotent corrections.
  let U : S.X₁ ⊞ T.X₂ ≅ S.X₁ ⊞ T.X₂ :=
    Biprod.unipotentLower
      (e.homotopyInvHomId.h₁ ≫ e.inv.τ₁ - e.inv.τ₂ ≫ e.homotopyHomInvId.h₁)
  let V : T.X₁ ⊞ S.X₂ ≅ T.X₁ ⊞ S.X₂ :=
    Biprod.unipotentLower
      (e.hom.τ₂ ≫ e.homotopyInvHomId.h₁ - e.homotopyHomInvId.h₁ ≫ e.hom.τ₁)
  let rightInv : T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ := stableBiprodInv e ≫ U.inv
  let leftInv : T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ := V.inv ≫ stableBiprodInv e
  have hright : stableBiprodHom e ≫ rightInv = 𝟙 _ := by
    -- The right correction removes the unipotent defect on `stableBiprodHom ≫ stableBiprodInv`.
    calc
      stableBiprodHom e ≫ rightInv = (stableBiprodHom e ≫ stableBiprodInv e) ≫ U.inv := by
        simp [rightInv, Category.assoc]
      _ = 𝟙 _ := by
        rw [stableBiprodHom_comp_stableBiprodInv_eq_unipotentLower e hT h0S, Iso.hom_inv_id]
  have hleft : leftInv ≫ stableBiprodHom e = 𝟙 _ := by
    -- The left correction removes the symmetric defect on the other composite.
    calc
      leftInv ≫ stableBiprodHom e = V.inv ≫ (stableBiprodInv e ≫ stableBiprodHom e) := by
        simp [leftInv, Category.assoc]
      _ = 𝟙 _ := by
        rw [stableBiprodInv_comp_stableBiprodHom_eq_unipotentLower e hS h0T, Iso.inv_hom_id]
  have hsame : leftInv = rightInv := by
    -- Any left inverse and right inverse of the same map must coincide.
    calc
      leftInv = leftInv ≫ 𝟙 _ := by simp
      _ = leftInv ≫ (stableBiprodHom e ≫ rightInv) := by rw [hright]
      _ = (leftInv ≫ stableBiprodHom e) ≫ rightInv := by simp [Category.assoc]
      _ = rightInv := by rw [hleft, Category.id_comp]
  -- Packaging the common inverse yields the desired `IsIso` witness.
  exact ⟨⟨leftInv, by simpa [hsame] using hright, hleft⟩⟩

end ShortComplex

variable {A B : ChainComplex C ℕ}

/-- The degree-`0` short-complex homotopy equivalence induced by a chain-complex homotopy
equivalence. This is the thin bridge from the chain-complex owner `HomotopyEquiv` to the
short-complex owner `ShortComplex.HomotopyEquiv`. -/
private noncomputable def HomotopyEquiv.toSc0 (e : HomotopyEquiv A B) :
    ShortComplex.HomotopyEquiv (A.sc 0) (B.sc 0) where
  hom := (shortComplexFunctor C (ComplexShape.down ℕ) 0).map e.hom
  inv := (shortComplexFunctor C (ComplexShape.down ℕ) 0).map e.inv
  homotopyHomInvId := e.homotopyHomInvId.toShortComplex 0
  homotopyInvHomId := e.homotopyInvHomId.toShortComplex 0

/-- The associated degree-`0` short complexes of a chain complex have zero second differential. -/
private lemma sc0_g_eq_zero (A : ChainComplex C ℕ) : (A.sc 0).g = 0 := by
  change A.d 0 ((ComplexShape.down ℕ).next 0) = 0
  simp

section

variable [HasBinaryBiproducts C]

private noncomputable def sourceBiprodIso (A B : ChainComplex C ℕ) :
    (A.sc 0).X₁ ⊞ (B.sc 0).X₂ ≅ A.X 1 ⊞ B.X 0 :=
  biprod.mapIso
    (A.XIsoOfEq <| by simp)
    (B.XIsoOfEq <| by simp)

private noncomputable def targetBiprodIso (A B : ChainComplex C ℕ) :
    (B.sc 0).X₁ ⊞ (A.sc 0).X₂ ≅ B.X 1 ⊞ A.X 0 :=
  biprod.mapIso
    (B.XIsoOfEq <| by simp)
    (A.XIsoOfEq <| by simp)

/-- The source-facing block morphism `A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0` induced by a homotopy
equivalence of chain complexes. It is the bridge/view obtained by transporting
`ShortComplex.stableBiprodHom (e.toSc0)` along the degree-`1` / degree-`0` identifications for
`A.sc 0` and `B.sc 0`. -/
noncomputable def term_complex_biprod_hom (e : HomotopyEquiv A B) :
    A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0 :=
  (sourceBiprodIso A B).inv ≫ ShortComplex.stableBiprodHom (e.toSc0) ≫ (targetBiprodIso A B).hom

/-- Lemma 10.134.14: if chain complexes in a preadditive category with binary biproducts are
homotopy equivalent, then the canonical block morphism
`A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0` induced by a homotopy equivalence is invertible. This is the
transport of the owner-level stable isomorphism for the associated two-term short complexes
`A.sc 0` and `B.sc 0`. -/
theorem term_complex_biprod_hom_isIso
    (hA : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → IsZero (A.X n))
    (hB : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → IsZero (B.X n))
    (e : HomotopyEquiv A B) :
    IsIso (term_complex_biprod_hom e) := by
  -- Route correction: we keep the source block-matrix argument, but execute it on `A.sc 0` and
  -- `B.sc 0`, where the concentration hypotheses kill the extra `toShortComplex` diagonal terms.
  have hA₂ : IsZero (A.X 2) := hA 2 (by norm_num) (by norm_num)
  have hB₂ : IsZero (B.X 2) := hB 2 (by norm_num) (by norm_num)
  have h0A : (e.homotopyHomInvId.toShortComplex 0).h₀ = 0 :=
    chain_homotopy_toSc0_h₀_eq_zero e.homotopyHomInvId hA₂
  have h0B : (e.homotopyInvHomId.toShortComplex 0).h₀ = 0 :=
    chain_homotopy_toSc0_h₀_eq_zero e.homotopyInvHomId hB₂
  -- The owner-level short-complex block map is invertible, so its transport is too.
  letI : IsIso (ShortComplex.stableBiprodHom (e.toSc0)) :=
    ShortComplex.stableBiprodHom_isIso_of_h₀_eq_zero (e.toSc0)
      (sc0_g_eq_zero A) (sc0_g_eq_zero B) h0A h0B
  change IsIso
    ((((sourceBiprodIso A B).symm ≪≫ asIso (ShortComplex.stableBiprodHom (e.toSc0)) ≪≫
        targetBiprodIso A B).hom))
  infer_instance


end

end

/-! ### Lemma_10_134_15 (from Chap10) -/
open Algebra
open Algebra.Generators
open Algebra.Extension
open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {n m : ℕ}
variable {ι ι' : Type u}

/- Domain-style sampling:
* primary domain: finite algebra presentations and their two-term cotangent complexes.
* sampled owner declarations:
  - `Generators.defaultHom`, the canonical comparison between two presentations;
  - `Extension.Cotangent.map_sub_map`, the homotopy identity on the conormal term;
  - `Extension.CotangentSpace.map_sub_map`, the parallel homotopy identity on the cotangent-space
    term;
  - `term_complex_biprod_hom`, the chapter owner extracting the stable block isomorphism from a
    two-term chain-complex homotopy equivalence.
* best owner abstraction: the primitive data are the extension-level naive cotangent complexes;
  the stable block equivalence is derived from the homotopy equivalence between those owner
  complexes, and the free-module surface is only a basis rewrite.
* primitive data vs. derived API:
  - primitive data: `P.naiveCotangentChainComplex` for `P : Extension.{u} R S`;
  - derived API: the stable equivalence between cotangent and cotangent-space summands;
  - bridge/view: the basis rewrite identifying cotangent spaces with finite free modules.
* layer triage:
  - `source-facing`: the textbook stabilization
    `I / I² ⊕ S^{⊕ m} ≃ J / J² ⊕ S^{⊕ n}`;
  - `core/canonical`: the stable block isomorphism for the two-term cotangent complexes;
  - `bridge/view`: the canonical basis coordinates on cotangent spaces.
-/

private abbrev LiftCotangent (P : Extension.{u} R S) :=
  ULift.{v, u} P.Cotangent

private noncomputable abbrev liftCotangentEquiv
    (P : Extension.{u} R S) :
    LiftCotangent P ≃ₗ[S] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def liftCotangentMap
    {P Q : Extension.{u} R S} (f : P.Hom Q) :
    LiftCotangent P →ₗ[S] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ Cotangent.map f ∘ₗ
    (liftCotangentEquiv P).toLinearMap

private noncomputable def liftCotangentHomotopyMap
    {P Q : Extension.{u} R S} (f g : P.Hom Q) :
    P.CotangentSpace →ₗ[S] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ f.sub g

private theorem liftCotangentMap_id (P : Extension.{u} R S) :
    liftCotangentMap (.id P) = LinearMap.id := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap]

private theorem liftCotangentMap_comp
    {P Q T : Extension.{u} R S} (f : P.Hom Q) (g : Q.Hom T) :
    liftCotangentMap (g.comp f) = (liftCotangentMap g).restrictScalars S ∘ₗ liftCotangentMap f := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap, Cotangent.map_comp, LinearMap.comp_assoc]

private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_not_rel0 (j : ℕ) : ¬ (ComplexShape.down ℕ).Rel 0 j := by
  simp [ComplexShape.down]

private noncomputable def naiveCotangentChainComplexXIsoPUnit
    (P : Extension.{u} R S) (i : ℕ) :
    P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{max u v} S PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{max u v} S} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{max u v} S) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{max u v} S PUnit, 0, zero_comp⟩
  simpa [Algebra.Extension.naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of.{max u v} S P.CotangentSpace)
      (ModuleCat.of.{max u v} S (LiftCotangent P))
      (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftCotangentEquiv P).toLinearMap))
      succZero i)

private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension.{u} R S) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  let e := naiveCotangentChainComplexXIsoPUnit P i
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{u} R S) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

private theorem naiveCotangentChainMap_id
    (P : Extension.{u} R S) :
    Extension.naiveCotangentChainMap (.id P) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (.id P)) =
        ModuleCat.ofHom (LinearMap.id : P.CotangentSpace →ₗ[S] P.CotangentSpace)
      congr
      exact Extension.CotangentSpace.map_id
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (.id P) x) : LiftCotangent P) =
            ULift.up x
          congr 1
          simp
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ P i
          ext x
          exact Subsingleton.elim _ _

private theorem naiveCotangentChainMap_comp
    {P Q T : Extension.{u} R S} (f : P.Hom Q) (g : Q.Hom T) :
    Extension.naiveCotangentChainMap (g.comp f) =
      Extension.naiveCotangentChainMap f ≫ Extension.naiveCotangentChainMap g := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (g.comp f)) =
        ModuleCat.ofHom ((CotangentSpace.map g).restrictScalars S ∘ₗ CotangentSpace.map f)
      congr
      exact Extension.CotangentSpace.map_comp f g
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (g.comp f) x) : LiftCotangent T) =
            ULift.up (Cotangent.map g (Cotangent.map f x))
          simp [Cotangent.map_comp]
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ T i
          ext x
          exact Subsingleton.elim _ _

private noncomputable def naiveCotangentChainHomotopyHom
    {P Q : Extension.{u} R S} (f g : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    P.naiveCotangentChainComplex.X i ⟶ Q.naiveCotangentChainComplex.X j := by
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero =>
          exact ModuleCat.ofHom (liftCotangentHomotopyMap f g)
      | succ j =>
          exact 0
  · exact 0

private theorem naiveCotangentChainMap_sub_eq_nullHomotopicMap
    {P Q : Extension.{u} R S} (f g : P.Hom Q) :
    Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g =
      Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 0 =
        (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 0
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left naiveCotangent_rel10
        naiveCotangent_not_rel0 (naiveCotangentChainHomotopyHom f g)]
      ext x
      simpa [Extension.naiveCotangentChainMap, naiveCotangentChainHomotopyHom,
        Algebra.Extension.naiveCotangentChainComplex, liftCotangentHomotopyMap,
        LinearMap.comp_assoc] using
        LinearMap.congr_fun (Extension.CotangentSpace.map_sub_map f g) x
  | succ i =>
      cases i with
      | zero =>
          change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 1 =
            (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 1
          rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10
            (naiveCotangentChainHomotopyHom f g)]
          ext x
          rcases x with ⟨x⟩
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            (ModuleCat.Hom.hom
                (P.naiveCotangentChainComplex.d 1 0 ≫
                  naiveCotangentChainHomotopyHom f g 0 1 naiveCotangent_rel10 +
                naiveCotangentChainHomotopyHom f g 1 2 naiveCotangent_rel21 ≫
                  Q.naiveCotangentChainComplex.d 2 1))
              { down := x }
          rw [Extension.naiveCotangentChainComplex_d_succ_succ Q 0,
            Extension.naiveCotangentChainComplex_d_1_0 P]
          simp [naiveCotangentChainHomotopyHom, liftCotangentHomotopyMap]
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            ULift.up ((f.sub g) (P.cotangentComplex x))
          rw [LinearMap.congr_fun (Extension.Cotangent.map_sub_map f g) x]
          rfl
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ Q i
          ext x
          exact Subsingleton.elim _ _

private noncomputable def naiveCotangentChainMapHomotopy
    {P Q : Extension.{u} R S} (f g : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f) (Extension.naiveCotangentChainMap g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (naiveCotangentChainMap_sub_eq_nullHomotopicMap f g)).trans
      (Homotopy.nullHomotopy' (naiveCotangentChainHomotopyHom f g)))

private noncomputable def defaultNaiveCotangentChainHomotopyEquiv
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    HomotopyEquiv P.toExtension.naiveCotangentChainComplex Q.toExtension.naiveCotangentChainComplex where
  hom := Extension.naiveCotangentChainMap (Generators.defaultHom P Q).toExtensionHom
  inv := Extension.naiveCotangentChainMap (Generators.defaultHom Q P).toExtensionHom
  homotopyHomInvId := by
    let f := (Generators.defaultHom P Q).toExtensionHom
    let g := (Generators.defaultHom Q P).toExtensionHom
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp f g).symm).trans
        ((naiveCotangentChainMapHomotopy (g.comp f) (.id P.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id P.toExtension)))
  homotopyInvHomId := by
    let f := (Generators.defaultHom P Q).toExtensionHom
    let g := (Generators.defaultHom Q P).toExtensionHom
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp g f).symm).trans
        ((naiveCotangentChainMapHomotopy (f.comp g) (.id Q.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id Q.toExtension)))

/-- The canonical basis equivalence identifying the cotangent space of a finite presentation with
its free module of generators. -/
private noncomputable abbrev presentationCotangentSpaceBasisEquiv
    {k : ℕ} (P : Generators R S (Fin k)) :
    P.toExtension.CotangentSpace ≃ₗ[S] (Fin k →₀ S) :=
  P.cotangentSpaceBasis.repr

/-- Helper for Lemma 10.134.15: the naive cotangent complex of an extension is zero in every
degree `i + 2`. -/
private theorem naiveCotangentChainComplex_isZero_of_succ_succ
    (P : Extension.{u} R S) (i : ℕ) :
    IsZero (P.naiveCotangentChainComplex.X (i + 2)) := by
  -- The higher terms are already known to be subsingletons, so the module object is zero.
  letI := naiveCotangentChainComplex_subsingleton_of_succ_succ P i
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 10.134.15: the naive cotangent complex of an extension is concentrated in
degrees `0` and `1`. -/
private theorem naiveCotangentChainComplex_concentrated_away_from_zero_one
    (P : Extension.{u} R S) (n : ℕ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    IsZero (P.naiveCotangentChainComplex.X n) := by
  -- Only the `n = i + 2` branch survives the case split; the other two are excluded by
  -- hypothesis.
  cases n with
  | zero =>
      exact False.elim (hn0 rfl)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim (hn1 rfl)
      | succ i =>
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            naiveCotangentChainComplex_isZero_of_succ_succ P i

/-- Helper for Lemma 10.134.15: a homotopy equivalence between naive cotangent complexes induces
an isomorphism on the stabilized degree-`1/0` block map from Lemma 10.134.14. -/
private theorem naiveCotangent_term_complex_biprod_hom_isIso
    {P Q : Extension.{u} R S}
    (e : HomotopyEquiv P.naiveCotangentChainComplex Q.naiveCotangentChainComplex) :
    IsIso (term_complex_biprod_hom e) := by
  -- Route correction: apply Lemma 10.134.14 through the explicit concentration API now required
  -- for the naive cotangent complexes.
  exact term_complex_biprod_hom_isIso
    (fun n hn0 hn1 ↦ naiveCotangentChainComplex_concentrated_away_from_zero_one P n hn0 hn1)
    (fun n hn0 hn1 ↦ naiveCotangentChainComplex_concentrated_away_from_zero_one Q n hn0 hn1)
    e

private noncomputable def naiveCotangentLiftCotangentSpaceStableEquiv
    {P Q : Extension.{u} R S}
    (e : HomotopyEquiv P.naiveCotangentChainComplex Q.naiveCotangentChainComplex) :
    (LiftCotangent P × Q.CotangentSpace) ≃ₗ[S]
      (LiftCotangent Q × P.CotangentSpace) := by
  -- The stable block isomorphism is exactly Lemma 10.134.14 applied to the concentrated naive
  -- cotangent complexes.
  letI : IsIso (term_complex_biprod_hom e) :=
    naiveCotangent_term_complex_biprod_hom_isIso e
  simpa [Algebra.Extension.naiveCotangentChainComplex] using
    (((ModuleCat.biprodIsoProd
        (P.naiveCotangentChainComplex.X 1)
        (Q.naiveCotangentChainComplex.X 0)).symm ≪≫
      asIso (term_complex_biprod_hom e) ≪≫
      ModuleCat.biprodIsoProd
        (Q.naiveCotangentChainComplex.X 1)
        (P.naiveCotangentChainComplex.X 0))).toLinearEquiv

-- Proof sketch: compare the two naive cotangent complexes by the canonical default maps between
-- the presentations. The `map_sub_map` identities give the chain homotopies showing those maps
-- are homotopy inverse. Applying `term_complex_biprod_hom` yields the stable block isomorphism,
-- and the `ULift` bridge is immediately removed.
private noncomputable def presentation_cotangentSpace_stable_equiv_aux
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    (P.toExtension.Cotangent × Q.toExtension.CotangentSpace) ≃ₗ[S]
      (Q.toExtension.Cotangent × P.toExtension.CotangentSpace) :=
    (LinearEquiv.prodCongr
      (liftCotangentEquiv P.toExtension).symm
      (LinearEquiv.refl S Q.toExtension.CotangentSpace)).trans <|
    (naiveCotangentLiftCotangentSpaceStableEquiv
      (defaultNaiveCotangentChainHomotopyEquiv P Q)).trans <|
      LinearEquiv.prodCongr
        (liftCotangentEquiv Q.toExtension)
        (LinearEquiv.refl S P.toExtension.CotangentSpace)

/-- Core/canonical companion: before rewriting the cotangent-space summands by their free bases,
the stable presentation-independence statement is the linear equivalence
`P.toExtension.Cotangent × Q.toExtension.CotangentSpace ≃ₗ[S]
  Q.toExtension.Cotangent × P.toExtension.CotangentSpace`. -/
noncomputable abbrev presentation_cotangentSpace_stable_equiv
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    (P.toExtension.Cotangent × Q.toExtension.CotangentSpace) ≃ₗ[S]
      (Q.toExtension.Cotangent × P.toExtension.CotangentSpace) :=
  presentation_cotangentSpace_stable_equiv_aux P Q

-- Proof sketch: transport the cotangent-space summands of
-- `presentation_cotangentSpace_stable_equiv` along the canonical basis equivalences
-- `Q.cotangentSpaceBasis.repr` and `P.cotangentSpaceBasis.repr`.
/-- Lemma 10.134.15: for two finite presentations of the same `R`-algebra `S`, rewriting the
cotangent spaces by their canonical free bases yields the textbook stabilization
`I / I² ⊕ S^{⊕ m} ≃ J / J² ⊕ S^{⊕ n}`. -/
noncomputable def presentation_cotangent_stable_equiv
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    (P.toExtension.Cotangent × (Fin m →₀ S)) ≃ₗ[S]
      (Q.toExtension.Cotangent × (Fin n →₀ S)) := by
  let eQ := presentationCotangentSpaceBasisEquiv Q
  let eP := presentationCotangentSpaceBasisEquiv P
  exact
    (LinearEquiv.prodCongr
        (LinearEquiv.refl S P.toExtension.Cotangent)
        eQ.symm).trans <|
      (presentation_cotangentSpace_stable_equiv P Q).trans <|
        LinearEquiv.prodCongr
          (LinearEquiv.refl S Q.toExtension.Cotangent)
          eP

-- Proof sketch: this is the defining basis-change decomposition of
-- `presentation_cotangent_stable_equiv`, so the statement is immediate by unfolding the
-- definition.
/-- Companion `_def` lemma: `presentation_cotangent_stable_equiv` is obtained by transporting
`presentation_cotangentSpace_stable_equiv` along the canonical cotangent-space basis
equivalences. -/
theorem presentation_cotangent_stable_equiv_def
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    presentation_cotangent_stable_equiv P Q =
      ((LinearEquiv.prodCongr
          (LinearEquiv.refl S P.toExtension.Cotangent)
          (presentationCotangentSpaceBasisEquiv Q).symm).trans <|
        (presentation_cotangentSpace_stable_equiv P Q).trans <|
          LinearEquiv.prodCongr
            (LinearEquiv.refl S Q.toExtension.Cotangent)
            (presentationCotangentSpaceBasisEquiv P)) := by
  rfl

end

/-! ### Lemma_10_134_16 (from Chap10) -/
open scoped TensorProduct
open Algebra
open Algebra.Generators
open Algebra.Extension

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {g : S} {n m : ℕ}

/- Domain-style sampling:
* primary domain: cotangent modules of finite algebra presentations under localization away from
  one element.
* sampled owner declarations:
  - `presentation_cotangent_stable_equiv`, the chapter owner for stable presentation-independence
    of conormal modules;
  - `Generators.cotangentCompLocalizationAwayEquiv`, the localization-away splitting of the
    cotangent module after adjoining an inverse;
  - `LocalizedModule.equivTensorProduct`, the canonical bridge between a localized module and the
    tensor-product base-change model;
  - `Generators.basisCotangentAway`, the canonical rank-one basis for the localization-away
    presentation.
* best owner abstraction: the source-facing object is the localized conormal module itself,
  modeled canonically as `LocalizedModule.Away g P.toExtension.Cotangent`; the tensor-product
  description is only the bridge used to connect this owner to
  `Generators.cotangentCompLocalizationAwayEquiv`.
* primitive data vs. derived API:
  - primitive data: the presentations `P` and `Q`, together with the away-localized cotangent
    module of `P`;
  - derived API: the stabilized isomorphism with the cotangent module of `Q`;
  - bridge/view: the tensor-product model and the extra rank-one summand coming from adjoining an
    inverse of `g`.
* layer triage:
  - `source-facing`: the stable isomorphism
    `(I / I²)_g ⊕ S_g^{⊕ m} ≅ J / J² ⊕ S_g^{⊕ n}`;
  - `core/canonical`: `presentation_cotangent_stable_equiv`;
  - `bridge/view`: `Generators.cotangentCompLocalizationAwayEquiv` together with
    `LocalizedModule.equivTensorProduct`.
-/

-- Proof sketch: let `P' := (Generators.localizationAway (Localization.Away g) g).comp P`, so
-- `P'` is the canonical presentation of `S_g` obtained from `P` by adjoining one inverse for `g`.
-- `Generators.cotangentCompLocalizationAwayEquiv` identifies `P'.toExtension.Cotangent` with the
-- tensor-product model `Localization.Away g ⊗[S] P.toExtension.Cotangent` plus one free rank-one
-- summand, and `LocalizedModule.equivTensorProduct` rewrites that tensor product as the source-
-- facing localized conormal module `LocalizedModule.Away g P.toExtension.Cotangent`.
-- Lemma `10.134.15` compares `P'` with the arbitrary presentation `Q`. Rewriting the
-- localization-away cotangent summand by its canonical rank-one basis yields the source-facing
-- stable equivalence promised by the Stacks lemma, so the clean public statement here is
-- existence rather than a non-canonical chosen witness.
/-- Lemma 10.134.16: for a presentation `P : R[x₁, …, xₙ] → S` and a presentation
`Q : R[y₁, …, yₘ] → S_g`, there exists a `Localization.Away g`-linear equivalence between the
localized conormal module of `P`, stabilized by `S_g^{⊕ m}`, and the conormal module of `Q`,
stabilized by `S_g^{⊕ n}`. This is the source-facing existence form of the textbook isomorphism
`(I / I²)_g ⊕ S_g^{⊕ m} ≅ J / J² ⊕ S_g^{⊕ n}`; the tensor-product base-change model is only the
bridge to the canonical localization APIs used in the proof. -/
theorem localized_presentation_cotangent_stable_equiv
    (P : Generators R S (Fin n)) (Q : Generators R (Localization.Away g) (Fin m)) :
    Nonempty
      ((LocalizedModule.Away g P.toExtension.Cotangent × (Fin m →₀ Localization.Away g)) ≃ₗ[Localization.Away g]
        (Q.toExtension.Cotangent × (Fin n →₀ Localization.Away g))) := by
  sorry

end
