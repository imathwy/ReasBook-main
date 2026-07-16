import stacks_proof.stacks_project.Chap10.Definition_10_134_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 07BR]
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
