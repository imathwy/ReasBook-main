import Mathlib
import StacksProject_2024.Chap18.«18_35_0_2»

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
