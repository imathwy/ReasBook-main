import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_23_1
import stacks_proof.stacks_project.Chap17.Definition_17_25_1
import stacks_proof.stacks_project.Chap17.Lemma_17_25_5
import stacks_proof.stacks_project.Chap17.TensorPowerSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
variable [MonoidalCategory (RingedSpace.Modules X)]
local notation "𝒪X" => (SheafOfModules.unit (RingedSpace.ringCatSheaf X) : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "IsInvertibleX" => (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

private abbrev internalHomUnit [MonoidalClosed ModX] (L : ModX) : ModX :=
  (ihom L).obj 𝒪X

private instance tensorLeft_isEquivalence_of_isInvertible
    (ℒ : ModX) [IsInvertibleX ℒ] :
    (tensorLeft ℒ).IsEquivalence :=
  (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).2 inferInstance

/- Domain-style sampling for Definition 17.25.6:
- primary domain: tensor powers of an invertible sheaf on a ringed space, with the source-facing
  owner defined by iterating the right-tensor autoequivalence `𝓕 ↦ 𝓕 ⊗ₘ ℒ`, and a companion
  bridge to the chapter's left-recursive/internal-Hom computational model;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `tensorLeft_isEquivalence_iff_tensorRight_isEquivalence`,
  `tensorRight_isEquivalence_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible`,
  `SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible`,
  `tensorRight`,
  `Functor.asEquivalence`,
  `CategoryTheory.Equivalence.pow`,
  `AlgebraicGeometry.RingedSpace.tensorPowerSheaf`,
  `AlgebraicGeometry.RingedSpace.tensorPowerSheaf_succ`,
  `SheafOfModules.unit X.ringCatSheaf`;
- best owner abstraction: the source-facing owner is the image of the structure sheaf under the
  `n`th power of `(tensorRight ℒ).asEquivalence` for an invertible sheaf `ℒ`; the chapter's
  left-recursive positive powers and internal-Hom negative powers form a bridge/view for
  calculations, and the tensor-power multiplication maps are derived companion isomorphisms built
  on the Chapter 18 invertibility/evaluation API;
- primitive data: an invertible sheaf `ℒ : ModX`;
- derived API: the source-facing owner `tensorPowerSheafInt ℒ n`, its textbook notation, the
  recursive computational model `tensorPowerSheafIntModel ℒ n`, its comparison isomorphism with
  the source-facing owner, and the canonical multiplication isomorphisms.

Layer triage:
- `source-facing`: the invertible-sheaf tensor-power family
  `((tensorRight ℒ).asEquivalence ^ n).functor.obj \mathcal O_X`, named `tensorPowerSheafInt ℒ n`;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible`, `tensorRight ℒ`,
  `Functor.asEquivalence`, `CategoryTheory.Equivalence.pow`, the nonnegative tensor-power owner
  `tensorPowerSheaf`, and the Chapter 17 tensor-inverse/internal-Hom comparison API;
- `bridge/view`: the left-recursive/internal-Hom model `tensorPowerSheafIntModel ℒ n`, the
  right-recursive source-faithful model, and the comparison isomorphisms from those models to the
  source-facing owner.
-/

/-- Definition 17.25.6: for an invertible sheaf `\mathcal L`, the tensor power
`\mathcal L^{\otimes n}` is the image of the structure sheaf under the `n`th power of the tensor
autoequivalence `𝓕 ↦ 𝓕 \otimes_{\mathcal O_X} \mathcal L`. -/
@[stacks 01CU]
noncomputable def tensorPowerSheafInt
    (ℒ : ModX) [IsInvertibleX ℒ] (n : ℤ) : ModX :=
  (((tensorRight ℒ).asEquivalence ^ n).functor.obj 𝒪X)

/-- Textbook notation for the integral tensor powers `\mathcal L^{\otimes n}` of an invertible
sheaf. -/
infixr:80 " ^⊗ " => AlgebraicGeometry.RingedSpace.tensorPowerSheafInt

/-- Computational companion for Definition 17.25.6: the recursive `\mathbf Z`-indexed model using
the usual nonnegative tensor powers and the canonical dual
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal L, \mathcal O_X)` in negative degrees. -/
private noncomputable def tensorPowerSheafIntModel [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] : ℤ → ModX
  | .ofNat n => T^[n] ℒ
  | .negSucc n => T^[n + 1] (internalHomUnit ℒ)

private noncomputable def tensorPowerSheafRight
    (ℱ : ModX) : ℕ → ModX
  | 0 => 𝒪X
  | n + 1 => tensorObj (tensorPowerSheafRight ℱ n) ℱ

private noncomputable def tensorPowerSheafIntRightModel [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] : ℤ → ModX
  | .ofNat n => tensorPowerSheafRight ℒ n
  | .negSucc n => tensorPowerSheafRight (internalHomUnit ℒ) (n + 1)

private theorem tensorRightPowUnitNatSuccEq
    (ℒ : ModX) [IsInvertibleX ℒ] (n : ℕ) :
    (((tensorRight ℒ).asEquivalence ^ ((n + 1 : ℕ) : ℤ)).functor.obj 𝒪X) =
      (((tensorRight ℒ).asEquivalence ^ (n : ℤ)).functor.obj 𝒪X) ⊗ₘ ℒ := by
  -- Unfold the positive power recursion once and read off the objectwise tensor-right action.
  cases n with
  | zero => rfl
  | succ n =>
      change (((tensorRight ℒ).asEquivalence).powNat (n + 2)).functor.obj 𝒪X =
        ((((tensorRight ℒ).asEquivalence).powNat (n + 1)).functor.obj 𝒪X) ⊗ₘ ℒ
      rfl

private theorem tensorRightPowUnitNegSuccEq
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℕ) :
    (((tensorRight ℒ).asEquivalence ^ Int.negSucc (n + 1)).functor.obj 𝒪X) =
      ((tensorRight ℒ).asEquivalence.inverse.obj
        (((tensorRight ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)) := by
  -- Unfold the negative power recursion once and keep the inverse functor in explicit form.
  cases n with
  | zero => rfl
  | succ n =>
      change (((tensorRight ℒ).asEquivalence).symm.powNat (n + 2)).functor.obj 𝒪X =
        (tensorRight ℒ).asEquivalence.inverse.obj
          ((((tensorRight ℒ).asEquivalence).symm.powNat (n + 1)).functor.obj 𝒪X)
      rfl

private theorem tensorRightPowUnitNegOneEq
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    (((tensorRight ℒ).asEquivalence ^ Int.negSucc 0).functor.obj 𝒪X) =
      ((tensorRight ℒ).asEquivalence.inverse.obj 𝒪X) := by
  -- The `-1` power is definitionally the inverse equivalence.
  rfl

private noncomputable def tensorPowerSheafIntUnitLeftIso
    (ℱ : ModX) :
    (𝒪X ⊗ₘ ℱ) ≅ ℱ :=
  (SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ

private noncomputable def tensorPowerSheafIntUnitRightIso
    (ℱ : ModX) :
    (ℱ ⊗ₘ 𝒪X) ≅ ℱ :=
  (Iso.refl ℱ ⊗ᵢ SheafOfModules.unitIsoTensorUnit) ≪≫ ρ_ ℱ

private noncomputable def tensorPowerSheafRightStepIso
    (ℱ : ModX) :
    (n : ℕ) → (ℱ ⊗ₘ tensorPowerSheafRight ℱ n) ≅ tensorPowerSheafRight ℱ (n + 1)
  | 0 =>
      (tensorPowerSheafIntUnitRightIso ℱ) ≪≫
        (tensorPowerSheafIntUnitLeftIso ℱ).symm
  | n + 1 =>
      (α_ ℱ (tensorPowerSheafRight ℱ n) ℱ).symm ≪≫
        (tensorPowerSheafRightStepIso ℱ n ▷ᵢ ℱ)

private noncomputable def tensorPowerSheafModelNatToRightIso
    (ℱ : ModX) :
    (n : ℕ) → (T^[n] ℱ) ≅ tensorPowerSheafRight ℱ n
  | 0 => Iso.refl 𝒪X
  | n + 1 =>
      eqToIso (by simpa using tensorPowerSheaf_succ ℱ n) ≪≫
        (Iso.refl ℱ ⊗ᵢ tensorPowerSheafModelNatToRightIso ℱ n) ≪≫
        tensorPowerSheafRightStepIso ℱ n

private noncomputable def tensorPowerSheafIntRightModelNatIso
    (ℒ : ModX) [IsInvertibleX ℒ] :
    (n : ℕ) → tensorPowerSheafRight ℒ n ≅ (ℒ ^⊗ (n : ℤ))
  | 0 => Iso.refl 𝒪X
  | n + 1 =>
      eqToIso rfl ≪≫
        (tensorPowerSheafIntRightModelNatIso ℒ n ⊗ᵢ Iso.refl ℒ) ≪≫
        (eqToIso (tensorRightPowUnitNatSuccEq ℒ n)).symm

private noncomputable def tensorPowerSheafIntEvaluationIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    (ℒ ⊗ₘ internalHomUnit ℒ) ≅ 𝒪X :=
  @asIso ModX _ _ _ ((ihom.ev ℒ).app 𝒪X)
    (SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible ℒ)

private noncomputable def tensorPowerSheafIntEvaluationRightIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    (internalHomUnit ℒ ⊗ₘ ℒ) ≅ 𝒪X :=
  (β_ (internalHomUnit ℒ) ℒ) ≪≫ tensorPowerSheafIntEvaluationIso ℒ

private noncomputable def tensorRightUnitIso :
    tensorRight 𝒪X ≅ 𝟭 ModX :=
  (tensoringRight ModX).mapIso SheafOfModules.unitIsoTensorUnit ≪≫
    rightUnitorNatIso ModX

private noncomputable def tensorRightCompInternalHomUnitIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    tensorRight ℒ ⋙ tensorRight (internalHomUnit ℒ) ≅ 𝟭 ModX :=
  (tensorRightTensor ℒ (internalHomUnit ℒ)).symm ≪≫
    (tensoringRight ModX).mapIso (tensorPowerSheafIntEvaluationIso ℒ) ≪≫
    tensorRightUnitIso

private noncomputable def internalHomUnitCompTensorRightIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    tensorRight (internalHomUnit ℒ) ⋙ tensorRight ℒ ≅ 𝟭 ModX :=
  (tensorRightTensor (internalHomUnit ℒ) ℒ).symm ≪≫
    (tensoringRight ModX).mapIso (tensorPowerSheafIntEvaluationRightIso ℒ) ≪≫
    tensorRightUnitIso

private noncomputable def tensorRightInternalHomUnitEquivalence
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    ModX ≌ ModX :=
  CategoryTheory.Equivalence.mk
    (tensorRight ℒ)
    (tensorRight (internalHomUnit ℒ))
    (tensorRightCompInternalHomUnitIso ℒ).symm
    (internalHomUnitCompTensorRightIso ℒ)

private noncomputable def tensorRightInverseIsoInternalHomUnit
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    ((tensorRight ℒ).asEquivalence).inverse ≅ tensorRight (internalHomUnit ℒ) :=
  Adjunction.rightAdjointUniq
    (tensorRight ℒ).asEquivalence.toAdjunction
    (tensorRightInternalHomUnitEquivalence ℒ).toAdjunction

private noncomputable def tensorPowerSheafIntRightModelNegSuccIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    (n : ℕ) →
      tensorPowerSheafRight (internalHomUnit ℒ) (n + 1) ≅ ℒ ^⊗ Int.negSucc n
  | 0 => by
      calc
        tensorPowerSheafRight (internalHomUnit ℒ) 1 ≅ 𝒪X ⊗ₘ internalHomUnit ℒ :=
          eqToIso rfl
        _ ≅ ((tensorRight ℒ).asEquivalence.inverse.obj 𝒪X) :=
          ((tensorRightInverseIsoInternalHomUnit ℒ).app 𝒪X).symm
        _ ≅ ℒ ^⊗ Int.negSucc 0 :=
          (eqToIso (tensorRightPowUnitNegOneEq ℒ)).symm
  | n + 1 => by
      calc
        tensorPowerSheafRight (internalHomUnit ℒ) (n + 2) ≅
            tensorPowerSheafRight (internalHomUnit ℒ) (n + 1) ⊗ₘ internalHomUnit ℒ :=
          eqToIso rfl
        _ ≅ (ℒ ^⊗ Int.negSucc n) ⊗ₘ internalHomUnit ℒ :=
          tensorPowerSheafIntRightModelNegSuccIso ℒ n ⊗ᵢ
            Iso.refl (internalHomUnit ℒ)
        _ ≅ ((tensorRight ℒ).asEquivalence.inverse.obj (ℒ ^⊗ Int.negSucc n)) :=
          ((tensorRightInverseIsoInternalHomUnit ℒ).app (ℒ ^⊗ Int.negSucc n)).symm
        _ ≅ ℒ ^⊗ Int.negSucc (n + 1) :=
          (eqToIso (tensorRightPowUnitNegSuccEq ℒ n)).symm

private noncomputable def tensorPowerSheafIntRightModelIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℤ) :
    tensorPowerSheafIntRightModel ℒ n ≅ ℒ ^⊗ n := by
  cases n with
  | ofNat n =>
      exact tensorPowerSheafIntRightModelNatIso ℒ n
  | negSucc n =>
      exact tensorPowerSheafIntRightModelNegSuccIso ℒ n

private noncomputable def tensorPowerSheafIntModelToRightModelIso
    [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℤ) :
    tensorPowerSheafIntModel ℒ n ≅ tensorPowerSheafIntRightModel ℒ n := by
  cases n with
  | ofNat n =>
      exact tensorPowerSheafModelNatToRightIso ℒ n
  | negSucc n =>
      exact tensorPowerSheafModelNatToRightIso (internalHomUnit ℒ) (n + 1)

/-- The recursive chapter model for `\mathcal L^{\otimes n}` identifies canonically with the
source-facing owner from Definition 17.25.6. -/
private noncomputable def tensorPowerSheafIntModelIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℤ) :
    tensorPowerSheafIntModel ℒ n ≅ ℒ ^⊗ n :=
  tensorPowerSheafIntModelToRightModelIso ℒ n ≪≫
    tensorPowerSheafIntRightModelIso ℒ n

private noncomputable def tensorPowerSheafIntModelNatIso
    (ℒ : ModX)
    [IsInvertibleX ℒ] :
    (n : ℕ) → (T^[n] ℒ) ≅ ℒ ^⊗ (n : ℤ)
  | n =>
      tensorPowerSheafModelNatToRightIso ℒ n ≪≫
        tensorPowerSheafIntRightModelNatIso ℒ n

private noncomputable def tensorPowerSheafIntModelNatSuccIso
    [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℕ) :
    tensorPowerSheafIntModel ℒ (((n + 1 : ℕ) : ℤ)) ≅
      ℒ ⊗ₘ tensorPowerSheafIntModel ℒ (n : ℤ) :=
  eqToIso (by simpa [tensorPowerSheafIntModel] using tensorPowerSheaf_succ ℒ n)

private noncomputable def tensorPowerSheafIntModelNegOneIso
    [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    tensorPowerSheafIntModel ℒ (-1 : ℤ) ≅ internalHomUnit ℒ :=
  calc
    tensorPowerSheafIntModel ℒ (-1 : ℤ) ≅
        internalHomUnit ℒ ⊗ₘ T^[0] (internalHomUnit ℒ) :=
      eqToIso (by
        simpa [tensorPowerSheafIntModel] using tensorPowerSheaf_succ (internalHomUnit ℒ) 0)
    _ ≅ internalHomUnit ℒ ⊗ₘ 𝒪X :=
      eqToIso rfl
    _ ≅ internalHomUnit ℒ ⊗ₘ (𝟙_ ModX) :=
      Iso.refl (internalHomUnit ℒ) ⊗ᵢ SheafOfModules.unitIsoTensorUnit
    _ ≅ internalHomUnit ℒ :=
      ρ_ (internalHomUnit ℒ)

private noncomputable def tensorPowerSheafIntModelNegSuccSuccIso
    [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℕ) :
    tensorPowerSheafIntModel ℒ (Int.negSucc (n + 1)) ≅
      internalHomUnit ℒ ⊗ₘ tensorPowerSheafIntModel ℒ (Int.negSucc n) :=
  eqToIso (by
    simpa [tensorPowerSheafIntModel] using tensorPowerSheaf_succ (internalHomUnit ℒ) (n + 1))

private noncomputable def tensorPowerSheafIntModelOneAddIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    (n : ℤ) →
      (ℒ ⊗ₘ tensorPowerSheafIntModel ℒ n) ≅ tensorPowerSheafIntModel ℒ (n + 1)
  | .ofNat n =>
      (tensorPowerSheafIntModelNatSuccIso ℒ n).symm
  | .negSucc 0 =>
      (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntModelNegOneIso ℒ) ≪≫
        tensorPowerSheafIntEvaluationIso ℒ ≪≫
        eqToIso (by
          have h : Int.negSucc 0 + 1 = (0 : ℤ) := by
            decide
          exact (congrArg (tensorPowerSheafIntModel ℒ) h).symm)
  | .negSucc (n + 1) =>
      (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntModelNegSuccSuccIso ℒ n) ≪≫
        (α_ ℒ (internalHomUnit ℒ) (tensorPowerSheafIntModel ℒ (Int.negSucc n))).symm ≪≫
        (tensorPowerSheafIntEvaluationIso ℒ ▷ᵢ tensorPowerSheafIntModel ℒ (Int.negSucc n)) ≪≫
        tensorPowerSheafIntUnitLeftIso (tensorPowerSheafIntModel ℒ (Int.negSucc n)) ≪≫
        eqToIso (congrArg (tensorPowerSheafIntModel ℒ) (by omega)).symm

private noncomputable def tensorPowerSheafIntModelNatAddIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    (m : ℕ) → (n : ℤ) →
      ((tensorPowerSheafIntModel ℒ (m : ℤ)) ⊗ₘ tensorPowerSheafIntModel ℒ n) ≅
        tensorPowerSheafIntModel ℒ ((m : ℤ) + n)
  | 0, n =>
      eqToIso rfl ▷ᵢ tensorPowerSheafIntModel ℒ n ≪≫
        tensorPowerSheafIntUnitLeftIso (tensorPowerSheafIntModel ℒ n) ≪≫
        eqToIso (congrArg (tensorPowerSheafIntModel ℒ) (by omega))
  | m + 1, n =>
      let h : (((m : ℤ) + n) + 1) = (((m + 1 : ℕ) : ℤ) + n) := by
        omega
      (tensorPowerSheafIntModelNatSuccIso ℒ m ▷ᵢ tensorPowerSheafIntModel ℒ n) ≪≫
        α_ ℒ (tensorPowerSheafIntModel ℒ (m : ℤ)) (tensorPowerSheafIntModel ℒ n) ≪≫
        (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntModelNatAddIso ℒ m n) ≪≫
        tensorPowerSheafIntModelOneAddIso ℒ ((m : ℤ) + n) ≪≫
        eqToIso (congrArg (tensorPowerSheafIntModel ℒ) h)

private noncomputable def tensorPowerSheafIntModelAddIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (m n : ℤ) :
    ((tensorPowerSheafIntModel ℒ m) ⊗ₘ tensorPowerSheafIntModel ℒ n) ≅
      tensorPowerSheafIntModel ℒ (m + n) := by
  cases m with
  | ofNat m =>
      exact tensorPowerSheafIntModelNatAddIso ℒ m n
  | negSucc a =>
      cases n with
      | ofNat n =>
          exact (β_ (tensorPowerSheafIntModel ℒ (Int.negSucc a))
              (tensorPowerSheafIntModel ℒ (n : ℤ))) ≪≫
            tensorPowerSheafIntModelNatAddIso ℒ n (Int.negSucc a) ≪≫
            eqToIso (congrArg (tensorPowerSheafIntModel ℒ)
              (Int.add_comm (n : ℤ) (Int.negSucc a)))
      | negSucc b =>
          exact (eqToIso rfl ⊗ᵢ eqToIso rfl) ≪≫
            tensorPowerSheafIntModelNatAddIso (internalHomUnit ℒ) (a + 1) (b + 1) ≪≫
            eqToIso (
              calc
                tensorPowerSheafIntModel (internalHomUnit ℒ)
                    ((((a + 1) + (b + 1) : ℕ) : ℤ)) =
                  tensorPowerSheafIntModel (internalHomUnit ℒ)
                    (((a + b + 2 : ℕ) : ℤ)) := by
                      exact congrArg (tensorPowerSheafIntModel (internalHomUnit ℒ)) (by omega)
                _ = tensorPowerSheafIntModel ℒ (Int.negSucc (a + b + 1)) := rfl
                _ = tensorPowerSheafIntModel ℒ (Int.negSucc a + Int.negSucc b) := by
                      have h : Int.negSucc (a + b + 1) = Int.negSucc a + Int.negSucc b := by
                        omega
                      exact congrArg (tensorPowerSheafIntModel ℒ) h
            )

/-- The zeroth tensor power `\mathcal L^{\otimes 0}` is canonically the structure sheaf. -/
noncomputable def tensorPowerSheafIntZeroIso
    (ℒ : ModX) [IsInvertibleX ℒ] :
    ℒ ^⊗ (0 : ℤ) ≅ 𝒪X :=
  (tensorPowerSheafIntModelNatIso ℒ 0).symm ≪≫ eqToIso rfl

/-- The first positive tensor power is `\mathcal L` tensored with the preceding nonnegative power.
-/
noncomputable def tensorPowerSheafIntNatSuccIso
    (ℒ : ModX) [IsInvertibleX ℒ] (n : ℕ) :
    ℒ ^⊗ (((n + 1 : ℕ) : ℤ)) ≅ ℒ ⊗ₘ (ℒ ^⊗ (n : ℤ)) :=
  (tensorPowerSheafIntModelNatIso ℒ (n + 1)).symm ≪≫
    eqToIso (by simpa using tensorPowerSheaf_succ ℒ n) ≪≫
    (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntModelNatIso ℒ n)

/-- The `(-1)`st tensor power is the first tensor power of the canonical internal-Hom inverse
sheaf. -/
noncomputable def tensorPowerSheafIntNegOneIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] :
    ℒ ^⊗ (-1 : ℤ) ≅ (ihom ℒ).obj 𝒪X :=
  (tensorPowerSheafIntModelIso ℒ (-1)).symm ≪≫
    tensorPowerSheafIntModelNegOneIso ℒ

/-- Beyond `\mathcal L^{-1}`, each further negative tensor power is obtained by tensoring once
more with the canonical internal-Hom inverse sheaf. -/
noncomputable def tensorPowerSheafIntNegSuccSuccIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℕ) :
    ℒ ^⊗ (Int.negSucc (n + 1)) ≅ ((ihom ℒ).obj 𝒪X) ⊗ₘ (ℒ ^⊗ Int.negSucc n) :=
  (tensorPowerSheafIntModelIso ℒ (Int.negSucc (n + 1))).symm ≪≫
    tensorPowerSheafIntModelNegSuccSuccIso ℒ n ≪≫
    (Iso.refl (internalHomUnit ℒ) ⊗ᵢ tensorPowerSheafIntModelIso ℒ (Int.negSucc n))

/-- Tensoring once by `\mathcal L` shifts the integral tensor-power owner by one degree. For
negative degrees this uses the canonical evaluation isomorphism
`\mathcal L \otimes \mathcal L^{-1} \cong \mathcal O_X` of an invertible sheaf. -/
noncomputable def tensorPowerSheafIntOneAddIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (n : ℤ) :
    (ℒ ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (n + 1) :=
  (Iso.refl ℒ ⊗ᵢ (tensorPowerSheafIntModelIso ℒ n).symm) ≪≫
    tensorPowerSheafIntModelOneAddIso ℒ n ≪≫
    tensorPowerSheafIntModelIso ℒ (n + 1)

/-- Tensoring `\mathcal L^{\otimes m}` with `\mathcal L^{\otimes n}` for `m,n \in \mathbf N`
canonically identifies with `\mathcal L^{\otimes (m+n)}`. -/
private noncomputable def tensorPowerSheafIntNatAddIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (m n : ℕ) :
    ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ (n : ℤ))) ≅
      ℒ ^⊗ (((m + n : ℕ) : ℤ)) :=
  ((tensorPowerSheafIntModelIso ℒ (m : ℤ)).symm ⊗ᵢ
      (tensorPowerSheafIntModelIso ℒ (n : ℤ)).symm) ≪≫
    tensorPowerSheafIntModelNatAddIso ℒ m (n : ℤ) ≪≫
    eqToIso (congrArg (tensorPowerSheafIntModel ℒ) (by exact_mod_cast rfl)) ≪≫
    tensorPowerSheafIntModelIso ℒ (((m + n : ℕ) : ℤ))

/-- Tensoring two tensor powers `\mathcal L^{\otimes m}` and `\mathcal L^{\otimes n}` canonically
identifies with `\mathcal L^{\otimes (m+n)}`. The proof is computed through the recursive
positive/dual model and transported back to the source-facing owner. -/
noncomputable def tensorPowerSheafIntAddIso
    [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX)
    [IsInvertibleX ℒ] (m n : ℤ) :
    ((ℒ ^⊗ m) ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (m + n) :=
  ((tensorPowerSheafIntModelIso ℒ m).symm ⊗ᵢ
      (tensorPowerSheafIntModelIso ℒ n).symm) ≪≫
    tensorPowerSheafIntModelAddIso ℒ m n ≪≫
    tensorPowerSheafIntModelIso ℒ (m + n)

end AlgebraicGeometry.RingedSpace
