import Mathlib
import stacks_project.Chap04.Lemma_4_43_3
import stacks_project.Chap17.Definition_17_23_1
import stacks_project.Chap17.Example_17_18_1
import stacks_project.Chap17.TensorPowerSheaf
import stacks_project.Chap18.Lemma_18_32_4
import stacks_project.Chap18.Example_18_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

/- Domain-style sampling for Definition 17.25.6:
- primary domain: tensor powers of an invertible sheaf on a ringed space, viewed both through the
  tensor autoequivalence `tensorLeft ℒ` and through the chapter's recursive `ℤ`-indexed model;
- inspected owner declarations:
  `tensorLeft`,
  `Functor.asEquivalence`,
  `CategoryTheory.Equivalence.pow`,
  `SheafOfModules.unitToTensorUnit`,
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `AlgebraicGeometry.RingedSpace.tensorPowerSheaf`,
  `AlgebraicGeometry.RingedSpace.tensorPowerSheaf_succ`,
  `SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible`,
  `SheafOfModules.RingedSite.ringedSiteModuleDual_exactPairing`,
  `ringedSiteModuleDual`,
  `SheafOfModules.unit ((RingedSpace.ringCatSheaf X))`;
- best owner abstraction: the source-facing object is the image of the structure sheaf under the
  `n`th power of the tensor autoequivalence `(tensorLeft ℒ).asEquivalence`; the recursive
  `ℤ`-indexed tensor-power owner is the concrete chapter model used to compute with that source
  object, while the tensor-power multiplication maps are derived companion isomorphisms;
- primitive data: an invertible sheaf `ℒ : ModX`;
- derived API: the invertible-sheaf tensor-power owner `tensorPowerSheafInt ℒ n`, its textbook
  notation, the companion comparison isomorphism with the tensor autoequivalence, the branch
  recursion lemmas, and the canonical multiplication morphisms.

Layer triage:
- `source-facing`: the invertible-sheaf tensor-power family `tensorPowerSheafInt ℒ n`, with
  companion comparison to the tensor autoequivalence power
  `((tensorLeft ℒ).asEquivalence ^ n).functor.obj \mathcal O_X`;
- `core/canonical`: `tensorLeft ℒ`, `Functor.asEquivalence`, the recursive positive owner
  `tensorPowerSheaf`, the canonical dual owner `ringedSiteModuleDual ℒ`, and the exact-pairing
  bridge for `ringedSiteModuleDual ℒ`;
- `bridge/view`: the comparison isomorphism from the recursive model to the tensor autoequivalence
  power, and the additive tensor-power isomorphisms.
 -/

/-- Definition 17.25.6: for an invertible sheaf `\mathcal L`, the integral tensor powers
`\mathcal L^{\otimes n}` are represented by the chapter's recursive `\mathbf Z`-indexed family,
using the usual nonnegative tensor powers and the canonical dual
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal L, \mathcal O_X)` in negative degrees. -/
noncomputable def tensorPowerSheafInt [MonoidalCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] : ℤ → ModX
  | .ofNat n => tensorPowerSheaf ℒ n
  | .negSucc n => tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1)

/-- Textbook notation for the integral tensor powers `\mathcal L^{\otimes n}` of an invertible
sheaf. -/
infixr:80 " ^⊗ " => AlgebraicGeometry.RingedSpace.tensorPowerSheafInt

private noncomputable instance tensorLeftIsEquivalenceOfIsInvertible
    [MonoidalCategory ModX] (ℒ : ModX) [IsInvertible ℒ] :
    (tensorLeft ℒ).IsEquivalence :=
  (CategoryTheory.tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).2 inferInstance

private theorem tensorLeftPowUnitNatSuccEq
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    (((tensorLeft ℒ).asEquivalence ^ ((n + 2 : ℕ) : ℤ)).functor.obj 𝒪X) =
      ℒ ⊗ₘ (((tensorLeft ℒ).asEquivalence ^ ((n + 1 : ℕ) : ℤ)).functor.obj 𝒪X) := by
  sorry

private theorem tensorLeftPowUnitOneEq
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    (((tensorLeft ℒ).asEquivalence ^ (1 : ℤ)).functor.obj 𝒪X) = ℒ ⊗ₘ 𝒪X := by
  sorry

private theorem tensorLeftPowUnitNegSuccEq
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    (((tensorLeft ℒ).asEquivalence ^ Int.negSucc (n + 1)).functor.obj 𝒪X) =
      ((tensorLeft ℒ).asEquivalence.inverse.obj
        (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)) := by
  sorry

private theorem tensorLeftPowUnitNegOneEq
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (((tensorLeft ℒ).asEquivalence ^ Int.negSucc 0).functor.obj 𝒪X) =
      ((tensorLeft ℒ).asEquivalence.inverse.obj 𝒪X) := by
  sorry

private noncomputable def tensorPowerSheafNatIsoTensorLeftPowUnit
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    (n : ℕ) → tensorPowerSheaf ℒ n ≅ (((tensorLeft ℒ).asEquivalence ^ (n : ℤ)).functor.obj 𝒪X)
  | 0 => Iso.refl 𝒪X
  | 1 => by
      calc
        tensorPowerSheaf ℒ 1 ≅ moduleTensor ℒ (tensorPowerSheaf ℒ 0) :=
          eqToIso (by simpa using tensorPowerSheaf_succ ℒ 0)
        _ ≅ ℒ ⊗ₘ tensorPowerSheaf ℒ 0 :=
          moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ 0)
        _ ≅ ℒ ⊗ₘ 𝒪X :=
          eqToIso rfl
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ (1 : ℤ)).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitOneEq ℒ)).symm
  | n + 2 => by
      calc
        tensorPowerSheaf ℒ (n + 2) ≅ moduleTensor ℒ (tensorPowerSheaf ℒ (n + 1)) :=
          eqToIso (by simpa using tensorPowerSheaf_succ ℒ (n + 1))
        _ ≅ ℒ ⊗ₘ tensorPowerSheaf ℒ (n + 1) :=
          moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ (n + 1))
        _ ≅ ℒ ⊗ₘ (((tensorLeft ℒ).asEquivalence ^ ((n + 1 : ℕ) : ℤ)).functor.obj 𝒪X) :=
          Iso.refl ℒ ⊗ᵢ tensorPowerSheafNatIsoTensorLeftPowUnit ℒ (n + 1)
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ ((n + 2 : ℕ) : ℤ)).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitNatSuccEq ℒ n)).symm

private noncomputable def tensorPowerSheafIntEvaluation
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) :
    (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ⟶ 𝒪X :=
  show (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ⟶ 𝒪X from
    (ℒ ◁ (ihom ℒ).map (asIso SheafOfModules.unitToTensorUnit).inv) ≫
      (ihom.ev ℒ).app 𝒪X

private theorem isIso_tensorPowerSheafIntEvaluation
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    IsIso (tensorPowerSheafIntEvaluation ℒ) := by
  let f :
      (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ⟶ (ℒ ⊗ₘ (ihom ℒ).obj 𝒪X) :=
    ℒ ◁ (ihom ℒ).map (asIso SheafOfModules.unitToTensorUnit).inv
  let g : (ℒ ⊗ₘ (ihom ℒ).obj 𝒪X) ⟶ 𝒪X :=
    (ihom.ev ℒ).app 𝒪X
  have hf : IsIso f := by
    dsimp [f]
    infer_instance
  have hg : IsIso g := by
    simpa [g] using
      (SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible ℒ)
  have hcomp : IsIso (f ≫ g) := by
    infer_instance
  simpa [tensorPowerSheafIntEvaluation, f, g] using hcomp

private noncomputable def tensorPowerSheafIntEvaluationIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ≅ 𝒪X := by
  letI : IsIso (tensorPowerSheafIntEvaluation ℒ) :=
    isIso_tensorPowerSheafIntEvaluation ℒ
  exact asIso (tensorPowerSheafIntEvaluation ℒ)

private noncomputable def tensorLeftInverseIsoRingedSiteModuleDual
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    ((tensorLeft ℒ).asEquivalence).inverse ≅ tensorLeft (ringedSiteModuleDual ℒ) := by
  let E₁ : ModX ≌ ModX := (tensorLeft ℒ).asEquivalence
  let e₁ : (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ≅ 𝟙_ ModX :=
    tensorPowerSheafIntEvaluationIso ℒ ≪≫ asIso SheafOfModules.unitToTensorUnit
  let e₂ : (ringedSiteModuleDual ℒ ⊗ₘ ℒ) ≅ 𝟙_ ModX :=
    β_ (ringedSiteModuleDual ℒ) ℒ ≪≫ e₁
  let η : 𝟭 ModX ≅ tensorLeft ℒ ⋙ tensorLeft (ringedSiteModuleDual ℒ) :=
    (leftUnitorNatIso ModX).symm ≪≫
      (tensoringLeft ModX).mapIso e₂.symm ≪≫
      tensorLeftTensor (ringedSiteModuleDual ℒ) ℒ
  let ε : tensorLeft (ringedSiteModuleDual ℒ) ⋙ tensorLeft ℒ ≅ 𝟭 ModX :=
    (tensorLeftTensor ℒ (ringedSiteModuleDual ℒ)).symm ≪≫
      (tensoringLeft ModX).mapIso e₁ ≪≫
      leftUnitorNatIso ModX
  letI : (tensorLeft ℒ).IsEquivalence :=
    Functor.IsEquivalence.mk'
      (tensorLeft (ringedSiteModuleDual ℒ))
      η
      ε
  let E₂ : ModX ≌ ModX := (tensorLeft ℒ).asEquivalence
  have hInv : E₁.inverse ≅ E₂.inverse :=
    Iso.isoInverseOfIsoFunctor (Iso.refl (tensorLeft ℒ))
  have hChosen : tensorLeft (ringedSiteModuleDual ℒ) ≅ E₂.inverse :=
    (Iso.isoCompInverse ε) ≪≫ Functor.leftUnitor E₂.inverse
  exact hInv ≪≫ hChosen.symm

private noncomputable def tensorPowerSheafNegSuccIsoTensorLeftPowUnit
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (n : ℕ) →
      tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1) ≅
        (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)
  | 0 => by
      calc
        tensorPowerSheaf (ringedSiteModuleDual ℒ) 1 ≅
            moduleTensor (ringedSiteModuleDual ℒ)
              (tensorPowerSheaf (ringedSiteModuleDual ℒ) 0) :=
          eqToIso (by simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) 0)
        _ ≅ ringedSiteModuleDual ℒ ⊗ₘ tensorPowerSheaf (ringedSiteModuleDual ℒ) 0 :=
          moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ)
            (tensorPowerSheaf (ringedSiteModuleDual ℒ) 0)
        _ ≅ (tensorLeft (ringedSiteModuleDual ℒ)).obj 𝒪X :=
          eqToIso rfl
        _ ≅ ((tensorLeft ℒ).asEquivalence.inverse.obj 𝒪X) :=
          ((tensorLeftInverseIsoRingedSiteModuleDual ℒ).app 𝒪X).symm
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ Int.negSucc 0).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitNegOneEq ℒ)).symm
  | n + 1 => by
      calc
        tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 2) ≅
            moduleTensor (ringedSiteModuleDual ℒ)
              (tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1)) :=
          eqToIso (by simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) (n + 1))
        _ ≅ ringedSiteModuleDual ℒ ⊗ₘ tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1) :=
          moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ)
            (tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1))
        _ ≅ ringedSiteModuleDual ℒ ⊗ₘ
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X) :=
          Iso.refl (ringedSiteModuleDual ℒ) ⊗ᵢ
            tensorPowerSheafNegSuccIsoTensorLeftPowUnit ℒ n
        _ ≅ (tensorLeft (ringedSiteModuleDual ℒ)).obj
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X) :=
          eqToIso rfl
        _ ≅ ((tensorLeft ℒ).asEquivalence.inverse.obj
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)) :=
          ((tensorLeftInverseIsoRingedSiteModuleDual ℒ).app
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)).symm
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ Int.negSucc (n + 1)).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitNegSuccEq ℒ n)).symm

/-- Definition 17.25.6: for an invertible sheaf `\mathcal L`, the tensor power
`\mathcal L^{\otimes n}` is the image of the structure sheaf under the `n`th power of the tensor
autoequivalence `tensorLeft ℒ`. The recursive owner `ℒ ^⊗ n` is the chapter's concrete model for
this source-defined object. -/
noncomputable def tensorPowerSheafIntIsoTensorLeftPowUnit
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (n : ℤ) :
    ℒ ^⊗ n ≅ (((tensorLeft ℒ).asEquivalence ^ n).functor.obj 𝒪X) := by
  cases n with
  | ofNat n =>
      exact tensorPowerSheafNatIsoTensorLeftPowUnit ℒ n
  | negSucc n =>
      exact tensorPowerSheafNegSuccIsoTensorLeftPowUnit ℒ n

/-- The first positive tensor power is `\mathcal L` tensored with the preceding nonnegative power.
-/
theorem tensorPowerSheafInt_natSucc
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (((n + 1 : ℕ) : ℤ)) = moduleTensor ℒ (ℒ ^⊗ (n : ℤ)) :=
  tensorPowerSheaf_succ ℒ n

/-- The `(-1)`st tensor power is the first tensor power of the canonical internal-Hom inverse
sheaf. -/
theorem tensorPowerSheafInt_negOne
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (-1 : ℤ) = moduleTensor (ringedSiteModuleDual ℒ) 𝒪X := by
  simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) 0

/-- Adding a nonnegative exponent to a nonnegative exponent stays on the nonnegative branch of the
integral tensor-power owner. -/
theorem tensorPowerSheafInt_natAdd_eq
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (m n : ℕ) :
    ℒ ^⊗ ((m : ℤ) + n) = ℒ ^⊗ (((m + n : ℕ) : ℤ)) := by
  exact congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by exact_mod_cast rfl)

/-- Beyond `\mathcal L^{-1}`, each further negative tensor power is obtained by tensoring once
more with the canonical internal-Hom inverse sheaf. -/
theorem tensorPowerSheafInt_negSucc_succ
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (Int.negSucc (n + 1)) =
      moduleTensor (ringedSiteModuleDual ℒ) (ℒ ^⊗ Int.negSucc n) := by
  simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) (n + 1)

/-- The zeroth tensor power `\mathcal L^{\otimes 0}` is the tensor unit, that is, the structure
sheaf viewed through the ambient monoidal-category owner. -/
theorem tensorPowerSheafInt_zero
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (0 : ℤ) = 𝒪X := rfl

/-- Adding `1` to `-1` lands at the zeroth tensor power. -/
theorem tensorPowerSheafInt_negSucc_add_one_zero
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (Int.negSucc 0 + 1) = 𝒪X := by
  have h : Int.negSucc 0 + 1 = (0 : ℤ) := by decide
  calc
    ℒ ^⊗ (Int.negSucc 0 + 1) = ℒ ^⊗ (0 : ℤ) := congrArg (fun k : ℤ ↦ ℒ ^⊗ k) h
    _ = 𝒪X := tensorPowerSheafInt_zero ℒ

/-- Adding `1` to a strictly smaller negative exponent shifts one step toward zero. -/
theorem tensorPowerSheafInt_negSucc_add_one_succ
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (Int.negSucc (n + 1) + 1) = ℒ ^⊗ Int.negSucc n := by
  exact congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by omega)

private noncomputable def tensorPowerSheafIntUnitLeftIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℱ : ModX) :
    (𝒪X ⊗ₘ ℱ) ≅ ℱ :=
  (SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ

private noncomputable def tensorPowerSheafIntNatSuccIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (((n + 1 : ℕ) : ℤ)) ≅ ℒ ⊗ₘ (ℒ ^⊗ (n : ℤ)) :=
  eqToIso (tensorPowerSheafInt_natSucc ℒ n) ≪≫
    moduleTensorIsoTensorObj ℒ (ℒ ^⊗ (n : ℤ))

private noncomputable def tensorPowerSheafIntNegOneIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (-1 : ℤ) ≅ ringedSiteModuleDual ℒ ⊗ₘ 𝒪X :=
  eqToIso (tensorPowerSheafInt_negOne ℒ) ≪≫
    moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ) 𝒪X

private noncomputable def tensorPowerSheafIntNegSuccSuccIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (Int.negSucc (n + 1)) ≅ ringedSiteModuleDual ℒ ⊗ₘ (ℒ ^⊗ Int.negSucc n) :=
  eqToIso (tensorPowerSheafInt_negSucc_succ ℒ n) ≪≫
    moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ) (ℒ ^⊗ Int.negSucc n)

private noncomputable def tensorPowerSheafIntOneAddIsoAux
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (n : ℤ) → (ℒ ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (n + 1)
  | .ofNat n =>
      (tensorPowerSheafIntNatSuccIso ℒ n).symm
  | .negSucc 0 =>
      (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntNegOneIso ℒ) ≪≫
        (α_ ℒ (ringedSiteModuleDual ℒ) 𝒪X).symm ≪≫
        (tensorPowerSheafIntEvaluationIso ℒ ▷ᵢ 𝒪X) ≪≫
        tensorPowerSheafIntUnitLeftIso 𝒪X ≪≫
        eqToIso (tensorPowerSheafInt_zero ℒ).symm
  | .negSucc (n + 1) =>
      (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntNegSuccSuccIso ℒ n) ≪≫
        (α_ ℒ (ringedSiteModuleDual ℒ) (ℒ ^⊗ Int.negSucc n)).symm ≪≫
        (tensorPowerSheafIntEvaluationIso ℒ ▷ᵢ (ℒ ^⊗ Int.negSucc n)) ≪≫
        tensorPowerSheafIntUnitLeftIso (ℒ ^⊗ Int.negSucc n) ≪≫
        eqToIso (tensorPowerSheafInt_negSucc_add_one_succ ℒ n).symm

private noncomputable def tensorPowerSheafIntNatAddIsoAux
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (m : ℕ) → (n : ℤ) →
      ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ ((m : ℤ) + n)
  | 0, n =>
      eqToIso (tensorPowerSheafInt_zero ℒ) ▷ᵢ (ℒ ^⊗ n) ≪≫
        tensorPowerSheafIntUnitLeftIso (ℒ ^⊗ n) ≪≫
        eqToIso (congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by omega))
  | m + 1, n =>
      let h : (((m : ℤ) + n) + 1) = (((m + 1 : ℕ) : ℤ) + n) := by
        omega
      (tensorPowerSheafIntNatSuccIso ℒ m ▷ᵢ (ℒ ^⊗ n)) ≪≫
        α_ ℒ (ℒ ^⊗ (m : ℤ)) (ℒ ^⊗ n) ≪≫
        (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntNatAddIsoAux ℒ m n) ≪≫
        tensorPowerSheafIntOneAddIsoAux ℒ ((m : ℤ) + n) ≪≫
        eqToIso (congrArg (fun k : ℤ ↦ ℒ ^⊗ k) h)

/-- Tensoring once by `\mathcal L` shifts the integral tensor-power owner by one degree. For
negative degrees this uses the canonical evaluation isomorphism
`\mathcal L \otimes \mathcal L^{-1} \cong \mathcal O_X` of an invertible sheaf. -/
noncomputable def tensorPowerSheafIntOneAddIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (n : ℤ) :
    (ℒ ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (n + 1) :=
  tensorPowerSheafIntOneAddIsoAux ℒ n

/-- Tensoring `\mathcal L^{\otimes m}` with `\mathcal L^{\otimes n}` for `m,n \in \mathbf N`
canonically identifies with `\mathcal L^{\otimes (m+n)}`. -/
noncomputable def tensorPowerSheafIntNatAddIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (m n : ℕ) :
    ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ (n : ℤ))) ≅
      ℒ ^⊗ (((m + n : ℕ) : ℤ)) :=
  tensorPowerSheafIntNatAddIsoAux ℒ m (n : ℤ) ≪≫
    eqToIso (tensorPowerSheafInt_natAdd_eq ℒ m n)

/-- Companion: tensoring two recursive-model powers
`\mathcal L^{\otimes m}` and `\mathcal L^{\otimes n}` canonically identifies with
`\mathcal L^{\otimes (m+n)}`. For negative exponents this is obtained by rewriting
`\mathcal L^{\otimes (-r)}` as a positive tensor power of the canonical dual and using the
evaluation isomorphism of an invertible sheaf. -/
noncomputable def tensorPowerSheafIntAddIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (m n : ℤ) :
    ((ℒ ^⊗ m) ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (m + n) := by
  cases m with
  | ofNat m =>
      exact tensorPowerSheafIntNatAddIsoAux ℒ m n
  | negSucc a =>
      cases n with
      | ofNat n =>
          exact (β_ (ℒ ^⊗ Int.negSucc a) (ℒ ^⊗ (n : ℤ))) ≪≫
            tensorPowerSheafIntNatAddIsoAux ℒ n (Int.negSucc a) ≪≫
            eqToIso (congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (Int.add_comm (n : ℤ) (Int.negSucc a)))
      | negSucc b =>
          exact (eqToIso rfl ⊗ᵢ eqToIso rfl) ≪≫
            tensorPowerSheafIntNatAddIso (ringedSiteModuleDual ℒ) (a + 1) (b + 1) ≪≫
            eqToIso (
              calc
                (ringedSiteModuleDual ℒ) ^⊗ ((((a + 1) + (b + 1) : ℕ) : ℤ)) =
                    (ringedSiteModuleDual ℒ) ^⊗ (((a + b + 2 : ℕ) : ℤ)) := by
                      exact congrArg (fun k : ℤ ↦ (ringedSiteModuleDual ℒ) ^⊗ k) (by omega)
                _ = ℒ ^⊗ Int.negSucc (a + b + 1) := rfl
                _ = ℒ ^⊗ (Int.negSucc a + Int.negSucc b) := by
                      exact congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by omega)
            )

end AlgebraicGeometry.RingedSpace
