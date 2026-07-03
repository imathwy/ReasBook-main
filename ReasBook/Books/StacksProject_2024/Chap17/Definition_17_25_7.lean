import Mathlib
import StacksProject_2024.Chap17.Definition_17_25_6
import StacksProject_2024.Chap17.Definition_17_23_1
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DirectSum

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X
local notation "ΓX" => X.presheaf.obj (op ⊤)
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

local instance : VAdd ℕ ℤ where
  vadd n i := (n : ℤ) + i

/- Domain-style sampling for Definition 17.25.7:
- primary domain: graded global sections attached to a sheaf of `\mathcal O_X`-modules, together
  with the `\mathbb Z`-graded twisted version attached to an invertible sheaf;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `tensorPowerSheaf`,
  `tensorPowerSheafInt`,
  `ringedSiteModuleDual`,
  `SheafOfModules.unitToTensorUnit`,
  `DirectSum.GCommRing`,
  `DirectSum.Gmodule`,
  `moduleTensor`;
- best owner abstraction: the source-facing owners are the direct sums
  `\Gamma_*(X, \mathcal L)` and `\Gamma_*(X, \mathcal L, \mathcal F)`, equipped with the canonical
  graded ring and graded module structures supplied by mathlib's direct-sum graded owners;
- primitive data: a sheaf `ℒ : ModX` for the ring owner, and an invertible sheaf `ℒ : ModX`
  together with `ℱ : ModX` for the twisted module owner;
- derived API: the top-open `ModuleCat ΓX` summands, the tensoring maps on homogeneous pieces, and
  the resulting external direct-sum ring/module owners, with the ring multiplication coming from
  the nonnegative tensor-power owner `tensorPowerSheaf` and the twisted action map coming from
  `tensorPowerSheafIntMul` in Definition 17.25.6.

Layer triage:
- `source-facing`: `\Gamma_*(X, \mathcal L)` and `\Gamma_*(X, \mathcal L, \mathcal F)`;
- `core/canonical`: the chapter owner `RingedSpace.Modules X`, the nonnegative tensor-power owner
  `T^[n] ℒ`, the integral tensor-power owner `ℒ ^⊗ n`, the twist owner `moduleTensor ℱ (ℒ ^⊗ n)`,
  the canonical tensor-unit comparison `unitToTensorUnit`, and the graded direct-sum owners
  `DirectSum.GCommRing` / `DirectSum.Gmodule`, with the negative branch using the canonical dual
  owner `ringedSiteModuleDual ℒ`;
- `bridge/view`: the degreewise identification theorems and the pure-degree multiplication/action
  maps, with the ring multiplication obtained by recursively tensoring the nonnegative tensor-power
  owner and the twisted module action obtained from associativity, symmetry, and whiskering of
  `tensorPowerSheafIntMul`.
-/

/-- The degree-`n` homogeneous piece of `\Gamma_*(X, \mathcal L)`. -/
abbrev gradedGlobalSectionsDegree
    (ℒ : ModX) (n : ℕ) : ModuleCat ΓX :=
  (T^[n] ℒ).val.obj (op ⊤)

/-- The degree-`n` homogeneous piece of `\Gamma_*(X, \mathcal L, \mathcal F)`. -/
abbrev gradedTwistedGlobalSectionsDegree
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) (n : ℤ) :
    ModuleCat ΓX :=
  (moduleTensor ℱ (ℒ ^⊗ n)).val.obj (op ⊤)

/-- Definition 17.25.7 (1): `\Gamma_*(X, \mathcal L)` is the direct sum of the nonnegative
tensor-power global sections. -/
abbrev gradedGlobalSections
    (ℒ : ModX) : Type _ :=
  ⨁ n : ℕ, gradedGlobalSectionsDegree ℒ n

/-- Definition 17.25.7 (2): `\Gamma_*(X, \mathcal L, \mathcal F)` is the direct sum of the
integer-indexed twisted global sections. -/
abbrev gradedTwistedGlobalSections
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) : Type _ :=
  ⨁ n : ℤ, gradedTwistedGlobalSectionsDegree ℒ ℱ n

/-- Textbook notation for the graded ring of global sections `\Gamma_*(X, \mathcal L)`. -/
scoped[AlgebraicGeometry] notation3:max "Γ_*(" ℒ ")" =>
  AlgebraicGeometry.RingedSpace.gradedGlobalSections ℒ

/-- Textbook notation for the graded module of twisted global sections
`\Gamma_*(X, \mathcal L, \mathcal F)`. -/
scoped[AlgebraicGeometry] notation3:max "Γ_*(" ℒ ", " ℱ ")" =>
  AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections ℒ ℱ

private noncomputable def tensorPowerSheafUnitLeftIso
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℱ : ModX) :
    (𝒪X ⊗ₘ ℱ) ≅ ℱ :=
  (SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ

private noncomputable def tensorTopHom
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℱ 𝒢 : ModX) :
    (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val).obj (op ⊤) ⟶
      (moduleTensor ℱ 𝒢).val.obj (op ⊤) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (show PresheafOfModules X.ringCatSheaf.obj from
      PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val)).app (op ⊤)

private noncomputable def tensorPowerSheafNatAddIso
    [MonoidalCategory ModX]
    [SymmetricCategory ModX]
    [MonoidalClosed ModX]
    (ℒ : ModX) :
    (m n : ℕ) →
      ((tensorPowerSheaf ℒ m) ⊗ₘ (tensorPowerSheaf ℒ n)) ≅ tensorPowerSheaf ℒ (m + n)
  | 0, n =>
      let zeroIso :
          ((tensorPowerSheaf ℒ 0) ⊗ₘ tensorPowerSheaf ℒ n) ≅
            (𝒪X ⊗ₘ tensorPowerSheaf ℒ n) :=
        eqToIso rfl ▷ᵢ tensorPowerSheaf ℒ n
      let unitIso :
          (𝒪X ⊗ₘ tensorPowerSheaf ℒ n) ≅ tensorPowerSheaf ℒ n :=
        tensorPowerSheafUnitLeftIso (tensorPowerSheaf ℒ n)
      let reindexIso :
          tensorPowerSheaf ℒ n ≅ tensorPowerSheaf ℒ (0 + n) :=
        eqToIso (congrArg (tensorPowerSheaf ℒ) (by simp))
      zeroIso ≪≫ unitIso ≪≫ reindexIso
  | m + 1, n =>
      let succIso :
          ((tensorPowerSheaf ℒ (m + 1)) ⊗ₘ tensorPowerSheaf ℒ n) ≅
            ((((ℒ ⊗ₘ tensorPowerSheaf ℒ m : ModX)) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) :=
        moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ m) ▷ᵢ tensorPowerSheaf ℒ n
      let assocIso :
          ((((ℒ ⊗ₘ tensorPowerSheaf ℒ m : ModX)) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) ≅
            (ℒ ⊗ₘ ((tensorPowerSheaf ℒ m) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) :=
        α_ ℒ (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n)
      let mulIso :
          (ℒ ⊗ₘ ((tensorPowerSheaf ℒ m) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) ≅
            (ℒ ⊗ₘ tensorPowerSheaf ℒ (m + n) : ModX) :=
        Iso.refl ℒ ⊗ᵢ tensorPowerSheafNatAddIso ℒ m n
      let targetIso :
          (ℒ ⊗ₘ tensorPowerSheaf ℒ (m + n) : ModX) ≅ tensorPowerSheaf ℒ ((m + n) + 1) :=
        (moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ (m + n))).symm
      let h : (m + n) + 1 = (m + 1) + n := by
        omega
      let reindexIso :
          tensorPowerSheaf ℒ ((m + n) + 1) ≅ tensorPowerSheaf ℒ ((m + 1) + n) :=
        eqToIso (congrArg (tensorPowerSheaf ℒ) h)
      succIso ≪≫ assocIso ≪≫ mulIso ≪≫ targetIso ≪≫ reindexIso

private noncomputable def tensorTopToTensorObjHom
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℱ 𝒢 : ModX) :
    (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val).obj (op ⊤) ⟶
      ((ℱ ⊗ₘ 𝒢 : ModX).val.obj (op ⊤)) :=
  tensorTopHom ℱ 𝒢 ≫ (moduleTensorIsoTensorObj ℱ 𝒢).hom.val.app (op ⊤)

private noncomputable def gradedGlobalSectionsMul
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) (m n : ℕ)
    (x : gradedGlobalSectionsDegree ℒ m) (y : gradedGlobalSectionsDegree ℒ n) :
    gradedGlobalSectionsDegree ℒ (m + n) :=
  let mulApp :
      ((tensorObj (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n) : ModX).val.obj (op ⊤)) ⟶
        gradedGlobalSectionsDegree ℒ (m + n) :=
    show ((tensorObj (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n) : ModX).val.obj (op ⊤)) ⟶
        (tensorPowerSheaf ℒ (m + n)).val.obj (op ⊤) from
      (tensorPowerSheafNatAddIso ℒ m n).hom.val.app (op ⊤)
  let mulHom :
      (PresheafOfModules.Monoidal.tensorObj
        (tensorPowerSheaf ℒ m).val (tensorPowerSheaf ℒ n).val).obj (op ⊤) ⟶
        gradedGlobalSectionsDegree ℒ (m + n) :=
    tensorTopToTensorObjHom (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n) ≫ mulApp
  mulHom (x ⊗ₜ y)

private noncomputable def gradedTwistedGlobalSectionsSheafSmul
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) :
    (m : ℕ) → (n : ℤ) →
      ((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n) : ModX) ⟶
        (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n)) : ModX)
  | m, n =>
      let shiftLeft :
          ((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n) : ModX) ⟶
            ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) :=
        show ((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n) : ModX) ⟶
            ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) from
          ((ℒ ^⊗ (m : ℤ)) ◁ (moduleTensorIsoTensorObj ℱ (ℒ ^⊗ n)).hom)
      let assocLeft :
          ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) :=
        show ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) from
          (α_ (ℒ ^⊗ (m : ℤ)) ℱ (ℒ ^⊗ n)).inv
      let braiding :
          (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) :=
        show (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) from
          ((β_ (ℒ ^⊗ (m : ℤ)) ℱ).hom ▷ (ℒ ^⊗ n))
      let assocRight :
          ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) :=
        show ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) from
          (α_ ℱ (ℒ ^⊗ (m : ℤ)) (ℒ ^⊗ n)).hom
      let mulWhisker :
          (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) :=
        show (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) from
          (ℱ ◁ (tensorPowerSheafIntAddIso ℒ (m : ℤ) n).hom)
      let shiftRight :
          (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) ⟶
            (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) :=
        show (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) ⟶
            (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) from
          (moduleTensorIsoTensorObj ℱ (ℒ ^⊗ ((m : ℤ) + n))).inv
      shiftLeft ≫ assocLeft ≫ braiding ≫ assocRight ≫ mulWhisker ≫ shiftRight

private noncomputable def gradedTwistedGlobalSectionsSmul
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) (m : ℕ) (n : ℤ)
    (x : gradedGlobalSectionsDegree ℒ m) (y : gradedTwistedGlobalSectionsDegree ℒ ℱ n) :
    gradedTwistedGlobalSectionsDegree ℒ ℱ ((m : ℤ) + n) :=
  let smulApp :
      (((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n)).val.obj (op ⊤)) ⟶
        (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n))).val.obj (op ⊤) :=
    show (((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n)).val.obj (op ⊤)) ⟶
        (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n))).val.obj (op ⊤) from
      (gradedTwistedGlobalSectionsSheafSmul ℒ ℱ m n).val.app (op ⊤)
  let smulHom :
      (PresheafOfModules.Monoidal.tensorObj
        ((ℒ ^⊗ (m : ℤ)).val) ((moduleTensor ℱ (ℒ ^⊗ n)).val)).obj (op ⊤) ⟶
        gradedTwistedGlobalSectionsDegree ℒ ℱ ((m : ℤ) + n) :=
    tensorTopToTensorObjHom (ℒ ^⊗ (m : ℤ)) (moduleTensor ℱ (ℒ ^⊗ n)) ≫ smulApp
  smulHom (x ⊗ₜ y)

/-- The homogeneous pieces of `Γ_*(ℒ)` form the canonical graded commutative ring owner. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) :
    DirectSum.GCommRing (fun n ↦ gradedGlobalSectionsDegree ℒ n) where
  one := show gradedGlobalSectionsDegree ℒ 0 from (1 : ΓX)
  mul := fun {m n} x y ↦ gradedGlobalSectionsMul ℒ m n x y
  one_mul := by
    intro a
    sorry
  mul_one := by
    intro a
    sorry
  mul_assoc := by
    intro a b c
    sorry
  mul_zero := by
    intro m n x
    sorry
  zero_mul := by
    intro m n y
    sorry
  mul_add := by
    intro m n x y z
    sorry
  add_mul := by
    intro m n x y z
    sorry
  natCast n := show gradedGlobalSectionsDegree ℒ 0 from (n : ΓX)
  natCast_zero := by
    sorry
  natCast_succ := by
    intro n
    sorry
  intCast z := show gradedGlobalSectionsDegree ℒ 0 from (z : ΓX)
  intCast_ofNat := by
    intro n
    sorry
  intCast_negSucc_ofNat := by
    intro n
    sorry
  mul_comm := by
    intro a b
    sorry
  gnpow_zero' := by
    sorry
  gnpow_succ' := by
    sorry

/-- The homogeneous pieces of `Γ_*(ℒ, ℱ)` form the canonical graded module over `Γ_*(ℒ)`. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) :
    DirectSum.Gmodule
      (fun n ↦ gradedGlobalSectionsDegree ℒ n)
      (fun n ↦ gradedTwistedGlobalSectionsDegree ℒ ℱ n) where
  smul := fun {m n} x y ↦ gradedTwistedGlobalSectionsSmul ℒ ℱ m n x y
  one_smul := by
    intro a
    sorry
  mul_smul := by
    intro a b c
    sorry
  smul_add := by
    intro m n x y z
    sorry
  smul_zero := by
    intro m n x
    sorry
  add_smul := by
    intro m n x y z
    sorry
  zero_smul := by
    intro m n y
    sorry

/-- The source-facing owner `Γ_*(ℒ)` carries its canonical commutative ring structure. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) :
    CommRing (Γ_*(ℒ)) :=
  inferInstance

/-- The source-facing owner `Γ_*(ℒ, ℱ)` carries its canonical module structure over `Γ_*(ℒ)`. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) :
    Module (Γ_*(ℒ)) (Γ_*(ℒ, ℱ)) :=
  inferInstance

end AlgebraicGeometry.RingedSpace
