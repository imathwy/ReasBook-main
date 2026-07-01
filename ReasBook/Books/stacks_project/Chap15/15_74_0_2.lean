import Mathlib
import stacks_project.Chap15.«15_74_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open scoped DerivedInternalHom
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The degree-zero derived object `R[0]`, viewed as the tensor unit input for derived duality and
the canonical ring object in `D(R)`. -/
abbrev ringSingle : DMod :=
  (single₀).obj (ModuleCat.of R R)

end

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "𝓗" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for 15.74.0.2:
- primary domain: cohomology of chosen derived internal-Hom objects in `D(R)` and its comparison
  with shifted morphisms in the derived category;
- sampled owner declarations:
  `DerivedInternalHom.obj`,
  `DerivedInternalHom.tensorLeftAdj`,
  `DerivedCategory.homologyFunctor`,
  `ShiftedHom`;
- best owner abstraction: the source-facing bridge should compare the cohomology module
  `H^n(RHom_R(L, M))`, realized as
  `((DerivedCategory.homologyFunctor (ModuleCat R) n).obj (RHom[H](L, M)))`, with the canonical
  `R`-module `ShiftedHom L M n`;
- primitive data: only the chosen derived internal-Hom owner `H : MonoidalClosed DMod`;
- derived API: the canonical tensor-unit bridge `R[0] ⊗^L L ≅ L`, the module-level comparison
  between `H^n(RHom_R(L, M))` and `ShiftedHom L M n`, and the resulting linear equivalence;
- source/core/bridge triage:
  `source-facing`: the source statement `H^n(RHom_R(L, M)) = Hom_{D(R)}(L, M[n])`;
  `core/canonical`: `DerivedInternalHom.obj`, `DerivedCategory.homologyFunctor`, `ShiftedHom`;
  `bridge/view`: the tensor-unit comparison below, the explicit comparison morphism, and the
  resulting isomorphism.

The previous file weakened the statement to an `AddEquiv` on an `ULift`ed underlying type, and
then to a bare existence witness. This refinement keeps the `R`-module semantics on both sides
and exposes the actual comparison map, with the isomorphism packaged from its `IsIso` theorem.
-/

/-- The canonical identification `R[0] ≅ 𝟙` in `D(R)`. -/
noncomputable def singleZeroIsoTensorUnit :
    (single₀).obj (ModuleCat.of R R) ≅ 𝟙_ DMod :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      (ModuleCat.of R R)) ≪≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (ModuleCat.of R R))).symm

/-- The canonical identification `R[0] \otimes_R^{\mathbf L} L ≅ L` in `D(R)`. -/
noncomputable def singleZeroDerivedTensorIso (L : DMod) :
    ((single₀).obj (ModuleCat.of R R)) ⊗[R]^L L ≅ L :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      ((single₀).obj (ModuleCat.of R R))
      L).symm ≪≫
    whiskerRightIso singleZeroIsoTensorUnit L ≪≫
      λ_ L

section

-- Proof sketch: use the owner-side unit comparison
-- `(derivedTensorProduct L).obj R[0] ≅ L` and the shift-compatibility of `derivedTensorProduct L`
-- to transport the adjunction `H.derivedTensorAdj L` into a map
-- `ShiftedHom L M n → H^n(RHom_R(L,M))`, viewed directly as an `R`-linear map.
/-- The canonical comparison map
`Hom_{D(R)}(L, M[n]) → H^n(RHom_R(L, M))`
attached to a chosen derived internal-Hom package on `D(R)`. -/
noncomputable def derivedHom_cohomology_comparison
    (H : RHomPkg) (L M : DMod) (n : ℤ) :
    ShiftedHom L M n →ₗ[R] (𝓗 n).obj (RHom[H](L, M)) where
  toFun := fun f ↦
    letI : MonoidalClosed DMod := H
    letI : (ihom L).CommShift ℤ :=
      (H.derivedTensorAdj L).rightAdjointCommShift ℤ
    let g :
        ((single₀).obj (ModuleCat.of R R)) ⟶ (RHom[H](L, M))⟦n⟧ :=
      (((H.derivedTensorAdj L).homEquiv
          ((single₀).obj (ModuleCat.of R R)) (M⟦n⟧))
          ((singleZeroDerivedTensorIso L).hom ≫ f)) ≫
        ((ihom L).commShiftIso n).hom.app M
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R R)) ≫
      (𝓗 0).shiftMap g 0 n (add_zero n)) (1 : ModuleCat.of R R)
  map_add' := by
    intro f g
    sorry
  map_smul' := by
    intro r f
    sorry

/-- 15.74.0.2: for a chosen derived internal-Hom package on `D(R)`, the degree-`n` cohomology
module of `RHom_R(L, M)` is canonically linearly equivalent to the canonical shifted-Hom module
`ShiftedHom L M n = Hom_{D(R)}(L, M[n])`. -/
noncomputable abbrev derivedHom_cohomology_iso_shiftedHom
    (H : RHomPkg) (L M : DMod) (n : ℤ) :
    ((𝓗 n).obj (RHom[H](L, M))) ≃ₗ[R] ShiftedHom L M n :=
  (LinearEquiv.ofBijective
      (derivedHom_cohomology_comparison H L M n)
      (by
        sorry)).symm

end

end

end CategoryTheory
