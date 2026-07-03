import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_project.Chap15.Lemma_15_119_2
import stacks_project.Chap17.Definition_17_14_1
import stacks_project.Chap17.Definition_17_23_1
import stacks_project.Chap17.Lemma_17_21_1
import stacks_project.Chap17.Lemma_17_21_3

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.26.1:
- primary domain: determinant subsheaves inside exterior algebra sheaves of `\mathcal O_X`-modules,
  with the finite locally free top-exterior model and short-exact multiplicativity as bridge data;
- inspected owner declarations:
  `Module.det`,
  `Module.mem_det_iff`,
  `Λ(ℱ)`,
  `Λ^[r] ℱ`,
  `SheafOfModules.annihilator`;
- best owner abstraction: the source-facing owner is the determinant subsheaf cut out inside the
  exterior algebra sheaf `Λ(ℱ)` by degree-one left multiplication, mirroring the module-level
  owner `Module.det`; finite locally free top-exterior-power presentations are derived bridge API,
  not the owner itself;
- primitive data: a module sheaf `ℱ : ModX`;
- derived API: the action map `Λ(ℱ) ⟶ \mathcal H\!om_{\mathcal O_X}(\mathcal F, \Lambda(\mathcal
  F))`, the kernel inclusion `det(ℱ) ⟶ Λ(ℱ)`, the constant-rank bridge
  `Λ^[r] ℱ ≅ det(ℱ)`, and the short-exact multiplicativity comparison.

Source/core/bridge triage:
- `source-facing`: the determinant sheaf owner `determinantSheaf ℱ` and the determinant tensor
  comparison for short exact sequences;
- `core/canonical`: `Λ(ℱ)`, `ihom`, `kernel`, `MonoidalClosed.curry`, and the module-level owner
  `Module.det`;
- `bridge/view`: the sectionwise degree-one left-multiplication map on `Λ(ℱ)`, the kernel
  inclusion `determinantSheafι`, and the constant-rank top exterior-power model. -/

/-- The commutative ring of sections of the structure sheaf over an open set. -/
private abbrev sectionRing (X : RingedSpace) (U : (Opens X)ᵒᵖ) :=
  X.presheaf.obj U

/-- The inverse of the sheafification counit for the underlying presheaf of a sheaf of
`\mathcal O_X`-modules. -/
private noncomputable abbrev sheafificationCounitInv
    (ℱ : ModX) :
    ℱ ⟶ (moduleSheafification X.sheaf).obj ℱ.val := by
  let e := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  exact (e.symm.app ℱ).hom

private abbrev tensorModel
    (ℱ 𝒢 : ModX) : ModX :=
  ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)) ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (moduleTensor ℱ 𝒢)

private theorem tensorModel_eq_tensorObj
    (ℱ 𝒢 : ModX) :
    tensorModel ℱ 𝒢 = (MonoidalCategoryStruct.tensorObj ℱ 𝒢 : ModX) := by
  sorry

private noncomputable abbrev moduleTensorIsoTensorObj
    (ℱ 𝒢 : ModX) :
    moduleTensor ℱ 𝒢 ≅ (MonoidalCategoryStruct.tensorObj ℱ 𝒢 : ModX) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
      (moduleTensor ℱ 𝒢))).symm ≪≫
    eqToIso (tensorModel_eq_tensorObj ℱ 𝒢)

/-- The presheaf-level degree-one left multiplication
`\mathcal F(U) \otimes \bigwedge \mathcal F(U) \to \bigwedge \mathcal F(U)`. -/
private noncomputable def determinantLeftTensorPresheafMap
    (ℱ : ModX) :
    PresheafOfModules.Monoidal.tensorObj ℱ.val (exteriorAlgebraPresheaf ℱ) ⟶
      exteriorAlgebraPresheaf ℱ where
  app U := by
    let R := sectionRing X U
    letI : CommRing R := by infer_instance
    change
      ModuleCat.of R ((ℱ.val.obj U) ⊗[R] ExteriorAlgebra R (ℱ.val.obj U)) ⟶
        ModuleCat.of R (ExteriorAlgebra R (ℱ.val.obj U))
    exact
      ModuleCat.ofHom <|
        (LinearMap.mul' R (ExteriorAlgebra R (ℱ.val.obj U))).comp
          (TensorProduct.map
            (ExteriorAlgebra.ι R)
            (LinearMap.id : ExteriorAlgebra R (ℱ.val.obj U) →ₗ[R]
              ExteriorAlgebra R (ℱ.val.obj U)))
  naturality := by
    intro U V i
    sorry

/-- The sheaf-level degree-one left multiplication
`\mathcal F \otimes \bigwedge \mathcal F \to \bigwedge \mathcal F`. -/
noncomputable def determinantLeftTensorMap
    (ℱ : ModX) :
    moduleTensor ℱ (Λ(ℱ)) ⟶ Λ(ℱ) :=
  moduleTensorMap (sheafificationCounitInv ℱ) (𝟙 (Λ(ℱ))) ≫
    (moduleSheafificationTensorIso X.sheaf ℱ.val (exteriorAlgebraPresheaf ℱ)).hom ≫
    (moduleSheafification X.sheaf).map (determinantLeftTensorPresheafMap ℱ)

/-- Currying degree-one left multiplication yields the action map
`\bigwedge \mathcal F \to \mathcal H\!om_{\mathcal O_X}(\mathcal F, \bigwedge \mathcal F)`. -/
noncomputable def determinantActionMap
    (ℱ : ModX) :
    Λ(ℱ) ⟶ (ihom ℱ).obj (Λ(ℱ)) :=
  MonoidalClosed.curry
    ((moduleTensorIsoTensorObj ℱ (Λ(ℱ))).inv ≫ determinantLeftTensorMap ℱ)

/-- The determinant sheaf of an `\mathcal O_X`-module is the subsheaf of `\bigwedge \mathcal F`
annihilated by degree-one left multiplication. -/
abbrev determinantSheaf (ℱ : ModX) : ModX :=
  kernel (determinantActionMap ℱ)

scoped[AlgebraicGeometry] notation3:max "det(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.determinantSheaf ℱ

/-- The determinant sheaf is definitionally the kernel of the degree-one action map on
`\bigwedge \mathcal F`. -/
theorem determinantSheaf_eq_kernel (ℱ : ModX) :
    det(ℱ) = kernel (determinantActionMap ℱ) :=
  rfl

/-- The determinant sheaf carries its canonical inclusion into the exterior algebra sheaf. -/
noncomputable abbrev determinantSheafι (ℱ : ModX) : det(ℱ) ⟶ Λ(ℱ) :=
  kernel.ι (determinantActionMap ℱ)

-- Proof sketch: if `ℱ` is finite locally free of constant rank `r`, then locally `ℱ` is a free
-- rank-`r` module. On each such neighbourhood, the module-level determinant owner of Remark
-- `15.119.1` identifies with the top exterior power, and these local identifications glue.
/-- For a finite locally free sheaf of constant rank `r`, the top exterior power
`\bigwedge^r \mathcal F` is canonically isomorphic to the determinant subsheaf `det(\mathcal F)`
inside `\bigwedge \mathcal F`. -/
theorem topExteriorPowerDeterminantSheafIso
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    Nonempty ((Λ^[r] ℱ) ≅ det(ℱ)) := by
  sorry

/- The owner exists by construction, so the source-facing existence statement remains a thin bridge
from the textbook existential phrasing to the canonical owner `det(ℱ)`. -/
/-- A module sheaf admits its canonical determinant subsheaf. -/
theorem exists_determinantSheaf
    (ℱ : ModX) :
    ∃ 𝒟 : ModX, Nonempty (𝒟 ≅ det(ℱ)) := by
  exact ⟨det(ℱ), ⟨Iso.refl _⟩⟩

/-- Any two determinant-sheaf presentations of the same module sheaf are compared by the canonical
isomorphism obtained by composing one presentation with the inverse of the other. -/
def determinantSheafComparisonIso
    (ℱ 𝒟 𝒟' : ModX)
    (e𝒟 : 𝒟 ≅ det(ℱ)) (e𝒟' : 𝒟' ≅ det(ℱ)) :
    𝒟 ≅ 𝒟' :=
  e𝒟 ≪≫ e𝒟'.symm

section ShortExact

variable {S : ShortComplex ModX}
variable [S.X₁.IsFiniteLocallyFree] [S.X₂.IsFiniteLocallyFree] [S.X₃.IsFiniteLocallyFree]

-- Proof sketch: refine locally to a neighbourhood where the three terms have constant ranks.
-- There the determinant subsheaf identifies with the top exterior power by
-- `topExteriorPowerDeterminantSheafIso`, and Chapter 15 gives the classical determinant tensor
-- comparison. The local maps glue to the global comparison below.
/-- For a short exact sequence of finite locally free modules, any chosen determinant-sheaf
presentations of the left and right terms tensor to a determinant-sheaf presentation of the middle
term. Taking the identity presentations recovers the canonical textbook comparison. -/
theorem determinantSheafTensorIso
    (hS : S.ShortExact)
    {𝒟₁ 𝒟₃ : ModX}
    (e𝒟₁ : 𝒟₁ ≅ determinantSheaf S.X₁)
    (e𝒟₃ : 𝒟₃ ≅ determinantSheaf S.X₃) :
    Nonempty (moduleTensor 𝒟₁ 𝒟₃ ≅ determinantSheaf S.X₂) := by
  sorry

end ShortExact

end AlgebraicGeometry.RingedSpace
