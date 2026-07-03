import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_26_1 (from Chap17) -/
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

/-! ### Lemma_17_26_2 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.26.2:
- primary domain: determinant subsheaves of flat finitely presented module sheaves on a ringed
  space and their invertibility;
- inspected owner declarations:
  `determinantSheaf`,
  `Module.det`,
  `IsFlat`,
  `SheafOfModules.IsFinitePresentation`,
  `isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat`,
  `isInvertible_of_isFiniteLocallyFreeOfRank_one`;
- best owner abstraction: the source-facing owner is the determinant subsheaf `det(ℱ)` from
  `Lemma_17_26_1`, defined intrinsically inside `Λ(ℱ)`; flatness and finite presentation are the
  primitive hypotheses, while the constant-rank top exterior-power results are bridge API;
- primitive data: a module sheaf `ℱ : ModX` together with `ℱ.IsFinitePresentation` and
  `IsFlat X.sheaf ℱ`;
- derived API: invertibility of `det(ℱ)`, transport of invertibility along determinant
  presentations, and the finite-locally-free specialization to `Λ^[r] ℱ`.

Source/core/bridge triage:
- `source-facing`: the invertibility of the determinant sheaf of a flat finitely presented
  `\mathcal O_X`-module;
- `core/canonical`: `determinantSheaf`, `IsFlat`,
  `SheafOfModules.IsFinitePresentation`, and `IsInvertible`;
- `bridge/view`: the constant-rank top exterior model `Λ^[r] ℱ`, its rank-one specialization, and
  transport along an isomorphism `𝒟 ≅ det(ℱ)`.

The determinant owner `det(ℱ)` is defined using the closed monoidal structure from
`Lemma_17_26_1`, so the determinant-sheaf theorems below genuinely live in that stronger ambient
context. Their public content stays at the invertible-owner layer on an arbitrary ringed space.
By contrast, the top-exterior companions are separate constant-rank bridge results stated over the
weaker canonical context from `Definition_17_14_1` and `Lemma_17_25_4`. -/

section Determinant

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

-- Proof sketch: by Lemma `17.18.3`, a flat finitely presented sheaf is locally a direct summand
-- of a finite free sheaf. On such a neighbourhood the determinant subsheaf identifies with the
-- determinant line of the corresponding finite projective module, which is an invertible module.
-- These local determinant-line identifications give the invertibility of `det(ℱ)`.
/-- Lemma 17.26.2: if `\mathcal F` is a flat finitely presented `\mathcal O_X`-module, then its
annihilator-defined determinant sheaf `det(\mathcal F) \subset \bigwedge \mathcal F` is
invertible. -/
theorem determinantSheaf_isInvertible
    (ℱ : ModX) [ℱ.IsFinitePresentation] [IsFlat X.sheaf ℱ] :
    IsInvertible (det(ℱ)) := by
  sorry

-- Proof sketch: transport the invertible structure along the comparison isomorphism.
/-- Any presentation of the determinant sheaf of a flat finitely presented module is invertible. -/
theorem isInvertible_of_determinantSheafIso
    (ℱ 𝒟 : ModX)
    [ℱ.IsFinitePresentation] [IsFlat X.sheaf ℱ]
    (e𝒟 : 𝒟 ≅ det(ℱ)) :
    IsInvertible 𝒟 := by
  sorry

end Determinant

section TopExterior

-- Proof sketch: around each point, trivialize `ℱ` by the free rank-`r` module sheaf
-- `\mathcal O_U^{\oplus r}`. On that neighbourhood, `Λ^[r] ℱ` identifies with the top exterior
-- power of a free rank-`r` module, hence with the free rank-one module sheaf `\mathcal O_U`.
/-- For a finite locally free sheaf of constant rank `r`, the top exterior power
`\bigwedge^r \mathcal F` is finite locally free of rank `1`. -/
theorem topExteriorPower_isFiniteLocallyFreeOfRank_one
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (Λ^[r] ℱ) := by
  sorry

section Invertible

variable [MonoidalCategory (RingedSpace.Modules X)]

-- Proof sketch: apply Lemma `17.25.4` to the rank-one locally free sheaf
-- `\bigwedge^r \mathcal F`.
/-- The constant-rank top exterior-power model `\bigwedge^r \mathcal F` of a finite locally free
rank-`r` sheaf is invertible. -/
theorem topExteriorPower_isInvertible
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    IsInvertible (Λ^[r] ℱ) := by
  sorry

end Invertible

end TopExterior

end AlgebraicGeometry.RingedSpace
