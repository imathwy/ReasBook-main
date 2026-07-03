import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Sites.Monoidal
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap17.Lemma_17_16_2
import stacks_project.Chap17.Lemma_17_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.4:
- primary domain: internal Hom for sheaves of modules on a ringed space and its comparison with
  stalkwise linear maps;
- inspected owner declarations:
  notation `A ⟶[C] B`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `AlgebraicGeometry.RingedSpace.moduleStalkHom`,
  `AlgebraicGeometry.RingedSpace.tensorProductStalkIso`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`;
- best owner abstraction:
  the source-facing comparison should be written on the theorem surface through the canonical
  internal-Hom owner notation `A ⟶[C] B`, with `RingedSpace.stalkModuleCat` supplying the stalk
  module owner and `ModuleCat` supplying the stalk internal Hom;
- primitive data:
  a ringed space `X`, sheaves `ℱ 𝒢 : (RingedSpace.Modules X)`, and a point `x : X`;
- derived API:
  the canonical comparison morphism from the stalk of `ℱ ⟶[ModX] 𝒢` to the internal Hom of the
  stalk modules, together with its finite-type and finite-presentation consequences.

Source/core/bridge triage:
- `source-facing`: the canonical comparison
  `(\mathcal H\!om_{\mathcal O_X}(\mathcal F,\mathcal G))_x →
    \mathcal H\!om_{\mathcal O_{X,x}}(\mathcal F_x,\mathcal G_x)`;
- `core/canonical`: `(RingedSpace.Modules X)`, `RingedSpace.stalkModuleCat`, `tensorProductStalkIso`, and
  `ihom`;
- `bridge/view`: the induced stalk morphism of the evaluation map, curried after transporting
  across the tensor-stalk isomorphism.
-/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "StalkMod" x => ModuleCat (X.presheaf.stalk x)
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)
set_option quotPrecheck false in
local notation A " ⟶[StalkMod " x "] " B:10 => ((@ihom (StalkMod x) _ _ A _).obj B)

private abbrev tensorModel (ℱ 𝒢 : ModX) : ModX :=
  ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)) ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (moduleTensor ℱ 𝒢)

private theorem tensorModel_eq_tensorObj
    (ℱ 𝒢 : ModX) :
    tensorModel ℱ 𝒢 = (ℱ ⊗ 𝒢 : ModX) := by
  sorry

private noncomputable abbrev moduleTensorIsoTensorObj
    (ℱ 𝒢 : ModX) :
    moduleTensor ℱ 𝒢 ≅ (ℱ ⊗ 𝒢 : ModX) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
      (moduleTensor ℱ 𝒢))).symm ≪≫
    eqToIso (tensorModel_eq_tensorObj ℱ 𝒢)

/-- The canonical comparison from the stalk of the sheaf internal Hom to the internal Hom of the
stalk modules. -/
noncomputable def internalHomStalkComparison
    (ℱ 𝒢 : ModX) (x : X) :
    stalkModuleCat (ℱ ⟶[ModX] 𝒢) x ⟶
      ((stalkModuleCat ℱ x) ⟶[StalkMod x] (stalkModuleCat 𝒢 x)) :=
  MonoidalClosed.curry
    ((tensorProductStalkIso ℱ (ℱ ⟶[ModX] 𝒢) x).inv ≫
      moduleStalkHom x
        ((moduleTensorIsoTensorObj ℱ (ℱ ⟶[ModX] 𝒢)).hom ≫
          (ihom.ev ℱ).app 𝒢))

/-- Uncurrying `internalHomStalkComparison` recovers the stalkwise evaluation morphism transported
across the stalk tensor-product isomorphism. -/
theorem uncurry_internalHomStalkComparison
    (ℱ 𝒢 : ModX) (x : X) :
    MonoidalClosed.uncurry (internalHomStalkComparison ℱ 𝒢 x) =
      (tensorProductStalkIso ℱ (ℱ ⟶[ModX] 𝒢) x).inv ≫
        moduleStalkHom x
          ((moduleTensorIsoTensorObj ℱ (ℱ ⟶[ModX] 𝒢)).hom ≫
            (ihom.ev ℱ).app 𝒢) := by
  exact MonoidalClosed.uncurry_curry _

-- Proof sketch: represent a germ of a local section of the internal-Hom sheaf by a morphism on
-- some neighbourhood of `x` and evaluate it on stalk germs using
-- `internalHomStalkComparison`. If `ℱ` is of finite type, a local morphism with zero stalk map
-- kills finitely many local generators after shrinking, hence vanishes near `x`.
/-- Lemma 17.22.4, injective clause: if `\mathcal F` is of finite type, then the canonical
comparison
`(\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G))_x \to
\mathcal H\!\mathit{om}_{\mathcal O_{X, x}}(\mathcal F_x, \mathcal G_x)`
is injective. -/
theorem internalHomStalkComparison_injective_of_isFiniteType
    (ℱ 𝒢 : ModX) (x : X) [ℱ.IsFiniteType] :
    Function.Injective (internalHomStalkComparison ℱ 𝒢 x) := sorry

-- Proof sketch: choose a finite presentation of `ℱ` locally, apply Lemma `17.22.2` to the
-- induced left exact sequence of internal-Hom sheaves, and compare with the corresponding exact
-- sequence of stalk `Hom` modules. The finite-type injectivity clause handles the left term.
/-- Lemma 17.22.4, isomorphism clause: if `\mathcal F` is finitely presented, then the canonical
comparison
`(\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G))_x \to
\mathcal H\!\mathit{om}_{\mathcal O_{X, x}}(\mathcal F_x, \mathcal G_x)`
is an isomorphism. -/
theorem internalHomStalkComparison_isIso_of_isFinitePresentation
    (ℱ 𝒢 : ModX) (x : X) [ℱ.IsFinitePresentation] :
    IsIso (internalHomStalkComparison ℱ 𝒢 x) := sorry

end AlgebraicGeometry.RingedSpace
