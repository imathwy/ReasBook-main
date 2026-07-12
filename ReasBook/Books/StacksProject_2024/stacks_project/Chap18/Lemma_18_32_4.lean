import Mathlib
import StacksProject_2024.Chap04.Lemma_4_43_3
import StacksProject_2024.Chap18.Definition_18_32_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.4:
- primary domain: invertible objects and duality in the symmetric monoidal closed category
  `ringedSiteModuleCategory J 𝒪`;
- sampled owner declarations:
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.iso_internalHom_unit_of_tensor_inverse`;
- best owner abstraction:
  `Functor.IsEquivalence (tensorRight ℒ)` on `ringedSiteModuleCategory J 𝒪`, with the tensor
  product `ℒ ⊗ 𝒩`,
  `ℒ ⟶[Mod] (SheafOfModules.unit (ringSheaf J 𝒪))`, and the closed-structure evaluation at the
  tensor unit as derived API;
- primitive data:
  invertible modules `ℒ` and `𝒩`;
- derived API:
  invertibility of `ℒ ⊗ 𝒩`, invertibility of `ℒ ⟶[Mod] (SheafOfModules.unit (ringSheaf J 𝒪))`,
  and the `IsIso` statement for the evaluation map at `SheafOfModules.unit (ringSheaf J 𝒪)`.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 18.32.4;
- `core/canonical`: `Functor.IsEquivalence (tensorRight ℒ)`,
  `ℒ ⟶[Mod] (SheafOfModules.unit (ringSheaf J 𝒪))`, and
  `(ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))`;
- `bridge/view`: the tensor-inverse and dual-comparison theorems from Lemma 18.32.2.
-/

section Tensor

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: right tensoring by `\mathcal L \otimes_{\mathcal O} \mathcal N` is the composite
-- of right tensoring by `\mathcal L` and by `\mathcal N`, so it is an equivalence when each
-- factor is.
/-- First clause of Lemma 18.32.4: if `\mathcal L` and `\mathcal N` are invertible `\mathcal O`-modules on a
ringed site, then their tensor product `\mathcal L \otimes_{\mathcal O} \mathcal N` is
invertible. -/
theorem isInvertible_tensor_of_isInvertible
    (L N : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight L)]
    [Functor.IsEquivalence (tensorRight N)] :
    Functor.IsEquivalence (tensorRight (L ⊗ N)) := by
  letI : Functor.IsEquivalence (tensorRight L ⋙ tensorRight N) := by
    infer_instance
  -- Proof comment: tensoring by `L ⊗ N` is canonically the composite of tensoring by `L` and
  -- then by `N`, so equivalence transports across `tensorRightTensor`.
  exact Functor.isEquivalence_of_iso (tensorRightTensor L N).symm

instance instIsInvertibleTensor
    (L N : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight L)]
    [Functor.IsEquivalence (tensorRight N)] :
    Functor.IsEquivalence (tensorRight (L ⊗ N)) :=
  isInvertible_tensor_of_isInvertible L N

end Tensor

section Duality

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "𝒪Mod" => (𝟙_ Mod : Mod)

/-- Helper for Lemma 18.32.4: invertibility for right tensoring transports to left tensoring via
the braiding isomorphism. -/
private theorem isEquivalence_tensorLeft_of_isInvertible
    (L : Mod)
    [Functor.IsEquivalence (tensorRight L)] :
    Functor.IsEquivalence (tensorLeft L) := by
  -- Proof comment: in a braided monoidal category, left tensoring by `L` is naturally
  -- isomorphic to right tensoring by `L`, so equivalence transports across the braiding.
  exact Functor.isEquivalence_of_iso (BraidedCategory.tensorLeftIsoTensorRight L).symm

variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

private abbrev ringedSiteModuleDual (L : Mod) :=
  (ihom L).obj (SheafOfModules.unit (ringSheaf J 𝒪))

/-- Helper for Lemma 18.32.4: the evaluation map is the counit component of `ihom.adjunction`,
and that counit is an isomorphism once tensoring on the left by `L` is an equivalence. -/
private theorem isIso_internalHom_unit_evaluation_of_isInvertible_aux
    (L : Mod)
    [Functor.IsEquivalence (tensorRight L)] :
    IsIso ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) := by
  letI : Functor.IsEquivalence (tensorLeft L) :=
    isEquivalence_tensorLeft_of_isInvertible (J := J) (𝒪 := 𝒪) L
  -- Proof comment: rewrite the evaluation map as the adjunction counit, then use the standard
  -- fact that the counit of an adjunction is an isomorphism when the left adjoint is an
  -- equivalence.
  simpa [ihom.ihom_adjunction_counit] using
    (inferInstance :
      IsIso ((ihom.adjunction L).counit.app (SheafOfModules.unit (ringSheaf J 𝒪))))

-- Proof sketch: by Lemma `18.32.2 (1)`, choose a tensor inverse `𝒩` for `ℒ`; then Lemma
-- `18.32.2 (5)` identifies `𝒩` with `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L,
-- \mathcal O)`, so the internal Hom inherits invertibility from the tensor inverse.
/-- Second clause of Lemma 18.32.4: if `\mathcal L` is an invertible `\mathcal O`-module on a ringed site,
then `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)` is invertible. -/
theorem isInvertible_internalHom_unit_of_isInvertible
    (L : Mod)
    [Functor.IsEquivalence (tensorRight L)] :
    Functor.IsEquivalence (tensorRight (ringedSiteModuleDual L)) := by
  let evalIso : IsIso ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) :=
    isIso_internalHom_unit_evaluation_of_isInvertible_aux (J := J) (𝒪 := 𝒪) L
  letI : IsIso ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) := evalIso
  let e :
      (L ⊗ ringedSiteModuleDual L) ≅ 𝒪Mod :=
    { hom :=
        ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) ≫
          (SheafOfModules.RingedSite.unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).hom
      inv :=
        (SheafOfModules.RingedSite.unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv ≫
          @inv _ _ _ _ ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) evalIso
      hom_inv_id := by
        simp [Category.assoc]
      inv_hom_id := by
        simp [Category.assoc] }
  -- Proof comment: the evaluation isomorphism gives a tensor trivialization
  -- `L ⊗ Lᘁ ≅ \mathcal O`, and the symmetric braiding supplies the opposite trivialization.
  exact
    (tensorRight_isEquivalence_iff_exists_tensor_inverse (ringedSiteModuleDual L)).2
      ⟨L, ⟨(β_ (ringedSiteModuleDual L) L) ≪≫ e⟩, ⟨e⟩⟩

instance instIsInvertibleInternalHomUnit
    (L : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight L)] :
    Functor.IsEquivalence (tensorRight (ringedSiteModuleDual L)) :=
  isInvertible_internalHom_unit_of_isInvertible L

-- Proof sketch: identify `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)` with a
-- tensor inverse of `ℒ` via Lemma `18.32.2 (5)`. Under this identification, the evaluation map
-- becomes the chosen trivialization `\mathcal L \otimes_{\mathcal O} \mathcal L^\vee \cong
-- \mathcal O`, hence it is an isomorphism.
/-- Lemma 18.32.4: for an invertible `\mathcal O`-module `\mathcal L` on a ringed site, the
evaluation map
`\mathcal L \otimes_{\mathcal O} \mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)
\to \mathcal O` is an isomorphism. -/
theorem isIso_internalHom_unit_evaluation_of_isInvertible
    (L : Mod)
    [Functor.IsEquivalence (tensorRight L)] :
    IsIso ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) := by
  exact
    isIso_internalHom_unit_evaluation_of_isInvertible_aux
      (J := J) (𝒪 := 𝒪) L

instance instIsIsoInternalHomUnitEvaluation
    (L : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight L)] :
    IsIso ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) :=
  isIso_internalHom_unit_evaluation_of_isInvertible L

end Duality

end SheafOfModules.RingedSite
