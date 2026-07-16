import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_24_1

-- Declarations for this item will be appended below by the statement pipeline.

set_option checkBinderAnnotations false
set_option quotPrecheck false

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {n : ℕ}

/- Domain-style sampling for Definition 17.24.2:
- primary domain: Koszul complexes of `\mathcal O_X`-modules attached to finitely many global
  sections of the structure sheaf;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.koszulComplex`,
  `stacks_project.Chap15.Definition_15_28_2.koszulLinearForm`,
  `AlgebraicGeometry.RingedSpace.koszulComplex_X`,
  `SheafOfModules.freeHomEquiv`,
  `SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection`;
- best owner abstraction: the chapter owner remains `koszulComplex`; for a finite family of global
  sections, the source-facing notation should point directly to this owner, with the canonical
  free-to-unit morphism obtained from `freeHomEquiv` exposed as the thin bridge/view
  `koszulSectionMap`;
- primitive data: a finite family
  `f : Fin n → (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf).sections`;
- derived API: the bridge morphism `koszulSectionMap f` and the notation `K^•(f)` for the owner
  complex.

Source/core/bridge triage:
- `source-facing`: the Koszul complex `K_•(\mathcal O_X, f_1, \ldots, f_n)`, exposed below by the
  notation `K^•(f)`;
- `core/canonical`: `AlgebraicGeometry.RingedSpace.koszulComplex`;
- `bridge/view`: the direct passage from `f` to the canonical morphism `koszulSectionMap f`
  produced by `freeHomEquiv.symm`. -/

/-
Definition 17.24.2: for global sections `f_1, \ldots, f_n` of `\mathcal O_X`, the source-facing
Koszul complex `K_•(\mathcal O_X, f_1, \ldots, f_n)` is the owner `koszulComplex` from
Definition 17.24.1 applied to the canonical free-to-unit morphism determined by the family `f`.
-/

/-- Definition 17.24.2: the canonical morphism from the free rank-`n` module sheaf to
`\mathcal O_X` determined by the family of global sections `f`. This is the bridge sending the
source data `(f_1, \ldots, f_n)` to the owner construction `koszulComplex`. -/
@[stacks 062L]
abbrev koszulSectionMap
    (f : Fin n →
      (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf).sections) :=
  -- `freeHomEquiv.symm` packages the family of global sections into the canonical map
  -- `\mathcal O_X^{\oplus n} ⟶ \mathcal O_X`.
  (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf).freeHomEquiv.symm
    (fun i : ULift.{u} (Fin n) ↦ f i.down)

scoped[AlgebraicGeometry] notation:max "K^•(" f ")" =>
  AlgebraicGeometry.RingedSpace.koszulComplex
    (AlgebraicGeometry.RingedSpace.koszulSectionMap f)

end AlgebraicGeometry.RingedSpace
