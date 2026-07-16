import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Definition_20_48_1_Core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_31_8
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Definition 20.48.1 (local clause):
- primary domain: local finite tor dimension in `D(𝒪_X)`;
- sampled owner declarations:
  `HasFiniteTorDimension`,
  `openSubspaceModuleCategory`,
  `restrictedModuleDerivedOnOpen`,
  `TopologicalSpace.IsOpenCover`;
- best owner abstraction: the tor-amplitude owners already live in
  `Definition_20_48_1_Core`; this file adds only the source-facing local finite-tor-dimension
  clause as the `ModuleDerived` owner `LocallyHasFiniteTorDimension`, using the canonical open
  restriction owners `openSubspaceModuleCategory X U`, `moduleDerivedOnOpen X U`, and `E↾[U]`.

Source/core/bridge triage:
- `source-facing`: `ModuleDerived.LocallyHasFiniteTorDimension`;
- `core/canonical`: `HasFiniteTorDimension`;
- `bridge/view`: restriction of `E` to the intrinsic derived category `D(𝒪_U)` of an open
  subspace.

Primitive vs derived:
- primitive data: the derived object `E` and an open cover together with the restricted objects on
  that cover;
- derived API: only the local finite-tor-dimension predicate.
-/

variable {X : RingedSpace.{u}}

variable [∀ U : Opens X.carrier, MonoidalCategory (moduleDerivedOnOpen X U)]

local notation "DMod" => ModuleDerived X
local notation "DMod[" U "]" => moduleDerivedOnOpen X U

namespace ModuleDerived

-- Defeq pin: `E↾[U]` lives in the restricted ringed-space owner `ModuleDerived (X.restrict U...)`,
-- while the available Chapter 20 monoidal instance is spelled through `moduleDerivedOnOpen X U`.
local instance restrictedModuleDerived_monoidalCategory (U : Opens X.carrier) :
    MonoidalCategory (ModuleDerived (X.restrict U.isOpenEmbedding)) := by
  change MonoidalCategory (moduleDerivedOnOpen X U)
  infer_instance

/-- The restriction `E↾[U]` of `E` to the open subspace `U` has finite tor dimension. -/
abbrev HasFiniteTorDimensionOnOpen (E : DMod) (U : Opens X.carrier) : Prop :=
  let EU : ModuleDerived (X.restrict U.isOpenEmbedding) := E↾[U]
  HasFiniteTorDimension EU

/-- Definition 20.48.1 (3): an object of `D(𝒪_X)` locally has finite tor dimension if
there is an open covering of `X` on whose members its restriction has finite tor dimension. -/
@[stacks 08CG]
def LocallyHasFiniteTorDimension (E : DMod) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι, HasFiniteTorDimensionOnOpen E (U i)

end ModuleDerived

end

section

variable {X : RingedSpace.{u}}

variable [∀ U : Opens X.carrier, MonoidalCategory (moduleDerivedOnOpen X U)]

local notation "DMod" => ModuleDerived X
local notation "DMod[" U "]" => moduleDerivedOnOpen X U

namespace ModuleDerived

/-- An open cover whose restricted objects all have finite tor dimension exhibits local finite tor
dimension. -/
theorem locallyHasFiniteTorDimension_of_isOpenCover
    {ι : Type u} {U : ι → Opens X.carrier} {E : DMod}
    (hU : IsOpenCover U)
    (hE : ∀ i, HasFiniteTorDimensionOnOpen E (U i)) :
    LocallyHasFiniteTorDimension E := by
  exact ⟨ι, U, hU, hE⟩

/-- Unfolding `LocallyHasFiniteTorDimension` gives the indexed-open-cover criterion from
Definition 20.48.1. -/
theorem locallyHasFiniteTorDimension_iff_exists_openCover
    (E : DMod) :
    LocallyHasFiniteTorDimension E ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, HasFiniteTorDimensionOnOpen E (U i) :=
  Iff.rfl

/-- A locally finite-tor-dimension object admits an indexed open cover on whose members its
restrictions have finite tor dimension. -/
theorem LocallyHasFiniteTorDimension.exists_openCover
    {E : DMod} (hE : LocallyHasFiniteTorDimension E) :
    ∃ (ι : Type u) (U : ι → Opens X.carrier),
      IsOpenCover U ∧
        ∀ i : ι, HasFiniteTorDimensionOnOpen E (U i) :=
  hE

/-- Eliminate `LocallyHasFiniteTorDimension` by choosing an indexed open cover with finite-tor-
dimension restrictions. -/
theorem LocallyHasFiniteTorDimension.elim
    {E : DMod} {P : Prop} (hE : LocallyHasFiniteTorDimension E)
    (h :
      ∀ {ι : Type u} (U : ι → Opens X.carrier),
        IsOpenCover U →
          (∀ i : ι, HasFiniteTorDimensionOnOpen E (U i)) → P) :
    P := by
  rcases hE with ⟨ι, U, hU, htor⟩
  exact h U hU htor

-- Proof sketch: unfold `LocallyHasFiniteTorDimension`; it is exactly the existence of an indexed
-- open cover on which the restricted derived object has finite tor dimension.
end ModuleDerived

end

end AlgebraicGeometry.RingedSpace
