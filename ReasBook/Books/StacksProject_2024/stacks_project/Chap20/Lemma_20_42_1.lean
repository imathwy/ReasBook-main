import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Lemma_20_31_8
import StacksProject_2024.Chap20.Open_subspace_module_core
import StacksProject_2024.Chap20.Sections_on_open

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed
open TopologicalSpace
open scoped CartesianClosed RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

open scoped RingedSpaceOpenHypercohomology

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
local notation "DModX" => ModuleDerived X
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]

/- Domain-style sampling for Lemma 20.42.1:
- primary domain: local Ext groups on an open subset of a ringed space, computed as
  zero-degree hypercohomology of the derived internal-Hom object;
- inspected owner declarations:
  `moduleOpenHypercohomology`,
  `moduleRestrictionToOpenDerived_obj_isomorphic_restrictedModuleDerivedOnOpen`,
  `localizedRestriction_derivedInternalHomComparison_isIso`,
  `openSubspaceHomComplex_homology_zero_isomorphic_restrictedDerivedHom`;
- best owner abstraction: the core owners are the Chapter 20 local hypercohomology owner
  `moduleOpenHypercohomology X U (L ⟹ M) 0`, together with the canonical open-subspace
  `H^0(Hom•) ≅ Hom` in `D(𝒪_U)`, viewed directly in
  `AddCommGrpCat`;
- primitive data: the ringed space `X`, the open subset `U`, and objects `L M : D(𝒪_X)`;
- derived API: the resulting additive-group identification with
  the canonical universe lift of `H^0(U, L ⟹ M)` and the actual local derived morphism group
  `AddCommGrpCat.of (L↾[U] ⟶ M↾[U])`.

No extra open-subspace monoidal-closed data should appear in the public statement: the target
comparison is between the Chapter 20 owners on `X` and on the restricted derived category
`D(𝒪_U)`.

Source/core/bridge triage:
- `source-facing`: the textbook identification
  `H^0(U, L ⟹ M) = Hom_{D(𝒪_U)}(L|_U, M|_U)`;
- `core/canonical`: `moduleOpenHypercohomology` and the Chapter 20 owner
  `openSubspaceHomComplex_homology_zero_isomorphic_restrictedDerivedHom`, together with its
  functorial-restriction companion
  `openSubspaceHomComplex_homology_zero_isomorphic_moduleRestrictionToOpenDerivedHom`;
- `bridge/view`: this file, which places that owner-level comparison directly on the
  `AddCommGrpCat` theorem surface by the canonical universe-lift bridge on `H^0(U, -)`.

The old `Nonempty (≃+)` statement duplicated the canonical owners behind an existential wrapper,
and the later `Shrink` target leaked an implementation-level universe repair into the public
surface. This file should expose the resulting additive-group comparison directly at the theorem
level on the actual local derived morphism group.
-/

-- Proof sketch: combine the owner-level bridges in Chapter 20.
-- First apply `moduleRestrictionToOpenDerived_obj_isomorphic_restrictedModuleDerivedOnOpen` to
-- identify
-- `H^0(U, L ⟹ M)` with the top-open hypercohomology of the restricted object on `X|_U`.
-- Next compare that restricted object with `(L↾[U]) ⟹ (M↾[U])` via the restriction comparison of
-- Lemma `20.42.3`. Finally use the degree-zero open-subspace Hom-complex owner from Lemma
-- `20.41.6`, namely
-- `openSubspaceHomComplex_homology_zero_isomorphic_restrictedDerivedHom`, to identify the
-- resulting top-open hypercohomology with
-- `AddCommGrpCat.of (L↾[U] ⟶ M↾[U])`.

/-- Lemma 20.42.1: for a ringed space `X`, an open subset `U ⊆ X`, and objects
`L, M : D(𝒪_X)`, the degree-zero hypercohomology group `H^0(U, L ⟹ M)` has a canonical universe
lift that is isomorphic in `AddCommGrpCat` to the local derived morphism group
`AddCommGrpCat.of (L↾[U] ⟶ M↾[U])`. -/
@[stacks 08DK]
theorem open_zeroHypercohomology_internalHom_isomorphic_restrictedDerivedHom
    (L M : DModX) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (H^0(U, L ⟹ M)))
      (AddCommGrpCat.of (L↾[U] ⟶ M↾[U])) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
