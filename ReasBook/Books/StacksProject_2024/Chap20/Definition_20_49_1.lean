import stacks_project.Chap20.Definition_20_47_1
import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/- 
Domain-style sampling for Definition 20.49.1:
- primary domain: perfect complexes and perfect derived `\mathcal O_X`-modules on a ringed space;
- sampled owner declarations:
  `moduleDerivedRestrictionToOpen`,
  `DerivedCategory.IsMPseudoCoherent`,
  `CochainComplex.IsStrictlyPerfect`,
  `DerivedCategory.IsPerfect` from Chapter 15;
- best owner abstraction: `CochainComplex.IsPerfect` remains the source-facing complex predicate,
  while the derived notion should be owned intrinsically by `DerivedCategory (RingedSpace.Modules X)`
  through local strictly perfect models after restriction to opens, not by a chosen global
  representative complex;
- primitive data: an open cover together with strictly perfect local models and local
  quasi-isomorphisms/isomorphisms on the restricted objects;
- derived API: bridge lemmas comparing the intrinsic derived predicate with perfect
  representatives.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsPerfect` and `DerivedCategory.IsPerfect`;
- `core/canonical`: `moduleDerivedRestrictionToOpen` and `CochainComplex.IsStrictlyPerfect`;
- `bridge/view`: representative-based existence theorems for perfect complexes.
-/
namespace AlgebraicGeometry.RingedSpace

local instance instModuleSheafRestrictionToOpenAdditive
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (U : Opens X) :
    (_root_.moduleSheafRestrictionToOpen U 𝒪).Additive := sorry

local instance instModuleSheafRestrictionToOpenPreservesFiniteLimits
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (U : Opens X) :
    PreservesFiniteLimits (_root_.moduleSheafRestrictionToOpen U 𝒪) := sorry

local instance instModuleSheafRestrictionToOpenPreservesFiniteColimits
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (U : Opens X) :
    PreservesFiniteColimits (_root_.moduleSheafRestrictionToOpen U 𝒪) := sorry

variable {X : TopCat.{u}} {𝒪 : X.Sheaf RingCat.{u}}

private abbrev OpenComplex (V : Opens X) :=
  CochainComplex (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} V.inclusion').obj 𝒪)) ℤ

/-- Definition 20.49.1 (1): a complex of `\mathcal O_X`-modules is perfect if there is an open
covering of `X` such that on each member of the cover its restriction is quasi-isomorphic to a
strictly perfect complex. -/
def CochainComplex.IsPerfect (E : CochainComplex (SheafOfModules 𝒪) ℤ) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X),
    iSup U = ⊤ ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ α : Ei ⟶
            (((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E),
          CochainComplex.IsStrictlyPerfect Ei ∧ QuasiIso α

-- Proof sketch: unfold `CochainComplex.IsPerfect`; this is exactly the local strict-perfect
-- presentation condition from the definition, expressed using the restriction functor to open
-- subspaces and the standard predicate `QuasiIso` for quasi-isomorphisms of complexes.
/-- A complex of `\mathcal O_X`-modules is perfect exactly when it is locally quasi-isomorphic to
a strictly perfect complex. -/
theorem cochainComplex_isPerfect_iff
    (E : CochainComplex (SheafOfModules 𝒪) ℤ) :
    CochainComplex.IsPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X),
        iSup U = ⊤ ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ α : Ei ⟶
                (((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj E),
              CochainComplex.IsStrictlyPerfect Ei ∧ QuasiIso α :=
  Iff.rfl

namespace DerivedCategory

local notation "DMod" => DerivedCategory (SheafOfModules 𝒪)

/-- Definition 20.49.1 (2): an object of `D(\mathcal O_X)` is perfect if some open covering of
`X` carries strictly perfect models for its restrictions in the derived categories of the open
subspaces. -/
def IsPerfect (E : DMod) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X),
    iSup U = ⊤ ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ _ : DerivedCategory.Q.obj Ei ≅
            ((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapDerivedCategory).obj E,
          CochainComplex.IsStrictlyPerfect Ei

-- Proof sketch: unfold `DerivedCategory.IsPerfect`; the statement is exactly the existence of a
-- open cover on which the restricted derived object is represented by strictly perfect
-- complexes.
/-- Unfolding `DerivedCategory.IsPerfect` gives the intrinsic open-cover condition by strictly
perfect local models in the restricted derived categories. -/
theorem isPerfect_iff
    (E : DMod) :
    IsPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X),
        iSup U = ⊤ ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ _ : DerivedCategory.Q.obj Ei ≅
                ((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapDerivedCategory).obj E,
              CochainComplex.IsStrictlyPerfect Ei :=
  Iff.rfl

-- Proof sketch: a perfect representative gives strictly perfect local models after restricting the
-- representative complex to the chosen open cover, while conversely local strictly perfect models
-- for the restricted derived object can be transported to any chosen representative complex.
/-- A derived `\mathcal O_X`-module is perfect exactly when it admits a perfect representative
complex. This is a bridge theorem from the intrinsic owner `DerivedCategory.IsPerfect` to chosen
representatives. -/
theorem isPerfect_iff_exists_perfect_representative
    (E : DMod) :
    IsPerfect E ↔
      ∃ K : CochainComplex (SheafOfModules 𝒪) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          CochainComplex.IsPerfect K := by
  sorry

end DerivedCategory
end AlgebraicGeometry.RingedSpace
