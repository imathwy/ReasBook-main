import Mathlib
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap20.Lemma_20_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/- Domain-style sampling for Lemma 20.33.1:
- primary domain: Mayer-Vietoris distinguished triangles in `D(\mathcal O_X)` built from
  restriction to opens and derived extension by zero;
- sampled owner declarations:
  `moduleSheafRestrictionToOpen`,
  `moduleSheafExtensionByZeroFromOpen`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `Triangle.mk`,
  `distTriang`;
- best owner abstraction: the Chapter 6 open-immersion restriction/extension-by-zero functors,
  passed to derived categories through the canonical owner `CategoryTheory.Functor.mapDerivedCategory`,
  together with the canonical triangle owner `Triangle`;
- primitive data: the cover opens `U, V`, the object `E`, and the three triangle morphisms
  `α, β, δ`;
- derived API: the two named Mayer-Vietoris vertices below, kept only to avoid repeating the same
  composite terms throughout the theorem statement.

Source/core/bridge triage:
- `source-facing`: the existence of the Mayer-Vietoris distinguished triangle for `E`;
- `core/canonical`: `moduleSheafRestrictionToOpen`, `moduleSheafExtensionByZeroFromOpen`,
  `CategoryTheory.Functor.mapDerivedCategory`, and `Triangle.mk`;
- `bridge/view`: the private derived-open functors and the two vertex abbreviations below.

This file therefore keeps only the two vertex names and uses `Triangle.mk` directly, rather than
introducing a parallel local triangle wrapper. -/

private abbrev openSubspaceModuleCategory (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))

private instance moduleSheafRestrictionToOpen_additive (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

private instance moduleSheafRestrictionToOpen_preservesFiniteLimits (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)) := sorry

private instance moduleSheafRestrictionToOpen_preservesFiniteColimits (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)) := sorry

private noncomputable abbrev moduleRestrictionToOpenDerived (U : Opens X.carrier) :
    DModX ⥤ DerivedCategory (openSubspaceModuleCategory U) :=
  (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory

private instance moduleSheafExtensionByZeroFromOpen_additive (U : Opens X.carrier) :
    (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

private instance moduleSheafExtensionByZeroFromOpen_preservesFiniteLimits
    (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

private instance moduleSheafExtensionByZeroFromOpen_preservesFiniteColimits
    (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

private noncomputable abbrev moduleExtensionByZeroFromOpenDerived (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory U) ⥤ DModX :=
  (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory

/-- The intersection term `j_{U ∩ V,!}(E|_{U ∩ V})` in the Mayer-Vietoris triangle. -/
abbrev moduleDerivedMayerVietorisIntersection
    (U V : Opens X.carrier) (E : DModX) : DModX :=
  (moduleExtensionByZeroFromOpenDerived (U ⊓ V)).obj
    ((moduleRestrictionToOpenDerived (U ⊓ V)).obj E)

/-- The middle term `j_{U,!}(E|_U) \oplus j_{V,!}(E|_V)` in the Mayer-Vietoris triangle. -/
abbrev moduleDerivedMayerVietorisMiddle
    (U V : Opens X.carrier) (E : DModX) : DModX :=
  (moduleExtensionByZeroFromOpenDerived U).obj
      ((moduleRestrictionToOpenDerived U).obj E) ⊞
    (moduleExtensionByZeroFromOpenDerived V).obj
      ((moduleRestrictionToOpenDerived V).obj E)

-- Proof sketch: choose a complex `\mathcal E^\bullet` representing `E`, apply restriction and
-- extension by zero termwise to obtain the short exact sequence of complexes
-- `0 \to j_{U \cap V,!}(\mathcal E^\bullet|_{U \cap V}) \to
-- j_{U,!}(\mathcal E^\bullet|_U) \oplus j_{V,!}(\mathcal E^\bullet|_V) \to \mathcal E^\bullet
-- \to 0`, and then pass to the associated distinguished triangle in the derived category.
/-- Lemma 20.33.1: if a ringed space `X` is covered by two opens `U` and `V`, then every object
`E` of `D(\mathcal O_X)` fits into a Mayer-Vietoris distinguished triangle
`j_{U \cap V,!}(E|_{U \cap V}) \to j_{U,!}(E|_U) \oplus j_{V,!}(E|_V) \to E \to
j_{U \cap V,!}(E|_{U \cap V})[1]`. -/
theorem moduleDerived_mayerVietoris_distinguishedTriangle
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (E : DModX) :
    ∃ (α : moduleDerivedMayerVietorisIntersection U V E ⟶
          moduleDerivedMayerVietorisMiddle U V E)
      (β : moduleDerivedMayerVietorisMiddle U V E ⟶ E)
      (δ : E ⟶ (moduleDerivedMayerVietorisIntersection U V E)⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang DModX := sorry

end

end AlgebraicGeometry.RingedSpace
