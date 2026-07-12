import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap21.Lemma_21_20_3
import StacksProject_2024.Chap21.Lemma_21_20_4
import StacksProject_2024.Chap21.Lemma_21_20_5_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open RingedSite.Hom
open scoped RingedSiteDerived
open scoped RingedSiteCohomology
open scoped RingedSiteDerivedSections

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable (X : RingedSite.{u, v})

local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X
local notation "DModLoc" U => ModuleDerived (X.localization U)
local notation "H0Ab" => DerivedCategory.homologyFunctor AddCommGrpCat (0 : ℤ)

local instance modAbelian : Abelian Mod := inferInstance
local instance dmodHasDerivedCategory : HasDerivedCategory Mod := HasDerivedCategory.standard Mod
local instance modLocAbelian (U : X) : Abelian (ModuleCat (X.localization U)) := inferInstance
local instance dmodLocHasDerivedCategory (U : X) :
    HasDerivedCategory (ModuleCat (X.localization U)) :=
  HasDerivedCategory.standard (ModuleCat (X.localization U))
local instance dmodCategory : Category DMod := inferInstance
local instance dmodPreadditive : Preadditive DMod := inferInstance
local instance dmodHomAdd (A B : DMod) : Add (A ⟶ B) := inferInstance
local instance dmodLocCategory (U : X) : Category (DModLoc U) := inferInstance
local instance dmodLocPreadditive (U : X) : Preadditive (DModLoc U) := inferInstance
local instance dmodLocHomAdd (U : X) (A B : DModLoc U) : Add (A ⟶ B) := inferInstance

set_option quotPrecheck false in
private abbrev derivedInternalHom
    [MonoidalCategory DMod] [MonoidalClosed DMod]
    (L M : DMod) : DMod :=
  (ihom L).obj M

local notation:20 A " ⟹ " B:19 => derivedInternalHom X A B

/- Domain-style sampling for Lemma 21.35.1:
- primary domain: degree-zero cohomology of the derived internal Hom on a ringed site and on its
  localizations;
- sampled owner declarations:
  `cohomologyOverObject`,
  `H^p(U, K)`,
  `localizedRestrictionDerived`,
  `moduleSectionsAsAbelianDerived`,
  `RΓ[X]`,
  `localizedHomComplex_homology_zero_addEquiv_localizedDerivedHom`,
  `homComplex_homology_zero_addEquiv_derivedHom`;
- best owner abstraction:
  `source-facing`: the degree-zero objectwise cohomology owner `H^0(U, L ⟹ M)` and the global
    degree-zero comparison for the derived internal Hom `(L ⟹ M)`;
  `core/canonical`: the Chapter 21 owners `cohomologyOverObject`,
    `localizedRestrictionDerived`, `moduleSectionsAsAbelianDerived`, `RΓ[X]`, and the degree-zero
    `Hom` comparisons of Lemma `21.34.6`;
  `bridge/view`: this file, which packages the comparison for the actual derived internal-Hom
    object `(L ⟹ M)` rather than for a chosen K-injective Hom-complex representative.

Primitive vs. derived:
- primitive data: a ringed site `X`, optionally an object `U : X`, the canonical restriction and
  sections functors on derived categories, and objects `L M : D(𝒪_X)`;
- derived API: the source-facing identifications
  `ULift (H^0(U, L ⟹ M)) ≅ Hom_{D(𝒪_U)}(L|_U, M|_U)`
  and
  `ULift (H^0(𝒞, L ⟹ M)) ≅ Hom_{D(𝒪_X)}(L, M)`.

Source/core/bridge triage:
- `source-facing`: the two `H^0(L ⟹ M)` comparison theorems below;
- `core/canonical`: `localizedHomComplex_homology_zero_addEquiv_localizedDerivedHom` and
  `homComplex_homology_zero_addEquiv_derivedHom`;
  Hom-complex owners, which this file uses only as upstream comparison targets for the
  proposition-valued source-facing statements below.

The old file duplicated this API by quantifying over an arbitrary comparison equivalence and then
asserting its bijectivity. This file only contributes the bridge from the derived internal-Hom
object `(L ⟹ M)` to the Chapter 21 owners of Lemma `21.34.6`. Since the concrete comparison data
would otherwise have to be chosen from theorem-shaped `IsIsomorphic` bridges, the public surface
here remains proposition-valued. -/

-- Proof sketch: choose a K-flat complex representing `L` and a K-injective complex representing
-- `M`. Lemma `21.34.8` makes the resulting internal-Hom complex K-injective, and the degree-zero
-- comparison is then the owner equivalence of Lemma `21.34.6`, transported across the
-- representation of the derived internal Hom `(L ⟹ M)` by that Hom complex.
/-- Lemma 21.35.1 (1): for every object `U` of a ringed site `(𝒞, 𝒪)`, the
canonical universe lift of the degree-zero cohomology of the derived internal Hom over `U`
identifies with the morphism group in the localized derived category:
`ULift (H^0(U, L ⟹ M)) ≅ Hom_{D(𝒪_U)}(L|_U, M|_U)`. -/
@[stacks 08JA]
theorem derivedInternalHom_objectwiseH0_isomorphic_localizedDerivedHom
    [HasBinaryProducts X.carrier]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (U : X)
    [(localizedRestriction X U).Additive]
    [PreservesFiniteLimits (localizedRestriction X U)]
    [PreservesFiniteColimits (localizedRestriction X U)]
    [MonoidalCategory DMod]
    [MonoidalClosed DMod]
    (L M : DMod) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{max (u + 1) (v + 1), max u v}).obj (H^0(U, L ⟹ M)))
      (AddCommGrpCat.of (((j[U]⁻¹).obj L) ⟶ ((j[U]⁻¹).obj M))) := by
  sorry

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

-- Proof sketch: the same argument with `U = X` and global sections identifies degree-zero
-- cohomology of the derived internal Hom `(L ⟹ M)` with the morphism group in `D(𝒪_X)`,
-- using the global owner `homComplex_homology_zero_addEquiv_derivedHom` from Lemma `21.34.6`.
/-- Lemma 21.35.1 (2): the canonical universe lift of the degree-zero global cohomology of the
derived internal Hom on a ringed site `(𝒞, 𝒪)` is canonically isomorphic, in `AddCommGrpCat`, to
the morphism group in `D(𝒪_X)`:
`ULift (H^0(𝒞, L ⟹ M)) ≅ Hom_{D(𝒪_X)}(L, M)`. -/
@[stacks 08JA]
theorem derivedInternalHom_globalH0_isomorphic_derivedHom
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
    [MonoidalCategory DMod]
    [MonoidalClosed DMod]
    (L M : DMod) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{max (u + 1) (v + 1), max u v}).obj
        ((H0Ab).obj ((RΓ[X]).obj (L ⟹ M))))
      (AddCommGrpCat.of (L ⟶ M)) := by
  sorry

end

end SheafOfModules.RingedSite
