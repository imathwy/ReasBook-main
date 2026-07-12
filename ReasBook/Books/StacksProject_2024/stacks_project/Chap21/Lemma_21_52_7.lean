import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap07.Lemma_7_17_7
import StacksProject_2024.Chap21.Definition_21_47_1
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open DerivedCategory.TStructure
open Opposite
open RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

open _root_.RingedSite.DerivedCategory

variable {C : Type u} [Category.{u} C]
variable [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Site" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => ModuleCat Site
local notation "DMod" => ModuleDerived Site
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty DMod)

variable [Abelian Mod]

variable [CategoryWithHomology Mod]
variable [∀ U : C,
  CategoryWithHomology (ModuleCat (RingedSite.localization (RingedSite.ofCommRingSheaf J 𝒪) U))]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]

/- Domain-style sampling for Lemma 21.52.7:
- primary domain: perfect objects and compactness in derived categories of sheaves of modules on a
  ringed site, with quasi-compact final-object and covering hypotheses on the underlying site;
- sampled owner declarations:
  `GrothendieckTopology.HasCofinalFiniteQuasiCompactOverlapCoverings`,
  `t.plus`,
  `ObjectProperty.ι`,
  `RingedSite.DerivedCategory.IsPerfect`,
  `Sheaf.H'`,
  `CategoryTheory.IsCompactObject`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroDegreeZero_isCompactObject_of_finiteCohomologicalDimension_and_directSumCompatibility`;
- best owner abstraction: the site-theoretic hypothesis is already owned upstream by
  `HasCofinalFiniteQuasiCompactOverlapCoverings`, while the bounded-below subcategory is
  canonically owned by `t.plus` and the inclusion `plusι`, and perfectness and compactness are
  owned by `RingedSite.DerivedCategory.IsPerfect`, the source cohomology owner
  `((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H' p X0`, and `IsCompactObject`; no global
  finite-wide-pullback structure belongs on the
  theorem surface, although the upstream ringed-site perfectness owner does require the ambient
  binary-products instance already made explicit here;
- primitive data: a quasi-compact final object `X0`, the overlap-covering hypothesis on each
  quasi-compact object, and the cohomological-dimension bound in part (2);
- derived API: bounded-below coproduct preservation and compactness for perfect objects.

Source/core/bridge triage:
- `source-facing`: the two assertions of Lemma 21.52.7;
- `core/canonical`: `HasCofinalFiniteQuasiCompactOverlapCoverings`,
  `t.plus`, `RingedSite.DerivedCategory.IsPerfect`, `Sheaf.H'`,
  and `IsCompactObject`;
- `bridge/view`: the represented `Hom`-coproduct comparison on `D⁺(\mathcal O)`, encoded by
  `PreservesColimitsOfShape` on `plusι ⋙ preadditiveCoyoneda.obj (op K)`. -/

/-- Lemma 21.52.7 (1): let `(𝒞, 𝒪)` be a ringed site with a quasi-compact final object `X0`,
and assume every quasi-compact object has a cofinal system of finite coverings by quasi-compact
objects, with quasi-compact pairwise overlaps. If `K` is a perfect object of `D(𝒪)`, then
`K` is compact with respect to bounded-below coproducts. In Lean, this is the canonical
`D⁺(𝒪)` bridge statement that the represented functor `Hom(K, -)` preserves all coproducts on the
bounded-below inclusion `plusι : D⁺(𝒪) ⥤ D(𝒪)`. -/
@[stacks 09JC]
theorem perfect_preserves_boundedBelowCoproducts
    (hQCovers : ∀ ⦃U : C⦄ (_ : J.QuasiCompactObject U),
      J.HasCofinalFiniteQuasiCompactOverlapCoverings U)
    (X0 : C) (hX0 : IsTerminal X0) (hX0qc : J.QuasiCompactObject X0)
    (K : DMod) (hK : K.IsPerfect) (I : Type w) :
    PreservesColimitsOfShape (Discrete I) (plusι ⋙ preadditiveCoyoneda.obj (op K)) := by
  sorry

/-- Lemma 21.52.7 (2): under the hypotheses of Lemma 21.52.7 (1), if there exists an integer `d`
such that `H^i(X0, ℱ) = 0` for every `i > d` and every `𝒪`-module `ℱ`, then every perfect object
`K` of `D(𝒪)` is a compact object of `D(𝒪)`. -/
@[stacks 09JC]
theorem perfect_isCompactObject_of_finiteCohomologicalDimension
    (hQCovers : ∀ ⦃U : C⦄ (_ : J.QuasiCompactObject U),
      J.HasCofinalFiniteQuasiCompactOverlapCoverings U)
    (X0 : C) (hX0 : IsTerminal X0) (hX0qc : J.QuasiCompactObject X0)
    (K : DMod) (hK : K.IsPerfect)
    (hfinite :
      ∃ d : ℤ, ∀ (p : ℕ) (_ : d < p) (ℱ : Mod),
        IsZero (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H' p X0)) :
    IsCompactObject K := by
  sorry

end

end SheafOfModules.RingedSite
