import StacksProject_2024.stacks_project.Chap21.Definition_21_45_1

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)
open scoped RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.DerivedCategory

set_option checkBinderAnnotations false

section

open _root_.RingedSite.DerivedCategory
open _root_.RingedSite.Hom.ModuleDerived

/- Domain-style sampling for Lemma 21.45.2:
- primary domain: pseudo-coherence for derived `𝒪_X`-modules on a ringed site, together
  with the complex-level owner and the derived representative bridge from Definition `21.45.1`;
- sampled owner declarations:
  `HasStrictlyPerfectApproximationInDegree`,
  `RingedSite.DerivedCategory.IsMPseudoCoherent`,
  `CochainComplex.IsMPseudoCoherent`,
  `j[U]⁻¹`;
- best owner abstraction: the source-facing theorem statements below should reuse the Chapter 21
  complex postfix bridge `F.IsMPseudoCoherent m` and the representative-based derived postfix
  owner `K.IsMPseudoCoherent m` directly on the bundled ringed site `X`, together with the local bridge
  `HasStrictlyPerfectApproximationInDegree K U m`, rather than rebuilding schematic local
  predicates or duplicating the local approximation data inside this file;
- primitive data: the ringed site `X`, the derived object `K`, a representing complex `F`, the
  integer `m`, and the final-object or local-cover hypotheses;
- derived API: the final-object cover criterion, the representative-to-complex bridge, and the
  local-to-global criterion for `K.IsMPseudoCoherent m`.

Source/core/bridge triage:
- `source-facing`: the three theorem statements below;
- `core/canonical`: `CochainComplex.IsMPseudoCoherent`,
  `RingedSite.DerivedCategory.IsMPseudoCoherent`,
  `HasStrictlyPerfectApproximationInDegree`, and `j[U]⁻¹`;
- `bridge/view`: part `(2)` is the representative bridge
  `RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.of_representation`, which keeps the derived owner
  `K.IsMPseudoCoherent m` source-facing while extracting the corresponding complex-level statement
  for a chosen representative. -/
variable {X : RingedSite.{u, v}}

variable [HasBinaryProducts X.carrier]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

local notation "Mod" => ModuleCat X
local notation "Cpx" => CochainComplex Mod ℤ
local notation "DMod" => ModuleDerived X

local instance : Abelian Mod := SheafOfModules.instAbelian X.structureSheaf

-- Proof sketch: choose a complex representing `K`. By Lemma `21.44.8`, after refining the given
-- cover of the final object `U`, each local derived morphism from a strictly perfect complex is
-- represented by an actual chain map to the localized representative complex. Since `U` is final,
-- covers of `U` restrict to covers of every object of `X`, so the representative complex is
-- `m`-pseudo-coherent. Packaging that representative back into `DerivedCategory.Q` gives
-- `K.IsMPseudoCoherent m`.
/-- Lemma 21.45.2 (1): if a derived `𝒪_X`-module admits on a cover of a final object local
strictly perfect approximations with cohomology isomorphisms above `m` and an epimorphism in
degree `m`, then it is `m`-pseudo-coherent. -/
@[stacks 08FU]
theorem isMPseudoCoherent_of_exists_cover_on_finalObject
    (K : DMod) (m : ℤ) (U : X) (hU : IsTerminal U)
    (hcover :
      ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        HasStrictlyPerfectApproximationInDegree K I.Y m) :
    K.IsMPseudoCoherent m := by
  sorry

-- Proof sketch: transport `K.IsMPseudoCoherent m` across the chosen representing isomorphism
-- `e.symm : K ≅ DerivedCategory.Q.obj F`, then unpack the owner predicate on `DerivedCategory.Q.obj F`
-- to recover the complex-level statement `F.IsMPseudoCoherent m`.
namespace _root_.RingedSite.Hom.ModuleDerived

/-- Lemma 21.45.2 (2): if `K` is `m`-pseudo-coherent, then every complex representing `K` is
`m`-pseudo-coherent as a complex of `𝒪_X`-modules. -/
@[stacks 08FU]
theorem IsMPseudoCoherent.of_representation
    {K : DMod} {F : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m)
    (e : DerivedCategory.Q.obj F ≅ K) :
    F.IsMPseudoCoherent m := by
  sorry

end _root_.RingedSite.Hom.ModuleDerived

/- Proof sketch: choose a representative complex `F` of `K`. The local hypothesis yields covers on
which each localized derived restriction of `K` is `m`-pseudo-coherent; by part `(2)`, the same
is true for the corresponding localized restrictions of `F`. Compose those covers using the
site-composition axiom to obtain `F.IsMPseudoCoherent m`, then package `F` back into the derived
representative bridge.

Lemma 21.45.2 (3): if every object of the site admits a covering on which the localized
restriction of `K` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
section

variable [∀ U : X, HasBinaryProducts (X.localization U).carrier]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{max u v}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : X, ∀ V : X.localization U,
  (localizedRestriction (X.localization U) V).Additive]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteLimits (localizedRestriction (X.localization U) V)]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteColimits (localizedRestriction (X.localization U) V)]
variable [∀ U : X, ∀ V : X.localization U,
  CategoryWithHomology (ModuleCat (((X.localization U).localization V)))]

local instance (U : X) : Abelian (ModuleCat (X.localization U)) :=
  SheafOfModules.instAbelian (X.localization U).structureSheaf

/-- Lemma 21.45.2 (3): if every object of the site admits a covering on which the localized
restriction of `K` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
@[stacks 08FU]
theorem isMPseudoCoherent_of_locally_isMPseudoCoherent
    (K : DMod) (m : ℤ)
    (hlocal :
      ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        ((j[I.Y]⁻¹).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := by
  sorry

end

end

end RingedSite.DerivedCategory
