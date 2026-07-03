import Mathlib
import stacks_project.Chap21.Definition_21_44_1
import stacks_project.Chap21.Lemma_21_20_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Definition 21.45.1:
- primary domain: pseudo-coherence for complexes and derived `\mathcal O`-modules on a ringed
  site, expressed through local strictly perfect models on localized ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.Hom.localizedRestriction`,
  `CochainComplex.IsStrictlyPerfect`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `ringedSiteModuleCategory`;
- best owner abstraction: keep the pseudo-coherence predicates as the source-facing owners, but
  organize the ambient module and derived categories through the ringed-site owner
  `X := RingedSite.ofCommRingSheaf J 𝒪`, reusing `ModuleCat X`, `ModuleDerived X`,
  `localizedRestriction X U`, and `localizedRestrictionDerived X U` instead of parallel local
  wheel declarations; representative criteria remain bridge theorems;
- primitive data: a cover of each localized object, a strictly perfect complex on each cover
  member, and a comparison morphism controlling cohomology above degree `m` and in degree `m`;
- derived API: the complex predicates and the intrinsic derived predicates.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`;
- `core/canonical`: `RingedSite.Hom.ModuleCat`, `RingedSite.Hom.ModuleDerived`,
  `CochainComplex.IsStrictlyPerfect`, `RingedSite.Hom.localizedRestrictionDerived`,
  `DerivedCategory.IsMPseudoCoherent`, and `DerivedCategory.IsPseudoCoherent`;
- `bridge/view`: the representative criteria for the derived predicates.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "ModLoc" U => LocalizedRingedSiteModules J 𝒪 U

variable [∀ U : C,
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).PreservesZeroMorphisms]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  CategoryTheory.Limits.PreservesFiniteLimits
    (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  CategoryTheory.Limits.PreservesFiniteColimits
    (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]

variable [CategoryWithHomology Mod]
variable [∀ U : C, CategoryWithHomology (ModLoc U)]

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪

namespace CochainComplex

/-- Definition 21.45.1: a complex of `\mathcal O`-modules on a ringed site is
`m`-pseudo-coherent if, after passing to a covering of every object `U`, its restriction to each
member of the cover admits a map from a strictly perfect complex inducing cohomology
isomorphisms in degrees `> m` and a surjection in degree `m`. -/
def IsMPseudoCoherent (E : Cpx) (m : ℤ) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
      CochainComplex.IsStrictlyPerfect E' ∧
        ∃ α :
          E' ⟶
            ((localizedRestriction X I.Y).mapHomologicalComplex (up ℤ)).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m)

/-- A complex of `\mathcal O`-modules on a ringed site is pseudo-coherent if it is
`m`-pseudo-coherent for every integer `m`. -/
def IsPseudoCoherent (E : Cpx) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent E m

end CochainComplex

variable [Abelian Mod]
local notation "DMod" => ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)

namespace DerivedCategory

/-- Definition 21.45.1 (derived `m`-version): an object of `D(\mathcal O)` is
`m`-pseudo-coherent if, after passing to a covering of every object `U`, each restricted derived
object is approximated by a strictly perfect complex inducing cohomology isomorphisms in degrees
`> m` and an epimorphism in degree `m`. -/
def IsMPseudoCoherent (K : DMod) (m : ℤ) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
      CochainComplex.IsStrictlyPerfect E' ∧
        ∃ α :
          DerivedCategory.Q.obj E' ⟶
            (localizedRestrictionDerived X I.Y).obj K,
          (∀ j : ℤ, m < j →
            IsIso ((DerivedCategory.homologyFunctor (ModLoc I.Y) j).map α)) ∧
              Epi ((DerivedCategory.homologyFunctor (ModLoc I.Y) m).map α)

/-- An object of `D(\mathcal O)` is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
def IsPseudoCoherent (K : DMod) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent K m

end DerivedCategory

end

end SheafOfModules.RingedSite
