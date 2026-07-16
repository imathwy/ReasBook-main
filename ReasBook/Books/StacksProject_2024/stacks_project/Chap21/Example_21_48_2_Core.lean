import StacksProject_2024.stacks_project.Chap18.Lemma_18_19_2
import StacksProject_2024.stacks_project.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "SiteLoc" U => RingedSite.ofCommRingSheaf (J.over U) (𝒪.over U)

/- Domain-style sampling for the local strict-perfectness owner used in Example 21.48.2 and
Lemma 21.48.3:
- primary domain: local strict perfectness for complexes of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `RingedSite.Hom.localizedRestriction`,
  `CochainComplex.IsStrictlyPerfect`,
  `GrothendieckTopology.Cover`,
  `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`;
- best owner abstraction:
  `source-facing`: the ringed-site predicate
    `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`;
  `core/canonical`: the same owner, since the mathematics is inherently local-on-the-site;
  `bridge/view`: the explicit cover-wise unfolding theorem
    `cochainComplex_isLocallyStrictlyPerfect_iff`.
- primitive data: for each object `U`, a cover of `U` whose localized restrictions are strictly
  perfect;
- derived API: only the owner predicate and its `Iff.rfl` unfolding theorem.

This owner should live in a lightweight core file so downstream lemmas can reuse it without
importing the heavier duality construction of Example 21.48.2. -/

/-- Restriction to a localized ringed site preserves zero morphisms. -/
private instance localizedRestriction_preservesZeroMorphisms
    (U : C) :
    (ringedSiteLocalizedRestriction J 𝒪 U).PreservesZeroMorphisms := by
  dsimp [ringedSiteLocalizedRestriction]
  refine ⟨fun _ _ ↦ ?_⟩
  rfl

/-- Restriction of cochain complexes of `𝒪`-modules to the localized ringed site over `U`. -/
private abbrev localizedRestrictionComplex (U : C) :
    Cpx ⥤ CochainComplex (ringedSiteModuleCategory (J.over U) (𝒪.over U)) ℤ :=
  (ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)

namespace CochainComplex

/-- A complex of `𝒪`-modules on a ringed site is locally strictly perfect if every object `U`
admits a covering on whose members the restricted complex is strictly perfect. -/
class IsLocallyStrictlyPerfect (E : Cpx) : Prop where
  out :
    ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
      CochainComplex.IsStrictlyPerfect ((localizedRestrictionComplex I.Y).obj E)

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat] in
/-- Unfolding `IsLocallyStrictlyPerfect` gives the explicit covering criterion by strictly perfect
restrictions. -/
theorem cochainComplex_isLocallyStrictlyPerfect_iff
    (E : Cpx) :
    IsLocallyStrictlyPerfect E ↔
      ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
        CochainComplex.IsStrictlyPerfect ((localizedRestrictionComplex I.Y).obj E) := by
  constructor
  · intro hE
    exact hE.out
  · intro hE
    exact ⟨hE⟩

end CochainComplex

end

end SheafOfModules.RingedSite
