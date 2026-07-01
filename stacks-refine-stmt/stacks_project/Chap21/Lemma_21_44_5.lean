import Mathlib
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "ModLoc" U => ringedSiteModuleCategory (J.over U) (𝒪.over U)

/-- Restriction from `\mathcal O_U`-modules to the iterated localization over `V : Over U`. -/
private abbrev localizedRestrictionToOver
    {U : C} (V : Over U) :
    ModLoc U ⥤ ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V) :=
  SheafOfModules.pushforward (𝟙 (((ringSheaf J 𝒪).over U).over V))

-- Proof sketch: choose a retract of `ℰ` from a finite free `\mathcal O_U`-module. For the
-- finitely many basis sections, use that an epimorphism of sheaves of modules is locally
-- surjective on the slice site `(C/U, J.over U)` to lift their images through `p` after refining
-- by a cover. These local lifts assemble to a lift from the finite free module, and composing with
-- the retraction data yields the desired local lifts from `ℰ`.
/-- Lemma 21.44.5: if `\mathcal E` is a direct summand of a finite free `\mathcal O_U`-module and
`p : \mathcal G \to \mathcal F` is surjective, then every morphism
`f : \mathcal E \to \mathcal F` lifts after passing to a covering of `U`. -/
theorem exists_cover_lift_of_epi_of_retract_finiteFree
    {U : C} {ℰ ℱ 𝒢 : ModLoc U}
    (f : ℰ ⟶ ℱ) (p : 𝒢 ⟶ ℱ) [Epi p]
    (hℰ : ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract ℰ (SheafOfModules.free I : ModLoc U))) :
    ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
      ∀ i : ι, ∃ l : ℰ.over (cover i) ⟶ 𝒢.over (cover i),
        l ≫ (localizedRestrictionToOver (𝒪 := 𝒪) (cover i)).map p =
          (localizedRestrictionToOver (𝒪 := 𝒪) (cover i)).map f := sorry

end SheafOfModules.RingedSite
