import Mathlib
import StacksProject_2024.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}

local notation "ModU" => LocalizedRingedSiteModules J 𝒪 U
local notation "ModOver" V =>
  LocalizedRingedSiteModules (J := J.over U) (𝒪 := 𝒪.over U) V

/-- Restriction from `\mathcal O_U`-modules to the iterated localization over `V : Over U`. -/
abbrev localizedRestrictionToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    ModU ⥤ ModOver V :=
  SheafOfModules.pushforward
    (𝟙 ((((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U).over V))

/-- Restriction to an iterated localization preserves zero morphisms. -/
instance localizedRestrictionToOver_preservesZeroMorphisms
    {U : C} (V : Over U) :
    (localizedRestrictionToOver 𝒪 V).PreservesZeroMorphisms := sorry

/-- Restriction of cochain complexes of `\mathcal O_U`-modules to the iterated localization over
`V : Over U`. -/
abbrev localizedRestrictionComplexToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    CochainComplex ModU ℤ ⥤ CochainComplex (ModOver V) ℤ :=
  (localizedRestrictionToOver 𝒪 V).mapHomologicalComplex (ComplexShape.up ℤ)

-- Proof sketch: form the composite `E ⟶ F ⟶ C(f)` with the canonical map to the mapping cone.
-- The hypotheses on `HomologicalComplex.homologyMap f` imply that `C(f)` has vanishing homology
-- in degrees `≥ a`, so Lemma `21.44.6` makes this composite locally null-homotopic after a cover
-- of `U`. Over each member of that cover, a null-homotopy of the composite yields a factorization
-- through the restricted cone, and the mapping-cone triangle then provides the desired local lift
-- of `α` through the restriction of `f` up to homotopy.
/-- Lemma 21.44.7: if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` and
`f : \mathcal G^\bullet \to \mathcal F^\bullet` are morphisms of complexes of
`\mathcal O_U`-modules, `\mathcal E^\bullet` is strictly perfect, `\mathcal E^j = 0` for
`j < a`, and `H^j(f)` is an isomorphism for `j > a` and surjective for `j = a`, then after a
covering of `U` each restriction of `\alpha` lifts through the restriction of `f` up to
homotopy. -/
theorem exists_cover_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
    [CategoryWithHomology ModU]
    (E F G : CochainComplex ModU ℤ) (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) :
    ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
      ∀ i : ι, ∃ β :
        ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj E) ⟶
          ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj G),
        Nonempty
          (Homotopy
            ((localizedRestrictionComplexToOver 𝒪 (cover i)).map α)
            (β ≫ (localizedRestrictionComplexToOver 𝒪 (cover i)).map f)) := sorry

end

end SheafOfModules.RingedSite
