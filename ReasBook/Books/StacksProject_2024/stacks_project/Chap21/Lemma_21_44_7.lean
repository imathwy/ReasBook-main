import StacksProject_2024.Chap21.Definition_21_44_1
import StacksProject_2024.Chap21.Lemma_21_44_6
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.44.7:
- primary domain: local lifting up to homotopy for morphisms of cochain complexes on a localized
  ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringedSiteLocalizedRestriction`,
  `CochainComplex.IsStrictlyPerfect`,
  `IsLocallyNullHomotopic`;
- best owner abstraction: the source-facing local lifting condition should live on the canonical
  localized module category `ringedSiteModuleCategory (J.over U) (𝒪.over U)` and use the
  canonical iterated localized restriction owner
  `ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V` on complexes;
- primitive data: morphisms `α` and `f` of localized cochain complexes together with a covering
  family over `U`;
- derived API: the source-facing predicate `HasLocalLiftUpToHomotopy` and the lifting theorem
  below.

Source/core/bridge triage:
- `source-facing`: `HasLocalLiftUpToHomotopy` and the theorem below;
- `core/canonical`: `ringedSiteLocalizedRestriction` and `Homotopy`;
- `bridge/view`: Lemma `21.44.6`, applied to the mapping-cone comparison to obtain the local
  lifting condition.

The duplicate wheel here is the hand-written iterated restriction functor; the public surface
should reuse `ringedSiteLocalizedRestriction` and its induced functor on complexes directly. -/
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {U : C}

local notation "ModLoc" => ringedSiteModuleCategory (J.over U) (𝒪.over U)
local notation "res[" V "]" =>
  ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V

/-- A morphism of complexes on `(C/U, 𝒪_U)` locally lifts through `f` up to homotopy if,
after passing to a cover of `U`, each restriction to an iterated localization is homotopic to a
factorization through the restricted `f`. -/
def HasLocalLiftUpToHomotopy {E F G : CochainComplex ModLoc ℤ} (α : E ⟶ F) (f : G ⟶ F) : Prop :=
  ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
    ∀ i : ι,
      let j := (res[cover i]).mapHomologicalComplex (up ℤ)
      ∃ β : j.obj E ⟶ j.obj G,
        Nonempty (Homotopy (j.map α) (β ≫ j.map f))

omit [HasBinaryProducts C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Unfolding `HasLocalLiftUpToHomotopy` gives the explicit cover-wise lifting criterion. -/
theorem hasLocalLiftUpToHomotopy_iff
    {E F G : CochainComplex ModLoc ℤ} (α : E ⟶ F) (f : G ⟶ F) :
    HasLocalLiftUpToHomotopy α f ↔
      ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
        ∀ i : ι,
          let j := (res[cover i]).mapHomologicalComplex (up ℤ)
          ∃ β : j.obj E ⟶ j.obj G,
            Nonempty (Homotopy (j.map α) (β ≫ j.map f)) :=
  Iff.rfl

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {U : C}

local notation "ModLoc" => ringedSiteModuleCategory (J.over U) (𝒪.over U)

-- Proof sketch: form the composite `E ⟶ F ⟶ C(f)` with the canonical map to the mapping cone.
-- The hypotheses on `HomologicalComplex.homologyMap f` imply that `C(f)` has vanishing homology
-- in degrees `≥ a`, so Lemma `21.44.6` makes this composite locally null-homotopic after a cover
-- of `U`. Over each member of that cover, a null-homotopy of the composite yields a factorization
-- through the restricted cone, and the mapping-cone triangle then provides the desired local lift
-- of `α` through the restriction of `f` up to homotopy.
/-- Lemma 21.44.7: if `α : 𝓔^• ⟶ 𝓕^•` and `f : 𝓖^• ⟶ 𝓕^•` are morphisms of complexes of
`𝒪_U`-modules, `𝓔^•` is strictly perfect, `𝓔^j = 0` for `j < a`, and `H^j(f)` is an
isomorphism for `j > a` and surjective for `j = a`, then after a covering of `U` each
restriction of `α` lifts through the restriction of `f` up to
homotopy. -/
@[stacks 08FQ]
theorem exists_cover_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
    [CategoryWithHomology ModLoc]
    (E F G : CochainComplex ModLoc ℤ) (α : E ⟶ F) (f : G ⟶ F)
    (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hE_ge : E.IsStrictlyGE a)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) :
    HasLocalLiftUpToHomotopy α f := sorry

end

end SheafOfModules.RingedSite
