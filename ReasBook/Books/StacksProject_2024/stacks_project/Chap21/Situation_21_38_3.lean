import StacksProject_2024.stacks_project.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.stacks_project.Chap18.Definition_18_8_1
import StacksProject_2024.stacks_project.Chap21.Situation_21_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryMor

open FibredCategoryOver

/- Domain-style sampling for Situation 21.38.3:
- primary domain: inherited ringed sites attached to fibred categories over a ringed site, and the
  canonical comparison morphism induced by a morphism of fibred categories;
- sampled owner declarations:
  `RingedSite.Hom`,
  `FibredCategoryMor.toFunctor`,
  `FibredCategoryMor.comm`,
  `FibredCategoryOver.projectionRingedSiteHom`,
  `Functor.sheafPushforwardContinuousComp'`;
- best owner abstraction:
  the comparison morphism belongs on the fibred-category morphism
  `u : C' ⟶ C` itself, as a canonical `RingedSite.Hom`
  `u.inheritedRingedSiteHom :
    inheritedRingedSite D C ⟶ inheritedRingedSite D C'`.
  The projection compatibility
  `CommSq (projectionRingedSiteHom D C) (projectionRingedSiteHom D C')
    u.inheritedRingedSiteHom (𝟙 _)`
  is derived bridge data, not primitive packaged data.

Source/core/bridge triage:
- `source-facing`: `u.inheritedRingedSiteHom`;
- `core/canonical`: `RingedSite.Hom`, `FibredCategoryMor.toFunctor`, `inheritedRingedSite`, and
  `projectionRingedSiteHom`;
- `bridge/view`: the projection-compatibility theorem
  `u.inheritedRingedSiteHom_projection`.

Primitive-vs-derived split:
- primitive data: the ringed site `D`, the fibred categories `C`, `C'`, and the morphism
  `u : C' ⟶ C`;
- derived API: the internal site-morphism instance for `toFunctor u`, the comparison morphism of
  inherited ringed sites, and the commutative projection diagram; the underlying base-functor
  compatibility is already the canonical theorem `FibredCategoryMor.comm`. -/

section

variable {D : RingedSite.{u, v}}
variable {C C' : FibredCategoryOver.{u, v} D}
variable (u : FibredCategoryMor C' C)

/-- Situation 21.38.3: given `u : C' ⟶ C` over the ringed site `D`, the
inherited ringed sites from Situation `21.38.1` are linked by the canonical comparison morphism of
ringed sites whose underlying functor is `u`, whenever the inherited-topology comparison functor
`u.toFunctor` is available as a site morphism and the two projection functors are continuous for
their inherited topologies. This is the site-presented bridge for the source's corresponding
morphism of ringed topoi. -/
@[stacks 08PA]
def inheritedRingedSiteHom
    (u : FibredCategoryMor C' C)
    [hCp' : Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
    [hCp : Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
    [hSite : IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)] :
    inheritedRingedSite D C ⟶ inheritedRingedSite D C' where
  base := toFunctor u
  isMorphismOfSites := hSite
  structureSheafMap :=
    let _ : Functor.IsContinuous
        C'.p
        (inheritedTopology D.siteTopology C')
        D.siteTopology := hCp'
    let _ : Functor.IsContinuous
        C.p
        (inheritedTopology D.siteTopology C)
        D.siteTopology := hCp
    let _ : Functor.IsContinuous
        (toFunctor u)
        (inheritedTopology D.siteTopology C')
        (inheritedTopology D.siteTopology C) := hSite.toIsContinuous
    let e :=
      Functor.sheafPushforwardContinuousComp'
        (eqToIso (comm u))
        RingCat.{max u v}
        (inheritedTopology D.siteTopology C')
        (inheritedTopology D.siteTopology C)
        D.siteTopology
    (e.symm.app D.structureSheaf).hom

variable [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
variable [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
variable [IsMorphismOfSites
  (inheritedTopology D.siteTopology C')
  (inheritedTopology D.siteTopology C)
  (toFunctor u)]

@[simp] theorem inheritedRingedSiteHom_base :
    RingedSite.Hom.base u.inheritedRingedSiteHom = toFunctor u :=
  rfl

variable [IsMorphismOfSites (inheritedTopology D.siteTopology C') D.siteTopology C'.p]
variable [IsMorphismOfSites (inheritedTopology D.siteTopology C) D.siteTopology C.p]

/-- Helper for Situation 21.38.3: two morphisms of ringed sites are equal once their underlying
site functors agree and their structure-sheaf maps agree as heterogeneous terms. -/
  private theorem ringedSiteHom_ext
    {X Y : RingedSite.{u, v}} :
    ∀ {f g : X ⟶ Y},
      f.base = g.base →
      HEq f.structureSheafMap g.structureSheafMap →
      f = g
  | { base := basef, isMorphismOfSites := instf, structureSheafMap := mapf },
    { base := baseg, isMorphismOfSites := instg, structureSheafMap := mapg }, hbase, hmap => by
      cases hbase
      cases Subsingleton.elim instf instg
      cases hmap
      rfl

/-- Helper for Situation 21.38.3: the comparison morphism induced by `u` makes the projection
triangle commute on the nose as an equality of ringed-site morphisms. -/
private theorem inheritedRingedSiteHom_projection_w_aux :
    projectionRingedSiteHom D C ≫ u.inheritedRingedSiteHom = projectionRingedSiteHom D C' := by
  -- Proof comment: the equality is determined by the base functor identity `toFunctor u ⋙ C.p =
  -- C'.p`, and after unpacking `u` the induced structure-sheaf map comparison is definitional.
  refine ringedSiteHom_ext ?_ ?_
  · simpa [RingedSite.Hom.comp] using comm u
  · cases u
    simp [RingedSite.Hom.comp, FibredCategoryMor.inheritedRingedSiteHom,
      FibredCategoryOver.projectionRingedSiteHom,
      CategoryTheory.Functor.sheafPushforwardContinuousComp,
      CategoryTheory.Functor.sheafPushforwardContinuousComp',
      CategoryTheory.Functor.sheafPushforwardContinuousNatTrans]

/-- The canonical comparison morphism attached to `u` is compatible with the projection morphisms
from the inherited ringed sites to `D`. This is the commutative diagram appearing in Situation
`21.38.3`, expressed as derived owner-level data rather than as a primitive field. -/
theorem inheritedRingedSiteHom_projection :
    CommSq
      (projectionRingedSiteHom D C)
      (projectionRingedSiteHom D C')
      u.inheritedRingedSiteHom
      (𝟙 (inheritedRingedSite D C')) := by
  -- Proof comment: this is exactly the equality of composites proved in the helper theorem.
  exact CommSq.mk (inheritedRingedSiteHom_projection_w_aux (D := D) (C := C) (C' := C') (u := u))

@[simp] theorem inheritedRingedSiteHom_projection_w :
    projectionRingedSiteHom D C ≫ u.inheritedRingedSiteHom = projectionRingedSiteHom D C' := by
  simpa using inheritedRingedSiteHom_projection_w_aux (D := D) (C := C) (C' := C') (u := u)

end

end FibredCategoryMor
end CategoryTheory
