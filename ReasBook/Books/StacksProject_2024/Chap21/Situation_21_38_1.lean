import Mathlib
import StacksProject_2024.Chap04.Definition_4_33_9
import StacksProject_2024.Chap08.Lemma_8_10_3
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

/- Domain-style sampling for Situation 21.38.1:
- primary domain: ringed sites and the morphisms of topoi induced by cocontinuous functors of
  sites;
- sampled owner declarations:
  `RingedSite`,
  `RingedSite.Hom`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`.
- best owner abstraction: the inherited ringed structure on the total category should be owned by a
  `RingedSite`, while the induced geometric morphism remains canonically owned by
  `P.p.morphismOfTopoiInOfCocontinuous`.
- primitive data: the inherited topology on `P.S` and the pulled-back ring sheaf
  `P.p.sheafPushforwardContinuous RingCat ...`;
- derived API: the high-reuse abbreviation `inheritedStructureSheaf`, the ringed-site projection
  `inheritedProjection`, and the direct canonical recall of the induced morphism of topoi.

Source/core/bridge triage:
- `source-facing`: `inheritedRingedSite`;
- `core/canonical`: `RingedSite`, `RingedSite.Hom`, and
  `P.p.morphismOfTopoiInOfCocontinuous`;
- `bridge/view`: `inheritedProjection` and the specialization of
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage` to `P.p`. -/

section

variable (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
variable [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]

local notation "Jₚ" => inheritedTopology X.siteTopology P

def inheritedRingedSite (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
    [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology] :
    RingedSite.{u, v} where
  carrier := P.S
  siteTopology := Jₚ
  structureSheaf :=
    (P.p.sheafPushforwardContinuous RingCat.{max u v} Jₚ X.siteTopology).obj X.structureSheaf

/-- The inverse-image structure sheaf `π^{-1}\mathcal O_X` on the total category of a fibred
category over a ringed site, for the topology inherited from the base site. This is the
structure sheaf of `inheritedRingedSite X P`. -/
abbrev inheritedStructureSheaf (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
    [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology] :
    Sheaf Jₚ RingCat.{max u v} :=
  (inheritedRingedSite X P).structureSheaf

variable [Functor.IsCocontinuous P.p Jₚ X.siteTopology]

/-- The projection from the inherited ringed site on the total category back to the base ringed
site. Its structure-sheaf map is the adjoint pushforward form
`\mathcal O_X \to \pi_* \pi^{-1}\mathcal O_X`. -/
def inheritedProjection
    (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
    [Functor.IsContinuous P.p Jₚ X.siteTopology]
    [Functor.IsCocontinuous P.p Jₚ X.siteTopology] :
    inheritedRingedSite X P ⟶ X where
  base := P.p
  isMorphismOfSites := by infer_instance
  structureSheafMap :=
    (P.p.sheafAdjunctionCocontinuous RingCat.{max u v} Jₚ X.siteTopology).unit.app
      X.structureSheaf

variable [∀ Q : P.Sᵒᵖ ⥤ Type (max u v), Functor.HasPointwiseRightKanExtension P.p.op Q]

/- Situation 21.38.1: the projection functor `P.p` already canonically owns the induced morphism
of topoi through `Functor.morphismOfTopoiInOfCocontinuous`. -/
#check
  (P.p.morphismOfTopoiInOfCocontinuous Jₚ X.siteTopology :
    MorphismOfTopoiIn X.siteTopology Jₚ)

/- Companion recall: the inverse-image functor of this canonical morphism of topoi is
`P.p.sheafPullbackCocontinuous`. -/
#check
  (Functor.morphismOfTopoiInOfCocontinuous_inverseImage P.p Jₚ X.siteTopology)

end

end FibredCategoryOver
end CategoryTheory
