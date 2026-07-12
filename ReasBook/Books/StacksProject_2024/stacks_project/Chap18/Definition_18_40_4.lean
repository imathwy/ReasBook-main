import Mathlib
import StacksProject_2024.Chap18.«18_40_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Every local section is locally either a unit or has unit complement. -/
class HasLocalUnitDichotomy
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{w}) : Prop where
  local_unit_dichotomy (U : C) (f : 𝒪.obj.obj (op U)) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      IsUnit ((𝒪.obj.map I.f.op).hom f) ∨
        IsUnit (1 - (𝒪.obj.map I.f.op).hom f)

section

variable [J.HasSheafCompose (forget CommRingCat.{max u v})]

/-- Definition 18.40.4: a commutative ringed site `(\mathcal C, \mathcal O)` is locally ringed
if the canonical morphism `\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` of
`18.40.2.1` is an isomorphism and the local unit dichotomy from Lemma `18.40.1` holds. -/
class IsLocallyRingedSite (𝒪 : Sheaf J CommRingCat.{max u v}) : Prop
    extends IsIso (oneNeverZeroEqualizerMap 𝒪), HasLocalUnitDichotomy J 𝒪

/-- Any commutative ringed site satisfying the `18.40.2.1` isomorphism and the local unit
dichotomy carries the canonical locally ringed-site instance. -/
instance instIsLocallyRingedSiteOfConditions
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [IsIso (oneNeverZeroEqualizerMap 𝒪)]
    [HasLocalUnitDichotomy J 𝒪] :
    IsLocallyRingedSite 𝒪 :=
  { toIsIso := inferInstance
    toHasLocalUnitDichotomy := inferInstance }

end

end CategoryTheory
