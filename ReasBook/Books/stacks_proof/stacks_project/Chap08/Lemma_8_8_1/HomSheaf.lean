import StacksProject_2024.Chap08.Lemma_8_8_1.BaseChange

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace DescentCompletionObject

/-- Source stage 3.12 target statement: after adjoining descent-data objects, the canonical
Hom presheaves of the projection functor are sheaves.  This is deliberately the direct
source-facing formulation; the theorem below identifies it with mathlib's `IsPrestack` owner. -/
def projectionFunctorHomPresheavesAreSheaves
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    Prop :=
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  ∀ (U : C) (D E : P.Fiber U),
    Presheaf.IsSheaf (J.over U)
      ((canonicalFiberPseudofunctor P).presheafHom D E)

/-- The source-facing Hom-sheaf statement for the descent completion is exactly the canonical
`IsPrestack` owner for its fiber pseudofunctor. -/
theorem projectionFunctorHomPresheavesAreSheaves_iff_isPrestack
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    projectionFunctorHomPresheavesAreSheaves (J := J) hSheaf ↔
      letI := category (J := J) hSheaf
      let P := projectionFunctor (J := J) hSheaf
      haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
      Pseudofunctor.IsPrestack
        (canonicalFiberPseudofunctor P) J := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  dsimp [projectionFunctorHomPresheavesAreSheaves]
  constructor
  · intro h
    exact ⟨fun {S} M N => h S M N⟩
  · intro h U D E
    letI : Pseudofunctor.IsPrestack (canonicalFiberPseudofunctor P) J := h
    exact
      Pseudofunctor.IsPrestack.isSheaf
        (F := canonicalFiberPseudofunctor P) (J := J) (S := U) D E

/-- Source stage 3.13 target statement in coverwise form: every descent datum for the descent
completion is effective.  Combined with stage 3.12, this is the coverwise equivalence criterion
from Lemma 8.4.2. -/
def projectionFunctorCoverwiseDescentEffective
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    Prop :=
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  ∀ (U : C) (S : J.Cover U),
    ((canonicalFiberPseudofunctor P).toDescentData
      (fun I : S.Arrow => I.f)).EssSurj

/-- Owner bridge for the final descent-completion step: once the source proof supplies the
coverwise descent equivalences, the completed projection is a stack over the site.  This keeps the
proof routed through the canonical `IsStackOnSite` owner rather than a universe shortcut. -/
theorem projectionFunctor_isStackOnSite_of_coverwise_canonicalDescentFunctor_isEquivalence
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (hcover :
      letI := category (J := J) hSheaf
      let P := projectionFunctor (J := J) hSheaf
      haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
      ∀ (U : C) (S : J.Cover U),
        ((canonicalFiberPseudofunctor P).toDescentData
          (fun I : S.Arrow => I.f)).IsEquivalence) :
    letI := category (J := J) hSheaf
    IsStackOnSite J (projectionFunctor (J := J) hSheaf) := by
  letI := category (J := J) hSheaf
  haveI : (projectionFunctor (J := J) hSheaf).IsFibered :=
    projectionFunctor_isFibered (J := J) hSheaf
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      J (projectionFunctor (J := J) hSheaf)).2 hcover

set_option backward.isDefEq.respectTransparency false in
/-- The owner-level form of source stages 3.12 and 3.13 together: Hom sheaves give full
faithfulness of each cover descent functor, and coverwise effectiveness gives essential
surjectivity, hence each cover descent functor is an equivalence. -/
theorem projectionFunctor_coverwise_canonicalDescentFunctor_isEquivalence_of_homSheaf_effective
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (hHom : projectionFunctorHomPresheavesAreSheaves (J := J) hSheaf)
    (hEff : projectionFunctorCoverwiseDescentEffective (J := J) hSheaf) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ∀ (U : C) (S : J.Cover U),
      ((canonicalFiberPseudofunctor P).toDescentData
        (fun I : S.Arrow => I.f)).IsEquivalence := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  dsimp
  have hPrestack : Pseudofunctor.IsPrestack (canonicalFiberPseudofunctor P) J :=
    (projectionFunctorHomPresheavesAreSheaves_iff_isPrestack (J := J) hSheaf).1 hHom
  letI : Pseudofunctor.IsPrestack (canonicalFiberPseudofunctor P) J := hPrestack
  intro U S
  let F := canonicalFiberPseudofunctor P
  let f : ∀ I : S.Arrow, I.Y ⟶ U := fun I => I.f
  let Φ := F.toDescentData f
  have hfcover : Sieve.ofArrows (fun I : S.Arrow => I.Y) f ∈ J U := by
    rw [GrothendieckTopology.Cover.ofArrows_eq S]
    exact S.condition
  have hff : Φ.FullyFaithful := F.fullyFaithfulToDescentData f hfcover
  have hess : Φ.EssSurj := hEff U S
  haveI : Φ.Faithful := hff.faithful
  haveI : Φ.Full := hff.full
  haveI : Φ.EssSurj := hess
  exact {}

/-- Source stages 3.12 and 3.13 imply that the descent-completion projection is a stack over
the site, still through the canonical `IsStackOnSite` owner. -/
theorem projectionFunctor_isStackOnSite_of_homSheaf_effective
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (hHom : projectionFunctorHomPresheavesAreSheaves (J := J) hSheaf)
    (hEff : projectionFunctorCoverwiseDescentEffective (J := J) hSheaf) :
    letI := category (J := J) hSheaf
    IsStackOnSite J (projectionFunctor (J := J) hSheaf) :=
  projectionFunctor_isStackOnSite_of_coverwise_canonicalDescentFunctor_isEquivalence
    (J := J) hSheaf
    (projectionFunctor_coverwise_canonicalDescentFunctor_isEquivalence_of_homSheaf_effective
      (J := J) hSheaf hHom hEff)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
