import Mathlib
import StacksProject_2024.Chap08.Definition_8_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered]
variable (hc : PullbackChoice p)
variable {U : C}

/-- The singleton family over `U` whose unique member is the identity arrow `𝟙 U`. -/
abbrev singletonIdentityFamily (U : C) : SemiRepresentableFamily.Over U :=
  ofArrows (fun _ : PUnit ↦ U) (fun _ ↦ 𝟙 U)

private theorem singletonIdentityHasPullback (U : C) : HasPullback (𝟙 U) (𝟙 U) := by
  let h : IsPullback (𝟙 U) (𝟙 U) (𝟙 U) (𝟙 U) := IsPullback.of_id_fst
  exact h.hasPullback

instance singletonIdentityFamily_hasDescentPullbacks (U : C) :
    HasDescentPullbacks (singletonIdentityFamily U) where
  pairwise i j := by
    cases i
    cases j
    simpa using singletonIdentityHasPullback U
  triple i j k := by
    cases i
    cases j
    cases k
    letI := singletonIdentityHasPullback U
    letI : HasPullbacksAlong (𝟙 U) := fun {W} h ↦ (IsPullback.id_horiz h).hasPullback
    change HasPullback (pullback.snd (𝟙 U) (𝟙 U)) (pullback.fst (𝟙 U) (𝟙 U))
    exact inferInstance

/-- The canonical functor from the fiber over `U` to descent data for the family `𝒰`. -/
noncomputable abbrev familyDescentFunctor
    (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰] :
    p.Fiber U ⥤ DescentDatum p hc 𝒰 :=
  ((hc.fiberPseudofunctor).toDescentData fun i : 𝒰.index ↦ (𝒰.obj i).hom) ⋙
    Pseudofunctor.DescentData'.fromDescentDataFunctor
      hc.fiberPseudofunctor
      𝒰.pairwisePullback
      𝒰.triplePullback

/-- Definition 8.3.5 (1): an object `X` of the fiber over `U` defines the trivial descent datum on
the singleton identity family `{id_U}`. -/
noncomputable abbrev trivialDescentDatum (X : p.Fiber U) :
    DescentDatum p hc (singletonIdentityFamily U) :=
  (familyDescentFunctor hc (singletonIdentityFamily U)).obj X

/-- The trivial descent datum is the image of `X` under the canonical descent-data functor for the
singleton identity family. -/
-- Proof sketch: unfold `trivialDescentDatum`; this is definitional because it was introduced as the
-- object part of `familyDescentFunctor` on the singleton identity family.
theorem trivialDescentDatum_def (X : p.Fiber U) :
    trivialDescentDatum hc X =
      (familyDescentFunctor hc (singletonIdentityFamily U)).obj X := by
  -- This is exactly the abbreviation introduced in `trivialDescentDatum`.
  rfl

namespace DescentDatum

/-- Definition 8.3.5 (3): a descent datum for a family `𝒰` is effective when it lies in the
essential image of the canonical descent functor `familyDescentFunctor hc 𝒰`. Equivalently, it is
isomorphic to the canonical descent datum obtained from some object of the fiber over `U`. -/
abbrev IsEffective {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]
    (D : DescentDatum p hc 𝒰) : Prop :=
  (familyDescentFunctor hc 𝒰).essImage D

/-- Helper for Definition 8.3.5: the canonical descent datum obtained from a global object is
effective. -/
theorem familyDescentFunctor_obj_isEffective
    {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰] (X : p.Fiber U) :
    DescentDatum.IsEffective (hc := hc) ((familyDescentFunctor hc 𝒰).obj X) := by
  -- The canonical descent datum is literally an object in the essential image of the functor.
  simpa [DescentDatum.IsEffective] using
    Functor.obj_mem_essImage (familyDescentFunctor hc 𝒰) X

end DescentDatum

end CategoryTheory
