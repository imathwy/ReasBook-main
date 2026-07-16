import Mathlib
import StacksProject_2024.stacks_project.Chap08.Definition_8_3_1

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
      (familyDescentFunctor hc (singletonIdentityFamily U)).obj X := sorry

/- Definition 8.3.5 (3): a descent datum is effective exactly when it lies in the essential image
of the canonical functor from the fiber over `U` to descent data for the family. Concretely, this
means it is isomorphic to the descent datum obtained by pulling back some object of the fiber over
`U` along the members of the family. -/
#check
  fun {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]
    (D : DescentDatum p hc 𝒰) ↦
      (familyDescentFunctor hc 𝒰).essImage D

end CategoryTheory
