import Mathlib
import StacksProject_2024.Chap04.Lemma_4_33_7
import StacksProject_2024.Chap25.Definition_25_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 8.3.1:
- primary domain: categorical descent data for a fixed-target family in a fibred category,
  expressed using chosen pairwise and triple overlaps.
- inspected owner-level declarations:
  `SemiRepresentableFamily.Over`,
  `Pseudofunctor.DescentData'`,
  `Pseudofunctor.DescentData'.Hom`,
  `ChosenPullback₃`.
- best owner abstraction: the fixed-target family owner `SemiRepresentableFamily.Over U`, with the
  extra chosen pairwise and triple pullbacks recorded as the minimal bridge data.
- primitive data: a family `𝒰 : SemiRepresentableFamily.Over U` together with the chosen overlap
  existence class `HasDescentPullbacks 𝒰`.
- derived API: the overlap objects and projections of `𝒰`, the diagonal and switching maps, the
  triple-overlap projections, and the specialization `DescentDatum p hc 𝒰` of
  `Pseudofunctor.DescentData'`.

Source/core/bridge triage:
- `source-facing`: the fixed-target family `𝒰` together with the chosen pairwise and triple
  pullbacks recorded by `HasDescentPullbacks 𝒰`.
- `core/canonical`: `Pseudofunctor.DescentData'`.
- `bridge/view`: `DescentDatum p hc 𝒰`, i.e. the chosen-overlap specialization of the fiber
  pseudofunctor to the family owner `𝒰`.
-/

/-- The pairwise pullbacks and triple pullbacks over the middle overlap leg needed to speak about
descent data for a fixed-target family. -/
class HasDescentPullbacks {U : C} (𝒰 : SemiRepresentableFamily.Over U) : Prop where
  /-- Every pair of members of the family has a chosen fiber product over the common target. -/
  pairwise (i i' : 𝒰.index) : HasPullback (𝒰.obj i).hom (𝒰.obj i').hom
  /-- The chosen model of every triple overlap exists as a pullback of
  `U_i ×[U] U_j ⟶ U_j` and `U_j ×[U] U_k ⟶ U_j`. -/
  triple (i j k : 𝒰.index) :
    let _ : HasPullback (𝒰.obj i).hom (𝒰.obj j).hom := pairwise i j
    let _ : HasPullback (𝒰.obj j).hom (𝒰.obj k).hom := pairwise j k
    HasPullback (pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom)
      (pullback.fst (𝒰.obj j).hom (𝒰.obj k).hom)

/-- A category with all pullbacks provides the pairwise and triple pullbacks needed for descent
data for every fixed-target family. -/
instance [HasPullbacks C] {U : C} (𝒰 : SemiRepresentableFamily.Over U) :
    HasDescentPullbacks 𝒰 where
  pairwise _ _ := inferInstance
  triple _ _ _ := inferInstance

/-- A family with descent pullbacks has the required pairwise pullbacks available by typeclass
search. -/
instance {U : C} (𝒰 : SemiRepresentableFamily.Over U) [h : HasDescentPullbacks 𝒰]
    (i i' : 𝒰.index) : HasPullback (𝒰.obj i).hom (𝒰.obj i').hom :=
  h.pairwise i i'

/-- A family with descent pullbacks has the chosen triple-overlap pullback model available by
typeclass search. -/
instance {U : C} (𝒰 : SemiRepresentableFamily.Over U) [h : HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) :
    let _ : HasPullback (𝒰.obj i).hom (𝒰.obj j).hom := h.pairwise i j
    let _ : HasPullback (𝒰.obj j).hom (𝒰.obj k).hom := h.pairwise j k
    HasPullback (pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom)
      (pullback.fst (𝒰.obj j).hom (𝒰.obj k).hom) :=
  h.triple i j k

namespace SemiRepresentableFamily.Over

/-- The chosen pairwise overlap of a fixed-target family, viewed through the canonical
`ChosenPullback` owner API. -/
abbrev pairwisePullback {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j : 𝒰.index) :
    ChosenPullback (𝒰.obj i).hom (𝒰.obj j).hom where
  pullback := pullback (𝒰.obj i).hom (𝒰.obj j).hom
  p₁ := pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom
  p₂ := pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom
  condition := pullback.condition
  isLimit := (IsPullback.of_hasPullback (𝒰.obj i).hom (𝒰.obj j).hom).isLimit

/-- The projections from the chosen pullback of
`U_i ×[U] U_j ⟶ U_j` and `U_j ×[U] U_k ⟶ U_j` define a morphism to `U_i ×[U] U_k`. -/
private theorem triplePullback_condition {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    pullback.fst
        (pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom)
        (pullback.fst (𝒰.obj j).hom (𝒰.obj k).hom) ≫
        (𝒰.pairwisePullback i j).p =
      pullback.snd
        (pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom)
        (pullback.fst (𝒰.obj j).hom (𝒰.obj k).hom) ≫
        (𝒰.pairwisePullback j k).p := by
  let hij := 𝒰.pairwisePullback i j
  let hjk := 𝒰.pairwisePullback j k
  simpa [ChosenPullback.p, Category.assoc] using
    congrArg
      (fun f ↦ f ≫ (𝒰.obj j).hom)
      (pullback.condition :
        pullback.fst hij.p₂ hjk.p₁ ≫ hij.p₂ =
          pullback.snd hij.p₂ hjk.p₁ ≫ hjk.p₁)

/-- The chosen triple overlap of a fixed-target family, viewed through the canonical
`ChosenPullback₃` owner API. -/
noncomputable def triplePullback {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    ChosenPullback₃
      (𝒰.pairwisePullback i j)
      (𝒰.pairwisePullback j k)
      (𝒰.pairwisePullback i k) := by
  let hij := 𝒰.pairwisePullback i j
  let hjk := 𝒰.pairwisePullback j k
  let hik := 𝒰.pairwisePullback i k
  refine
    { chosenPullback :=
        { pullback := pullback hij.p₂ hjk.p₁
          p₁ := pullback.fst hij.p₂ hjk.p₁
          p₂ := pullback.snd hij.p₂ hjk.p₁
          condition := by
            simpa using
              (pullback.condition :
                pullback.fst hij.p₂ hjk.p₁ ≫ hij.p₂ =
                  pullback.snd hij.p₂ hjk.p₁ ≫ hjk.p₁)
          isLimit := (IsPullback.of_hasPullback hij.p₂ hjk.p₁).isLimit }
      l :=
        { f := hik.isPullback.lift
            (pullback.fst hij.p₂ hjk.p₁ ≫ hij.p₁)
            (pullback.snd hij.p₂ hjk.p₁ ≫ hjk.p₂)
            (by
              simpa [ChosenPullback.p, Category.assoc] using
                triplePullback_condition 𝒰 i j k) } }

/-- The chosen pairwise overlap `Uᵢ ×[U] Uⱼ`. -/
abbrev overlap {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) : C :=
  (𝒰.pairwisePullback i j).pullback

/-- The first projection `Uᵢ ×[U] Uⱼ ⟶ Uᵢ`. -/
abbrev pr0 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) : 𝒰.overlap i j ⟶ (𝒰.obj i).left :=
  (𝒰.pairwisePullback i j).p₁

/-- The second projection `Uᵢ ×[U] Uⱼ ⟶ Uⱼ`. -/
abbrev pr1 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) : 𝒰.overlap i j ⟶ (𝒰.obj j).left :=
  (𝒰.pairwisePullback i j).p₂

/-- The two overlap projections lie over the same morphism to `U`. -/
@[reassoc]
theorem pr0_map_eq_pr1_map {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j : 𝒰.index) :
    𝒰.pr0 i j ≫ (𝒰.obj i).hom = 𝒰.pr1 i j ≫ (𝒰.obj j).hom :=
  (𝒰.pairwisePullback i j).condition

/-- The first overlap projection lies over the common map to `U`. -/
@[reassoc]
theorem pr0_map {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) :
    𝒰.pr0 i j ≫ (𝒰.obj i).hom = (𝒰.pairwisePullback i j).p := by
  exact (𝒰.pairwisePullback i j).hp₁

/-- The second overlap projection lies over the common map to `U`. -/
@[reassoc]
theorem pr1_map {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) :
    𝒰.pr1 i j ≫ (𝒰.obj j).hom = (𝒰.pairwisePullback i j).p := by
  exact (𝒰.pairwisePullback i j).hp₂

/-- The canonical diagonal morphism `Uᵢ ⟶ Uᵢ ×[U] Uᵢ`. -/
noncomputable def diagonal {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i : 𝒰.index) :
    (𝒰.obj i).left ⟶ 𝒰.overlap i i :=
  (𝒰.pairwisePullback i i).isPullback.lift (𝟙 _) (𝟙 _) (by simp)

/-- The diagonal morphism composed with the first projection is the identity. -/
@[reassoc]
theorem diagonal_pr0 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i : 𝒰.index) :
    𝒰.diagonal i ≫ 𝒰.pr0 i i = 𝟙 ((𝒰.obj i).left) := by
  simpa [diagonal, pr0] using
    (𝒰.pairwisePullback i i).isPullback.lift_fst
      (𝟙 ((𝒰.obj i).left))
      (𝟙 ((𝒰.obj i).left))
      (by simp)

/-- The diagonal morphism composed with the second projection is the identity. -/
@[reassoc]
theorem diagonal_pr1 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i : 𝒰.index) :
    𝒰.diagonal i ≫ 𝒰.pr1 i i = 𝟙 ((𝒰.obj i).left) := by
  simpa [diagonal, pr1] using
    (𝒰.pairwisePullback i i).isPullback.lift_snd
      (𝟙 ((𝒰.obj i).left))
      (𝟙 ((𝒰.obj i).left))
      (by simp)

/-- The canonical switching morphism
`Uᵢ ×[U] Uⱼ ⟶ Uⱼ ×[U] Uᵢ`. -/
noncomputable def switch {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j : 𝒰.index) :
    𝒰.overlap i j ⟶ 𝒰.overlap j i :=
  (𝒰.pairwisePullback j i).isPullback.lift
    (𝒰.pr1 i j)
    (𝒰.pr0 i j)
    ((𝒰.pr0_map_eq_pr1_map i j).symm)

/-- The switching morphism composed with the first projection is the second projection. -/
@[reassoc]
theorem switch_pr0 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) :
    𝒰.switch i j ≫ 𝒰.pr0 j i = 𝒰.pr1 i j := by
  change
    (𝒰.pairwisePullback j i).isPullback.lift
        (𝒰.pr1 i j)
        (𝒰.pr0 i j)
        ((𝒰.pr0_map_eq_pr1_map i j).symm) ≫
      (𝒰.pairwisePullback j i).p₁ = 𝒰.pr1 i j
  exact
    (𝒰.pairwisePullback j i).isPullback.lift_fst
      (𝒰.pr1 i j)
      (𝒰.pr0 i j)
      ((𝒰.pr0_map_eq_pr1_map i j).symm)

/-- The switching morphism composed with the second projection is the first projection. -/
@[reassoc]
theorem switch_pr1 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) :
    𝒰.switch i j ≫ 𝒰.pr1 j i = 𝒰.pr0 i j := by
  change
    (𝒰.pairwisePullback j i).isPullback.lift
        (𝒰.pr1 i j)
        (𝒰.pr0 i j)
        ((𝒰.pr0_map_eq_pr1_map i j).symm) ≫
      (𝒰.pairwisePullback j i).p₂ = 𝒰.pr0 i j
  exact
    (𝒰.pairwisePullback j i).isPullback.lift_snd
      (𝒰.pr1 i j)
      (𝒰.pr0 i j)
      ((𝒰.pr0_map_eq_pr1_map i j).symm)

/-- The chosen triple overlap `Uᵢ ×[U] Uⱼ ×[U] Uₖ`. -/
abbrev tripleOverlap {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) : C :=
  (𝒰.triplePullback i j k).pullback

/-- The projection `Uᵢ ×[U] Uⱼ ×[U] Uₖ ⟶ Uᵢ`. -/
abbrev triplePr0 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) : 𝒰.tripleOverlap i j k ⟶ (𝒰.obj i).left :=
  (𝒰.triplePullback i j k).p₁

/-- The projection `Uᵢ ×[U] Uⱼ ×[U] Uₖ ⟶ Uⱼ`. -/
abbrev triplePr1 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) : 𝒰.tripleOverlap i j k ⟶ (𝒰.obj j).left :=
  (𝒰.triplePullback i j k).p₂

/-- The projection `Uᵢ ×[U] Uⱼ ×[U] Uₖ ⟶ Uₖ`. -/
abbrev triplePr2 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) : 𝒰.tripleOverlap i j k ⟶ (𝒰.obj k).left :=
  (𝒰.triplePullback i j k).p₃

/-- The first triple-overlap projection lies over the common map to `U`. -/
@[reassoc]
theorem triplePr0_map {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) :
    𝒰.triplePr0 i j k ≫ (𝒰.obj i).hom = (𝒰.triplePullback i j k).p := by
  exact (𝒰.triplePullback i j k).w₁

/-- The second triple-overlap projection lies over the common map to `U`. -/
@[reassoc]
theorem triplePr1_map {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) :
    𝒰.triplePr1 i j k ≫ (𝒰.obj j).hom = (𝒰.triplePullback i j k).p := by
  exact (𝒰.triplePullback i j k).w₂

/-- The third triple-overlap projection lies over the common map to `U`. -/
@[reassoc]
theorem triplePr2_map {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) :
    𝒰.triplePr2 i j k ≫ (𝒰.obj k).hom = (𝒰.triplePullback i j k).p := by
  exact (𝒰.triplePullback i j k).w₃

/-- The projection to `Uᵢ ×[U] Uⱼ`. -/
abbrev pr01 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) : 𝒰.tripleOverlap i j k ⟶ 𝒰.overlap i j :=
  (𝒰.triplePullback i j k).p₁₂

/-- The projection to `Uⱼ ×[U] Uₖ`. -/
abbrev pr12 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) : 𝒰.tripleOverlap i j k ⟶ 𝒰.overlap j k :=
  (𝒰.triplePullback i j k).p₂₃

/-- The projection to `Uᵢ ×[U] Uₖ`. -/
abbrev pr02 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j k : 𝒰.index) : 𝒰.tripleOverlap i j k ⟶ 𝒰.overlap i k :=
  (𝒰.triplePullback i j k).p₁₃

/-- The `(i,j)`-projection followed by the first overlap projection recovers `Uᵢ`. -/
theorem triplePr0_eq_pr01_pr0 {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    𝒰.triplePr0 i j k = 𝒰.pr01 i j k ≫ 𝒰.pr0 i j := by
  simpa [triplePr0, pr01, pr0] using (𝒰.triplePullback i j k).p₁₂_p₁.symm

/-- The `(i,j)`-projection followed by the second overlap projection recovers `Uⱼ`. -/
theorem triplePr1_eq_pr01_pr1 {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    𝒰.triplePr1 i j k = 𝒰.pr01 i j k ≫ 𝒰.pr1 i j := by
  simpa [triplePr1, pr01, pr1] using (𝒰.triplePullback i j k).p₁₂_p₂.symm

/-- The `(j,k)`-projection followed by the first overlap projection recovers `Uⱼ`. -/
theorem triplePr1_eq_pr12_pr0 {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    𝒰.triplePr1 i j k = 𝒰.pr12 i j k ≫ 𝒰.pr0 j k := by
  simpa [triplePr1, pr12, pr0] using (𝒰.triplePullback i j k).p₂₃_p₂.symm

/-- The `(j,k)`-projection followed by the second overlap projection recovers `Uₖ`. -/
theorem triplePr2_eq_pr12_pr1 {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    𝒰.triplePr2 i j k = 𝒰.pr12 i j k ≫ 𝒰.pr1 j k := by
  simpa [triplePr2, pr12, pr1] using (𝒰.triplePullback i j k).p₂₃_p₃.symm

/-- The `(i,k)`-projection followed by the first overlap projection recovers `Uᵢ`. -/
theorem triplePr0_eq_pr02_pr0 {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    𝒰.triplePr0 i j k = 𝒰.pr02 i j k ≫ 𝒰.pr0 i k := by
  simpa [triplePr0, pr02, pr0] using (𝒰.triplePullback i j k).p₁₃_p₁.symm

/-- The `(i,k)`-projection followed by the second overlap projection recovers `Uₖ`. -/
theorem triplePr2_eq_pr02_pr1 {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j k : 𝒰.index) :
    𝒰.triplePr2 i j k = 𝒰.pr02 i j k ≫ 𝒰.pr1 i k := by
  simpa [triplePr2, pr02, pr1] using (𝒰.triplePullback i j k).p₁₃_p₃.symm

/-- The canonical map
`Δ₁₃ : Uᵢ ×[U] Uⱼ ⟶ Uᵢ ×[U] Uⱼ ×[U] Uᵢ`. -/
noncomputable def delta13 {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] (i j : 𝒰.index) :
    𝒰.overlap i j ⟶ 𝒰.tripleOverlap i j i :=
  let h :
      𝟙 (𝒰.overlap i j) ≫ (𝒰.pairwisePullback i j).p₁ =
        (𝒰.pr0 i j ≫ 𝒰.diagonal i) ≫ (𝒰.pairwisePullback i i).p₁ := by
    simpa [pr0, Category.assoc] using
      congrArg (fun f ↦ 𝒰.pr0 i j ≫ f) (𝒰.diagonal_pr0 i).symm
  (𝒰.triplePullback i j i).isPullback₁.lift (𝟙 (𝒰.overlap i j)) (𝒰.pr0 i j ≫ 𝒰.diagonal i) h

/-- The canonical map `Δ₁₃` composed with `pr₀₁` is the identity. -/
@[reassoc]
theorem delta13_pr01 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) :
    𝒰.delta13 i j ≫ 𝒰.pr01 i j i = 𝟙 (𝒰.overlap i j) := by
  let h :
      𝟙 (𝒰.overlap i j) ≫ (𝒰.pairwisePullback i j).p₁ =
        (𝒰.pr0 i j ≫ 𝒰.diagonal i) ≫ (𝒰.pairwisePullback i i).p₁ := by
    simpa [pr0, Category.assoc] using
      congrArg (fun f ↦ 𝒰.pr0 i j ≫ f) (𝒰.diagonal_pr0 i).symm
  exact
    (𝒰.triplePullback i j i).isPullback₁.lift_fst
      (𝟙 (𝒰.overlap i j))
      (𝒰.pr0 i j ≫ 𝒰.diagonal i)
      h

/-- The canonical map `Δ₁₃` composed with `pr₀₂` is the diagonal on the first factor. -/
@[reassoc]
theorem delta13_pr02 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) :
    𝒰.delta13 i j ≫ 𝒰.pr02 i j i = 𝒰.pr0 i j ≫ 𝒰.diagonal i := by
  let h :
      𝟙 (𝒰.overlap i j) ≫ (𝒰.pairwisePullback i j).p₁ =
        (𝒰.pr0 i j ≫ 𝒰.diagonal i) ≫ (𝒰.pairwisePullback i i).p₁ := by
    simpa [pr0, Category.assoc] using
      congrArg (fun f ↦ 𝒰.pr0 i j ≫ f) (𝒰.diagonal_pr0 i).symm
  exact
    (𝒰.triplePullback i j i).isPullback₁.lift_snd
      (𝟙 (𝒰.overlap i j))
      (𝒰.pr0 i j ≫ 𝒰.diagonal i)
      h

/-- The canonical map `Δ₁₃` composed with `pr₁₂` is the switching morphism. -/
@[reassoc]
theorem delta13_pr12 {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    (i j : 𝒰.index) :
    𝒰.delta13 i j ≫ 𝒰.pr12 i j i = 𝒰.switch i j := by
  apply (𝒰.pairwisePullback j i).hom_ext
  · have h :
        (𝒰.delta13 i j ≫ 𝒰.pr12 i j i) ≫ 𝒰.pr0 j i = 𝒰.pr1 i j := by
        calc
          (𝒰.delta13 i j ≫ 𝒰.pr12 i j i) ≫ 𝒰.pr0 j i
              = 𝒰.delta13 i j ≫ 𝒰.triplePr1 i j i := by
                  simpa [Category.assoc] using
                    congrArg (fun f ↦ 𝒰.delta13 i j ≫ f) (𝒰.triplePr1_eq_pr12_pr0 i j i).symm
          _ = 𝒰.delta13 i j ≫ 𝒰.pr01 i j i ≫ 𝒰.pr1 i j := by
                simpa [Category.assoc] using
                  congrArg (fun f ↦ 𝒰.delta13 i j ≫ f) (𝒰.triplePr1_eq_pr01_pr1 i j i)
          _ = 𝒰.pr1 i j := by
                calc
                  𝒰.delta13 i j ≫ 𝒰.pr01 i j i ≫ 𝒰.pr1 i j
                      = (𝒰.delta13 i j ≫ 𝒰.pr01 i j i) ≫ 𝒰.pr1 i j := by
                          simp [Category.assoc]
                  _ = 𝟙 (𝒰.overlap i j) ≫ 𝒰.pr1 i j := by rw [𝒰.delta13_pr01 i j]
                  _ = 𝒰.pr1 i j := by simp
    change (𝒰.delta13 i j ≫ 𝒰.pr12 i j i) ≫ (𝒰.pairwisePullback j i).p₁ =
        𝒰.switch i j ≫ (𝒰.pairwisePullback j i).p₁
    simpa [Category.assoc, pr0] using h.trans (𝒰.switch_pr0 i j).symm
  · have h :
        (𝒰.delta13 i j ≫ 𝒰.pr12 i j i) ≫ 𝒰.pr1 j i = 𝒰.pr0 i j := by
        calc
          (𝒰.delta13 i j ≫ 𝒰.pr12 i j i) ≫ 𝒰.pr1 j i
              = 𝒰.delta13 i j ≫ 𝒰.triplePr2 i j i := by
                  simpa [Category.assoc] using
                    congrArg (fun f ↦ 𝒰.delta13 i j ≫ f) (𝒰.triplePr2_eq_pr12_pr1 i j i).symm
          _ = 𝒰.delta13 i j ≫ 𝒰.pr02 i j i ≫ 𝒰.pr1 i i := by
                simpa [Category.assoc] using
                  congrArg (fun f ↦ 𝒰.delta13 i j ≫ f) (𝒰.triplePr2_eq_pr02_pr1 i j i)
          _ = 𝒰.pr0 i j := by
                calc
                  𝒰.delta13 i j ≫ 𝒰.pr02 i j i ≫ 𝒰.pr1 i i
                      = (𝒰.delta13 i j ≫ 𝒰.pr02 i j i) ≫ 𝒰.pr1 i i := by
                          simp [Category.assoc]
                  _ = (𝒰.pr0 i j ≫ 𝒰.diagonal i) ≫ 𝒰.pr1 i i := by rw [𝒰.delta13_pr02 i j]
                  _ = 𝒰.pr0 i j ≫ (𝒰.diagonal i ≫ 𝒰.pr1 i i) := by simp [Category.assoc]
                  _ = 𝒰.pr0 i j ≫ 𝟙 ((𝒰.obj i).left) := by rw [𝒰.diagonal_pr1 i]
                  _ = 𝒰.pr0 i j := by simp
    change (𝒰.delta13 i j ≫ 𝒰.pr12 i j i) ≫ (𝒰.pairwisePullback j i).p₂ =
        𝒰.switch i j ≫ (𝒰.pairwisePullback j i).p₂
    simpa [Category.assoc, pr1] using h.trans (𝒰.switch_pr1 i j).symm

attribute [simp]
  pr0_map_eq_pr1_map_assoc
  pr0_map_assoc
  pr1_map_assoc
  diagonal_pr0_assoc
  diagonal_pr1_assoc
  switch_pr0_assoc
  switch_pr1_assoc
  triplePr0_map_assoc
  triplePr1_map_assoc
  triplePr2_map_assoc
  delta13_pr01_assoc
  delta13_pr02_assoc
  delta13_pr12_assoc

end SemiRepresentableFamily.Over

/-- Definition 8.3.1: a descent datum for a fixed-target family `𝒰` in a fibred category with
chosen overlaps is the canonical chosen-pullback descent data for the fiber pseudofunctor
attached to `hc`, specialized to the pairwise and triple overlaps of `𝒰`. -/
@[stacks 026B]
abbrev DescentDatum
    (p : S ⥤ C) (hc : PullbackChoice p)
    {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰] :=
  (hc.fiberPseudofunctor).DescentData' (𝒰.pairwisePullback) (𝒰.triplePullback)

namespace DescentDatum

open Pseudofunctor.DescentData'

variable {p : S ⥤ C} {hc : PullbackChoice p}
variable {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]

/-- The comparison isomorphism on the chosen overlap `Uᵢ ×[U] Uⱼ`, obtained from the canonical
descent-data isomorphism on the chosen overlap. -/
noncomputable abbrev iso
    (D : DescentDatum p hc 𝒰) (i j : 𝒰.index) :
    hc.obj (𝒰.pr0 i j) (D.obj i) ≅ hc.obj (𝒰.pr1 i j) (D.obj j) :=
  D.descentData.iso
    (𝒰.pairwisePullback i j).p
    (𝒰.pr0 i j)
    (𝒰.pr1 i j)
    (𝒰.pr0_map i j)
    (𝒰.pr1_map i j)

@[simp]
theorem iso_hom
    (D : DescentDatum p hc 𝒰) (i j : 𝒰.index) :
    (D.iso i j).hom = D.hom i j := by
  simpa [iso, Pseudofunctor.DescentData.iso] using
    (Pseudofunctor.DescentData'.pullHom'_eq_hom D i j)

/-- The pullback to the triple overlap of the comparison isomorphism on the `(i,j)` overlap. -/
noncomputable abbrev pr01PullbackIso
    (D : DescentDatum p hc 𝒰) (i j k : 𝒰.index) :
    hc.obj (𝒰.triplePr0 i j k) (D.obj i) ≅ hc.obj (𝒰.triplePr1 i j k) (D.obj j) :=
  D.descentData.iso
    (𝒰.triplePullback i j k).p
    (𝒰.triplePr0 i j k)
    (𝒰.triplePr1 i j k)
    (𝒰.triplePr0_map i j k)
    (𝒰.triplePr1_map i j k)

/-- The pullback to the triple overlap of the comparison isomorphism on the `(j,k)` overlap. -/
noncomputable abbrev pr12PullbackIso
    (D : DescentDatum p hc 𝒰) (i j k : 𝒰.index) :
    hc.obj (𝒰.triplePr1 i j k) (D.obj j) ≅ hc.obj (𝒰.triplePr2 i j k) (D.obj k) :=
  D.descentData.iso
    (𝒰.triplePullback i j k).p
    (𝒰.triplePr1 i j k)
    (𝒰.triplePr2 i j k)
    (𝒰.triplePr1_map i j k)
    (𝒰.triplePr2_map i j k)

/-- The pullback to the triple overlap of the comparison isomorphism on the `(i,k)` overlap. -/
noncomputable abbrev pr02PullbackIso
    (D : DescentDatum p hc 𝒰) (i j k : 𝒰.index) :
    hc.obj (𝒰.triplePr0 i j k) (D.obj i) ≅ hc.obj (𝒰.triplePr2 i j k) (D.obj k) :=
  D.descentData.iso
    (𝒰.triplePullback i j k).p
    (𝒰.triplePr0 i j k)
    (𝒰.triplePr2 i j k)
    (𝒰.triplePr0_map i j k)
    (𝒰.triplePr2_map i j k)

-- Proof sketch: this is the chosen-triple-overlap specialization of the canonical cocycle
-- relation `comp_pullHom'` for `Pseudofunctor.DescentData'`.
/-- The pairwise comparison isomorphisms satisfy the cocycle condition on the chosen triple
overlaps. -/
theorem cocycle
    (D : DescentDatum p hc 𝒰) (i j k : 𝒰.index) :
    D.pr01PullbackIso i j k ≪≫ D.pr12PullbackIso i j k = D.pr02PullbackIso i j k := by
  ext
  rw [Iso.trans_hom]
  simp only [id_obj, Pseudofunctor.DescentData.iso_hom, const_obj_obj, descentData_hom,
    ChosenPullback₃.w₁, map_comp]
  exact congrArg Fiber.fiberInclusion.map <|
    D.comp_pullHom'
      (𝒰.triplePullback i j k).p
      (𝒰.triplePr0 i j k)
      (𝒰.triplePr1 i j k)
      (𝒰.triplePr2 i j k)
      (𝒰.triplePr0_map i j k)
      (𝒰.triplePr1_map i j k)
      (𝒰.triplePr2_map i j k)

end DescentDatum

end CategoryTheory
