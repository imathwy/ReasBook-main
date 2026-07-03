import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_3_1 (from Chap08) -/
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

/-! ### Lemma_8_3_3 (from Chap08) -/
noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open SemiRepresentableFamily.Over

namespace CategoryTheory

/- Domain-style sampling for Lemma 8.3.3:
- primary domain: categorical descent data for fixed-target families in a fibred category.
- inspected owner-level declarations:
  `SemiRepresentableFamily.map`,
  `DescentDatum` from 8.3.1,
  `Pseudofunctor.DescentData.pullFunctor`,
  `Pseudofunctor.DescentData.pullFunctorIso`,
  `Pseudofunctor.DescentData'.descentDataEquivalence`.
- best owner abstraction: the fixed-target family owner `SemiRepresentableFamily.Over U`, together
  with the chapter owner `DescentDatum p hc 𝒰`.
- primitive data: a fixed-target family `𝒰`, a second family `𝒱`, and a morphism of families over
  a base map.
- derived API: the equivalence from chosen-overlap descent data to canonical descent data, the
  induced pullback functor, and the canonical isomorphism between pullback functors over the same
  base map.

Source/core/bridge triage:
- `source-facing`: morphisms of fixed-target families over a base map.
- `core/canonical`: `DescentDatum p hc 𝒰` and `Pseudofunctor.DescentData.pullFunctor`.
- `bridge/view`: the equivalence
  `Pseudofunctor.DescentData'.descentDataEquivalence` specialized to the owner-level chosen
  overlaps of `𝒰`.
-/

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

private noncomputable abbrev familyDescentDataEquivalence
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰] :
    DescentDatum p hc 𝒰 ≌
      (hc.fiberPseudofunctor).DescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom) :=
  Pseudofunctor.DescentData'.descentDataEquivalence
    hc.fiberPseudofunctor
    𝒰.pairwisePullback
    𝒰.triplePullback

section PullbackOfDescentData

variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
variable {U V : C}
variable {𝒰 : SemiRepresentableFamily.Over U} {𝒱 : SemiRepresentableFamily.Over V}
variable [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]

omit [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱] in
private theorem familyMorphism_w
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (i : 𝒰.index) :
    (φ.f i).left ≫ (𝒱.obj (φ.α i)).hom = (𝒰.obj i).hom ≫ base := by
  simpa using Over.w (φ.f i)

omit [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱] in
private noncomputable abbrev familyPullFunctor
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    (hc.fiberPseudofunctor).DescentData (fun i : 𝒱.index ↦ (𝒱.obj i).hom) ⥤
      (hc.fiberPseudofunctor).DescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom) :=
  Pseudofunctor.DescentData.pullFunctor hc.fiberPseudofunctor (familyMorphism_w base φ)

omit [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱] in
private noncomputable def familyPullFunctorIso
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    familyPullFunctor hc base φ ≅ familyPullFunctor hc base φ' :=
  let wφ : ∀ i : 𝒰.index,
      (φ.f i).left ≫ (fun j : 𝒱.index ↦ (𝒱.obj j).hom) (φ.α i) = (𝒰.obj i).hom ≫ base :=
    familyMorphism_w base φ
  let wφ' : ∀ i : 𝒰.index,
      (φ'.f i).left ≫ (fun j : 𝒱.index ↦ (𝒱.obj j).hom) (φ'.α i) = (𝒰.obj i).hom ≫ base :=
    familyMorphism_w base φ'
  @Pseudofunctor.DescentData.pullFunctorIso
    C _ hc.fiberPseudofunctor
    𝒱.index V
    (fun i : 𝒱.index ↦ (𝒱.obj i).left)
    (fun i : 𝒱.index ↦ (𝒱.obj i).hom)
    U base
    𝒰.index
    (fun i : 𝒰.index ↦ (𝒰.obj i).left)
    (fun i : 𝒰.index ↦ (𝒰.obj i).hom)
    φ.α
    (fun i ↦ (φ.f i).left)
    wφ
    φ'.α
    (fun i ↦ (φ'.f i).left)
    wφ'

/-- Lemma 8.3.3 (1): pullback along a morphism of fixed-target families over `base : U ⟶ V`,
given canonically by a morphism `((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)`,
defines a functor on descent data. -/
noncomputable def pullbackFamilyDescentFunctor
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    DescentDatum p hc 𝒱 ⥤ DescentDatum p hc 𝒰 :=
  let e𝒱 := familyDescentDataEquivalence hc 𝒱
  let e𝒰 := familyDescentDataEquivalence hc 𝒰
  (e𝒱.functor ⋙ familyPullFunctor hc base φ) ⋙ e𝒰.inverse

/-- The image of one descent datum under the pullback functor from Lemma 8.3.3. -/
noncomputable abbrev pullbackFamilyDescentDatum
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    DescentDatum p hc 𝒰 :=
  (pullbackFamilyDescentFunctor hc base φ).obj D

-- Proof sketch: this is definitional from `pullbackFamilyDescentDatum`.
/-- Applying the pullback functor to `D` gives the pulled-back descent datum. -/
theorem pullbackFamilyDescentFunctor_obj
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    (pullbackFamilyDescentFunctor hc base φ).obj D =
      pullbackFamilyDescentDatum hc base φ D := by
  -- The public object-level API is just the abbreviation for the pulled-back descent datum.
  rfl

/-- Evaluating the pulled-back descent datum at `i` gives the pullback of the local object
`D.obj (φ.α i)` along the component map `Uᵢ ⟶ V_{α(i)}`. -/
theorem pullbackFamilyDescentDatum_obj
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) (i : 𝒰.index) :
    (pullbackFamilyDescentDatum hc base φ D).obj i =
      hc.obj (φ.f i).left (D.obj (φ.α i)) :=
  rfl

/-- Lemma 8.3.3 (2): two pullback functors induced by morphisms of fixed-target families over the
same base map are canonically isomorphic. -/
noncomputable def pullbackFamilyDescentFunctorIso
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱)) :
    pullbackFamilyDescentFunctor hc base φ ≅ pullbackFamilyDescentFunctor hc base φ' :=
  let e𝒱 := familyDescentDataEquivalence hc 𝒱
  let e𝒰 := familyDescentDataEquivalence hc 𝒰
  let pullIso := familyPullFunctorIso hc base φ φ'
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft e𝒱.functor pullIso)
    e𝒰.inverse

/-- The component at `D` of the canonical comparison isomorphism between two pullback functors. -/
noncomputable abbrev pullbackFamilyDescentDatumIso
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    pullbackFamilyDescentDatum hc base φ D ≅ pullbackFamilyDescentDatum hc base φ' D :=
  (pullbackFamilyDescentFunctorIso hc base φ φ').app D

-- Proof sketch: this is the objectwise component of the natural isomorphism
-- `pullbackFamilyDescentFunctorIso`.
/-- Evaluating the comparison isomorphism of pullback functors at `D` gives the comparison
isomorphism between the pulled-back descent data. -/
theorem pullbackFamilyDescentFunctorIso_app
    (base : U ⟶ V)
    (φ φ' : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    (D : DescentDatum p hc 𝒱) :
    (pullbackFamilyDescentFunctorIso hc base φ φ').app D =
      pullbackFamilyDescentDatumIso hc base φ φ' D := by
  -- The component comparison is exactly the abbreviation defining the objectwise isomorphism.
  rfl

end PullbackOfDescentData

end CategoryTheory

/-! ### Definition_8_3_4 (from Chap08) -/
namespace CategoryTheory

/- Domain-style sampling for Definition 8.3.4:
- primary domain: pullback functoriality on descent data for morphisms of fixed-target families in
  a fibred category;
- sampled owner abstractions:
  `Pseudofunctor.DescentData.pullFunctor`,
  `Pseudofunctor.DescentData.pullFunctorIso`,
  `Pseudofunctor.DescentData'.descentDataEquivalence`,
  `pullbackFamilyDescentFunctor` from 8.3.3;
- source-facing layer: pullback on descent data attached to a morphism of fixed-target families
  over a base map;
- core/canonical owner: `Pseudofunctor.DescentData.pullFunctor`;
- bridge/view layer: `pullbackFamilyDescentFunctor`, the chapter specialization through
  `DescentDatum p hc 𝒰`.

Primitive data are the two fixed-target families and a morphism between them over a base arrow.
The induced pullback functor and its same-base comparison isomorphism are derived owner-level API,
so this file should remain a pure recall surface rather than introducing a parallel wrapper.
-/

/- Definition 8.3.4: with `𝒰 = {U_i ⟶ U}_{i ∈ I}`, `𝒱 = {V_j ⟶ V}_{j ∈ J}`, an index map
`α : I → J`, a base morphism `h : U ⟶ V`, and component maps `g_i : U_i ⟶ V_{α(i)}` as in Lemma
8.3.3, the functor
`(Y_j, \varphi_{jj'}) ↦ (g_i^* Y_{α(i)}, (g_i × g_{i'})^* \varphi_{α(i)α(i')})`
constructed there is the pullback functor on descent data. -/
recall pullbackFamilyDescentFunctor

/- Companion recall: if two morphisms of fixed-target families have the same base map, then the
resulting pullback functors on descent data are canonically isomorphic. This is the source-text
reason one may write `h^*` when the chosen lift of `h` is irrelevant. -/
recall pullbackFamilyDescentFunctorIso

end CategoryTheory

/-! ### Definition_8_3_5 (from Chap08) -/
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

/-! ### Lemma_8_3_6 (from Chap08) -/
noncomputable section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

variable {p : S ⥤ C} (hc : PullbackChoice p)
variable {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]

/-- Helper for Lemma 8.3.6: the two overlap composites to `U` induce the same chosen pullback
object after transporting along `pr₀ ≫ f_i = pr₁ ≫ f_j`. -/
private theorem family_descent_functor_obj_overlap_transport
    (X : p.Fiber U) (i i' : 𝒰.index) :
    hc.obj (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) X =
      hc.obj (𝒰.pr1 i i' ≫ (𝒰.obj i').hom) X := by
  simpa using congrArg (fun f ↦ hc.obj f X) (𝒰.pr0_map_eq_pr1_map i i')

/-- Helper for Lemma 8.3.6: the left overlap composite and the chosen overlap map induce the same
pullback object in the fiber over `U`. -/
private theorem family_descent_functor_obj_pr0_transport
    (X : p.Fiber U) (i i' : 𝒰.index) :
    hc.obj (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) X =
      hc.obj (𝒰.pairwisePullback i i').p X := by
  simpa using congrArg (fun f ↦ hc.obj f X) (𝒰.pr0_map i i')

/-- Helper for Lemma 8.3.6: the chosen overlap map and the right overlap composite induce the same
pullback object in the fiber over `U`. -/
private theorem family_descent_functor_obj_pr1_transport
    (X : p.Fiber U) (i i' : 𝒰.index) :
    hc.obj (𝒰.pairwisePullback i i').p X =
      hc.obj (𝒰.pr1 i i' ≫ (𝒰.obj i').hom) X := by
  simpa using (congrArg (fun f ↦ hc.obj f X) (𝒰.pr1_map i i')).symm

/-- Helper for Lemma 8.3.6: the overlap transport factors through the chosen overlap map. -/
private theorem family_descent_functor_obj_overlap_transport_eq
    (X : p.Fiber U) (i i' : 𝒰.index) :
    family_descent_functor_obj_overlap_transport (hc := hc) (𝒰 := 𝒰) X i i' =
      (family_descent_functor_obj_pr0_transport (hc := hc) (𝒰 := 𝒰) X i i').trans
        (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') := by
  apply Subsingleton.elim

/-- Helper for Lemma 8.3.6: the inverse component of the fiber pseudofunctor's flexible
composition comparison is the chosen pullback-composition comparison in the fiber. -/
private theorem fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
        (f.op.toLoc ≫ g.op.toLoc) (by simp)).inv.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).inv := by
  simp [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

/-- Helper for Lemma 8.3.6: the hom component of the fiber pseudofunctor's flexible composition
comparison is the chosen pullback-composition comparison in the fiber. -/
private theorem fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
        (f.op.toLoc ≫ g.op.toLoc) (by simp)).hom.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).hom := by
  simp [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

/-- Helper for Lemma 8.3.6: on the left overlap leg, the localized opposite composite agrees with
the chosen pairwise-overlap map. -/
private theorem family_descent_functor_obj_pr0_map_toLoc
    (i i' : 𝒰.index) :
    (𝒰.obj i).hom.op.toLoc ≫ (𝒰.pr0 i i').op.toLoc =
      ((𝒰.pairwisePullback i i').p).op.toLoc := by
  simpa using congrArg (fun f ↦ f.op.toLoc) (𝒰.pr0_map i i')

/-- Helper for Lemma 8.3.6: on the right overlap leg, the localized opposite composite agrees
with the chosen pairwise-overlap map. -/
private theorem family_descent_functor_obj_pr1_map_toLoc
    (i i' : 𝒰.index) :
    (𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc =
      ((𝒰.pairwisePullback i i').p).op.toLoc := by
  simpa using congrArg (fun f ↦ f.op.toLoc) (𝒰.pr1_map i i')

/-- Helper for Lemma 8.3.6: the left pullback-comparison iso on the pairwise overlap. -/
private noncomputable abbrev familyDescentFunctor_obj_pr0Comparison
    (i i' : 𝒰.index) :
    hc.fiberPseudofunctor.map ((𝒰.pairwisePullback i i').p).op.toLoc ≅
      hc.fiberPseudofunctor.map (𝒰.obj i).hom.op.toLoc ≫
        hc.fiberPseudofunctor.map (𝒰.pr0 i i').op.toLoc :=
  hc.fiberPseudofunctor.mapComp'
    (𝒰.obj i).hom.op.toLoc
    (𝒰.pr0 i i').op.toLoc
    ((𝒰.pairwisePullback i i').p).op.toLoc
    (family_descent_functor_obj_pr0_map_toLoc (𝒰 := 𝒰) i i')

/-- Helper for Lemma 8.3.6: the right pullback-comparison iso on the pairwise overlap. -/
private noncomputable abbrev familyDescentFunctor_obj_pr1Comparison
    (i i' : 𝒰.index) :
    hc.fiberPseudofunctor.map ((𝒰.pairwisePullback i i').p).op.toLoc ≅
      hc.fiberPseudofunctor.map (𝒰.obj i').hom.op.toLoc ≫
        hc.fiberPseudofunctor.map (𝒰.pr1 i i').op.toLoc :=
  hc.fiberPseudofunctor.mapComp'
    (𝒰.obj i').hom.op.toLoc
    (𝒰.pr1 i i').op.toLoc
    ((𝒰.pairwisePullback i i').p).op.toLoc
    (family_descent_functor_obj_pr1_map_toLoc (𝒰 := 𝒰) i i')

/-- Helper for Lemma 8.3.6: the overlap morphism of the canonical descent datum of `X` is the
owner-side `DescentData.ofObj` transition on the chosen overlap. -/
private theorem family_descent_functor_obj_hom_shell
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor hc 𝒰).obj X).hom i i' =
      ((familyDescentFunctor_obj_pr0Comparison (hc := hc) (𝒰 := 𝒰) i i').inv.toNatTrans.app X) ≫
        ((familyDescentFunctor_obj_pr1Comparison (hc := hc) (𝒰 := 𝒰) i i').hom.toNatTrans.app X) := by
  rfl

/-- Helper for Lemma 8.3.6: the strict right-leg composition comparison evaluates to the Chapter
4 pullback-composition comparison in the fiber. -/
private theorem fiberPseudofunctor_mapComp_hom_app_eq_pullbackCompComponentIso_hom
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).hom := by
  -- The strict comparison is the `rfl` instance of the flexible `mapComp'` comparison.
  simpa [Pseudofunctor.mapComp'_eq_mapComp] using
    (fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom (hc := hc)
      (f := f) (g := g) X)

/-- Helper for Lemma 8.3.6: the right overlap comparison splits into the equality transport from
the chosen overlap map to the strict composite, followed by the strict composition comparison. -/
private theorem family_descent_functor_obj_pr1Comparison_eq_map₂Iso_comp_mapComp
    (i i' : 𝒰.index) :
    familyDescentFunctor_obj_pr1Comparison (hc := hc) (𝒰 := 𝒰) i i' =
      hc.fiberPseudofunctor.map₂Iso
          (eqToIso (by
            simpa using (family_descent_functor_obj_pr1_map_toLoc
              (𝒰 := 𝒰) i i').symm)) ≪≫
        hc.fiberPseudofunctor.mapComp (𝒰.obj i').hom.op.toLoc (𝒰.pr1 i i').op.toLoc := by
  -- This is the defining expansion of `mapComp'` specialized to the chosen overlap map.
  simp [familyDescentFunctor_obj_pr1Comparison, Pseudofunctor.mapComp']

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.3.6: the left comparison for the chosen overlap is the Chapter 4
pullback-composition comparison followed by the transport from `pr₀ ≫ f_i` to the chosen overlap
map. -/
private theorem family_descent_functor_obj_pr0Comparison_inv_normalize
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor_obj_pr0Comparison (hc := hc) (𝒰 := 𝒰) i i').inv.toNatTrans.app X) =
      (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
        eqToHom (family_descent_functor_obj_pr0_transport (hc := hc) (𝒰 := 𝒰) X i i') := by
  -- Unfold the packaged left comparison and expose the transport from `(pr₀ ≫ f_i)^* X` to the
  -- chosen overlap pullback `pᵢᵢ'^* X`.
  simpa [familyDescentFunctor_obj_pr0Comparison,
    family_descent_functor_obj_pr0_map_toLoc, family_descent_functor_obj_pr0_transport] using
    (fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv (hc := hc)
      (f := (𝒰.obj i).hom) (g := 𝒰.pr0 i i') X)

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.3.6: the right comparison for the chosen overlap is the transport from the
chosen overlap map to `pr₁ ≫ f_j`, followed by the Chapter 4 pullback-composition comparison. -/
private theorem family_descent_functor_obj_pr1Comparison_hom_normalize
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor_obj_pr1Comparison (hc := hc) (𝒰 := 𝒰) i i').hom.toNatTrans.app X) =
      eqToHom (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') ≫
        (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
  let transportIso :
      hc.fiberPseudofunctor.map ((𝒰.pairwisePullback i i').p).op.toLoc ≅
        hc.fiberPseudofunctor.map
          ((𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc) :=
    hc.fiberPseudofunctor.map₂Iso
      (eqToIso (show ((𝒰.pairwisePullback i i').p).op.toLoc =
          (𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc from by
        simpa using (family_descent_functor_obj_pr1_map_toLoc
          (𝒰 := 𝒰) i i').symm))
  have htransport :
      transportIso.hom.toNatTrans.app X =
        eqToHom (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') := by
    -- The equality-2-morphism component is exactly the transport between the two pullback objects.
    dsimp [transportIso]
    let hfg :
        ((𝒰.pairwisePullback i i').p).op.toLoc =
          (𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc := by
      simpa using (family_descent_functor_obj_pr1_map_toLoc (𝒰 := 𝒰) i i').symm
    have hmap :
        hc.fiberPseudofunctor.toPrelaxFunctor.map₂ (eqToHom hfg) =
          eqToHom (by rw [← hfg]) := by
      simpa using
        (PrelaxFunctor.map₂_eqToHom (F := hc.fiberPseudofunctor.toPrelaxFunctor)
          ((𝒰.pairwisePullback i i').p).op.toLoc
          ((𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc) hfg)
    simpa [hfg, PullbackChoice.fiberPseudofunctor, family_descent_functor_obj_pr1_transport] using
      congrArg (fun α ↦ α.toNatTrans.app X) hmap
  -- Route correction: unfold the actual flexible `mapComp'` shell here so the owner-side cast
  -- from the chosen overlap map to `(pr₁ ≫ f_j)` is exposed explicitly before normalization.
  rw [family_descent_functor_obj_pr1Comparison_eq_map₂Iso_comp_mapComp
    (hc := hc) (𝒰 := 𝒰) i i']
  -- After exposing the transport shell, evaluate the `map₂Iso` factor and the strict `mapComp`
  -- factor separately.
  change transportIso.hom.toNatTrans.app X ≫
      (hc.fiberPseudofunctor.mapComp (𝒰.obj i').hom.op.toLoc
        (𝒰.pr1 i i').op.toLoc).hom.toNatTrans.app X =
    eqToHom (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') ≫
      (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom
  rw [htransport]
  rw [fiberPseudofunctor_mapComp_hom_app_eq_pullbackCompComponentIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.3.6: the owner-side overlap isomorphism of the canonical descent datum has
the textbook underlying morphism. -/
private theorem family_descent_functor_obj_iso_hom
    (X : p.Fiber U) (i i' : 𝒰.index) :
    (((familyDescentFunctor hc 𝒰).obj X).iso i i').hom =
      (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
        eqToHom (family_descent_functor_obj_overlap_transport
          (hc := hc) (𝒰 := 𝒰) X i i') ≫
        (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
  -- First rewrite the descent datum morphism to the common overlap shell.
  calc
    (((familyDescentFunctor hc 𝒰).obj X).iso i i').hom
      =
        (((hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
            eqToHom (family_descent_functor_obj_pr0_transport
              (hc := hc) (𝒰 := 𝒰) X i i')) ≫
          (eqToHom (family_descent_functor_obj_pr1_transport
              (hc := hc) (𝒰 := 𝒰) X i i') ≫
            (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom)) := by
          -- The two adapter lemmas identify the packaged `mapComp'` terms with the textbook
          -- pullback-composition comparisons on the left and right overlap legs.
          rw [DescentDatum.iso_hom, family_descent_functor_obj_hom_shell,
            family_descent_functor_obj_pr0Comparison_inv_normalize,
            family_descent_functor_obj_pr1Comparison_hom_normalize]
    _ =
        (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
          (eqToHom (family_descent_functor_obj_pr0_transport
              (hc := hc) (𝒰 := 𝒰) X i i') ≫
            eqToHom (family_descent_functor_obj_pr1_transport
              (hc := hc) (𝒰 := 𝒰) X i i')) ≫
          (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
          -- Reassociate so the two transport morphisms become adjacent.
          simp
    _ =
        (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
          eqToHom
            ((family_descent_functor_obj_pr0_transport (hc := hc) (𝒰 := 𝒰) X i i').trans
              (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i')) ≫
          (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
          -- The two transports compose to the transport from `pr₀ ≫ f_i` to `pr₁ ≫ f_j`.
          rw [eqToHom_trans]
    _ =
        (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
          eqToHom (family_descent_functor_obj_overlap_transport
            (hc := hc) (𝒰 := 𝒰) X i i') ≫
          (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
          -- Replace the composite transport through the chosen overlap by the direct overlap
          -- transport.
          rw [family_descent_functor_obj_overlap_transport_eq]

/-- Lemma 8.3.6: for the canonical descent datum attached to a global object `X`, the overlap
isomorphism on `U_i ×[U] U_j` is the composite of the inverse component of the
pullback-composition comparison, the transport along `pr₀ ≫ f_i = pr₁ ≫ f_j`, and the forward
component of the pullback-composition comparison. -/
theorem familyDescentFunctor_obj_iso
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor hc 𝒰).obj X).iso i i' =
      (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).symm ≪≫
        eqToIso (family_descent_functor_obj_overlap_transport (hc := hc) (𝒰 := 𝒰) X i i') ≪≫
        hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X := by
  apply Iso.ext
  exact family_descent_functor_obj_iso_hom (hc := hc) (𝒰 := 𝒰) X i i'

end CategoryTheory

/-! ### Lemma_8_3_7 (from Chap08) -/
noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

/-- Helper for Lemma 8.3.7: once the local faithful and full halves of the identity-refinement
comparison functor are available, the main equivalence-transfer theorem can use that comparison as
its fully faithful bridge. -/
private noncomputable def pullbackFamilyDescentFunctor_fullyFaithful_of_refinement_local
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i i' : 𝒰.index,
      HasDescentPullbacks (𝒱.overlapBaseChange 𝒰 i i')]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i i' : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.overlapBaseChange 𝒰 i i'))]
    (φ : 𝒱 ⟶ 𝒰) :
    (pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)).FullyFaithful :=
  letI := pullbackFamilyDescentFunctor_faithful_of_refinement
    hc 𝒰 𝒱 φ
  letI := pullbackFamilyDescentFunctor_full_of_refinement
    hc 𝒰 𝒱 φ
  Functor.FullyFaithful.ofFullyFaithful _

/-- Lemma 8.3.7: let `φ : 𝒱 ⟶ 𝒰` be a refinement of fixed-target families over `U`, and for each
`i` and `(i,i')` write `𝒱_i = baseChange 𝒱 (𝒰.obj i).hom` and
`𝒱_{ii'} = baseChange 𝒱 (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)`. Assume descent data
are defined for `𝒰`, `𝒱`, every `𝒱_i`, and every `𝒱_{ii'}`. If `𝒮_U ⥤ DD(𝒱)` is an equivalence,
if each `𝒮_{U_i} ⥤ DD(𝒱_i)` is fully faithful, and if each
`𝒮_{U_i ×[U] U_{i'}} ⥤ DD(𝒱_{ii'})` is faithful, then `𝒮_U ⥤ DD(𝒰)` is an equivalence. -/
theorem familyDescentFunctor_isEquivalence_of_refinement
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i i' : 𝒰.index,
      HasDescentPullbacks (𝒱.overlapBaseChange 𝒰 i i')]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i i' : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.overlapBaseChange 𝒰 i i'))]
    (φ : 𝒱 ⟶ 𝒰) [Functor.IsEquivalence (familyDescentFunctor hc 𝒱)] :
    Functor.IsEquivalence (familyDescentFunctor hc 𝒰) := by
  -- Package the local faithful and full comparison into the fully faithful bridge used by the
  -- equivalence-transfer theorem.
  have hPullback :
      (pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).FullyFaithful :=
    -- The identity-target refinement comparison is fully faithful because its faithful and full
    -- halves were established in the imported local descent files.
    pullbackFamilyDescentFunctor_fullyFaithful_of_refinement_local
      hc 𝒰 𝒱 φ
  -- With that bridge named, the source-proof route is just the imported comparison theorem.
  exact familyDescentFunctor_isEquivalence_of_refinement_of_pullbackFullyFaithful
    hc 𝒰 𝒱 φ hPullback

end CategoryTheory
