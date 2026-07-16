import stacks_proof.stacks_project.Chap08.Lemma_8_12_1

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: the canonical source pullback cone is commutative. -/
theorem sourceChosenPullback_condition
    {U X Y : C} (f : X ⟶ U) (g : Y ⟶ U) [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  -- The source overlap uses the ambient category's canonical pullback square.
  exact pullback.condition

/-- Helper for Chap08 Lemma 8 12 2: the first source pullback projection has the declared
map to the base. -/
theorem sourceChosenPullback_hp₁
    {U X Y : C} (f : X ⟶ U) (g : Y ⟶ U) [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.fst f g ≫ f := by
  -- This records the displayed base map used in the chosen-pullback package.
  rfl

/-- Helper for Chap08 Lemma 8 12 2: the canonical source pullback packaged as a chosen
pullback. -/
noncomputable def sourceChosenPullback
    {U X Y : C} (f : X ⟶ U) (g : Y ⟶ U) [HasPullback f g] :
    ChosenPullback f g where
  pullback := pullback f g
  p₁ := pullback.fst f g
  p₂ := pullback.snd f g
  condition := sourceChosenPullback_condition f g
  isLimit := pullbackIsPullback f g
  p := pullback.fst f g ≫ f
  hp₁ := sourceChosenPullback_hp₁ f g

/-- Helper for Chap08 Lemma 8 12 2: a pullback of the two middle projections gives a wide
threefold overlap. -/
theorem chosenPullbackTriple_liftStruct_nonempty
    {U X₁ X₂ X₃ : C} {f₁ : X₁ ⟶ U} {f₂ : X₂ ⟶ U} {f₃ : X₃ ⟶ U}
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) (h : ChosenPullback h₁₂.p₂ h₂₃.p₁) :
    Nonempty (h₁₃.LiftStruct (h.p₁ ≫ h₁₂.p₁) (h.p₂ ≫ h₂₃.p₂)
      (h.p₁ ≫ h₁₂.p)) := by
  -- The middle pullback identifies the two projections to `X₂`; composing with the two outer
  -- pairwise pullback squares gives the common map to the base.
  apply ChosenPullback.LiftStruct.nonempty
  · calc
      (h.p₁ ≫ h₁₂.p₁) ≫ f₁ = h.p₁ ≫ h₁₂.p := by
        rw [Category.assoc, h₁₂.hp₁]
      _ = h.p₁ ≫ (h₁₂.p₂ ≫ f₂) := by
        rw [h₁₂.hp₂]
      _ = (h.p₁ ≫ h₁₂.p₂) ≫ f₂ := by
        simp only [Category.assoc]
      _ = (h.p₂ ≫ h₂₃.p₁) ≫ f₂ := by
        rw [h.condition]
      _ = h.p₂ ≫ (h₂₃.p₁ ≫ f₂) := by
        simp only [Category.assoc]
      _ = h.p₂ ≫ h₂₃.p := by
        rw [h₂₃.hp₁]
      _ = (h.p₂ ≫ h₂₃.p₂) ≫ f₃ := by
        rw [Category.assoc, h₂₃.hp₂]
  · calc
      (h.p₁ ≫ h₁₂.p₁) ≫ f₁ = h.p₁ ≫ (h₁₂.p₁ ≫ f₁) := by
        simp only [Category.assoc]
      _ = h.p₁ ≫ h₁₂.p := by
        rw [h₁₂.hp₁]

/-- Helper for Chap08 Lemma 8 12 2: build a chosen threefold overlap from pairwise overlaps
and a chosen pullback of the middle projections. -/
noncomputable def chosenPullbackTripleOfMiddle
    {U X₁ X₂ X₃ : C} {f₁ : X₁ ⟶ U} {f₂ : X₂ ⟶ U} {f₃ : X₃ ⟶ U}
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) (h : ChosenPullback h₁₂.p₂ h₂₃.p₁) :
    ChosenPullback₃ h₁₂ h₂₃ h₁₃ where
  chosenPullback := h
  l := Classical.choice (chosenPullbackTriple_liftStruct_nonempty h₁₂ h₂₃ h₁₃ h)

/-- Helper for Chap08 Lemma 8 12 2: the canonical source threefold overlap obtained by
pulling back the two middle projections. -/
noncomputable def sourceChosenPullback₃
    {U X₁ X₂ X₃ : C} (f₁ : X₁ ⟶ U) (f₂ : X₂ ⟶ U) (f₃ : X₃ ⟶ U)
    [HasPullback f₁ f₂] [HasPullback f₂ f₃] [HasPullback f₁ f₃]
    [HasPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)] :
    ChosenPullback₃ (sourceChosenPullback f₁ f₂) (sourceChosenPullback f₂ f₃)
      (sourceChosenPullback f₁ f₃) :=
  chosenPullbackTripleOfMiddle
    (sourceChosenPullback f₁ f₂) (sourceChosenPullback f₂ f₃)
    (sourceChosenPullback f₁ f₃)
    (sourceChosenPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃))

/-- Helper for Chap08 Lemma 8 12 2: the image of a source pullback cone is a commutative
target cone. -/
theorem imageChosenPullback_condition
    [PreservesLimitsOfShape WalkingCospan u]
    {U X Y : C} (f : X ⟶ U) (g : Y ⟶ U) [HasPullback f g] :
    u.map (pullback.fst f g) ≫ u.map f =
      u.map (pullback.snd f g) ≫ u.map g := by
  -- Map the source pullback square and rewrite functoriality on both composite legs.
  rw [← u.map_comp, ← u.map_comp, pullback.condition]

/-- Helper for Chap08 Lemma 8 12 2: the mapped first projection has the declared common
image map. -/
theorem imageChosenPullback_hp₁
    [PreservesLimitsOfShape WalkingCospan u]
    {U X Y : C} (f : X ⟶ U) (g : Y ⟶ U) [HasPullback f g] :
    u.map (pullback.fst f g) ≫ u.map f = u.map (pullback.fst f g ≫ f) := by
  -- The chosen projection to the base is named as the image of the source first composite.
  rw [u.map_comp]

/-- Helper for Chap08 Lemma 8 12 2: a pullback-preserving functor sends the chosen source
pullback cone to a limiting target cone. -/
noncomputable def imageChosenPullback_isLimit
    [PreservesLimitsOfShape WalkingCospan u]
    {U X Y : C} (f : X ⟶ U) (g : Y ⟶ U) [HasPullback f g] :
    IsLimit (PullbackCone.mk (u.map (pullback.fst f g)) (u.map (pullback.snd f g))
      (imageChosenPullback_condition u f g)) :=
  isLimitOfHasPullbackOfPreservesLimit u f g

/-- Helper for Chap08 Lemma 8 12 2: the image under a pullback-preserving functor of the
canonical source pullback, packaged as a chosen target pullback. -/
noncomputable def imageChosenPullback
    [PreservesLimitsOfShape WalkingCospan u]
    {U X Y : C} (f : X ⟶ U) (g : Y ⟶ U) [HasPullback f g] :
    ChosenPullback (u.map f) (u.map g) where
  pullback := u.obj (pullback f g)
  p₁ := u.map (pullback.fst f g)
  p₂ := u.map (pullback.snd f g)
  condition := imageChosenPullback_condition u f g
  isLimit := imageChosenPullback_isLimit u f g
  p := u.map (pullback.fst f g ≫ f)
  hp₁ := imageChosenPullback_hp₁ u f g

/-- Helper for Chap08 Lemma 8 12 2: the image of the canonical source threefold overlap,
packaged as a chosen target threefold overlap. -/
theorem imageChosenPullbackTriple_liftStruct_nonempty
    [PreservesLimitsOfShape WalkingCospan u]
    {U X₁ X₂ X₃ : C} (f₁ : X₁ ⟶ U) (f₂ : X₂ ⟶ U) (f₃ : X₃ ⟶ U)
    [HasPullback f₁ f₂] [HasPullback f₂ f₃] [HasPullback f₁ f₃]
    [HasPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)] :
    Nonempty ((imageChosenPullback u f₁ f₃).LiftStruct
      (u.map (sourceChosenPullback₃ f₁ f₂ f₃).p₁)
      (u.map (sourceChosenPullback₃ f₁ f₂ f₃).p₃)
      (u.map (sourceChosenPullback₃ f₁ f₂ f₃).p)) := by
  -- The source wide-pullback equations map to the target wide-pullback equations.
  let srcTri := sourceChosenPullback₃ f₁ f₂ f₃
  apply ChosenPullback.LiftStruct.nonempty
  · rw [← u.map_comp, ← u.map_comp, srcTri.w₁, srcTri.w₃]
  · rw [← u.map_comp, srcTri.w₁]

/-- Helper for Chap08 Lemma 8 12 2: the mapped first wide projection agrees with the first
projection of the mapped middle pullback square. -/
theorem imageChosenPullbackTriple_hp₁
    [PreservesLimitsOfShape WalkingCospan u]
    {U X₁ X₂ X₃ : C} (f₁ : X₁ ⟶ U) (f₂ : X₂ ⟶ U) (f₃ : X₃ ⟶ U)
    [HasPullback f₁ f₂] [HasPullback f₂ f₃] [HasPullback f₁ f₃]
    [HasPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)] :
    (imageChosenPullback u (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)).p₁ ≫
        (imageChosenPullback u f₁ f₂).p₁ =
      u.map (sourceChosenPullback₃ f₁ f₂ f₃).p₁ := by
  -- This is the image of the corresponding source wide-pullback projection identity.
  let srcTri := sourceChosenPullback₃ f₁ f₂ f₃
  simpa [srcTri, sourceChosenPullback₃, chosenPullbackTripleOfMiddle,
    sourceChosenPullback, imageChosenPullback, Functor.map_comp] using
    congrArg (fun m ↦ u.map m) srcTri.hp₁

/-- Helper for Chap08 Lemma 8 12 2: the mapped third wide projection agrees with the second
projection of the mapped middle pullback square. -/
theorem imageChosenPullbackTriple_hp₃
    [PreservesLimitsOfShape WalkingCospan u]
    {U X₁ X₂ X₃ : C} (f₁ : X₁ ⟶ U) (f₂ : X₂ ⟶ U) (f₃ : X₃ ⟶ U)
    [HasPullback f₁ f₂] [HasPullback f₂ f₃] [HasPullback f₁ f₃]
    [HasPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)] :
    (imageChosenPullback u (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)).p₂ ≫
        (imageChosenPullback u f₂ f₃).p₂ =
      u.map (sourceChosenPullback₃ f₁ f₂ f₃).p₃ := by
  -- This is the image of the corresponding source wide-pullback projection identity.
  let srcTri := sourceChosenPullback₃ f₁ f₂ f₃
  simpa [srcTri, sourceChosenPullback₃, chosenPullbackTripleOfMiddle,
    sourceChosenPullback, imageChosenPullback, Functor.map_comp] using
    congrArg (fun m ↦ u.map m) srcTri.hp₃

/-- Helper for Chap08 Lemma 8 12 2: the image of the canonical source threefold overlap,
packaged as a chosen target threefold overlap. -/
noncomputable def imageChosenPullback₃
    [PreservesLimitsOfShape WalkingCospan u]
    {U X₁ X₂ X₃ : C} (f₁ : X₁ ⟶ U) (f₂ : X₂ ⟶ U) (f₃ : X₃ ⟶ U)
    [HasPullback f₁ f₂] [HasPullback f₂ f₃] [HasPullback f₁ f₃]
    [HasPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)] :
    ChosenPullback₃ (imageChosenPullback u f₁ f₂) (imageChosenPullback u f₂ f₃)
      (imageChosenPullback u f₁ f₃) :=
  { chosenPullback := imageChosenPullback u (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)
    p := u.map (sourceChosenPullback₃ f₁ f₂ f₃).p
    p₁ := u.map (sourceChosenPullback₃ f₁ f₂ f₃).p₁
    p₃ := u.map (sourceChosenPullback₃ f₁ f₂ f₃).p₃
    l := Classical.choice (imageChosenPullbackTriple_liftStruct_nonempty u f₁ f₂ f₃)
    hp₁ := imageChosenPullbackTriple_hp₁ u f₁ f₂ f₃
    hp₃ := imageChosenPullbackTriple_hp₃ u f₁ f₂ f₃ }

/-- Helper for Chap08 Lemma 8 12 2: pairwise source overlaps for the arrows of a fixed
cover. -/
noncomputable def coverSourceChosenPullback
    [HasPullbacks C] {U : C} (T : J.Cover U) (I J : T.Arrow) :
    ChosenPullback I.f J.f :=
  sourceChosenPullback I.f J.f

/-- Helper for Chap08 Lemma 8 12 2: threefold source overlaps for the arrows of a fixed
cover. -/
noncomputable def coverSourceChosenPullback₃
    [HasPullbacks C] {U : C} (T : J.Cover U) (I J L : T.Arrow) :
    ChosenPullback₃ (coverSourceChosenPullback T I J) (coverSourceChosenPullback T J L)
      (coverSourceChosenPullback T I L) :=
  sourceChosenPullback₃ I.f J.f L.f

/-- Helper for Chap08 Lemma 8 12 2: pairwise image overlaps for the arrows of a fixed
cover. -/
noncomputable def coverImageChosenPullback
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    {U : C} (T : J.Cover U) (I J : T.Arrow) :
    ChosenPullback (u.map I.f) (u.map J.f) :=
  imageChosenPullback u I.f J.f

/-- Helper for Chap08 Lemma 8 12 2: threefold image overlaps for the arrows of a fixed
cover. -/
noncomputable def coverImageChosenPullback₃
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    {U : C} (T : J.Cover U) (I J L : T.Arrow) :
    ChosenPullback₃ (coverImageChosenPullback u T I J) (coverImageChosenPullback u T J L)
      (coverImageChosenPullback u T I L) :=
  imageChosenPullback₃ u I.f J.f L.f

end

end CategoryTheory
