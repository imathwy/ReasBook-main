import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap08.Definition_8_3_5
import stacks_project.Chap08.Lemma_8_3_3

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

namespace SemiRepresentableFamily.Over

/-- For a family `𝒱` over `U` and a member `Uᵢ ⟶ U` of `𝒰`, the restricted family `𝒱ᵢ` is the
base change of `𝒱` along `Uᵢ ⟶ U`. -/
abbrev memberBaseChange {U : C} (𝒱 𝒰 : SemiRepresentableFamily.Over U)
    [h : ∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (i : 𝒰.index) : SemiRepresentableFamily.Over ((𝒰.obj i).left) :=
  ofArrows
    (fun j : 𝒱.index ↦ pullback (𝒱.obj j).hom (𝒰.obj i).hom)
    (fun j ↦ pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)

/-- Helper for Lemma 8.3.7: each member of the restricted family `𝒱ᵢ` lies over the base-changed
target map `Uᵢ ⟶ U`. -/
@[reassoc]
theorem memberBaseChange_obj_hom
    {U : C} (𝒱 𝒰 : SemiRepresentableFamily.Over U)
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (i : 𝒰.index) (j : (𝒱.memberBaseChange 𝒰 i).index) :
    ((𝒱.memberBaseChange 𝒰 i).obj j).hom ≫ (𝒰.obj i).hom =
      pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒱.obj j).hom := by
  -- Unfold the restricted family: its structure map is the second pullback projection.
  simpa [SemiRepresentableFamily.Over.memberBaseChange] using
    (pullback.condition :
      pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒱.obj j).hom =
        pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom).symm

/-- For a family `𝒱` over `U` and a pairwise overlap `Uᵢ ×[U] Uᵢ'` of `𝒰`, the restricted family
`𝒱ᵢᵢ'` is the base change of `𝒱` along `Uᵢ ×[U] Uᵢ' ⟶ U`. -/
abbrev overlapBaseChange {U : C} (𝒱 𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [h : ∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) : SemiRepresentableFamily.Over (𝒰.overlap i i') :=
  ofArrows
    (fun j : 𝒱.index ↦ pullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
    (fun j ↦ pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))

/-- Helper for Lemma 8.3.7: each member of the overlap-restricted family `𝒱ᵢᵢ'` lies over the
chosen overlap map `Uᵢ ×[U] Uᵢ' ⟶ U`. -/
@[reassoc]
theorem overlapBaseChange_obj_hom
    {U : C} (𝒱 𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) =
      pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom := by
  -- The overlap-restricted family is also defined by the universal pullback square.
  simpa [SemiRepresentableFamily.Over.overlapBaseChange] using
    (pullback.condition :
      pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
          (𝒱.obj j).hom =
        pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
          (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)).symm

end SemiRepresentableFamily.Over

/-- Helper for Lemma 8.3.7: the components of a same-target refinement also lie over the identity
base-change of the source family. -/
theorem identity_refinement_component_w
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U} (φ : 𝒱 ⟶ 𝒰)
    (j : ((SemiRepresentableFamily.map (Over.map (𝟙 U))).obj 𝒱).index) :
    (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom =
      (((SemiRepresentableFamily.map (Over.map (𝟙 U))).obj 𝒱).obj j).hom := by
  -- The identity base map only changes the target by postcomposition with `𝟙 U`.
  simpa using Over.w (φ.f j)

/-- Helper for Lemma 8.3.7: under the identity base map, a same-target refinement already has the
source type expected by `pullbackFamilyDescentFunctor`. -/
noncomputable def identity_refinement_adapter
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U} (φ : 𝒱 ⟶ 𝒰) :
    ((SemiRepresentableFamily.map (Over.map (𝟙 U))).obj 𝒱 ⟶ 𝒰) where
  α := φ.α
  f := fun j ↦ Over.homMk (φ.f j).left (identity_refinement_component_w φ j)

/-- Helper for Lemma 8.3.7: the canonical map from `U_i ×[U] V_j` back to `V_j` lies over
`(𝒰.obj i).hom`. -/
theorem member_base_change_refinement_component_w
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (i : 𝒰.index) (j : (𝒱.memberBaseChange 𝒰 i).index) :
    pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒱.obj j).hom =
      ((𝒱.memberBaseChange 𝒰 i).obj j).hom ≫ (𝒰.obj i).hom := by
  -- The first pullback projection gives the comparison map back to `V_j`.
  simpa [SemiRepresentableFamily.Over.memberBaseChange] using
    (pullback.condition :
      pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒱.obj j).hom =
        pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)

/-- Helper for Lemma 8.3.7: the canonical refinement of `𝒱_i` back to `𝒱` is given componentwise
by the first pullback projections. -/
noncomputable def member_base_change_refinement_adapter
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (i : 𝒰.index) :
    ((SemiRepresentableFamily.map (Over.map (𝒰.obj i).hom)).obj
      (𝒱.memberBaseChange 𝒰 i)) ⟶ 𝒱 where
  α := fun j ↦ j
  f := fun j ↦ Over.homMk
    (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
    (member_base_change_refinement_component_w 𝒰 𝒱 i j)

/-- Helper for Lemma 8.3.7: on `U_i ×[U] V_j`, the route through the refinement component and the
route through `U_i` define the same map to `U`. -/
theorem member_base_change_comparison_component_map
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom =
      pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom := by
  -- Rewrite along the refinement square, then use the defining pullback condition.
  have hφ :
      pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom =
        pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒱.obj j).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ k)
        (Over.w (φ.f j))
  exact hφ.trans pullback.condition

/-- Helper for Lemma 8.3.7: over `U_i ×[U] V_j`, the restricted pullback of `P.obj D` is
canonically identified with the pullback of `D.obj i` along the second projection. -/
noncomputable def member_base_change_comparison_component_iso
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    hc.obj (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
        ((pullbackFamilyDescentDatum hc (𝟙 U) (identity_refinement_adapter φ) D).obj j) ≅
      hc.obj (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj i) :=
  -- Route correction: the faithful half compares `P.obj D` to `D.obj i` by first collapsing the
  -- iterated pullback and then using the descent datum iso for the two maps to `U`.
  (hc.pullbackCompComponentIso (φ.f j).left
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).symm ≪≫
    (D.descentData.iso
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
      rfl
      (by simpa [Category.assoc] using member_base_change_comparison_component_map φ i j)).symm

/-- Helper for Lemma 8.3.7: the `hom` of the component comparison is the inverse pullback
composition comparison followed by the inverse descent comparison. -/
@[simp]
theorem member_base_change_comparison_component_iso_hom
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    (member_base_change_comparison_component_iso hc D φ i j).hom =
      (hc.pullbackCompComponentIso (φ.f j).left
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv ≫
      (D.descentData.iso
        (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
        (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
        rfl
        (by simpa [Category.assoc] using member_base_change_comparison_component_map φ i j)).inv := by
  -- This is definitional from the chosen composite isomorphism above.
  rfl

/-- Helper for Lemma 8.3.7: after forgetting to the ambient category, a mapped pullback morphism
factors through the chosen cartesian arrow over the target object. -/
theorem fiberInclusion_map_pullbackFunctor_map_fac
    {U V : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y =
      hc.map f x ≫ φ.1 := by
  -- Unfold the chosen pullback map as the universal arrow induced by strong cartesianness.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : p.IsHomLift f (hc.map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f (hc.map f x) U φ.1
  change Functor.IsStronglyCartesian.map p f (hc.map f y) (Category.id_comp f).symm
      (hc.map f x ≫ φ.1) ≫ hc.map f y = hc.map f x ≫ φ.1
  -- The defining factorization of the chosen lift is exactly the desired ambient equality.
  simpa using
    (IsStronglyCartesian.fac p f (hc.map f y) (Category.id_comp f).symm
      (hc.map f x ≫ φ.1))

/-- Helper for Lemma 8.3.7: the factorization of a mapped pullback morphism is stable after a
fixed ambient postcomposition. -/
theorem fiberInclusion_map_pullbackFunctor_map_fac_assoc
    {U V : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) {Z : S}
    (m : y.1 ⟶ Z) :
    Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y ≫ m =
      hc.map f x ≫ φ.1 ≫ m := by
  -- Postcompose the basic factorization equality by the fixed ambient morphism `m`.
  have hpost :
      (Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y) ≫ m =
        (hc.map f x ≫ φ.1) ≫ m := by
    exact congrArg (fun k ↦ k ≫ m)
      (fiberInclusion_map_pullbackFunctor_map_fac (hc := hc) f φ)
  calc
    Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y ≫ m
      = (hc.map f x ≫ φ.1) ≫ m := by
          simpa [Category.assoc] using hpost
    _ = hc.map f x ≫ φ.1 ≫ m := by
          simp [Category.assoc]

end CategoryTheory
