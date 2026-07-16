import stacks_proof.stacks_project.Chap08.Lemma_8_3_7.ComparisonCocycle
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7.Faithful

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

private theorem member_base_change_comparison_coherence
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
        ((member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
    ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂ =
    (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
      (member_base_change_refinement_adapter 𝒰 𝒱 i)
      ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom j₁ j₂ ≫
      (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
        ((member_base_change_comparison_component_iso hc D φ i j₂).hom) := by
  -- The descent-datum coherence is now reduced to equality in the ambient category.
  apply Functor.Fiber.hom_ext
  -- The owner-side cocycle helper packages the exact normalized calculation needed here.
  simpa using member_base_change_comparison_owner_cocycle
    (hc := hc) D φ i j₁ j₂

/-- Helper for Lemma 8.3.7: the componentwise comparison on `U_i ×[U] V_j` packages into an
isomorphism of descent data over the restricted family `𝒱_i`. -/
private noncomputable def member_base_change_comparison_iso
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) :
    pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
      (member_base_change_refinement_adapter 𝒰 𝒱 i)
      ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D) ≅
        (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i) := by
  -- Route correction: the fullness argument needs a descent-datum level comparison, not just
  -- the componentwise iso. We therefore package the existing component comparison via `isoMk`.
  refine Pseudofunctor.DescentData'.isoMk
    (fun j ↦ member_base_change_comparison_component_iso hc D φ i j) ?_
  intro j₁ j₂
  -- The only nontrivial step is the coherence square isolated above.
  simpa using member_base_change_comparison_coherence
    (hc := hc) D φ i j₁ j₂

/-- Helper for Lemma 8.3.7: the `j`-component of the datum-level comparison is the original
componentwise comparison isomorphism. -/
@[simp]
private theorem member_base_change_comparison_iso_hom
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    (member_base_change_comparison_iso hc D φ i).hom.hom j =
      (member_base_change_comparison_component_iso hc D φ i j).hom := by
  -- The packaged isomorphism was defined componentwise from the comparison isos.
  rfl

/-- Helper for Lemma 8.3.7: the inverse `j`-component of the datum-level comparison is the inverse
of the original componentwise comparison isomorphism. -/
@[simp]
private theorem member_base_change_comparison_iso_inv
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    (member_base_change_comparison_iso hc D φ i).inv.hom j =
      (member_base_change_comparison_component_iso hc D φ i j).inv := by
  -- The inverse morphism is likewise assembled componentwise by `isoMk`.
  rfl

/-- Helper for Lemma 8.3.7: a morphism between the refined descent data on `𝒱` transports to a
local morphism in `DD(𝒱_i)` by restricting along the canonical refinement of `𝒱_i` and conjugating
with the comparison isomorphisms. -/
private noncomputable abbrev member_base_change_transported_hom
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i : 𝒰.index) :
    ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D₁.obj i)) ⟶
      ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D₂.obj i)) :=
  (member_base_change_comparison_iso hc D₁ φ i).inv ≫
    ((pullbackFamilyDescentFunctor (p := p) (hc := hc)
      (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
      (member_base_change_refinement_adapter 𝒰 𝒱 i)).map θ) ≫
    (member_base_change_comparison_iso hc D₂ φ i).hom


/-- Helper for Lemma 8.3.7: the local morphism extracted from fullness on `DD(𝒱_i)` is the fully
faithful preimage of the transported morphism. -/
private noncomputable abbrev local_member_base_change_preimage
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i : 𝒰.index) :
    D₁.obj i ⟶ D₂.obj i :=
  let hff := Functor.FullyFaithful.ofFullyFaithful
    (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))
  hff.preimage (member_base_change_transported_hom
    hc 𝒰 𝒱 φ θ i)

/-- Helper for Lemma 8.3.7: mapping the chosen local preimage recovers the transported morphism in
`DD(𝒱_i)`. This is the exact local specification used later both for the component formula and for
the overlap comparison. -/
private theorem local_member_base_change_preimage_spec
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i : 𝒰.index) :
    (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).map
        (local_member_base_change_preimage
          hc 𝒰 𝒱 φ θ i) =
      member_base_change_transported_hom
        hc 𝒰 𝒱 φ θ i := by
  -- Unfold the chosen local preimage so the statement reduces to the standard `map_preimage`
  -- identity for the fully faithful local descent functor on `𝒱_i`.
  let hff := Functor.FullyFaithful.ofFullyFaithful
    (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))
  simpa [local_member_base_change_preimage, member_base_change_transported_hom, hff] using
    hff.map_preimage
      (member_base_change_transported_hom
        hc 𝒰 𝒱 φ θ i)

/-- Helper for Lemma 8.3.7: the overlap object
`U_i ×[U] U_i' ×[U] V_j` satisfies the pullback equation needed to map to `U_i ×[U] V_j`. -/
private theorem overlap_base_change_left_lift_condition
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom =
      (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ 𝒰.pr0 i i') ≫
        (𝒰.obj i).hom := by
  -- The overlap object maps to `U_i` through `pr₀`, so the pullback equation collapses to the
  -- defining square of `U_i ×[U] U_i' ×[U] V_j`.
  calc
    pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom
        =
          pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
            (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) := by
              simpa using
                (pullback.condition :
                  pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom =
                    pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
                      (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
    _ =
          (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ 𝒰.pr0 i i') ≫
            (𝒰.obj i).hom := by
              simp [Category.assoc]

/-- Helper for Lemma 8.3.7: the overlap object maps canonically to the local pullback
`U_i ×[U] V_j`. -/
private noncomputable def overlap_base_change_left_component_map
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    ((𝒱.overlapBaseChange 𝒰 i i').obj j).left ⟶ ((𝒱.memberBaseChange 𝒰 i).obj j).left :=
  pullback.lift
    (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
    (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ 𝒰.pr0 i i')
    (overlap_base_change_left_lift_condition 𝒰 𝒱 i i' j)

/-- Helper for Lemma 8.3.7: the left overlap adapter keeps the `V_j`-projection of the overlap
pullback unchanged. This gives the transport-stable `fst` normalization needed before comparing
overlap branches in the ambient category. -/
private theorem overlap_base_change_left_component_map_fst
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    overlap_base_change_left_component_map 𝒰 𝒱 i i' j ≫
        pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom =
      pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) := by
  -- The universal morphism into `U_i ×[U] V_j` was defined with this first projection.
  simpa [overlap_base_change_left_component_map] using
    (pullback.lift_fst (f := (𝒱.obj j).hom) (g := (𝒰.obj i).hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
      (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
        𝒰.pr0 i i')
      (overlap_base_change_left_lift_condition 𝒰 𝒱 i i' j))

/-- Helper for Lemma 8.3.7: the canonical map from the overlap restriction `𝒱_{ii'}` to the local
restriction `𝒱_i` lies over the first overlap projection `U_i ×[U] U_i' ⟶ U_i`. -/
private theorem overlap_base_change_left_adapter_component_w
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    overlap_base_change_left_component_map 𝒰 𝒱 i i' j ≫
        ((𝒱.memberBaseChange 𝒰 i).obj j).hom =
      ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i' := by
  -- The left adapter is defined by the universal morphism into `U_i ×[U] V_j`.
  simpa [overlap_base_change_left_component_map, SemiRepresentableFamily.Over.memberBaseChange,
    SemiRepresentableFamily.Over.overlapBaseChange] using
    (pullback.lift_snd (f := (𝒱.obj j).hom) (g := (𝒰.obj i).hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
      (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
        𝒰.pr0 i i')
      (overlap_base_change_left_lift_condition 𝒰 𝒱 i i' j))

/-- Helper for Lemma 8.3.7: the canonical overlap restriction to `𝒱_i` is induced by the
universal morphisms into the pullbacks `U_i ×[U] V_j`. -/
private noncomputable def overlap_base_change_left_adapter
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) :
    ((SemiRepresentableFamily.map (Over.map (𝒰.pr0 i i'))).obj
      (𝒱.overlapBaseChange 𝒰 i i')) ⟶ (𝒱.memberBaseChange 𝒰 i) where
  α := fun j ↦ j
  f := fun j ↦ Over.homMk
    (overlap_base_change_left_component_map 𝒰 𝒱 i i' j)
    (overlap_base_change_left_adapter_component_w 𝒰 𝒱 i i' j)

/-- Helper for Lemma 8.3.7: the canonical map from the overlap restriction `𝒱_{ii'}` to the local
restriction `𝒱_{i'}` lies over the second overlap projection `U_i ×[U] U_i' ⟶ U_i'`. -/
private theorem overlap_base_change_right_lift_condition
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom =
      (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ 𝒰.pr1 i i') ≫
        (𝒰.obj i').hom := by
  -- The second overlap projection gives the parallel map to `U_{i'}`.
  have hcond :
      pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom =
        pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
          (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) := by
    simpa using
      (pullback.condition :
        pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom =
          pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
            (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
  have hbase :
      pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
          (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) =
        pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
          (𝒰.pr1 i i' ≫ (𝒰.obj i').hom) := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦
          pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ f)
        (𝒰.pr0_map_eq_pr1_map i i')
  simpa [Category.assoc] using hcond.trans hbase

/-- Helper for Lemma 8.3.7: the overlap object maps canonically to the local pullback
`U_{i'} ×[U] V_j`. -/
private noncomputable def overlap_base_change_right_component_map
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    ((𝒱.overlapBaseChange 𝒰 i i').obj j).left ⟶ ((𝒱.memberBaseChange 𝒰 i').obj j).left :=
  pullback.lift
    (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
    (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ 𝒰.pr1 i i')
    (overlap_base_change_right_lift_condition 𝒰 𝒱 i i' j)

/-- Helper for Lemma 8.3.7: the right overlap adapter also keeps the `V_j`-projection of the
overlap pullback unchanged. This is the fixed postcomposition target used by the overlap
cancellation route. -/
private theorem overlap_base_change_right_component_map_fst
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    overlap_base_change_right_component_map 𝒰 𝒱 i i' j ≫
        pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom =
      pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) := by
  -- The right universal morphism into `U_i' ×[U] V_j` is defined with the same first projection.
  simpa [overlap_base_change_right_component_map] using
    (pullback.lift_fst (f := (𝒱.obj j).hom) (g := (𝒰.obj i').hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
      (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
        𝒰.pr1 i i')
      (overlap_base_change_right_lift_condition 𝒰 𝒱 i i' j))

/-- Helper for Lemma 8.3.7: the canonical map from the overlap restriction `𝒱_{ii'}` to the local
restriction `𝒱_{i'}` lies over the second overlap projection `U_i ×[U] U_i' ⟶ U_i'`. -/
private theorem overlap_base_change_right_adapter_component_w
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) :
    overlap_base_change_right_component_map 𝒰 𝒱 i i' j ≫
        ((𝒱.memberBaseChange 𝒰 i').obj j).hom =
      ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i' := by
  -- The right adapter is the analogous universal morphism into `U_i' ×[U] V_j`.
  simpa [overlap_base_change_right_component_map, SemiRepresentableFamily.Over.memberBaseChange,
    SemiRepresentableFamily.Over.overlapBaseChange] using
    (pullback.lift_snd (f := (𝒱.obj j).hom) (g := (𝒰.obj i').hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
      (pullback.snd (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫
        𝒰.pr1 i i')
      (overlap_base_change_right_lift_condition 𝒰 𝒱 i i' j))

/-- Helper for Lemma 8.3.7: the canonical overlap restriction to `𝒱_{i'}` is induced by the
universal morphisms into the pullbacks `U_{i'} ×[U] V_j`. -/
private noncomputable def overlap_base_change_right_adapter
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) :
    ((SemiRepresentableFamily.map (Over.map (𝒰.pr1 i i'))).obj
      (𝒱.overlapBaseChange 𝒰 i i')) ⟶ (𝒱.memberBaseChange 𝒰 i') where
  α := fun j ↦ j
  f := fun j ↦ Over.homMk
    (overlap_base_change_right_component_map 𝒰 𝒱 i i' j)
    (overlap_base_change_right_adapter_component_w 𝒰 𝒱 i i' j)


/-- Helper for Lemma 8.3.7: the left-overlap component has two pullback routes to `U_i`, namely
via the overlap projection and via the canonical component map into `U_i ×[U] V_j`. This is the
explicit route isomorphism between those two chosen pullbacks. -/
private noncomputable def overlap_base_change_left_route_iso
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) (X : p.Fiber ((𝒰.obj i).left)) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).obj
        ((hc.pullbackFunctor (𝒰.pr0 i i')).obj X) ≅
      (hc.pullbackFunctor (overlap_base_change_left_component_map 𝒰 𝒱 i i' j)).obj
        ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i).obj j).hom)).obj X) := by
  let a := ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
  let b := 𝒰.pr0 i i'
  let q := overlap_base_change_left_component_map 𝒰 𝒱 i i' j
  let c := ((𝒱.memberBaseChange 𝒰 i).obj j).hom
  have hbase : q ≫ c = a ≫ b := by
    simpa [q, c, a, b] using overlap_base_change_left_adapter_component_w 𝒰 𝒱 i i' j
  exact
    (hc.pullbackCompComponentIso b a X).symm ≪≫
      (eqToIso (congrArg (fun f => hc.obj f X) hbase.symm)) ≪≫
      (hc.pullbackCompComponentIso c q X)

/-- Helper for Lemma 8.3.7: the right-overlap component has two pullback routes to `U_i'`, namely
via the second overlap projection and via the canonical component map into `U_i' ×[U] V_j`. This
is the explicit route isomorphism between those two chosen pullbacks. -/
private noncomputable def overlap_base_change_right_route_iso
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) (X : p.Fiber ((𝒰.obj i').left)) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).obj
        ((hc.pullbackFunctor (𝒰.pr1 i i')).obj X) ≅
      (hc.pullbackFunctor (overlap_base_change_right_component_map 𝒰 𝒱 i i' j)).obj
        ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i').obj j).hom)).obj X) := by
  let a := ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
  let b := 𝒰.pr1 i i'
  let q := overlap_base_change_right_component_map 𝒰 𝒱 i i' j
  let c := ((𝒱.memberBaseChange 𝒰 i').obj j).hom
  have hbase : q ≫ c = a ≫ b := by
    simpa [q, c, a, b] using overlap_base_change_right_adapter_component_w 𝒰 𝒱 i i' j
  exact
    (hc.pullbackCompComponentIso b a X).symm ≪≫
      (eqToIso (congrArg (fun f => hc.obj f X) hbase.symm)) ≪≫
      (hc.pullbackCompComponentIso c q X)

/-- Helper for Lemma 8.3.7: postcompose an outer left-overlap pullback route through the canonical
route comparison and then through the chosen cartesian arrow over the component map. -/
private noncomputable abbrev overlap_base_change_left_route_postcompose
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) (X : p.Fiber ((𝒰.obj i).left)) :=
  Functor.Fiber.fiberInclusion.map
      (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).hom ≫
    hc.map (overlap_base_change_left_component_map 𝒰 𝒱 i i' j)
      ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i).obj j).hom)).obj X)

/-- Helper for Lemma 8.3.7: postcompose an outer right-overlap pullback route through the canonical
route comparison and then through the chosen cartesian arrow over the component map. -/
private noncomputable abbrev overlap_base_change_right_route_postcompose
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) (X : p.Fiber ((𝒰.obj i').left)) :=
  Functor.Fiber.fiberInclusion.map
      (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).hom ≫
    hc.map (overlap_base_change_right_component_map 𝒰 𝒱 i i' j)
      ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i').obj j).hom)).obj X)


/-- Helper for Lemma 8.3.7: changing a pullback route by an equality of base morphisms is
natural in the pulled-back fiber object. -/
private theorem pullbackFunctor_eqToIso_naturality
    {U V : C} {f g : V ⟶ U} (h : f = g)
    {X Y : p.Fiber U} (η : X ⟶ Y) :
    (hc.pullbackFunctor f).map η ≫
        (eqToIso (congrArg (fun r => hc.obj r Y) h)).hom =
      (eqToIso (congrArg (fun r => hc.obj r X) h)).hom ≫
        (hc.pullbackFunctor g).map η := by
  cases h
  have hY : congrArg (fun r => hc.obj r Y) (rfl : f = f) = rfl := Subsingleton.elim _ _
  have hX : congrArg (fun r => hc.obj r X) (rfl : f = f) = rfl := Subsingleton.elim _ _
  rw [hY, hX]
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  exact Category.comp_id ((hc.pullbackFunctor f).map η)

/-- Helper for Lemma 8.3.7: pulling back along a morphism with a section is faithful. -/
private theorem pullbackFunctor_faithful_of_section
    {U V : C} (f : V ⟶ U) (s : U ⟶ V) (hs : s ≫ f = 𝟙 U) :
    Functor.Faithful (hc.pullbackFunctor f) := by
  let e : hc.pullbackFunctor f ⋙ hc.pullbackFunctor s ≅ 𝟭 (p.Fiber U) :=
    (hc.pullbackCompIso f s).symm ≪≫
      eqToIso (by rw [hs]) ≪≫
      (hc.pullbackIdIso U).symm
  exact Functor.Faithful.of_comp_iso e

/-- Helper for Lemma 8.3.7: the refinement arrow `V_j ⟶ U_{φ(j)}` gives a section of the
first projection from `V_j ×[U] U_{φ(j)}`. -/
private noncomputable def member_base_change_graph
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (φ : 𝒱 ⟶ 𝒰) (j : 𝒱.index) :
    (𝒱.obj j).left ⟶ ((𝒱.memberBaseChange 𝒰 (φ.α j)).obj j).left :=
  pullback.lift (𝟙 _) (φ.f j).left
    (by
      simpa using (Over.w (φ.f j)).symm)

/-- Helper for Lemma 8.3.7: the graph section really splits the first projection. -/
private theorem member_base_change_graph_fst
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (φ : 𝒱 ⟶ 𝒰) (j : 𝒱.index) :
    member_base_change_graph (𝒰 := 𝒰) (𝒱 := 𝒱) φ j ≫
        pullback.fst (𝒱.obj j).hom (𝒰.obj (φ.α j)).hom =
      𝟙 _ := by
  simpa [member_base_change_graph] using
    (pullback.lift_fst (f := (𝒱.obj j).hom) (g := (𝒰.obj (φ.α j)).hom)
      (𝟙 (𝒱.obj j).left) (φ.f j).left
      (by
        simpa using (Over.w (φ.f j)).symm))


/-- Helper for Lemma 8.3.7: the left-overlap route comparison is natural in the fiber object. -/
private theorem overlap_base_change_left_route_iso_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index)
    {X Y : p.Fiber ((𝒰.obj i).left)} (η : X ⟶ Y) :
    ((hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
        ((hc.pullbackFunctor (𝒰.pr0 i i')).map η)) ≫
      (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).hom =
    (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).hom ≫
      (hc.pullbackFunctor (overlap_base_change_left_component_map 𝒰 𝒱 i i' j)).map
        ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i).obj j).hom)).map η) := by
  let a := ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
  let b := 𝒰.pr0 i i'
  let q := overlap_base_change_left_component_map 𝒰 𝒱 i i' j
  let c := ((𝒱.memberBaseChange 𝒰 i).obj j).hom
  have hbase : a ≫ b = q ≫ c := by
    simpa [a, b, q, c] using
      (overlap_base_change_left_adapter_component_w 𝒰 𝒱 i i' j).symm
  have hleft :
      ((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
          (hc.pullbackCompComponentIso b a Y).inv =
        (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η := by
    simpa [a, b, Functor.comp_map] using
      pullbackCompComponentIso_inv_naturality (p := p) (hc := hc) b a η
  have hmiddle :
      (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom =
        (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η := by
    simpa using
      pullbackFunctor_eqToIso_naturality (p := p) (hc := hc) hbase η
  have hright :
      (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        (hc.pullbackCompComponentIso c q X).hom ≫
          (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) := by
    simpa [c, q, Functor.comp_map] using
      (hc.pullbackCompIso c q).hom.naturality η
  have hleft_assoc :
      ((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
          (hc.pullbackCompComponentIso b a Y).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom := by
    calc
      ((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
          (hc.pullbackCompComponentIso b a Y).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom
          = (((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
              (hc.pullbackCompComponentIso b a Y).inv) ≫
              (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
      _ = ((hc.pullbackCompComponentIso b a X).inv ≫
              (hc.pullbackFunctor (a ≫ b)).map η) ≫
              (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q Y).hom := by
              rw [hleft]
              rfl
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              (hc.pullbackFunctor (a ≫ b)).map η ≫
              (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
  have hmiddle_assoc :
      (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        (hc.pullbackCompComponentIso b a X).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom := by
    calc
      (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom
          = (hc.pullbackCompComponentIso b a X).inv ≫
              ((hc.pullbackFunctor (a ≫ b)).map η ≫
                (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom) ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              ((eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
                (hc.pullbackFunctor (q ≫ c)).map η) ≫
              (hc.pullbackCompComponentIso c q Y).hom := by
                exact congrArg
                  (fun k ↦ (hc.pullbackCompComponentIso b a X).inv ≫ k ≫
                    (hc.pullbackCompComponentIso c q Y).hom) hmiddle
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              (hc.pullbackFunctor (q ≫ c)).map η ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
  have hright_assoc :
      (hc.pullbackCompComponentIso b a X).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        ((hc.pullbackCompComponentIso b a X).inv ≫
            (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
            (hc.pullbackCompComponentIso c q X).hom) ≫
          (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) := by
    calc
      (hc.pullbackCompComponentIso b a X).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom
          = (hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              ((hc.pullbackFunctor (q ≫ c)).map η ≫
                (hc.pullbackCompComponentIso c q Y).hom) := by simp only [← Category.assoc]
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              ((hc.pullbackCompComponentIso c q X).hom ≫
                (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η)) := by
                exact congrArg
                  (fun k ↦ (hc.pullbackCompComponentIso b a X).inv ≫
                    (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫ k) hright
      _ = ((hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q X).hom) ≫
              (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) := by simp only [← Category.assoc]
  simpa [overlap_base_change_left_route_iso, a, b, q, c, hbase, Category.assoc,
    Functor.comp_map] using hleft_assoc.trans (hmiddle_assoc.trans hright_assoc)

/-- Helper for Lemma 8.3.7: postcomposition along the left-overlap route comparison is natural
in the local fiber morphism. -/
private theorem overlap_base_change_left_route_postcompose_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index)
    {X Y : p.Fiber ((𝒰.obj i).left)} (η : X ⟶ Y) :
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
          ((hc.pullbackFunctor (𝒰.pr0 i i')).map η)) ≫
      overlap_base_change_left_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j Y =
    overlap_base_change_left_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j X ≫
      Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i).obj j).hom)).map η) := by
  let a := ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
  let b := 𝒰.pr0 i i'
  let q := overlap_base_change_left_component_map 𝒰 𝒱 i i' j
  let c := ((𝒱.memberBaseChange 𝒰 i).obj j).hom
  let routeX := (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).hom
  let routeY := (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).hom
  let ηa := (hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)
  let ηq := (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η)
  let ηc := (hc.pullbackFunctor c).map η
  have hroute : ηa ≫ routeY = routeX ≫ ηq := by
    simpa [a, b, q, c, routeX, routeY, ηa, ηq] using
      overlap_base_change_left_route_iso_naturality
        (p := p) (hc := hc) 𝒰 𝒱 i i' j η
  have hq :
      Functor.Fiber.fiberInclusion.map ηq ≫ hc.map q ((hc.pullbackFunctor c).obj Y) =
        hc.map q ((hc.pullbackFunctor c).obj X) ≫
          Functor.Fiber.fiberInclusion.map ηc := by
    simpa [q, c, ηq, ηc] using
      fiberInclusion_map_pullbackFunctor_map_fac (p := p) (hc := hc) q ηc
  calc
    Functor.Fiber.fiberInclusion.map ηa ≫
        overlap_base_change_left_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j Y
        = Functor.Fiber.fiberInclusion.map (ηa ≫ routeY) ≫
            hc.map q ((hc.pullbackFunctor c).obj Y) := by
            simp [overlap_base_change_left_route_postcompose, a, b, q, c, routeY, ηa,
              Category.assoc]
    _ = Functor.Fiber.fiberInclusion.map (routeX ≫ ηq) ≫
            hc.map q ((hc.pullbackFunctor c).obj Y) := by
            rw [hroute]
    _ = Functor.Fiber.fiberInclusion.map routeX ≫
            Functor.Fiber.fiberInclusion.map ηq ≫
            hc.map q ((hc.pullbackFunctor c).obj Y) := by
            simp [Category.assoc]
    _ = Functor.Fiber.fiberInclusion.map routeX ≫
            hc.map q ((hc.pullbackFunctor c).obj X) ≫
            Functor.Fiber.fiberInclusion.map ηc := by
            simpa [Category.assoc] using congrArg
              (fun k ↦ Functor.Fiber.fiberInclusion.map routeX ≫ k) hq
    _ = overlap_base_change_left_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j X ≫
            Functor.Fiber.fiberInclusion.map ηc := by
            simp [overlap_base_change_left_route_postcompose, q, c, routeX, ηc,
              Category.assoc]

/-- Helper for Lemma 8.3.7: the right-overlap route comparison is natural in the fiber object. -/
private theorem overlap_base_change_right_route_iso_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index)
    {X Y : p.Fiber ((𝒰.obj i').left)} (η : X ⟶ Y) :
    ((hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
        ((hc.pullbackFunctor (𝒰.pr1 i i')).map η)) ≫
      (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).hom =
    (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).hom ≫
      (hc.pullbackFunctor (overlap_base_change_right_component_map 𝒰 𝒱 i i' j)).map
        ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i').obj j).hom)).map η) := by
  let a := ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
  let b := 𝒰.pr1 i i'
  let q := overlap_base_change_right_component_map 𝒰 𝒱 i i' j
  let c := ((𝒱.memberBaseChange 𝒰 i').obj j).hom
  have hbase : a ≫ b = q ≫ c := by
    simpa [a, b, q, c] using
      (overlap_base_change_right_adapter_component_w 𝒰 𝒱 i i' j).symm
  have hleft :
      ((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
          (hc.pullbackCompComponentIso b a Y).inv =
        (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η := by
    simpa [a, b, Functor.comp_map] using
      pullbackCompComponentIso_inv_naturality (p := p) (hc := hc) b a η
  have hmiddle :
      (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom =
        (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η := by
    simpa using
      pullbackFunctor_eqToIso_naturality (p := p) (hc := hc) hbase η
  have hright :
      (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        (hc.pullbackCompComponentIso c q X).hom ≫
          (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) := by
    simpa [c, q, Functor.comp_map] using
      (hc.pullbackCompIso c q).hom.naturality η
  have hleft_assoc :
      ((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
          (hc.pullbackCompComponentIso b a Y).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom := by
    calc
      ((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
          (hc.pullbackCompComponentIso b a Y).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom
          = (((hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)) ≫
              (hc.pullbackCompComponentIso b a Y).inv) ≫
              (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
      _ = ((hc.pullbackCompComponentIso b a X).inv ≫
              (hc.pullbackFunctor (a ≫ b)).map η) ≫
              (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q Y).hom := by
              rw [hleft]
              rfl
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              (hc.pullbackFunctor (a ≫ b)).map η ≫
              (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
  have hmiddle_assoc :
      (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        (hc.pullbackCompComponentIso b a X).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom := by
    calc
      (hc.pullbackCompComponentIso b a X).inv ≫
          (hc.pullbackFunctor (a ≫ b)).map η ≫
          (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom ≫
          (hc.pullbackCompComponentIso c q Y).hom
          = (hc.pullbackCompComponentIso b a X).inv ≫
              ((hc.pullbackFunctor (a ≫ b)).map η ≫
                (eqToIso (congrArg (fun r => hc.obj r Y) hbase)).hom) ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              ((eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
                (hc.pullbackFunctor (q ≫ c)).map η) ≫
              (hc.pullbackCompComponentIso c q Y).hom := by
                exact congrArg
                  (fun k ↦ (hc.pullbackCompComponentIso b a X).inv ≫ k ≫
                    (hc.pullbackCompComponentIso c q Y).hom) hmiddle
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              (hc.pullbackFunctor (q ≫ c)).map η ≫
              (hc.pullbackCompComponentIso c q Y).hom := by simp only [← Category.assoc]
  have hright_assoc :
      (hc.pullbackCompComponentIso b a X).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom =
        ((hc.pullbackCompComponentIso b a X).inv ≫
            (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
            (hc.pullbackCompComponentIso c q X).hom) ≫
          (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) := by
    calc
      (hc.pullbackCompComponentIso b a X).inv ≫
          (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
          (hc.pullbackFunctor (q ≫ c)).map η ≫
          (hc.pullbackCompComponentIso c q Y).hom
          = (hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              ((hc.pullbackFunctor (q ≫ c)).map η ≫
                (hc.pullbackCompComponentIso c q Y).hom) := by simp only [← Category.assoc]
      _ = (hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              ((hc.pullbackCompComponentIso c q X).hom ≫
                (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η)) := by
                exact congrArg
                  (fun k ↦ (hc.pullbackCompComponentIso b a X).inv ≫
                    (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫ k) hright
      _ = ((hc.pullbackCompComponentIso b a X).inv ≫
              (eqToIso (congrArg (fun r => hc.obj r X) hbase)).hom ≫
              (hc.pullbackCompComponentIso c q X).hom) ≫
              (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) := by simp only [← Category.assoc]
  simpa [overlap_base_change_right_route_iso, a, b, q, c, hbase, Category.assoc,
    Functor.comp_map] using hleft_assoc.trans (hmiddle_assoc.trans hright_assoc)


/-- Helper for Lemma 8.3.7: postcomposition along the right-overlap route comparison is natural
in the local fiber morphism. -/
private theorem overlap_base_change_right_route_postcompose_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index)
    {X Y : p.Fiber ((𝒰.obj i').left)} (η : X ⟶ Y) :
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
          ((hc.pullbackFunctor (𝒰.pr1 i i')).map η)) ≫
      overlap_base_change_right_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j Y =
    overlap_base_change_right_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j X ≫
      Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor (((𝒱.memberBaseChange 𝒰 i').obj j).hom)).map η) := by
  let a := ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
  let b := 𝒰.pr1 i i'
  let q := overlap_base_change_right_component_map 𝒰 𝒱 i i' j
  let c := ((𝒱.memberBaseChange 𝒰 i').obj j).hom
  let routeX := (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).hom
  let routeY := (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).hom
  let ηa := (hc.pullbackFunctor a).map ((hc.pullbackFunctor b).map η)
  let ηq := (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η)
  let ηc := (hc.pullbackFunctor c).map η
  have hroute : ηa ≫ routeY = routeX ≫ ηq := by
    simpa [a, b, q, c, routeX, routeY, ηa, ηq] using
      overlap_base_change_right_route_iso_naturality
        (p := p) (hc := hc) 𝒰 𝒱 i i' j η
  have hq :
      Functor.Fiber.fiberInclusion.map ηq ≫ hc.map q ((hc.pullbackFunctor c).obj Y) =
        hc.map q ((hc.pullbackFunctor c).obj X) ≫
          Functor.Fiber.fiberInclusion.map ηc := by
    simpa [q, c, ηq, ηc] using
      fiberInclusion_map_pullbackFunctor_map_fac (p := p) (hc := hc) q ηc
  calc
    Functor.Fiber.fiberInclusion.map ηa ≫
        overlap_base_change_right_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j Y
        = Functor.Fiber.fiberInclusion.map (ηa ≫ routeY) ≫
            hc.map q ((hc.pullbackFunctor c).obj Y) := by
            simp [overlap_base_change_right_route_postcompose, a, b, q, c, routeY, ηa,
              Category.assoc]
    _ = Functor.Fiber.fiberInclusion.map (routeX ≫ ηq) ≫
            hc.map q ((hc.pullbackFunctor c).obj Y) := by
            rw [hroute]
    _ = Functor.Fiber.fiberInclusion.map routeX ≫
            Functor.Fiber.fiberInclusion.map ηq ≫
            hc.map q ((hc.pullbackFunctor c).obj Y) := by
            simp [Category.assoc]
    _ = Functor.Fiber.fiberInclusion.map routeX ≫
            hc.map q ((hc.pullbackFunctor c).obj X) ≫
            Functor.Fiber.fiberInclusion.map ηc := by
            simpa [Category.assoc] using congrArg
              (fun k ↦ Functor.Fiber.fiberInclusion.map routeX ≫ k) hq
    _ = overlap_base_change_right_route_postcompose (p := p) (hc := hc) 𝒰 𝒱 i i' j X ≫
            Functor.Fiber.fiberInclusion.map ηc := by
            simp [overlap_base_change_right_route_postcompose, q, c, routeX, ηc,
              Category.assoc]



/-- Helper for Lemma 8.3.7: the direct pullback from the overlap object to `V_j` agrees with the
route through the left local pullback `V_j ×[U] U_i`. -/
private noncomputable def overlap_base_change_left_common_route_iso
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) (X : p.Fiber ((𝒱.obj j).left)) :
    (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).obj X ≅
      (hc.pullbackFunctor (overlap_base_change_left_component_map 𝒰 𝒱 i i' j)).obj
        ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).obj X) := by
  let v := pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)
  let q := overlap_base_change_left_component_map 𝒰 𝒱 i i' j
  let c := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom
  have hbase : v = q ≫ c := by
    simpa [v, q, c] using (overlap_base_change_left_component_map_fst 𝒰 𝒱 i i' j).symm
  exact
    eqToIso (congrArg (fun r => hc.obj r X) hbase) ≪≫
      (hc.pullbackCompComponentIso c q X)

/-- Helper for Lemma 8.3.7: the direct pullback from the overlap object to `V_j` agrees with the
route through the right local pullback `V_j ×[U] U_i'`. -/
private noncomputable def overlap_base_change_right_common_route_iso
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index) (X : p.Fiber ((𝒱.obj j).left)) :
    (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).obj X ≅
      (hc.pullbackFunctor (overlap_base_change_right_component_map 𝒰 𝒱 i i' j)).obj
        ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom)).obj X) := by
  let v := pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)
  let q := overlap_base_change_right_component_map 𝒰 𝒱 i i' j
  let c := pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom
  have hbase : v = q ≫ c := by
    simpa [v, q, c] using (overlap_base_change_right_component_map_fst 𝒰 𝒱 i i' j).symm
  exact
    eqToIso (congrArg (fun r => hc.obj r X) hbase) ≪≫
      (hc.pullbackCompComponentIso c q X)

/-- Helper for Lemma 8.3.7: the left local restriction of `D` over an overlap maps canonically to the
common direct pullback of the refined `j`-component. -/
private noncomputable def overlap_base_change_left_to_common_iso
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i i' : 𝒰.index)
    (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).obj
        ((hc.pullbackFunctor (𝒰.pr0 i i')).obj (D.obj i)) ≅
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).obj
        (((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D).obj j) :=
  let q := overlap_base_change_left_component_map 𝒰 𝒱 i i' j
  (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j (D.obj i)) ≪≫
    (hc.pullbackFunctor q).mapIso (member_base_change_comparison_component_iso hc D φ i j).symm ≪≫
    (overlap_base_change_left_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j
      (((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D).obj j)).symm

/-- Helper for Lemma 8.3.7: the right local restriction of `D` over an overlap maps canonically to the
same common direct pullback of the refined `j`-component. -/
private noncomputable def overlap_base_change_right_to_common_iso
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i i' : 𝒰.index)
    (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).obj
        ((hc.pullbackFunctor (𝒰.pr1 i i')).obj (D.obj i')) ≅
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).obj
        (((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D).obj j) :=
  let q := overlap_base_change_right_component_map 𝒰 𝒱 i i' j
  (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j (D.obj i')) ≪≫
    (hc.pullbackFunctor q).mapIso (member_base_change_comparison_component_iso hc D φ i' j).symm ≪≫
    (overlap_base_change_right_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j
      (((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D).obj j)).symm

/-- Helper for Lemma 8.3.7: the inverse comparison from a common owner leg to one local leg,
followed by the comparison between two local legs, is the inverse comparison to the second local
leg. This is exactly the `comp_pullHom'` cocycle for a descent datum, repackaged in `iso` notation. -/
private theorem descentData_iso_inv_comp_hom
    {U : C} {𝒰 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    (D : DescentDatum p hc 𝒰)
    {Y : C} (q : Y ⟶ U) {i₀ i₁ i₂ : 𝒰.index}
    (f₀ : Y ⟶ (𝒰.obj i₀).left) (f₁ : Y ⟶ (𝒰.obj i₁).left)
    (f₂ : Y ⟶ (𝒰.obj i₂).left)
    (hf₀ : f₀ ≫ (𝒰.obj i₀).hom = q := by cat_disch)
    (hf₁ : f₁ ≫ (𝒰.obj i₁).hom = q := by cat_disch)
    (hf₂ : f₂ ≫ (𝒰.obj i₂).hom = q := by cat_disch) :
    (D.descentData.iso q f₁ f₀ hf₁ hf₀).inv ≫
        (D.descentData.iso q f₁ f₂ hf₁ hf₂).hom =
      (D.descentData.iso q f₂ f₀ hf₂ hf₀).inv := by
  simpa only [Pseudofunctor.DescentData.iso, Pseudofunctor.DescentData.iso_hom] using
    (Pseudofunctor.DescentData'.comp_pullHom' D q f₀ f₁ f₂ hf₀ hf₁ hf₂)



private theorem fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv_local
    {U V W : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc)
        (by aesop)).inv.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).inv := by
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

private theorem fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom_local
    {U V W : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc)
        (by aesop)).hom.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).hom := by
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

set_option backward.isDefEq.respectTransparency false in
private theorem overlap_base_change_map_descent_hom_comp_inv
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (D : DescentDatum p hc 𝒰) (i i' : 𝒰.index)
    (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map (D.hom i i') ≫
        (hc.pullbackCompComponentIso (𝒰.pr1 i i') ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
          (D.obj i')).inv =
      (hc.pullbackCompComponentIso (𝒰.pr0 i i') ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
        (D.obj i)).inv ≫
      Pseudofunctor.DescentData'.pullHom' D.hom
        ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
        (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i')
        (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i')
        rfl
        (by
          simpa [Category.assoc] using
            (congrArg (fun f ↦ ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ f)
              (𝒰.pr0_map_eq_pr1_map i i')).symm) := by
  let a := ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom
  have hmap :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := hc.fiberPseudofunctor) (φ := D.hom i i')
      a (a ≫ 𝒰.pr0 i i') (a ≫ 𝒰.pr1 i i') rfl rfl
  have hhom :
      D.hom i i' =
        Pseudofunctor.DescentData'.pullHom' D.hom
          ((𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
          (𝒰.pr0 i i') (𝒰.pr1 i i') rfl (by simpa using (𝒰.pr0_map_eq_pr1_map i i').symm) := by
    simpa [SemiRepresentableFamily.Over.pr0, SemiRepresentableFamily.Over.pr1] using
      (Pseudofunctor.DescentData'.pullHom'_eq_hom D i i').symm
  rw [hhom] at hmap
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Pseudofunctor.DescentData'.pullHom' D.hom
            (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)
            (𝒰.pr0 i i') (𝒰.pr1 i i') rfl
            (by simpa using (𝒰.pr0_map_eq_pr1_map i i').symm))
          a (a ≫ 𝒰.pr0 i i') (a ≫ 𝒰.pr1 i i') rfl rfl =
        Pseudofunctor.DescentData'.pullHom' D.hom
          ((a ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
          (a ≫ 𝒰.pr0 i i') (a ≫ 𝒰.pr1 i i') rfl
          (by
            simpa [Category.assoc] using
              (congrArg (fun f ↦ a ≫ f) (𝒰.pr0_map_eq_pr1_map i i')).symm) := by
    simpa [Category.assoc] using
      (Pseudofunctor.DescentData'.pullHom_pullHom' (hom := D.hom)
        (g := a)
        (q := 𝒰.pr0 i i' ≫ (𝒰.obj i).hom)
        (q' := (a ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
        (f₁ := 𝒰.pr0 i i') (f₂ := 𝒰.pr1 i i')
        (gf₁ := a ≫ 𝒰.pr0 i i') (gf₂ := a ≫ 𝒰.pr1 i i')
        (hq := by simp [Category.assoc])
        (hf₁ := rfl)
        (hf₂ := by simpa using (𝒰.pr0_map_eq_pr1_map i i').symm)
        (hgf₁ := rfl) (hgf₂ := rfl))
  rw [hpull] at hmap
  simp only [SemiRepresentableFamily.Over.pr0, SemiRepresentableFamily.Over.pr1] at hmap
  have hpost := congrArg (fun k => k ≫
      (hc.pullbackCompComponentIso (pullback.snd (𝒰.obj i).hom (𝒰.obj i').hom) a (D.obj i')).inv) hmap
  dsimp at hpost
  simp only [
    fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv_local,
    fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom_local] at hpost
  rw [hhom]
  simpa [a, SemiRepresentableFamily.Over.pr0, SemiRepresentableFamily.Over.pr1,
    PullbackChoice.pullbackFunctor, Category.assoc] using hpost
private theorem local_member_base_change_preimage_component_spec
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i : 𝒰.index) (j : 𝒱.index) :
    (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map
        (local_member_base_change_preimage
          hc 𝒰 𝒱 φ θ i) =
      (member_base_change_comparison_component_iso hc D₁ φ i j).inv ≫
        (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom j) ≫
        (member_base_change_comparison_component_iso hc D₂ φ i j).hom := by
  -- Evaluate the local preimage specification at the component `j`.
  have hcomponent :=
    congrArg (fun ψ ↦ ψ.hom j)
      (local_member_base_change_preimage_spec
        hc 𝒰 𝒱 φ θ i)
  simpa [familyDescentFunctor_map_hom, member_base_change_transported_hom,
    pullbackFamilyDescentFunctor_map_hom] using hcomponent

/-- Helper for Lemma 8.3.7: the comparison between the direct overlap pullback and the route
through the left local pullback is natural in the refined fiber object. -/
private theorem overlap_base_change_left_common_route_iso_inv_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index)
    {X Y : p.Fiber ((𝒱.obj j).left)} (η : X ⟶ Y) :
    (hc.pullbackFunctor (overlap_base_change_left_component_map 𝒰 𝒱 i i' j)).map
        ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map η) ≫
      (overlap_base_change_left_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).inv =
    (overlap_base_change_left_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).inv ≫
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map η := by
  let q := overlap_base_change_left_component_map 𝒰 𝒱 i i' j
  let c := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom
  have hbase : pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) = q ≫ c := by
    simpa [q, c] using (overlap_base_change_left_component_map_fst 𝒰 𝒱 i i' j).symm
  have hY :
      (overlap_base_change_left_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).inv =
        (hc.pullbackCompComponentIso c q Y).inv ≫
          eqToHom ((congrArg (fun r ↦ hc.obj r Y) hbase).symm) := rfl
  have hX :
      (overlap_base_change_left_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).inv =
        (hc.pullbackCompComponentIso c q X).inv ≫
          eqToHom ((congrArg (fun r ↦ hc.obj r X) hbase).symm) := rfl
  have hcomp :
      (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) ≫
          (hc.pullbackCompComponentIso c q Y).inv =
        (hc.pullbackCompComponentIso c q X).inv ≫
          (hc.pullbackFunctor (q ≫ c)).map η :=
    pullbackCompComponentIso_inv_naturality (p := p) (hc := hc) c q η
  have heq :
      (hc.pullbackFunctor (q ≫ c)).map η ≫
          eqToHom ((congrArg (fun r ↦ hc.obj r Y) hbase).symm) =
        eqToHom ((congrArg (fun r ↦ hc.obj r X) hbase).symm) ≫
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
            (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map η :=
    pullbackFunctor_eqToIso_naturality (p := p) (hc := hc) hbase.symm η
  rw [hY, hX]
  exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ eqToHom ((congrArg (fun r ↦ hc.obj r Y) hbase).symm))
        hcomp)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (hc.pullbackCompComponentIso c q X).inv ≫ k) heq).trans
        (Category.assoc _ _ _).symm))

/-- Helper for Lemma 8.3.7: the comparison between the direct overlap pullback and the route
through the right local pullback is natural in the refined fiber object. -/
private theorem overlap_base_change_right_common_route_iso_inv_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) (j : 𝒱.index)
    {X Y : p.Fiber ((𝒱.obj j).left)} (η : X ⟶ Y) :
    (hc.pullbackFunctor (overlap_base_change_right_component_map 𝒰 𝒱 i i' j)).map
        ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom)).map η) ≫
      (overlap_base_change_right_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).inv =
    (overlap_base_change_right_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).inv ≫
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map η := by
  let q := overlap_base_change_right_component_map 𝒰 𝒱 i i' j
  let c := pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom
  have hbase : pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) = q ≫ c := by
    simpa [q, c] using (overlap_base_change_right_component_map_fst 𝒰 𝒱 i i' j).symm
  have hY :
      (overlap_base_change_right_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j Y).inv =
        (hc.pullbackCompComponentIso c q Y).inv ≫
          eqToHom ((congrArg (fun r ↦ hc.obj r Y) hbase).symm) := rfl
  have hX :
      (overlap_base_change_right_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j X).inv =
        (hc.pullbackCompComponentIso c q X).inv ≫
          eqToHom ((congrArg (fun r ↦ hc.obj r X) hbase).symm) := rfl
  have hcomp :
      (hc.pullbackFunctor q).map ((hc.pullbackFunctor c).map η) ≫
          (hc.pullbackCompComponentIso c q Y).inv =
        (hc.pullbackCompComponentIso c q X).inv ≫
          (hc.pullbackFunctor (q ≫ c)).map η :=
    pullbackCompComponentIso_inv_naturality (p := p) (hc := hc) c q η
  have heq :
      (hc.pullbackFunctor (q ≫ c)).map η ≫
          eqToHom ((congrArg (fun r ↦ hc.obj r Y) hbase).symm) =
        eqToHom ((congrArg (fun r ↦ hc.obj r X) hbase).symm) ≫
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
            (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map η :=
    pullbackFunctor_eqToIso_naturality (p := p) (hc := hc) hbase.symm η
  rw [hY, hX]
  exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ eqToHom ((congrArg (fun r ↦ hc.obj r Y) hbase).symm))
        hcomp)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (hc.pullbackCompComponentIso c q X).inv ≫ k) heq).trans
        (Category.assoc _ _ _).symm))

/-- Helper for Lemma 8.3.7: the left local restriction of the preimage candidate matches the
direct overlap pullback of `θ` through the left common-route comparison. -/
private theorem overlap_base_change_left_to_common_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i i' : 𝒰.index) (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
        ((hc.pullbackFunctor (𝒰.pr0 i i')).map
          (local_member_base_change_preimage
            hc 𝒰 𝒱 φ θ i)) ≫
      (overlap_base_change_left_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₂ φ i i' j).hom =
    (overlap_base_change_left_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₁ φ i i' j).hom ≫
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map (θ.hom j) := by
  let pre := local_member_base_change_preimage
    hc 𝒰 𝒱 φ θ i
  let q := overlap_base_change_left_component_map 𝒰 𝒱 i i' j
  let M := (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
    ((hc.pullbackFunctor (𝒰.pr0 i i')).map pre)
  let R₁ := (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j (D₁.obj i)).hom
  let R₂ := (overlap_base_change_left_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j (D₂.obj i)).hom
  let K₁ := (hc.pullbackFunctor q).map
    (member_base_change_comparison_component_iso hc D₁ φ i j).inv
  let K₂ := (hc.pullbackFunctor q).map
    (member_base_change_comparison_component_iso hc D₂ φ i j).inv
  let C₁ := (overlap_base_change_left_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j
    (((pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)).obj D₁).obj j)).inv
  let C₂ := (overlap_base_change_left_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j
    (((pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)).obj D₂).obj j)).inv
  let P := (hc.pullbackFunctor q).map
    ((hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map pre)
  let G := (hc.pullbackFunctor q).map
    ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom j))
  let W := (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
    (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map (θ.hom j)
  -- Naturality of the outer route comparison in the preimage morphism.
  have hroute : M ≫ R₂ = R₁ ≫ P :=
    overlap_base_change_left_route_iso_naturality (p := p) (hc := hc) 𝒰 𝒱 i i' j pre
  -- The member-level comparison exchanges the preimage with the `j`-component of `θ`.
  have hmid :
      (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map pre ≫
          (member_base_change_comparison_component_iso hc D₂ φ i j).inv =
        (member_base_change_comparison_component_iso hc D₁ φ i j).inv ≫
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom j) := by
    rw [local_member_base_change_preimage_component_spec
      hc 𝒰 𝒱 φ θ i j]
    exact (Iso.comp_inv_eq _).2 (Category.assoc _ _ _).symm
  have hPK : P ≫ K₂ = K₁ ≫ G :=
    (((hc.pullbackFunctor q).map_comp
        ((hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map pre)
        (member_base_change_comparison_component_iso hc D₂ φ i j).inv).symm.trans
      (congrArg (fun k ↦ (hc.pullbackFunctor q).map k) hmid)).trans
      ((hc.pullbackFunctor q).map_comp
        (member_base_change_comparison_component_iso hc D₁ φ i j).inv
        ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom j)))
  -- The common-route comparison exchanges the refined pullbacks of `θ`.
  have hcommon : G ≫ C₂ = C₁ ≫ W :=
    overlap_base_change_left_common_route_iso_inv_naturality
      (p := p) (hc := hc) 𝒰 𝒱 i i' j (θ.hom j)
  show M ≫ R₂ ≫ K₂ ≫ C₂ = (R₁ ≫ K₁ ≫ C₁) ≫ W
  calc M ≫ R₂ ≫ K₂ ≫ C₂
      = (M ≫ R₂) ≫ K₂ ≫ C₂ := (Category.assoc M R₂ (K₂ ≫ C₂)).symm
    _ = (R₁ ≫ P) ≫ K₂ ≫ C₂ := congrArg (fun k ↦ k ≫ (K₂ ≫ C₂)) hroute
    _ = R₁ ≫ P ≫ K₂ ≫ C₂ := Category.assoc R₁ P (K₂ ≫ C₂)
    _ = R₁ ≫ (P ≫ K₂) ≫ C₂ := congrArg (fun k ↦ R₁ ≫ k) (Category.assoc P K₂ C₂).symm
    _ = R₁ ≫ (K₁ ≫ G) ≫ C₂ := congrArg (fun k ↦ R₁ ≫ k ≫ C₂) hPK
    _ = R₁ ≫ K₁ ≫ G ≫ C₂ := congrArg (fun k ↦ R₁ ≫ k) (Category.assoc K₁ G C₂)
    _ = R₁ ≫ K₁ ≫ C₁ ≫ W := congrArg (fun k ↦ R₁ ≫ K₁ ≫ k) hcommon
    _ = R₁ ≫ (K₁ ≫ C₁) ≫ W := congrArg (fun k ↦ R₁ ≫ k) (Category.assoc K₁ C₁ W).symm
    _ = (R₁ ≫ K₁ ≫ C₁) ≫ W := (Category.assoc R₁ (K₁ ≫ C₁) W).symm

/-- Helper for Lemma 8.3.7: the right local restriction of the preimage candidate matches the
direct overlap pullback of `θ` through the right common-route comparison. -/
private theorem overlap_base_change_right_to_common_naturality
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i i' : 𝒰.index) (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
        ((hc.pullbackFunctor (𝒰.pr1 i i')).map
          (local_member_base_change_preimage
            hc 𝒰 𝒱 φ θ i')) ≫
      (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₂ φ i i' j).hom =
    (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₁ φ i i' j).hom ≫
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
        (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map (θ.hom j) := by
  let pre := local_member_base_change_preimage
    hc 𝒰 𝒱 φ θ i'
  let q := overlap_base_change_right_component_map 𝒰 𝒱 i i' j
  let M := (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
    ((hc.pullbackFunctor (𝒰.pr1 i i')).map pre)
  let R₁ := (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j (D₁.obj i')).hom
  let R₂ := (overlap_base_change_right_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j (D₂.obj i')).hom
  let K₁ := (hc.pullbackFunctor q).map
    (member_base_change_comparison_component_iso hc D₁ φ i' j).inv
  let K₂ := (hc.pullbackFunctor q).map
    (member_base_change_comparison_component_iso hc D₂ φ i' j).inv
  let C₁ := (overlap_base_change_right_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j
    (((pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)).obj D₁).obj j)).inv
  let C₂ := (overlap_base_change_right_common_route_iso (p := p) (hc := hc) 𝒰 𝒱 i i' j
    (((pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)).obj D₂).obj j)).inv
  let P := (hc.pullbackFunctor q).map
    ((hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i').hom)).map pre)
  let G := (hc.pullbackFunctor q).map
    ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom)).map (θ.hom j))
  let W := (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
    (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map (θ.hom j)
  have hroute : M ≫ R₂ = R₁ ≫ P :=
    overlap_base_change_right_route_iso_naturality (p := p) (hc := hc) 𝒰 𝒱 i i' j pre
  have hmid :
      (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i').hom)).map pre ≫
          (member_base_change_comparison_component_iso hc D₂ φ i' j).inv =
        (member_base_change_comparison_component_iso hc D₁ φ i' j).inv ≫
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom)).map (θ.hom j) := by
    rw [local_member_base_change_preimage_component_spec
      hc 𝒰 𝒱 φ θ i' j]
    exact (Iso.comp_inv_eq _).2 (Category.assoc _ _ _).symm
  have hPK : P ≫ K₂ = K₁ ≫ G :=
    (((hc.pullbackFunctor q).map_comp
        ((hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i').hom)).map pre)
        (member_base_change_comparison_component_iso hc D₂ φ i' j).inv).symm.trans
      (congrArg (fun k ↦ (hc.pullbackFunctor q).map k) hmid)).trans
      ((hc.pullbackFunctor q).map_comp
        (member_base_change_comparison_component_iso hc D₁ φ i' j).inv
        ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom)).map (θ.hom j)))
  have hcommon : G ≫ C₂ = C₁ ≫ W :=
    overlap_base_change_right_common_route_iso_inv_naturality
      (p := p) (hc := hc) 𝒰 𝒱 i i' j (θ.hom j)
  show M ≫ R₂ ≫ K₂ ≫ C₂ = (R₁ ≫ K₁ ≫ C₁) ≫ W
  calc M ≫ R₂ ≫ K₂ ≫ C₂
      = (M ≫ R₂) ≫ K₂ ≫ C₂ := (Category.assoc M R₂ (K₂ ≫ C₂)).symm
    _ = (R₁ ≫ P) ≫ K₂ ≫ C₂ := congrArg (fun k ↦ k ≫ (K₂ ≫ C₂)) hroute
    _ = R₁ ≫ P ≫ K₂ ≫ C₂ := Category.assoc R₁ P (K₂ ≫ C₂)
    _ = R₁ ≫ (P ≫ K₂) ≫ C₂ := congrArg (fun k ↦ R₁ ≫ k) (Category.assoc P K₂ C₂).symm
    _ = R₁ ≫ (K₁ ≫ G) ≫ C₂ := congrArg (fun k ↦ R₁ ≫ k ≫ C₂) hPK
    _ = R₁ ≫ K₁ ≫ G ≫ C₂ := congrArg (fun k ↦ R₁ ≫ k) (Category.assoc K₁ G C₂)
    _ = R₁ ≫ K₁ ≫ C₁ ≫ W := congrArg (fun k ↦ R₁ ≫ K₁ ≫ k) hcommon
    _ = R₁ ≫ (K₁ ≫ C₁) ≫ W := congrArg (fun k ↦ R₁ ≫ k) (Category.assoc K₁ C₁ W).symm
    _ = (R₁ ≫ K₁ ≫ C₁) ≫ W := (Category.assoc R₁ (K₁ ≫ C₁) W).symm

/-- Helper for Lemma 8.3.7: pulling back a flexible-leg descent comparison along a further
morphism is the flexible-leg comparison at the composite legs, conjugated by the chosen
composition comparisons. -/
private theorem pullbackFunctor_map_pullHom'
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]
    (D : DescentDatum p hc 𝒰)
    {Y Z : C} (g : Z ⟶ Y) (q : Y ⟶ U) {i₁ i₂ : 𝒰.index}
    (f₁ : Y ⟶ (𝒰.obj i₁).left) (f₂ : Y ⟶ (𝒰.obj i₂).left)
    (hf₁ : f₁ ≫ (𝒰.obj i₁).hom = q) (hf₂ : f₂ ≫ (𝒰.obj i₂).hom = q) :
    (hc.pullbackFunctor g).map
        (Pseudofunctor.DescentData'.pullHom' D.hom q f₁ f₂ hf₁ hf₂) =
      (hc.pullbackCompComponentIso f₁ g (D.obj i₁)).inv ≫
        Pseudofunctor.DescentData'.pullHom' D.hom (g ≫ q) (g ≫ f₁) (g ≫ f₂)
          (by simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) hf₁)
          (by simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) hf₂) ≫
        (hc.pullbackCompComponentIso f₂ g (D.obj i₂)).hom := by
  have hmap :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := hc.fiberPseudofunctor)
      (φ := Pseudofunctor.DescentData'.pullHom' D.hom q f₁ f₂ hf₁ hf₂)
      g (g ≫ f₁) (g ≫ f₂) rfl rfl
  rw [Pseudofunctor.DescentData'.pullHom_pullHom' (hom := D.hom) g q (g ≫ q) f₁ f₂
    (g ≫ f₁) (g ≫ f₂) rfl hf₁ hf₂ rfl rfl] at hmap
  have hinv :
      (hc.fiberPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc
          (by aesop)).inv.toNatTrans.app (D.obj i₁) =
        (hc.pullbackCompComponentIso f₁ g (D.obj i₁)).inv :=
    fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv_local hc f₁ g (D.obj i₁)
  have hhom :
      (hc.fiberPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc
          (by aesop)).hom.toNatTrans.app (D.obj i₂) =
        (hc.pullbackCompComponentIso f₂ g (D.obj i₂)).hom :=
    fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom_local hc f₂ g (D.obj i₂)
  have step1 := congrArg
    (fun k ↦ k ≫
      Pseudofunctor.DescentData'.pullHom' D.hom (g ≫ q) (g ≫ f₁) (g ≫ f₂)
        (by simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) hf₁)
        (by simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) hf₂) ≫
      (hc.fiberPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc
        (by aesop)).hom.toNatTrans.app (D.obj i₂)) hinv
  have step2 := congrArg
    (fun k ↦ (hc.pullbackCompComponentIso f₁ g (D.obj i₁)).inv ≫
      Pseudofunctor.DescentData'.pullHom' D.hom (g ≫ q) (g ≫ f₁) (g ≫ f₂)
        (by simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) hf₁)
        (by simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) hf₂) ≫ k) hhom
  exact (hmap.trans step1).trans step2

/-- Helper for Lemma 8.3.7: transporting the chosen cartesian arrow along an equality of base
morphisms acts on ambient values by the canonical identification. -/
private theorem eqToHom_val_comp_map
    {U V : C} {f g : V ⟶ U} (hb : f = g) (X : p.Fiber U) :
    Functor.Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun r ↦ hc.obj r X) hb)) ≫ hc.map g X =
      hc.map f X := by
  cases hb
  exact (congrArg (fun k ↦ k ≫ hc.map f X)
      (Functor.Fiber.fiberInclusion.map_id (hc.obj f X))).trans
    (Category.id_comp (hc.map f X))

/-- Helper for Lemma 8.3.7: pulling back a chosen composition comparison along a further morphism
is the composition comparison of the composite, up to the canonical associativity transport. This
is the coherence pentagon for the chosen pullbacks, proved by cancelling against the chosen
strongly cartesian arrows. -/
private theorem pullbackFunctor_map_pullbackCompComponentIso_hom
    {T V W Z : C} (f : V ⟶ T) (x : W ⟶ V) (g : Z ⟶ W) (X : p.Fiber T) :
    (hc.pullbackFunctor g).map ((hc.pullbackCompComponentIso f x X).hom) =
      (hc.pullbackCompComponentIso (x ≫ f) g X).inv ≫
        eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
        (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
        (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom := by
  apply Functor.Fiber.hom_ext
  letI hcart : p.IsStronglyCartesian ((g ≫ x) ≫ f)
      (hc.map g (x ^*[hc] (f ^*[hc] X)) ≫ hc.map x (f ^*[hc] X) ≫ hc.map f X) := by
    have h : p.IsStronglyCartesian (g ≫ (x ≫ f))
        (hc.map g (x ^*[hc] (f ^*[hc] X)) ≫ hc.map x (f ^*[hc] X) ≫ hc.map f X) :=
      inferInstance
    rwa [← Category.assoc] at h
  letI hα : p.IsHomLift (𝟙 Z)
      (Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor g).map ((hc.pullbackCompComponentIso f x X).hom))) :=
    ((hc.pullbackFunctor g).map ((hc.pullbackCompComponentIso f x X).hom)).2
  letI hβ : p.IsHomLift (𝟙 Z)
      (Functor.Fiber.fiberInclusion.map
        ((hc.pullbackCompComponentIso (x ≫ f) g X).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
          (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
          (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom)) :=
    ((hc.pullbackCompComponentIso (x ≫ f) g X).inv ≫
      eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
      (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
      (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom).2
  refine
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      ((g ≫ x) ≫ f)
      (hc.map g (x ^*[hc] (f ^*[hc] X)) ≫ hc.map x (f ^*[hc] X) ≫ hc.map f X)
      hcart _ _ (𝟙 Z)
      (Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor g).map ((hc.pullbackCompComponentIso f x X).hom)))
      (Functor.Fiber.fiberInclusion.map
        ((hc.pullbackCompComponentIso (x ≫ f) g X).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
          (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
          (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom))
      hα hβ ?_
  have hleft :
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackFunctor g).map ((hc.pullbackCompComponentIso f x X).hom)) ≫
        hc.map g (x ^*[hc] (f ^*[hc] X)) ≫ hc.map x (f ^*[hc] X) ≫ hc.map f X =
      hc.map g ((x ≫ f) ^*[hc] X) ≫ hc.map (x ≫ f) X := by
    have h1 :
        Functor.Fiber.fiberInclusion.map
            ((hc.pullbackFunctor g).map ((hc.pullbackCompComponentIso f x X).hom)) ≫
          hc.map g (x ^*[hc] (f ^*[hc] X)) ≫
            (hc.map x (f ^*[hc] X) ≫ hc.map f X) =
        hc.map g ((x ≫ f) ^*[hc] X) ≫
          Functor.Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f x X).hom) ≫
            (hc.map x (f ^*[hc] X) ≫ hc.map f X) :=
      fiberInclusion_map_pullbackFunctor_map_fac_assoc (hc := hc) g
        ((hc.pullbackCompComponentIso f x X).hom) (hc.map x (f ^*[hc] X) ≫ hc.map f X)
    have h2 :
        Functor.Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f x X).hom) ≫
            (hc.map x (f ^*[hc] X) ≫ hc.map f X) =
          hc.map (x ≫ f) X :=
      hc.pullbackCompComponentIso_fac f x X
    calc
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackFunctor g).map ((hc.pullbackCompComponentIso f x X).hom)) ≫
        hc.map g (x ^*[hc] (f ^*[hc] X)) ≫ hc.map x (f ^*[hc] X) ≫ hc.map f X
          = hc.map g ((x ≫ f) ^*[hc] X) ≫
              Functor.Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f x X).hom) ≫
                (hc.map x (f ^*[hc] X) ≫ hc.map f X) := h1
      _ = hc.map g ((x ≫ f) ^*[hc] X) ≫ hc.map (x ≫ f) X :=
            congrArg (fun k ↦ hc.map g ((x ≫ f) ^*[hc] X) ≫ k) h2
  have hr1 :
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) ≫
        hc.map g (x ^*[hc] (f ^*[hc] X)) ≫ hc.map x (f ^*[hc] X) =
      hc.map (g ≫ x) (f ^*[hc] X) :=
    hc.pullbackCompComponentIso_fac x g (f ^*[hc] X)
  have hr2 :
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso f (g ≫ x) X).hom) ≫
        hc.map (g ≫ x) (f ^*[hc] X) ≫ hc.map f X =
      hc.map ((g ≫ x) ≫ f) X :=
    hc.pullbackCompComponentIso_fac f (g ≫ x) X
  have hr3 :
      Functor.Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm)) ≫
        hc.map ((g ≫ x) ≫ f) X =
      hc.map (g ≫ x ≫ f) X :=
    eqToHom_val_comp_map (hc := hc) (Category.assoc g x f).symm X
  have hr4 :
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso (x ≫ f) g X).inv) ≫
        hc.map (g ≫ x ≫ f) X =
      hc.map g ((x ≫ f) ^*[hc] X) ≫ hc.map (x ≫ f) X := by
    have h := hc.pullbackCompComponentIso_inv_fac (x ≫ f) g X
    simpa using h
  -- Distribute the ambient inclusion over the comparison composite, then percolate the chosen
  -- cartesian arrows through the four factors.
  refine hleft.trans (Eq.symm ?_)
  have d3 :
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
            (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) =
        Functor.Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f (g ≫ x) X).hom) ≫
          Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) :=
    Functor.Fiber.fiberInclusion.map_comp _ _
  have d2 :
      Functor.Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
            (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
            (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) =
        Functor.Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm)) ≫
          Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
              (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) :=
    Functor.Fiber.fiberInclusion.map_comp _ _
  have d1 :
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso (x ≫ f) g X).inv ≫
            eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
            (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
            (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) =
        Functor.Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso (x ≫ f) g X).inv) ≫
          Functor.Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
              (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
              (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) :=
    Functor.Fiber.fiberInclusion.map_comp _ _
  -- Shorthand ambient factors.
  let A := Functor.Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso (x ≫ f) g X).inv)
  let E := Functor.Fiber.fiberInclusion.map
    (eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm))
  let B := Functor.Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f (g ≫ x) X).hom)
  let Cc := Functor.Fiber.fiberInclusion.map
    ((hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom)
  let m₁ := hc.map g (x ^*[hc] (f ^*[hc] X))
  let m₂ := hc.map x (f ^*[hc] X)
  let m₃ := hc.map f X
  have hdist :
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso (x ≫ f) g X).inv ≫
            eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
            (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
            (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) =
        A ≫ E ≫ B ≫ Cc :=
    d1.trans (congrArg (fun k ↦ A ≫ k) (d2.trans (congrArg (fun k ↦ E ≫ k) d3)))
  have hcc : Cc ≫ m₁ ≫ m₂ ≫ m₃ = hc.map (g ≫ x) (f ^*[hc] X) ≫ m₃ :=
    ((congrArg (fun k ↦ Cc ≫ k) (Category.assoc m₁ m₂ m₃).symm).trans
      (Category.assoc Cc (m₁ ≫ m₂) m₃).symm).trans
      (congrArg (fun k ↦ k ≫ m₃) hr1)
  have hbc : B ≫ Cc ≫ m₁ ≫ m₂ ≫ m₃ = hc.map ((g ≫ x) ≫ f) X :=
    ((congrArg (fun k ↦ B ≫ k) hcc).trans
      (Category.assoc B (hc.map (g ≫ x) (f ^*[hc] X)) m₃).symm).trans
      ((Category.assoc B (hc.map (g ≫ x) (f ^*[hc] X)) m₃).trans hr2)
  have hec : E ≫ B ≫ Cc ≫ m₁ ≫ m₂ ≫ m₃ = hc.map (g ≫ x ≫ f) X :=
    (congrArg (fun k ↦ E ≫ k) hbc).trans hr3
  have hac : A ≫ E ≫ B ≫ Cc ≫ m₁ ≫ m₂ ≫ m₃ =
      hc.map g ((x ≫ f) ^*[hc] X) ≫ hc.map (x ≫ f) X :=
    (congrArg (fun k ↦ A ≫ k) hec).trans hr4
  calc
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackCompComponentIso (x ≫ f) g X).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r X) (Category.assoc g x f).symm) ≫
          (hc.pullbackCompComponentIso f (g ≫ x) X).hom ≫
          (hc.pullbackCompComponentIso x g ((hc.pullbackFunctor f).obj X)).hom) ≫
      m₁ ≫ m₂ ≫ m₃
        = (A ≫ E ≫ B ≫ Cc) ≫ m₁ ≫ m₂ ≫ m₃ :=
          congrArg (fun k ↦ k ≫ m₁ ≫ m₂ ≫ m₃) hdist
    _ = A ≫ (E ≫ B ≫ Cc) ≫ m₁ ≫ m₂ ≫ m₃ :=
          Category.assoc A (E ≫ B ≫ Cc) (m₁ ≫ m₂ ≫ m₃)
    _ = A ≫ E ≫ (B ≫ Cc) ≫ m₁ ≫ m₂ ≫ m₃ :=
          congrArg (fun k ↦ A ≫ k) (Category.assoc E (B ≫ Cc) (m₁ ≫ m₂ ≫ m₃))
    _ = A ≫ E ≫ B ≫ Cc ≫ m₁ ≫ m₂ ≫ m₃ :=
          congrArg (fun k ↦ A ≫ E ≫ k) (Category.assoc B Cc (m₁ ≫ m₂ ≫ m₃))
    _ = hc.map g ((x ≫ f) ^*[hc] X) ≫ hc.map (x ≫ f) X := hac

/-- Helper for Lemma 8.3.7: the flexible-leg descent comparison only depends on the legs up to
equality of morphisms, with the canonical transports on either side. -/
private theorem pullHom'_leg_congr
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]
    (D : DescentDatum p hc 𝒰) {Y : C} {q : Y ⟶ U} {i₁ i₂ : 𝒰.index}
    {f₁ f₁' : Y ⟶ (𝒰.obj i₁).left} {f₂ f₂' : Y ⟶ (𝒰.obj i₂).left}
    (h₁ : f₁ = f₁') (h₂ : f₂ = f₂')
    (hf₁ : f₁ ≫ (𝒰.obj i₁).hom = q) (hf₂ : f₂ ≫ (𝒰.obj i₂).hom = q) :
    Pseudofunctor.DescentData'.pullHom' D.hom q f₁ f₂ hf₁ hf₂ =
      eqToHom (congrArg (fun r ↦ hc.obj r (D.obj i₁)) h₁) ≫
        Pseudofunctor.DescentData'.pullHom' D.hom q f₁' f₂'
          (h₁ ▸ hf₁) (h₂ ▸ hf₂) ≫
        eqToHom (congrArg (fun r ↦ hc.obj r (D.obj i₂)) h₂).symm := by
  cases h₁
  cases h₂
  exact (Category.id_comp _).symm.trans
    (congrArg (fun k ↦ (𝟙 (hc.obj f₁ (D.obj i₁)) : _ ⟶ _) ≫ k)
      (Category.comp_id _).symm)

/-- Helper for Lemma 8.3.7: the chosen composition comparison transports along an equality of its
outer base morphism. -/
private theorem pullbackCompComponentIso_hom_base_congr
    {T V W : C} (f : V ⟶ T) {x x' : W ⟶ V} (h : x = x') (X : p.Fiber T) :
    (hc.pullbackCompComponentIso f x X).hom ≫
        eqToHom (congrArg (fun r ↦ hc.obj r ((hc.pullbackFunctor f).obj X)) h) =
      eqToHom (congrArg (fun r ↦ hc.obj r X)
          (congrArg (fun r ↦ r ≫ f) h)) ≫
        (hc.pullbackCompComponentIso f x' X).hom := by
  cases h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Helper for Lemma 8.3.7: a closed pair of canonical transports collapses. -/
private theorem eqToHom_collapse₂ {E : Type*} [Category E] {X A Y : E}
    (h₁ : X = A) (h₂ : A = X) (f : X ⟶ Y) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ f = f := by
  cases h₁
  exact (Category.id_comp _).trans (Category.id_comp f)

/-- Helper for Lemma 8.3.7: a closed triple of canonical transports collapses. -/
private theorem eqToHom_collapse₃ {E : Type*} [Category E] {X A B Y : E}
    (h₁ : X = A) (h₂ : A = B) (h₃ : B = X) (f : X ⟶ Y) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ ≫ f = f := by
  cases h₁
  cases h₂
  exact (Category.id_comp _).trans ((Category.id_comp _).trans (Category.id_comp f))

/-- Helper for Lemma 8.3.7: the generic normal form for one branch of the to-common comparison.
The expanded route/member/common composite collapses to the flexible-leg descent comparison
between the outer leg and the common refined leg, conjugated by the outer and final composition
comparisons. -/
private theorem to_common_route_normalize
    {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]
    (D : DescentDatum p hc 𝒰) {k kα : 𝒰.index}
    {Z O Mem Vj : C} (a : Z ⟶ O) (b : O ⟶ (𝒰.obj k).left)
    (q' : Z ⟶ Mem) (c : Mem ⟶ (𝒰.obj k).left) (fst : Mem ⟶ Vj)
    (fj : Vj ⟶ (𝒰.obj kα).left) (w : Z ⟶ Vj)
    (hbase : q' ≫ c = a ≫ b)
    (hwfst : w = q' ≫ fst)
    (hmem : (fst ≫ fj) ≫ (𝒰.obj kα).hom = c ≫ (𝒰.obj k).hom)
    (hWleg : (w ≫ fj) ≫ (𝒰.obj kα).hom = (a ≫ b) ≫ (𝒰.obj k).hom) :
    ((hc.pullbackCompComponentIso b a (D.obj k)).inv ≫
      (eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
        (hc.pullbackCompComponentIso c q' (D.obj k)).hom)) ≫
      ((hc.pullbackFunctor q').map
          (Pseudofunctor.DescentData'.pullHom' D.hom (c ≫ (𝒰.obj k).hom) c (fst ≫ fj)
            rfl hmem ≫
            (hc.pullbackCompComponentIso fj fst (D.obj kα)).hom) ≫
        ((hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm)) =
    (hc.pullbackCompComponentIso b a (D.obj k)).inv ≫
      Pseudofunctor.DescentData'.pullHom' D.hom ((a ≫ b) ≫ (𝒰.obj k).hom)
        (a ≫ b) (w ≫ fj) rfl hWleg ≫
      (hc.pullbackCompComponentIso fj w (D.obj kα)).hom := by
  have hpath : q' ≫ (fst ≫ fj) = w ≫ fj :=
    (Category.assoc q' fst fj).symm.trans (congrArg (fun r ↦ r ≫ fj) hwfst.symm)
  have hT :
      (hc.pullbackFunctor q').map
          (Pseudofunctor.DescentData'.pullHom' D.hom (c ≫ (𝒰.obj k).hom) c (fst ≫ fj)
            rfl hmem) =
        (hc.pullbackCompComponentIso c q' (D.obj k)).inv ≫
          Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
          (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).hom :=
    pullbackFunctor_map_pullHom' (p := p) (hc := hc) D q' (c ≫ (𝒰.obj k).hom) c (fst ≫ fj)
      rfl hmem
  have hP :
      (hc.pullbackFunctor q').map ((hc.pullbackCompComponentIso fj fst (D.obj kα)).hom) =
        (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm) ≫
          (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).hom :=
    pullbackFunctor_map_pullbackCompComponentIso_hom (p := p) (hc := hc) fj fst q' (D.obj kα)
  have hC2 :
      (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm =
        eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
            (congrArg (fun r ↦ r ≫ fj) (hwfst.symm : q' ≫ fst = w))) ≫
          (hc.pullbackCompComponentIso fj w (D.obj kα)).hom :=
    pullbackCompComponentIso_hom_base_congr (p := p) (hc := hc) fj
      (hwfst.symm : q' ≫ fst = w) (D.obj kα)
  have hLC :
      Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
          (q' ≫ c) (q' ≫ (fst ≫ fj))
          (by simpa [Category.assoc] using
            congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
          (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) =
        eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase) ≫
          Pseudofunctor.DescentData'.pullHom' D.hom ((a ≫ b) ≫ (𝒰.obj k).hom)
            (a ≫ b) (w ≫ fj) rfl hWleg ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) hpath).symm :=
    pullHom'_leg_congr (p := p) (hc := hc) D hbase hpath _ _
  simp only [Category.assoc]
  refine (cancel_epi (hc.pullbackCompComponentIso b a (D.obj k)).inv).2 ?_
  calc
    eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
        (hc.pullbackCompComponentIso c q' (D.obj k)).hom ≫
        (hc.pullbackFunctor q').map
          (Pseudofunctor.DescentData'.pullHom' D.hom (c ≫ (𝒰.obj k).hom) c (fst ≫ fj)
            rfl hmem ≫
            (hc.pullbackCompComponentIso fj fst (D.obj kα)).hom) ≫
        (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
        eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm
      = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          (hc.pullbackCompComponentIso c q' (D.obj k)).hom ≫
          ((hc.pullbackFunctor q').map
            (Pseudofunctor.DescentData'.pullHom' D.hom (c ≫ (𝒰.obj k).hom) c (fst ≫ fj)
              rfl hmem) ≫
          (hc.pullbackFunctor q').map
            ((hc.pullbackCompComponentIso fj fst (D.obj kα)).hom)) ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm := by
        exact congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
            (hc.pullbackCompComponentIso c q' (D.obj k)).hom ≫ kk ≫
            (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm)
          ((hc.pullbackFunctor q').map_comp _ _)
    _ = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          (hc.pullbackCompComponentIso c q' (D.obj k)).hom ≫
          (((hc.pullbackCompComponentIso c q' (D.obj k)).inv ≫
            Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
              (q' ≫ c) (q' ≫ (fst ≫ fj))
              (by simpa [Category.assoc] using
                congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
              (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
            (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).hom) ≫
          ((hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).inv ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
              (Category.assoc q' fst fj).symm) ≫
            (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
            (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).hom)) ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm := by
        exact congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
            (hc.pullbackCompComponentIso c q' (D.obj k)).hom ≫ kk ≫
            (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm)
          (congrArg₂ (fun kk₁ kk₂ ↦ kk₁ ≫ kk₂) hT hP)
    _ = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          (hc.pullbackCompComponentIso c q' (D.obj k)).hom ≫
          (hc.pullbackCompComponentIso c q' (D.obj k)).inv ≫
          Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
          (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm) ≫
          (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm := by
        simp only [Category.assoc]
    _ = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
          (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm) ≫
          (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm :=
        congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫ kk)
          (Iso.hom_inv_id_assoc (hc.pullbackCompComponentIso c q' (D.obj k))
            (Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
              (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).hom ≫
              (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα)).inv ≫
              eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
                (Category.assoc q' fst fj).symm) ≫
              (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
              (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).hom ≫
              (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
              eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm))
    _ = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm) ≫
          (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).hom ≫
          (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm :=
        congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
            Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫ kk)
          (Iso.hom_inv_id_assoc (hc.pullbackCompComponentIso (fst ≫ fj) q' (D.obj kα))
            (eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
                (Category.assoc q' fst fj).symm) ≫
              (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
              (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).hom ≫
              (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα)).inv ≫
              eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm))
    _ = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm) ≫
          (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm :=
        congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
            Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
              (Category.assoc q' fst fj).symm) ≫
            (hc.pullbackCompComponentIso fj (q' ≫ fst) (D.obj kα)).hom ≫ kk)
          (Iso.hom_inv_id_assoc (hc.pullbackCompComponentIso fst q' (fj ^*[hc] D.obj kα))
            (eqToHom (congrArg (fun r ↦ hc.obj r (fj ^*[hc] D.obj kα)) hwfst).symm))
    _ = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
            (q' ≫ c) (q' ≫ (fst ≫ fj))
            (by simpa [Category.assoc] using
              congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
            (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm) ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
            (congrArg (fun r ↦ r ≫ fj) (hwfst.symm : q' ≫ fst = w))) ≫
          (hc.pullbackCompComponentIso fj w (D.obj kα)).hom := by
        exact congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
            Pseudofunctor.DescentData'.pullHom' D.hom (q' ≫ (c ≫ (𝒰.obj k).hom))
              (q' ≫ c) (q' ≫ (fst ≫ fj))
              (by simpa [Category.assoc] using
                congrArg (fun r ↦ q' ≫ r) (rfl : c ≫ (𝒰.obj k).hom = c ≫ (𝒰.obj k).hom))
              (by simpa [Category.assoc] using congrArg (fun r ↦ q' ≫ r) hmem) ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
              (Category.assoc q' fst fj).symm) ≫ kk)
          hC2
    _ = eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
          (eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase) ≫
            Pseudofunctor.DescentData'.pullHom' D.hom ((a ≫ b) ≫ (𝒰.obj k).hom)
              (a ≫ b) (w ≫ fj) rfl hWleg ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) hpath).symm) ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm) ≫
          eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
            (congrArg (fun r ↦ r ≫ fj) (hwfst.symm : q' ≫ fst = w))) ≫
          (hc.pullbackCompComponentIso fj w (D.obj kα)).hom := by
        exact congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫ kk ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
              (Category.assoc q' fst fj).symm) ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (D.obj kα))
              (congrArg (fun r ↦ r ≫ fj) (hwfst.symm : q' ≫ fst = w))) ≫
            (hc.pullbackCompComponentIso fj w (D.obj kα)).hom)
          hLC
    _ = Pseudofunctor.DescentData'.pullHom' D.hom ((a ≫ b) ≫ (𝒰.obj k).hom)
          (a ≫ b) (w ≫ fj) rfl hWleg ≫
          (hc.pullbackCompComponentIso fj w (D.obj kα)).hom := by
        simp only [Category.assoc]
        refine Eq.trans (congrArg
          (fun kk ↦ eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm) ≫
            eqToHom (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase) ≫
            Pseudofunctor.DescentData'.pullHom' D.hom ((a ≫ b) ≫ (𝒰.obj k).hom)
              (a ≫ b) (w ≫ fj) rfl hWleg ≫ kk)
          (eqToHom_collapse₃
            ((congrArg (fun r ↦ hc.obj r (D.obj kα)) hpath).symm)
            (congrArg (fun r ↦ hc.obj r (D.obj kα)) (Category.assoc q' fst fj).symm)
            (congrArg (fun r ↦ hc.obj r (D.obj kα))
              (congrArg (fun r ↦ r ≫ fj) (hwfst.symm : q' ≫ fst = w)))
            ((hc.pullbackCompComponentIso fj w (D.obj kα)).hom))) ?_
        exact eqToHom_collapse₂
          (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase.symm)
          (congrArg (fun r ↦ hc.obj r (D.obj k)) hbase)
          (Pseudofunctor.DescentData'.pullHom' D.hom ((a ≫ b) ≫ (𝒰.obj k).hom)
            (a ≫ b) (w ≫ fj) rfl hWleg ≫
            (hc.pullbackCompComponentIso fj w (D.obj kα)).hom)

/-- Helper for Lemma 8.3.7: through the two common-route comparisons, the descent morphism of `D`
on the chosen overlap becomes the identity of the direct overlap pullback. This is the
three-leg cocycle of `D` at `(i, i', φ.α j)` transported to the overlap member. -/
private theorem overlap_base_change_descent_hom_to_common
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i i' : 𝒰.index)
    (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map (D.hom i i') ≫
      (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D φ i i' j).hom =
    (overlap_base_change_left_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D φ i i' j).hom := by
  -- The common refined leg maps to `U` through the left overlap route.
  have hWlegL :
      ((pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) ≫ (𝒰.obj (φ.α j)).hom) =
        ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom) := by
    have t1 := Category.assoc (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) ((φ.f j).left) ((𝒰.obj (φ.α j)).hom)
    have t2 := congrArg (fun r ↦ pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ r) (Over.w (φ.f j))
    have t3 : pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (𝒱.obj j).hom = ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) :=
      pullback.condition
    have t4 := (Category.assoc (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (𝒰.pr0 i i') ((𝒰.obj i).hom)).symm
    exact ((t1.trans t2).trans t3).trans t4
  -- The two outer overlap legs agree over `U`.
  have hpr :
      ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') ≫ (𝒰.obj i').hom) =
        ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun r ↦ ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ r) (𝒰.pr0_map_eq_pr1_map i i').symm).trans
        (Category.assoc _ _ _).symm)
  have hWlegR :
      ((pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) ≫ (𝒰.obj (φ.α j)).hom) =
        ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') ≫ (𝒰.obj i').hom) :=
    hWlegL.trans hpr.symm
  -- Normal forms of the two to-common comparisons.
  have hbaseL : overlap_base_change_left_component_map 𝒰 𝒱 i i' j ≫
        pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom =
      ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i' :=
    overlap_base_change_left_adapter_component_w 𝒰 𝒱 i i' j
  have hwfstL : pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) =
      overlap_base_change_left_component_map 𝒰 𝒱 i i' j ≫
        pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom :=
    (overlap_base_change_left_component_map_fst 𝒰 𝒱 i i' j).symm
  have hmemL : (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left) ≫
        (𝒰.obj (φ.α j)).hom =
      pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom :=
    (Category.assoc _ _ _).trans (member_base_change_comparison_component_map φ i j)
  have hL :
      (overlap_base_change_left_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D φ i i' j).hom =
        (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫
          Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegL ≫
          (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom :=
    to_common_route_normalize (p := p) (hc := hc) D
      (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (𝒰.pr0 i i')
      (overlap_base_change_left_component_map 𝒰 𝒱 i i' j)
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
      ((φ.f j).left) (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
      hbaseL hwfstL hmemL hWlegL
  have hbaseR : overlap_base_change_right_component_map 𝒰 𝒱 i i' j ≫
        pullback.snd (𝒱.obj j).hom (𝒰.obj i').hom =
      ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i' :=
    overlap_base_change_right_adapter_component_w 𝒰 𝒱 i i' j
  have hwfstR : pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) =
      overlap_base_change_right_component_map 𝒰 𝒱 i i' j ≫
        pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom :=
    (overlap_base_change_right_component_map_fst 𝒰 𝒱 i i' j).symm
  have hmemR : (pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom ≫ (φ.f j).left) ≫
        (𝒰.obj (φ.α j)).hom =
      pullback.snd (𝒱.obj j).hom (𝒰.obj i').hom ≫ (𝒰.obj i').hom :=
    (Category.assoc _ _ _).trans (member_base_change_comparison_component_map φ i' j)
  have hR :
      (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D φ i i' j).hom =
        (hc.pullbackCompComponentIso (𝒰.pr1 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i')).inv ≫
          Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') ≫ (𝒰.obj i').hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegR ≫
          (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom :=
    to_common_route_normalize (p := p) (hc := hc) D
      (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (𝒰.pr1 i i')
      (overlap_base_change_right_component_map 𝒰 𝒱 i i' j)
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i').hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i').hom)
      ((φ.f j).left) (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))
      hbaseR hwfstR hmemR hWlegR
  -- The transported descent morphism from the already established overlap transport.
  have h1037 := overlap_base_change_map_descent_hom_comp_inv (p := p) (hc := hc) 𝒰 𝒱 D i i' j
  -- The three-leg cocycle of the flexible descent comparisons.
  have hco :
      Pseudofunctor.DescentData'.pullHom' D.hom
          ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
          (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') rfl hpr ≫
        Pseudofunctor.DescentData'.pullHom' D.hom
          ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
          (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL =
      Pseudofunctor.DescentData'.pullHom' D.hom
          ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
          (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegL :=
    Pseudofunctor.DescentData'.comp_pullHom' D
      ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
      (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left)
      rfl hpr hWlegL
  have e1 : (hc.pullbackFunctor (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom)).map (D.hom i i') ≫ (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D φ i i' j).hom =
      (hc.pullbackFunctor (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom)).map (D.hom i i') ≫ ((hc.pullbackCompComponentIso (𝒰.pr1 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i')).inv ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') ≫ (𝒰.obj i').hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegR ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom)) :=
    congrArg (fun kk ↦ (hc.pullbackFunctor (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom)).map (D.hom i i') ≫ kk) hR
  have e2 : (hc.pullbackFunctor (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom)).map (D.hom i i') ≫ ((hc.pullbackCompComponentIso (𝒰.pr1 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i')).inv ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') ≫ (𝒰.obj i').hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegR ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom)) =
      ((hc.pullbackFunctor (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom)).map (D.hom i i') ≫ (hc.pullbackCompComponentIso (𝒰.pr1 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i')).inv) ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') ≫ (𝒰.obj i').hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegR ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) :=
    (Category.assoc _ _ _).symm
  have e3 : ((hc.pullbackFunctor (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom)).map (D.hom i i') ≫ (hc.pullbackCompComponentIso (𝒰.pr1 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i')).inv) ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') ≫ (𝒰.obj i').hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegR ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) =
      ((hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') rfl hpr) ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) :=
    congrArg
      (fun kk ↦ kk ≫ (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom))
      h1037
  have e4 : ((hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') rfl hpr) ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) =
      (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') rfl hpr ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom)) :=
    Category.assoc _ _ _
  have e5 : (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') rfl hpr ≫
        (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom)) =
      (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ ((Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') rfl hpr ≫ Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL) ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) :=
    congrArg (fun kk ↦ (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ kk) (Category.assoc _ _ _).symm
  have e6 : (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ ((Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') rfl hpr ≫ Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr1 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) hpr hWlegL) ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) =
      (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegL ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) :=
    congrArg (fun kk ↦ (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ (kk ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom)) hco
  have e7 : (hc.pullbackCompComponentIso (𝒰.pr0 i i') (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom) (D.obj i)).inv ≫ (Pseudofunctor.DescentData'.pullHom' D.hom
            ((((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') ≫ (𝒰.obj i).hom)
            (((𝒱.overlapBaseChange 𝒰 i i').obj j).hom ≫ 𝒰.pr0 i i') (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) ≫ (φ.f j).left) rfl hWlegL ≫ (hc.pullbackCompComponentIso (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)) (D.obj (φ.α j))).hom) = (overlap_base_change_left_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D φ i i' j).hom :=
    hL.symm
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

-- After applying the overlap descent functor, the gluing obstruction is an equality of
-- the fixed `j`-components over `V_{ii'}`.  We keep this proof at the component level; the
-- comparison-isomorphism normalization is supplied by the descent-data cocycle and the local
-- preimage specification.
private theorem local_member_base_change_preimage_overlap_component_cancel
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
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i i' : 𝒰.index) (j : (𝒱.overlapBaseChange 𝒰 i i').index) :
    (((familyDescentFunctor hc (𝒱.overlapBaseChange 𝒰 i i')).map
        ((hc.pullbackFunctor (𝒰.pr0 i i')).map
            (local_member_base_change_preimage
              hc 𝒰 𝒱 φ θ i) ≫
          D₂.hom i i')).hom j) =
      (((familyDescentFunctor hc (𝒱.overlapBaseChange 𝒰 i i')).map
        (D₁.hom i i' ≫
          (hc.pullbackFunctor (𝒰.pr1 i i')).map
            (local_member_base_change_preimage
              hc 𝒰 𝒱 φ θ i'))).hom j) := by
  have hcore :
      (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
          ((hc.pullbackFunctor (𝒰.pr0 i i')).map
            (local_member_base_change_preimage
              hc 𝒰 𝒱 φ θ i)) ≫
        (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map (D₂.hom i i') =
      (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map (D₁.hom i i') ≫
        (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
          ((hc.pullbackFunctor (𝒰.pr1 i i')).map
            (local_member_base_change_preimage
              hc 𝒰 𝒱 φ θ i')) := by
    apply (cancel_mono
      (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₂ φ i i' j).hom).1
    let Mpre := (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
      ((hc.pullbackFunctor (𝒰.pr0 i i')).map
        (local_member_base_change_preimage
          hc 𝒰 𝒱 φ θ i))
    let Mpre' := (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map
      ((hc.pullbackFunctor (𝒰.pr1 i i')).map
        (local_member_base_change_preimage
          hc 𝒰 𝒱 φ θ i'))
    let MD₁ := (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map (D₁.hom i i')
    let MD₂ := (hc.pullbackFunctor ((𝒱.overlapBaseChange 𝒰 i i').obj j).hom).map (D₂.hom i i')
    let Λ₁ := (overlap_base_change_left_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₁ φ i i' j).hom
    let Λ₂ := (overlap_base_change_left_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₂ φ i i' j).hom
    let Ρ₁ := (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₁ φ i i' j).hom
    let Ρ₂ := (overlap_base_change_right_to_common_iso (p := p) (hc := hc) 𝒰 𝒱 D₂ φ i i' j).hom
    let W := (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom
      (𝒰.pr0 i i' ≫ (𝒰.obj i).hom))).map (θ.hom j)
    have hB₁ : MD₁ ≫ Ρ₁ = Λ₁ :=
      overlap_base_change_descent_hom_to_common (p := p) (hc := hc) 𝒰 𝒱 D₁ φ i i' j
    have hB₂ : MD₂ ≫ Ρ₂ = Λ₂ :=
      overlap_base_change_descent_hom_to_common (p := p) (hc := hc) 𝒰 𝒱 D₂ φ i i' j
    have hA : Mpre ≫ Λ₂ = Λ₁ ≫ W :=
      overlap_base_change_left_to_common_naturality (p := p) (hc := hc) 𝒰 𝒱 φ θ i i' j
    have hA' : Mpre' ≫ Ρ₂ = Ρ₁ ≫ W :=
      overlap_base_change_right_to_common_naturality (p := p) (hc := hc) 𝒰 𝒱 φ θ i i' j
    show (Mpre ≫ MD₂) ≫ Ρ₂ = (MD₁ ≫ Mpre') ≫ Ρ₂
    calc (Mpre ≫ MD₂) ≫ Ρ₂
        = Mpre ≫ MD₂ ≫ Ρ₂ := Category.assoc Mpre MD₂ Ρ₂
      _ = Mpre ≫ Λ₂ := congrArg (fun k ↦ Mpre ≫ k) hB₂
      _ = Λ₁ ≫ W := hA
      _ = (MD₁ ≫ Ρ₁) ≫ W := congrArg (fun k ↦ k ≫ W) hB₁.symm
      _ = MD₁ ≫ Ρ₁ ≫ W := Category.assoc MD₁ Ρ₁ W
      _ = MD₁ ≫ Mpre' ≫ Ρ₂ := congrArg (fun k ↦ MD₁ ≫ k) hA'.symm
      _ = (MD₁ ≫ Mpre') ≫ Ρ₂ := (Category.assoc MD₁ Mpre' Ρ₂).symm
  simp only [Pseudofunctor.DescentData'.comp_hom, familyDescentFunctor_map_hom,
    Functor.map_comp]
  exact hcore

/-- Helper for Lemma 8.3.7: after applying the faithful overlap descent functor, the gluing
compatibility reduces to equality of the fixed `j`-components. -/
private theorem local_member_base_change_preimage_overlap_compat
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
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂))
    (i i' : 𝒰.index) :
    (hc.pullbackFunctor (𝒰.pr0 i i')).map
        (local_member_base_change_preimage
          hc 𝒰 𝒱 φ θ i) ≫
      D₂.hom i i' =
    D₁.hom i i' ≫
      (hc.pullbackFunctor (𝒰.pr1 i i')).map
        (local_member_base_change_preimage
          hc 𝒰 𝒱 φ θ i') := by
  let F := familyDescentFunctor hc (𝒱.overlapBaseChange 𝒰 i i')
  letI : Functor.Faithful F := inferInstance
  -- Route correction: follow the source proof literally by moving to `DD(𝒱_{ii'})`, proving the
  -- equality componentwise there, and then reflecting back through overlap faithfulness.
  apply F.map_injective
  apply Pseudofunctor.DescentData'.hom_ext
  intro j
  -- The only remaining overlap work is the fixed-`j` component comparison isolated above.
  exact local_member_base_change_preimage_overlap_component_cancel
    hc 𝒰 𝒱 φ θ i i' j

/-- Helper for Lemma 8.3.7: gluing the local preimages produces the global morphism in
`DD(𝒰)` used in the fullness argument. -/
noncomputable def glued_local_member_base_change_preimage
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
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂)) :
    D₁ ⟶ D₂ where
  hom i :=
    local_member_base_change_preimage
      hc 𝒰 𝒱 φ θ i
  comm i i' :=
    local_member_base_change_preimage_overlap_compat
      hc 𝒰 𝒱 φ θ i i'

/-- Helper for Lemma 8.3.7: the glued preimage maps back to the original morphism `θ` under the
refinement pullback functor. -/
theorem glued_local_member_base_change_preimage_maps_to_theta
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
    (φ : 𝒱 ⟶ 𝒰)
    {D₁ D₂ : DescentDatum p hc 𝒰}
    (θ :
      ((pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).obj D₁) ⟶
        ((pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ)).obj D₂)) :
    (pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)).map
        (glued_local_member_base_change_preimage
          hc 𝒰 𝒱 φ θ) =
      θ := by
  let P :=
    pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)
  let η :=
    glued_local_member_base_change_preimage
      hc 𝒰 𝒱 φ θ
  -- Route correction: fix a single component `j`, transport the glued morphism through the same
  -- comparison isomorphisms as in the faithfulness proof, and cancel those isomorphisms there.
  apply Pseudofunctor.DescentData'.hom_ext
  intro j
  let i : 𝒰.index := φ.α j
  let e₁ := member_base_change_comparison_component_iso hc D₁ φ i j
  let e₂ := member_base_change_comparison_component_iso hc D₂ φ i j
  have hnat :
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
          ((P.map η).hom j) ≫ e₂.hom =
        e₁.hom ≫
          (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (η.hom i) := by
    -- The packaged comparison isomorphisms convert the refined component to the local component.
    simpa [P, η, i, e₁, e₂] using
      (member_base_change_comparison_component_naturality
        (p := p) (hc := hc) (D₁ := D₁) (D₂ := D₂) η φ i j)
  have hspec :
      (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (η.hom i) =
        e₁.inv ≫
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom j) ≫
          e₂.hom := by
    -- At the chosen index `i = φ.α j`, the glued morphism uses the local preimage specified
    -- earlier by full faithfulness on `DD(𝒱_i)`.
    simpa [η, i, e₁, e₂] using
      (local_member_base_change_preimage_component_spec
        hc 𝒰 𝒱 φ θ i j)
  have hcomp :
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
          ((P.map η).hom j) ≫ e₂.hom =
        (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
          (θ.hom j) ≫ e₂.hom := by
    -- Substitute the local preimage formula, then collapse the two comparison isomorphisms.
    let x :=
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom j)
    have hsubst :
        e₁.hom ≫
            (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (η.hom i) =
          e₁.hom ≫ (e₁.inv ≫ x ≫ e₂.hom) := by
      rw [hspec]
      rfl
    have hcancel : e₁.hom ≫ (e₁.inv ≫ x ≫ e₂.hom) = x ≫ e₂.hom := by
      rw [← Category.assoc e₁.hom e₁.inv (x ≫ e₂.hom), e₁.hom_inv_id]
      simpa [Category.assoc] using Category.id_comp (x ≫ e₂.hom)
    exact hnat.trans (hsubst.trans hcancel)
  have hfst :
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
          ((P.map η).hom j) =
        (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
          (θ.hom j) := by
    -- Cancel the right comparison isomorphism to reduce to equality after one pullback functor.
    exact (cancel_mono e₂.hom).1 hcomp
  -- The first pullback projection has the graph of the refinement arrow as a section, hence its
  -- chosen pullback functor is faithful.
  letI : Functor.Faithful
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)) :=
    pullbackFunctor_faithful_of_section (p := p) (hc := hc)
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
      (member_base_change_graph (𝒰 := 𝒰) (𝒱 := 𝒱) φ j)
      (by
        simpa [i] using member_base_change_graph_fst (𝒰 := 𝒰) (𝒱 := 𝒱) φ j)
  exact (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map_injective hfst

end CategoryTheory
