import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4
import StacksProject_2024.stacks_project.Chap13.Remark_13_34_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_10
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SequentialProObjectMorphismRep

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local notation "DAbSeq" => DerivedCategory AbSeq
local notation "H" => DerivedCategory.homologyFunctor AddCommGrpCat

/- Domain-style sampling for Lemma 15.87.13:
- primary domain: stagewise towers in `D(Ab)` attached to objects of `D(Ab(\mathbf N))`, viewed as
  sequential pro-objects;
- sampled owner declarations:
  `stagewiseAbelianGroupDerivedTowerFunctor`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`,
  `exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit`;
- best owner abstraction: the pro-object comparison should be owned by the Chapter 4/15 canonical
  representative type `SequentialProObjectMorphismRep` and its pro-morphism
  `(ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom`, not by a
  parallel local wrapper;
- primitive data: the stagewise towers
  `stagewiseAbelianGroupDerivedTower E` and `stagewiseAbelianGroupDerivedTower D`;
- derived API: the canonical stagewise tower functor
  `stagewiseAbelianGroupDerivedTowerFunctor`, the strict identity-reindex representative induced by
  `φ`, and the resulting morphism between the associated sequential pro-objects.

Source/core/bridge triage:
- `source-facing`: the theorem that a stagewise pro-isomorphism induces an isomorphism on `R lim`;
- `core/canonical`: `IsDerivedLimit` for the stagewise towers and `SequentialProObjectMorphismRep`
  together with `.toProObjectHom`;
- `bridge/view`: the canonical identity-reindex representative
  `ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)`. -/
-- Proof sketch: Lemma 15.87.9 identifies `R lim(E)` and `R lim(D)` with derived limits of the
-- stagewise towers `(E_n)` and `(D_n)`. Applying the Milnor short exact sequences of
-- Lemma 15.87.10 together with the pro-isomorphism invariance of `\varprojlim` and
-- `R^1 \!\varprojlim` from Lemma 15.87.4 shows that the induced map on every cohomology object is
-- an isomorphism, hence the canonical map on derived inverse limits is an isomorphism in
-- `D(\operatorname{Ab})`.
/-- Lemma 15.87.13: if a morphism `E ⟶ D` in `D(\operatorname{Ab}(\mathbf N))` induces an
isomorphism of the associated stagewise pro-objects `(E_n) ⟶ (D_n)` in
`D(\operatorname{Ab})`, then the induced morphism `R lim(E) ⟶ R lim(D)` is an isomorphism in
`D(\operatorname{Ab})`. -/
/-- Helper for Lemma 15.87.13: the pro-object morphism represented by a composite representative
is the composite of the represented pro-object morphisms. -/
private theorem compRep_toProObjectHom
    {C : Type*} [Category C]
    {X Y Z : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    (compRep r s).toProObjectHom = r.toProObjectHom ≫ s.toProObjectHom := by
  -- Proof comment: both morphisms are represented by the same stagewise composites
  -- `r.map (s.reindex n) ≫ s.map n`, so their Hom-colimit classes agree levelwise.
  ext W x
  rfl

/-- Helper for Lemma 15.87.13: if the pro-object morphism induced by a natural transformation is
an isomorphism, then the corresponding sequential representative is a pro-isomorphism. -/
private theorem ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom
    {C : Type*} [Category C]
    {X Y : ℕᵒᵖ ⥤ C} (α : X ⟶ Y)
    (hαIso : IsIso (ofNatTrans α).toProObjectHom) :
    (ofNatTrans α).IsProIsomorphism := by
  -- Proof comment: choose a representative of the inverse pro-morphism and compare both
  -- composites with the identity representative through the Chapter 4 equivalence relation.
  let η := (ofNatTrans α).toProObjectHom
  rcases exists_representative (inv η) with ⟨s, hs⟩
  refine ⟨s, ?_, ?_⟩
  · -- Proof comment: the chosen representative of `inv η` is a left inverse in the pro-category.
    apply (represents_eq_iff_equivalent (compRep (ofNatTrans α) s) (idRep X)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.hom_inv_id η
  · -- Proof comment: the same representative is also a right inverse in the pro-category.
    apply (represents_eq_iff_equivalent (compRep s (ofNatTrans α)) (idRep Y)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.inv_hom_id η

/-- Helper for Lemma 15.87.13: a representative-level pro-isomorphism induces an isomorphism of
the associated pro-object morphism. -/
private theorem isIso_toProObjectHom_of_isProIsomorphism
    {C : Type*} [Category C]
    {X Y : ℕᵒᵖ ⥤ C} (r : SequentialProObjectMorphismRep X Y)
    (hr : r.IsProIsomorphism) :
    IsIso r.toProObjectHom := by
  -- Proof comment: pro-isomorphism gives bijectivity on every Hom-colimit evaluation, and those
  -- pointwise bijections assemble to an isomorphism of functors.
  letI : ∀ Z : C, IsIso (r.toProObjectHom.app Z) := fun Z ↦
    (CategoryTheory.isIso_iff_bijective (r.toProObjectHom.app Z)).2
      (SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective hr Z)
  exact NatIso.isIso_of_isIso_app r.toProObjectHom

/-- Helper for Lemma 15.87.13: applying a functor to the level maps of a sequential representative
produces the corresponding representative between the whiskered towers. -/
private theorem mapRep_naturality
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    {X Y : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y) :
    ∀ ⦃n n' : ℕ⦄ (g : op n ⟶ op n'),
      (F.map (((r.reindex.toFunctor.op ⋙ X).map g))) ≫ F.map (r.hom.app (op n')) =
        F.map (r.hom.app (op n)) ≫ F.map (Y.map g) := by
  intro n n' g
  -- Proof comment: the mapped naturality square is just `Functor.map` applied to the original
  -- naturality relation of `r.hom`.
  simpa [Functor.map_comp] using congrArg (fun t ↦ F.map t) (r.hom.naturality g)

/-- Helper for Lemma 15.87.13: a sequential representative may be transported through any functor
by mapping all of its level maps. -/
private def mapRep
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    {X Y : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y) :
    SequentialProObjectMorphismRep (X ⋙ F) (Y ⋙ F) where
  reindex := r.reindex
  hom :=
    { app := fun n ↦ F.map (r.hom.app n)
      naturality := mapRep_naturality F r }

/-- Helper for Lemma 15.87.13: applying a functor to a pro-isomorphism representative preserves
the representative-level inverse data. -/
private theorem mapRep_isProIsomorphism
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    {X Y : ℕᵒᵖ ⥤ C}
    {r : SequentialProObjectMorphismRep X Y}
    (hr : r.IsProIsomorphism) :
    (mapRep F r).IsProIsomorphism := by
  rcases hr with ⟨s, hs_left, hs_right⟩
  refine ⟨mapRep F s, ?_, ?_⟩
  · rcases hs_left with ⟨reindex', h₁, h₂, hmaps⟩
    refine ⟨reindex', h₁, h₂, ?_⟩
    intro n
    -- Proof comment: the common-refinement equalities are preserved after applying `F` to every
    -- stage map of the original inverse witness.
    simpa [mapRep, SequentialProObjectMorphismRep.map, Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ F.map t) (hmaps n)
  · rcases hs_right with ⟨reindex', h₁, h₂, hmaps⟩
    refine ⟨reindex', h₁, h₂, ?_⟩
    intro n
    -- Proof comment: the right-inverse refinement identities are preserved for the same reason.
    simpa [mapRep, SequentialProObjectMorphismRep.map, Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ F.map t) (hmaps n)

/-- Helper for Lemma 15.87.13: mapping `ofNatTrans α` through a functor represents the same
pro-object morphism as the representative built directly from the whiskered natural
transformation. -/
private theorem mapRep_ofNatTrans_toProObjectHom_eq
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    {X Y : ℕᵒᵖ ⥤ C}
    (α : X ⟶ Y) :
    (mapRep F (ofNatTrans α)).toProObjectHom =
      (ofNatTrans (Functor.whiskerRight α F)).toProObjectHom := by
  -- Proof comment: both representatives have identity reindexing and the same level maps after
  -- applying `F`, so they are equivalent through the trivial common refinement.
  apply (represents_eq_iff_equivalent
    (mapRep F (ofNatTrans α))
    (ofNatTrans (Functor.whiskerRight α F))).2
  refine ⟨OrderHom.id, ?_, ?_, ?_⟩
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n
    simp [mapRep, SequentialProObjectMorphismRep.map]

/-- Helper for Lemma 15.87.13: the stagewise pro-isomorphism hypothesis remains true after
applying degree-`p` cohomology to the stagewise tower map. -/
private theorem stagewise_homology_toProObjectHom_isIso
    {E D : DAbSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom)
    (p : ℤ) :
    IsIso
      (ofNatTrans
        (Functor.whiskerRight
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
          (H p))).toProObjectHom := by
  let r :
      SequentialProObjectMorphismRep
        (stagewiseAbelianGroupDerivedTower E)
        (stagewiseAbelianGroupDerivedTower D) :=
    ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
  let rH :
      SequentialProObjectMorphismRep
        (stagewiseAbelianGroupDerivedTower E ⋙ H p)
        (stagewiseAbelianGroupDerivedTower D ⋙ H p) :=
    mapRep (H p) r
  have hr : r.IsProIsomorphism := by
    -- Proof comment: the given hypothesis says exactly that the canonical stagewise
    -- representative becomes invertible in the pro-category.
    simpa [r] using
      ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ) hφ
  have hrH : rH.IsProIsomorphism := by
    -- Proof comment: degreewise cohomology preserves the representative-level inverse data.
    simpa [rH] using mapRep_isProIsomorphism (H p) hr
  have hrHIso : IsIso rH.toProObjectHom :=
    isIso_toProObjectHom_of_isProIsomorphism rH hrH
  have hcompare :
      rH.toProObjectHom =
        (ofNatTrans
          (Functor.whiskerRight
            (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
            (H p))).toProObjectHom := by
    -- Proof comment: `rH` is exactly the representative obtained by whiskering the original
    -- stagewise map with `H^p`.
    simpa [r, rH] using
      mapRep_ofNatTrans_toProObjectHom_eq
        (H p)
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
  rw [← hcompare]
  exact hrHIso

/-- Helper for Lemma 15.87.13: the stagewise map induced by `φ` on the Milnor product terms is
the product of the component maps on the stagewise derived towers. -/
private abbrev stagewise_product_map
    {E D : DAbSeq} (φ : E ⟶ D) :
    ∏ᶜ inverseSystemFamily (stagewiseAbelianGroupDerivedTower E) ⟶
      ∏ᶜ inverseSystemFamily (stagewiseAbelianGroupDerivedTower D) :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n ≫
      (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n)

/-- Helper for Lemma 15.87.13: postcomposing the stagewise product map with a projection reads off
the corresponding stagewise component map. -/
private theorem stagewise_product_map_π
    {E D : DAbSeq} (φ : E ⟶ D) (n : ℕ) :
    stagewise_product_map φ ≫
        Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n =
      Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n ≫
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) := by
  -- Proof comment: the product map was defined by `Pi.lift`, so each projection is immediate.
  rw [stagewise_product_map, Pi.lift_π]

/-- Helper for Lemma 15.87.13: the product-level comparison attached to `φ` commutes with the
Milnor difference maps of the two stagewise derived towers. -/
private theorem stagewise_product_map_commutes_milnor_difference
    {E D : DAbSeq} (φ : E ⟶ D) :
    CommSq
      (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E))
      (stagewise_product_map φ)
      (stagewise_product_map φ)
      (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower D)) := by
  -- Proof comment: compare both composites after projection to each stage and use the naturality
  -- of the stagewise tower map to identify the successor terms.
  refine CommSq.mk ?_
  apply Pi.hom_ext
  intro n
  calc
    ((derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E)) ≫
        stagewise_product_map φ) ≫
        Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n =
      (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E)) ≫
        (Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n ≫
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n)) := by
            rw [Category.assoc, stagewise_product_map_π]
    _ =
      ((derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E)) ≫
          Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n) ≫
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) := by
            simp [Category.assoc]
    _ =
      (Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n -
          Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) (n + 1) ≫
            (stagewiseAbelianGroupDerivedTower E).transitionMap (Nat.le_succ n)) ≫
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) := by
            rw [derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n ≫
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) -
        (Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) (n + 1) ≫
            (stagewiseAbelianGroupDerivedTower E).transitionMap (Nat.le_succ n)) ≫
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) := by
            rw [Preadditive.sub_comp]
            simp [Category.assoc]
    _ =
      Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n ≫
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) -
        Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) (n + 1) ≫
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op (n + 1)) ≫
            (stagewiseAbelianGroupDerivedTower D).transitionMap (Nat.le_succ n) := by
            congr 1
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) (n + 1) ≫ t)
                ((stagewiseAbelianGroupDerivedTowerFunctor.map φ).naturality
                  ((homOfLE (Nat.le_succ n)).op))
    _ =
      (stagewise_product_map φ ≫
          Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n) -
        (stagewise_product_map φ ≫
            Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) (n + 1)) ≫
          (stagewiseAbelianGroupDerivedTower D).transitionMap (Nat.le_succ n) := by
            rw [stagewise_product_map_π, stagewise_product_map_π]
    _ =
      stagewise_product_map φ ≫
        ((Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n) -
            Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) (n + 1) ≫
              (stagewiseAbelianGroupDerivedTower D).transitionMap (Nat.le_succ n)) := by
            rw [Preadditive.comp_sub]
            simp [Category.assoc]
    _ =
      stagewise_product_map φ ≫
        derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower D) ≫
          Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n := by
            rw [derivedLimitDifferenceMap_comp_π]
    _ =
      (stagewise_product_map φ ≫
          derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower D)) ≫
        Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n := by
            simp [Category.assoc]

/-- Helper for Lemma 15.87.13: the owner-level inverse-limit map on the degree-`p` homology tower
agrees with the representative-level map obtained by applying `H^p` stagewise. -/
private theorem stagewise_homology_inducedLimitMap_eq_limitMap
    {E D : DAbSeq} (φ : E ⟶ D) (p : ℤ) :
    CategoryTheory.inducedLimitMap
      ((ofNatTrans
          (Functor.whiskerRight
            (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
            (H p))).toProObjectHom) =
        (mapRep
          (H p)
          (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ))).limitMap := by
  -- Proof comment: the owner map may be computed using any representative of the same
  -- pro-morphism, and `mapRep` is exactly the representative obtained by whiskering with `H^p`.
  simpa using
    (CategoryTheory.inducedLimitMap_eq_limitMap
      (mapRep
        (H p)
        (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)))
      (mapRep_ofNatTrans_toProObjectHom_eq
        (H p)
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ)))

/-- Helper for Lemma 15.87.13: the owner-level `R^1 \!\varprojlim` map on the degree-`p-1`
homology tower agrees with the representative-level map obtained by applying `H^{p-1}`
stagewise. -/
private theorem stagewise_homology_inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
    {E D : DAbSeq} (φ : E ⟶ D) (p : ℤ) :
    CategoryTheory.inducedFirstDerivedLimitMap
      ((ofNatTrans
          (Functor.whiskerRight
            (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
            (H (p - 1)))).toProObjectHom) =
        (mapRep
          (H (p - 1))
          (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ))).firstDerivedLimitMap := by
  -- Proof comment: the same representative-independence argument computes the induced
  -- `R^1 \!\varprojlim` map using the whiskered representative in degree `p - 1`.
  simpa using
    (CategoryTheory.inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
      (mapRep
        (H (p - 1))
        (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)))
      (mapRep_ofNatTrans_toProObjectHom_eq
        (H (p - 1))
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ)))

/-- Helper for Lemma 15.87.13: the ordinary inverse-limit functor has its canonical projection to
the `n`-th stage. -/
private abbrev inverse_limit_projection (n : ℕ) :
    (lim : AbSeq ⥤ AddCommGrpCat) ⟶
      (evaluation ℕᵒᵖ AddCommGrpCat).obj (op n) where
  app K := limit.π K (op n)
  naturality := by
    intro K L φ
    -- Proof comment: naturality of the limit cone is exactly the functoriality of the inverse-
    -- limit projection to stage `n`.
    simpa using limit.pre_π (F := K) (α := φ) (j := op n)

/-- Helper for Lemma 15.87.13: the canonical map from `R lim(K)` to the `n`-th stage of the
stagewise derived tower is the right-derived image of the ordinary limit projection. -/
private abbrev derived_inverse_limit_toStageNatTrans (n : ℕ) :
    (additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)) ⟶
      ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)).mapDerivedCategory :=
  Functor.rightDerivedNatTrans
    (additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat))
    (((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)).mapDerivedCategory)
    ((lim : AbSeq ⥤ AddCommGrpCat).mapDerivedCategoryFactors.inv)
    (((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)).mapDerivedCategoryFactors.inv)
    (HomologicalComplex.quasiIso AbSeq (ComplexShape.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        (inverse_limit_projection n)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- Helper for Lemma 15.87.13: the canonical derived inverse-limit object maps functorially to
each stage of the stagewise tower. -/
private abbrev derived_inverse_limit_toStage
    (K : DAbSeq) (n : ℕ) :
    (R lim(K)) ⟶
      (stagewiseAbelianGroupDerivedTower K).obj (op n) :=
  (derived_inverse_limit_toStageNatTrans n).app K

/-- Helper for Lemma 15.87.13: the canonical stage projections of `R lim` are natural in
`K ∈ D(\operatorname{Ab}(\mathbf N))`. -/
private theorem derived_inverse_limit_toStage_naturality
    {E D : DAbSeq} (φ : E ⟶ D) (n : ℕ) :
    ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) ≫
        derived_inverse_limit_toStage D n =
      derived_inverse_limit_toStage E n ≫
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) := by
  -- Proof comment: this is the naturality of the right-derived transformation built from the
  -- ordinary inverse-limit projection.
  simpa [derived_inverse_limit_toStage, derived_inverse_limit_toStageNatTrans,
    stagewiseAbelianGroupDerivedTowerFunctor, stagewiseAbelianGroupDerivedTower] using
    (derived_inverse_limit_toStageNatTrans n).naturality φ

/-- Helper for Lemma 15.87.13: the chosen Milnor product map for `R lim(K)` should use the
canonical stage projections of the right-derived inverse-limit functor. -/
private theorem canonical_stagewise_milnor_withMap
    (K : DAbSeq) :
    HasMilnorTriangle.WithMap
      (stagewiseAbelianGroupDerivedTower K)
      (Pi.lift fun n ↦ derived_inverse_limit_toStage K n) := sorry

/-- Helper for Lemma 15.87.13: after freezing the Milnor triangles for `R lim(E)` and
`R lim(D)` using the canonical stage projections, the stagewise product map extends to a morphism
of those distinguished triangles whose first component is the canonical map on `R lim`. -/
private theorem canonical_stagewise_milnor_triangle_naturality
    {E D : DAbSeq} (φ : E ⟶ D) :
    ∃ (δE :
        ∏ᶜ inverseSystemFamily (stagewiseAbelianGroupDerivedTower E) ⟶
          (R lim(E))⟦(1 : ℤ)⟧)
      (hE :
        Triangle.mk
            (Pi.lift fun n ↦ derived_inverse_limit_toStage E n)
            (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E))
            δE ∈
          distTriang (DerivedCategory AddCommGrpCat))
      (δD :
        ∏ᶜ inverseSystemFamily (stagewiseAbelianGroupDerivedTower D) ⟶
          (R lim(D))⟦(1 : ℤ)⟧)
      (hD :
        Triangle.mk
            (Pi.lift fun n ↦ derived_inverse_limit_toStage D n)
            (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower D))
            δD ∈
          distTriang (DerivedCategory AddCommGrpCat))
      (ψ :
        Triangle.mk
            (Pi.lift fun n ↦ derived_inverse_limit_toStage E n)
            (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E))
            δE ⟶
          Triangle.mk
            (Pi.lift fun n ↦ derived_inverse_limit_toStage D n)
            (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower D))
            δD),
      ψ.hom₁ =
          ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) ∧
        ψ.hom₂ = stagewise_product_map φ := by
  let ιE :
      (R lim(E)) ⟶
        ∏ᶜ inverseSystemFamily (stagewiseAbelianGroupDerivedTower E) :=
    Pi.lift fun n ↦ derived_inverse_limit_toStage E n
  let ιD :
      (R lim(D)) ⟶
        ∏ᶜ inverseSystemFamily (stagewiseAbelianGroupDerivedTower D) :=
    Pi.lift fun n ↦ derived_inverse_limit_toStage D n
  rcases canonical_stagewise_milnor_withMap E with ⟨δE, hE⟩
  rcases canonical_stagewise_milnor_withMap D with ⟨δD, hD⟩
  have hι :
      ιE ≫ stagewise_product_map φ =
        ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) ≫ ιD := by
    -- Proof comment: compare both product maps after every projection and use the stagewise
    -- naturality of the derived inverse-limit projections.
    apply Pi.hom_ext
    intro n
    calc
      (ιE ≫ stagewise_product_map φ) ≫
          Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n =
        ιE ≫
          (Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n ≫
            (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n)) := by
              rw [Category.assoc, stagewise_product_map_π]
      _ =
        (ιE ≫ Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower E)) n) ≫
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) := by
              simp [Category.assoc]
      _ =
        derived_inverse_limit_toStage E n ≫
          (stagewiseAbelianGroupDerivedTowerFunctor.map φ).app (op n) := by
              rw [ιE, Pi.lift_π]
      _ =
        ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) ≫
          derived_inverse_limit_toStage D n := by
              rw [derived_inverse_limit_toStage_naturality]
      _ =
        ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) ≫
          (ιD ≫ Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n) := by
              rw [ιD, Pi.lift_π]
      _ =
        (((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) ≫ ιD) ≫
          Pi.π (inverseSystemFamily (stagewiseAbelianGroupDerivedTower D)) n := by
              simp [Category.assoc]
  obtain ⟨ψ₃, hψ₂, hψ₃⟩ :=
    complete_distinguished_triangle_morphism
      (Triangle.mk
        ιE
        (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E))
        δE)
      (Triangle.mk
        ιD
        (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower D))
        δD)
      hE
      hD
      ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ)
      (stagewise_product_map φ)
      hι
  let ψ :
      Triangle.mk
          ιE
          (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower E))
          δE ⟶
        Triangle.mk
          ιD
          (derivedLimitDifferenceMap (stagewiseAbelianGroupDerivedTower D))
          δD :=
    Triangle.homMk
      _ _ _
      (stagewise_product_map φ)
      ψ₃
      hι
      hψ₂
      hψ₃
  exact ⟨δE, hE, δD, hD, ψ, rfl, rfl⟩

/-- Helper for Lemma 15.87.13: there exist chosen Milnor short exact rows for `E` and `D` that
are connected by the canonical cohomology map induced by the stagewise tower morphism. -/
private theorem milnor_shortExact_naturality_of_stagewise_map
    {E D : DAbSeq} (φ : E ⟶ D) (p : ℤ) :
    ∃ (ιE :
      SequentialInverseSystem.firstDerivedLimit
        (stagewiseAbelianGroupDerivedTower E ⋙ H (p - 1)) ⟶
          (H p).obj (R lim(E)))
      (πE :
      (H p).obj (R lim(E)) ⟶
        limit (stagewiseAbelianGroupDerivedTower E ⋙ H p))
      (hE : ιE ≫ πE = 0)
      (hshortE : (ShortComplex.mk ιE πE hE).ShortExact)
      (ιD :
      SequentialInverseSystem.firstDerivedLimit
        (stagewiseAbelianGroupDerivedTower D ⋙ H (p - 1)) ⟶
          (H p).obj (R lim(D)))
      (πD :
      (H p).obj (R lim(D)) ⟶
        limit (stagewiseAbelianGroupDerivedTower D ⋙ H p))
      (hD : ιD ≫ πD = 0)
      (hshortD : (ShortComplex.mk ιD πD hD).ShortExact)
      (ψ : (ShortComplex.mk ιE πE hE) ⟶ (ShortComplex.mk ιD πD hD)),
      ψ.τ₁ =
        CategoryTheory.inducedFirstDerivedLimitMap
          ((ofNatTrans
              (Functor.whiskerRight
                (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
                (H (p - 1)))).toProObjectHom) ∧
      ψ.τ₂ =
        ((H p).map
          ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ)) ∧
      ψ.τ₃ =
        CategoryTheory.inducedLimitMap
          ((ofNatTrans
              (Functor.whiskerRight
                (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
                (H p))).toProObjectHom) := by
  rcases canonical_stagewise_milnor_triangle_naturality φ with
    ⟨δE, hE, δD, hD, ψT, hψT₁, hψT₂⟩
  let _ := hE
  let _ := hD
  let _ := ψT
  let _ := hψT₁
  let _ := hψT₂
  -- Route correction: the old interface quantified over arbitrary existential Milnor witnesses,
  -- which loses the functorial control needed for the canonical map `((R lim).map φ)`. The
  -- canonical triangle morphism with first component `((R lim).map φ)` is now fixed; only the
  -- row extraction from the two Milnor triangles remains.
  -- TODO: apply `H p` and `H (p - 1)` to `ψT`, read off the degree-`p` short exact ladder from
  -- the two exact sequences attached to `hE` and `hD`, use `hψT₁` to identify the middle
  -- vertical arrow with
  -- `((H p).map ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ))`, and
  -- rewrite the outer arrows via
  -- `stagewise_homology_inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap` and
  -- `stagewise_homology_inducedLimitMap_eq_limitMap`.
  sorry

/-- Helper for Lemma 15.87.13: once the two Milnor short exact sequences are compared in degree
`p`, the cohomology map of the canonical derived inverse-limit morphism is an isomorphism. -/
private theorem homology_map_isIso_of_stagewise_proIsomorphism
    {E D : DAbSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom)
    (p : ℤ) :
    IsIso
      ((H p).map
        ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ)) := by
  -- Route correction: the source proof must compare the two Milnor short exact sequences for the
  -- chosen maps `R lim(E) -> lim H^p(E_n)` and `R lim(D) -> lim H^p(D_n)` rather than switch to
  -- the non-canonical existence theorem from Lemma `15.87.6`.
  let ηprev :
      colimit ((stagewiseAbelianGroupDerivedTower D ⋙ H (p - 1)).op ⋙ uliftCoyoneda.{0}) ⟶
        proSystemHomColimitFunctor (stagewiseAbelianGroupDerivedTower E ⋙ H (p - 1)) ⋙
          uliftFunctor.{0} :=
    (ofNatTrans
      (Functor.whiskerRight
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
        (H (p - 1)))).toProObjectHom
  let ηcurr :
      colimit ((stagewiseAbelianGroupDerivedTower D ⋙ H p).op ⋙ uliftCoyoneda.{0}) ⟶
        proSystemHomColimitFunctor (stagewiseAbelianGroupDerivedTower E ⋙ H p) ⋙
          uliftFunctor.{0} :=
    (ofNatTrans
      (Functor.whiskerRight
        (stagewiseAbelianGroupDerivedTowerFunctor.map φ)
        (H p))).toProObjectHom
  have hηprev : IsIso ηprev :=
    stagewise_homology_toProObjectHom_isIso φ hφ (p - 1)
  have hηcurr : IsIso ηcurr :=
    stagewise_homology_toProObjectHom_isIso φ hφ p
  let _ := hηprev
  let _ := hηcurr
  have houter₁ :
      IsIso (CategoryTheory.inducedFirstDerivedLimitMap ηprev) := by
    exact
      (CategoryTheory.inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso
        (η := ηprev)).2
  have houter₃ :
      IsIso (CategoryTheory.inducedLimitMap ηcurr) := by
    exact
      (CategoryTheory.inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso
        (η := ηcurr)).1
  let hlimE :
      IsDerivedLimit
        (stagewiseAbelianGroupDerivedTower E)
        (R lim(E)) :=
    abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation E
  let hlimD :
      IsDerivedLimit
        (stagewiseAbelianGroupDerivedTower D)
        (R lim(D)) :=
    abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation D
  rcases milnor_shortExact_naturality_of_stagewise_map
      φ p with
    ⟨ιE, πE, hE, hshortE, ιD, πD, hD, hshortD, ψ, hψ₁, hψ₂, hψ₃⟩
  let _ := hlimE
  let _ := hlimD
  haveI : IsIso ψ.τ₁ := by
    rw [hψ₁]
    exact houter₁
  haveI : IsIso ψ.τ₃ := by
    rw [hψ₃]
    exact houter₃
  have hmiddle : IsIso ψ.τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ hshortE hshortD
  simpa [hψ₂] using hmiddle

theorem isIso_map_derivedInverseLimit_of_stagewise_proIsomorphism
    {E D : DAbSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom) :
    IsIso ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) := by
  -- Proof comment: detect isomorphisms in `D(Ab)` on every cohomology object and reduce the
  -- source theorem to the degreewise Milnor comparison.
  rw [CategoryTheory.derivedCategory_isIso_iff_homology_map_isIso]
  intro p
  -- Proof comment: degree `p` is handled by comparing the two Milnor short exact sequences in
  -- cohomology and using the outer isomorphisms induced by the stagewise pro-isomorphism.
  exact homology_map_isIso_of_stagewise_proIsomorphism φ hφ p
