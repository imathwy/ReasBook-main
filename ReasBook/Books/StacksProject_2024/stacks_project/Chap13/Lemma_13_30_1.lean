import Mathlib
import StacksProject_2024.stacks_project.Chap04.Remark_4_27_7
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open ComplexShape
open Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

private theorem mapHomologicalComplex_id_map
    {K L : HomologicalComplex C (up ℤ)} (f : K ⟶ L) :
    ((𝟭 C).mapHomologicalComplex (up ℤ)).map f = f := by
  ext i
  simp

private theorem mapHomotopyCategory_id_map
    {K L : HomotopyCategory C (up ℤ)} (f : K ⟶ L) :
    ((𝟭 C).mapHomotopyCategory (up ℤ)).map f = f := by
  rw [← HomotopyCategory.quotient_map_out f]
  change
    (HomotopyCategory.quotient C (up ℤ)).map (((𝟭 C).mapHomologicalComplex (up ℤ)).map f.out) =
      (HomotopyCategory.quotient C (up ℤ)).map f.out
  rw [mapHomologicalComplex_id_map C f.out]
  rfl

/-- Applying `mapHomotopyCategory` to the identity additive functor yields the identity functor on
the homotopy category. -/
noncomputable def mapHomotopyCategoryIdIso :
    (𝟭 C).mapHomotopyCategory (up ℤ) ≅ 𝟭 (HomotopyCategory C (up ℤ)) :=
  NatIso.ofComponents (fun K ↦ Iso.refl K) (by
    intro K L f
    change ((𝟭 C).mapHomotopyCategory (up ℤ)).map f ≫ 𝟙 L = 𝟙 K ≫ f
    rw [mapHomotopyCategory_id_map C f]
    exact (Category.comp_id f).trans (Category.id_comp f).symm)

end

end Functor

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  {S : MorphismProperty D} {S' : MorphismProperty D'}
  {F : D ⥤ D'} {G : D' ⥤ D}

namespace MorphismProperty

open CategoryTheory.Limits
open CategoryTheory.MorphismProperty.LeftFraction
open Opposite

/-- Helper for Lemma 13.30.1: a left fraction in the localization is the numerator followed by
the canonical localization map of that fraction. -/
theorem left_fraction_homMk_eq
    (W : MorphismProperty D) [W.HasLeftCalculusOfFractions]
    {X Y Y' : D} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    LeftFraction.Localization.homMk (LeftFraction.mk f s hs) =
      (LeftFraction.mk f s hs).map (Localization.Q W)
        (Localization.inverts (Localization.Q W) W) := by
  -- Proof comment: normalize `homMk` to the owner-level fraction map used by the localization.
  simpa using LeftFraction.Localization.homMk_eq (LeftFraction.mk f s hs)

end MorphismProperty

/- Domain-style sampling:
- primary domain: pointwise left/right derived values along localization functors, together with
  the Hom-set comparison induced by an underived adjunction;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `CategoryTheory.rightDerivedValue`,
  `CategoryTheory.leftDerivedValue`,
  `Adjunction.homEquiv`;
- owner abstraction:
  `source-facing`: the Stacks lemma compares the localized Hom-sets attached to the chosen
    pointwise derived values at `K` and `M`;
  `core/canonical`: the project owners `rightDerivedValue` / `leftDerivedValue` built on the
    mathlib pointwise derived-functor API, together with the underived adjunction owner
    `Adjunction.homEquiv`;
  `bridge/view`: the owner introduced in this file,
    `Adjunction.pointwiseDerivedHomEquiv`, built directly from those canonical ingredients.

Primitive data are exactly the adjunction `adj : G ⊣ F` and the pointwise derivability hypotheses
at the two chosen objects. The Hom-set equivalence is derived API, so this file should expose that
equivalence directly rather than through a second public wrapper family. We keep this source-facing
bridge instead of collapsing it to `Adjunction.derived`, because that functor-level owner requires
stronger absolute-derived hypotheses and would change the local source semantics.
-/

-- Proof sketch: express `Hom_{(S')⁻¹D'}(M, RF(K))` and `Hom_{S⁻¹D}(LG(M), K)` using the
-- pointwise right/left derived-value constructions together with the localization Hom-colimit
-- formulas from Chapter 4. Then commute the two colimits, apply the underived adjunction
-- `adj.homEquiv` termwise, and transport the result back to the localized Hom-sets.
namespace Adjunction

open CategoryTheory
open CategoryTheory.Limits

/-- An adjunction `G ⊣ F` induces an adjunction on homological complexes of any fixed shape. -/
noncomputable def mapHomologicalComplex
    {C : Type u₁} {D : Type u₂} {ι : Type*}
    [Category.{v₁} C] [Category.{v₂} D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    {F : C ⥤ D} {G : D ⥤ C}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (adj : G ⊣ F) (c : ComplexShape ι) :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c :=
  Adjunction.mkOfUnitCounit <|
    Adjunction.CoreUnitCounit.mk
      ((Functor.mapHomologicalComplexIdIso D c).inv ≫
        NatTrans.mapHomologicalComplex adj.unit c)
      (NatTrans.mapHomologicalComplex adj.counit c ≫
        (Functor.mapHomologicalComplexIdIso C c).hom)
      (by
        ext M i
        simp)
      (by
        ext K i
        simp)

/-- Helper for Lemma 13.30.1: a homotopy between maps into `K` transports across the Hom-equivalence
of `adj.mapHomologicalComplex`. -/
private theorem homotopy_mapHomologicalComplex_homEquiv
    {C : Type u₁} {D : Type u₂} {ι : Type*}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [G.Additive]
    (adj : G ⊣ F) (c : ComplexShape ι)
    {L : HomologicalComplex D c} {K : HomologicalComplex C c}
    {f g : (G.mapHomologicalComplex c).obj L ⟶ K} (h : Homotopy f g) :
    Nonempty
      (Homotopy
        (((adj.mapHomologicalComplex c).homEquiv L K) f)
        (((adj.mapHomologicalComplex c).homEquiv L K) g)) := by
  -- Proof comment: map the given homotopy across `F`, then postcompose with the unit of the
  -- lifted adjunction to recover the Hom-equivalence formula.
  letI : F.Additive := adj.right_adjoint_additive
  refine ⟨?_⟩
  simpa [Adjunction.homEquiv_unit] using
    (F.mapHomotopy h).compLeft ((adj.mapHomologicalComplex c).unit.app L)

/-- Helper for Lemma 13.30.1: a homotopy between maps out of `L` transports across the inverse
Hom-equivalence of `adj.mapHomologicalComplex`. -/
private theorem homotopy_mapHomologicalComplex_homEquiv_symm
    {C : Type u₁} {D : Type u₂} {ι : Type*}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.Additive]
    (adj : G ⊣ F) (c : ComplexShape ι)
    {L : HomologicalComplex D c} {K : HomologicalComplex C c}
    {f g : L ⟶ (F.mapHomologicalComplex c).obj K} (h : Homotopy f g) :
    Nonempty
      (Homotopy
        (((adj.mapHomologicalComplex c).homEquiv L K).symm f)
        (((adj.mapHomologicalComplex c).homEquiv L K).symm g)) := by
  -- Proof comment: dually, map the homotopy across `G` and postcompose with the lifted counit.
  letI : G.Additive := adj.left_adjoint_additive
  refine ⟨?_⟩
  simpa [Adjunction.homEquiv_counit] using
    (G.mapHomotopy h).compRight ((adj.mapHomologicalComplex c).counit.app K)

/-- Helper for Lemma 13.30.1: two chain maps have the same image in the homotopy category exactly
when they are homotopic. -/
private theorem quotient_map_eq_iff_homotopy
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} {f g : K ⟶ L} :
    (HomotopyCategory.quotient C c).map f = (HomotopyCategory.quotient C c).map g ↔
      Nonempty (Homotopy f g) := by
  constructor
  · intro hfg
    have hzero : (HomotopyCategory.quotient C c).map (f - g) = 0 := by
      simpa [Functor.map_sub, hfg] using sub_eq_zero.mpr hfg
    rcases (HomotopyCategory.quotient_map_eq_zero_iff (f - g)).1 hzero with ⟨h⟩
    refine ⟨?_⟩
    -- Proof comment: add back the identity homotopy on `g` to convert a null-homotopy of
    -- `f - g` into a homotopy from `f` to `g`.
    simpa [sub_eq_add_neg, add_assoc] using Homotopy.add h (Homotopy.refl g)
  · rintro ⟨h⟩
    exact HomotopyCategory.eq_of_homotopy _ _ h

/-- Helper for Lemma 13.30.1: the chain-level adjunction descends to the quotient Hom-sets of the
homotopy categories. -/
private noncomputable def mapHomotopyCategory_coreHomEquiv
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    Adjunction.CoreHomEquiv (G.mapHomotopyCategory (up ℤ)) (F.mapHomotopyCategory (up ℤ)) where
  homEquiv L K :=
    { toFun := fun f ↦
        -- Proof comment: transpose a chosen chain-level representative, then descend back to
        -- the quotient Hom-set of the homotopy category.
        (HomotopyCategory.quotient D (up ℤ)).map
          (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as) f.out)
      invFun := fun g ↦
        -- Proof comment: the inverse transpose is descended in the same way via quotient maps.
        (HomotopyCategory.quotient C (up ℤ)).map
          (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).symm g.out)
      left_inv := by
        intro f
        let qC := HomotopyCategory.quotient C (up ℤ)
        let qD := HomotopyCategory.quotient D (up ℤ)
        let htrans :
            L.as ⟶ (F.mapHomologicalComplex (up ℤ)).obj K.as :=
          ((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as) ((qC.map f.out).out)
        -- Proof comment: the chosen representative of `qD.map htrans` is only defined up to
        -- homotopy, so first compare it to `htrans` in the quotient and then transport that
        -- homotopy back across the inverse Hom-equivalence.
        rw [← HomotopyCategory.quotient_map_out f]
        dsimp
        have hqD :
            qD.map ((qD.map htrans : L ⟶ (F.mapHomotopyCategory (up ℤ)).obj K).out) =
              qD.map htrans := by
          simpa [qD, htrans] using
            (HomotopyCategory.quotient_map_out
              (qD.map htrans : L ⟶ (F.mapHomotopyCategory (up ℤ)).obj K))
        rcases
            (quotient_map_eq_iff_homotopy (C := D) (c := up ℤ)).1 hqD with
          ⟨hout⟩
        rcases
            homotopy_mapHomologicalComplex_homEquiv_symm
              (adj := adj) (c := up ℤ) hout with
          ⟨hback⟩
        have hqC :
            qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).symm
                ((qD.map htrans).out)) =
              qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).symm htrans) :=
          (quotient_map_eq_iff_homotopy (C := C) (c := up ℤ)).2 ⟨hback⟩
        have hleft :
            qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).symm htrans) =
              qC.map ((qC.map f.out).out) := by
          exact congrArg qC.map
            (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).left_inv
              ((qC.map f.out).out))
        have hout :
            qC.map ((qC.map f.out).out) = qC.map f.out := by
          simpa [qC] using
            (HomotopyCategory.quotient_map_out
              (qC.map f.out : (G.mapHomotopyCategory (up ℤ)).obj L ⟶ K))
        exact hqC.trans <| hleft.trans hout
      right_inv := by
        intro g
        let qC := HomotopyCategory.quotient C (up ℤ)
        let qD := HomotopyCategory.quotient D (up ℤ)
        let htrans :
            (G.mapHomologicalComplex (up ℤ)).obj L.as ⟶ K.as :=
          ((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).symm ((qD.map g.out).out)
        -- Proof comment: dually, compare the chosen representative of `qC.map htrans` with the
        -- canonical inverse transpose and carry that homotopy forward across the Hom-equivalence.
        rw [← HomotopyCategory.quotient_map_out g]
        dsimp
        have hqC :
            qC.map ((qC.map htrans :
                (G.mapHomotopyCategory (up ℤ)).obj L ⟶ K).out) =
              qC.map htrans := by
          simpa [qC, htrans] using
            (HomotopyCategory.quotient_map_out
              (qC.map htrans :
                (G.mapHomotopyCategory (up ℤ)).obj L ⟶ K))
        rcases
            (quotient_map_eq_iff_homotopy (C := C) (c := up ℤ)).1 hqC with
          ⟨hout⟩
        rcases
            homotopy_mapHomologicalComplex_homEquiv
              (adj := adj) (c := up ℤ) hout with
          ⟨hforward⟩
        have hqD :
            qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as)
                ((qC.map htrans).out)) =
              qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as) htrans) :=
          (quotient_map_eq_iff_homotopy (C := D) (c := up ℤ)).2 ⟨hforward⟩
        have hright :
            qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as) htrans) =
              qD.map ((qD.map g.out).out) := by
          exact congrArg qD.map
            (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).right_inv
              ((qD.map g.out).out))
        have hout :
            qD.map ((qD.map g.out).out) = qD.map g.out := by
          simpa [qD] using
            (HomotopyCategory.quotient_map_out
              (qD.map g.out : L ⟶ (F.mapHomotopyCategory (up ℤ)).obj K))
        exact hqD.trans <| hright.trans hout }
  homEquiv_naturality_left_symm := by
    sorry
  homEquiv_naturality_right := by
    sorry

/-- An adjunction of additive functors induces an adjunction on homotopy categories of cochain
complexes. -/
noncomputable def mapHomotopyCategory
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    G.mapHomotopyCategory (up ℤ) ⊣ F.mapHomotopyCategory (up ℤ) :=
  -- Route correction: the unit/counit transport route leaves non-definitional quotient
  -- composites on morphisms. The source-faithful fix is to descend the chain-level Hom-bijection
  -- to the homotopy categories and package it with `Adjunction.mkOfHomEquiv`.
  Adjunction.mkOfHomEquiv (mapHomotopyCategory_coreHomEquiv adj)

/-- Internal notation for the source Hom-set in Lemma 13.30.1. -/
private abbrev pointwiseDerivedHomSource
    (F : D ⥤ D') (S : MorphismProperty D) (S' : MorphismProperty D')
    (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K] :=
  (S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K

/-- Internal notation for the target Hom-set in Lemma 13.30.1. -/
private abbrev pointwiseDerivedHomTarget
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (M : D') (K : D)
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :=
  leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K

private def IsCanonicalPointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M]
    (e : pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K) : Prop :=
  ∀ {K' : D} {M' : D'} (m : M ⟶ M') (hm : S' m) (k : K ⟶ K') (hk : S k)
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M']
    (φ : M' ⟶ F.obj K'),
      e (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
        leftDerivedValueMap S' (G ⋙ S.Q) m ≫
          leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
          S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
          (Localization.isoOfHom S.Q S k hk).inv

-- Proof sketch: construct the comparison family by transporting the Chapter 4 left/right
-- localization Hom descriptions through the underived adjunction `adj.homEquiv`, then descend
-- through the pointwise right/left derived-value presentations. The same denominator formulas
-- give both naturality laws and the normalization on basic fraction generators, and these three
-- clauses characterize the family uniquely.
private theorem existsUnique_pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    ∃! e : pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K,
      IsCanonicalPointwiseDerivedHomEquiv adj S S' K M e := by
  -- TODO: build the explicit six-step comparison from the source proof. The first remaining
  -- blocker is an exported theorem computing the left-localization Hom-colimit comparison on a
  -- coprojection, followed by endpoint rewrite lemmas for the pointwise derived-value factors.
  sorry

/-- Lemma 13.30.1: if `F` is right adjoint to `G`, if the pointwise right derived value of
`F ⋙ S'.Q` is defined at `K`, and if the pointwise left derived value of `G ⋙ S.Q` is defined at
`M`, then the localized Hom-sets
`Hom_{(S')⁻¹\mathcal D'}(M, RF(K))` and `Hom_{S⁻¹\mathcal D}(LG(M), K)` are canonically
equivalent. -/
noncomputable def pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    ((S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) ≃
      (leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K) :=
  Classical.choose (existsUnique_pointwiseDerivedHomEquiv adj S S' K M)

private theorem pointwiseDerivedHomEquiv_spec
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    IsCanonicalPointwiseDerivedHomEquiv adj S S' K M
      (pointwiseDerivedHomEquiv adj S S' K M) := by
  rcases Classical.choose_spec (existsUnique_pointwiseDerivedHomEquiv adj S S' K M) with ⟨he, -⟩
  exact he

theorem pointwiseDerivedHomEquiv_naturality_left
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    {K : D} {M₁ M₂ : D'} (m : M₁ ⟶ M₂)
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₁]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₂]
    (f : (S'.Q.obj M₂) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) :
    adj.pointwiseDerivedHomEquiv S S' K M₁ ((S'.Q.map m) ≫ f) =
      leftDerivedValueMap S' (G ⋙ S.Q) m ≫ adj.pointwiseDerivedHomEquiv S S' K M₂ f :=
by
  -- TODO: rewrite `pointwiseDerivedHomEquiv` to the explicit canonical composite and use the
  -- naturality of its six factors. This is blocked by the missing canonical composite from the
  -- existential theorem above.
  sorry

theorem pointwiseDerivedHomEquiv_naturality_right
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    {K₁ K₂ : D} {M : D'} (k : K₁ ⟶ K₂)
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₁]
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₂]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M]
    (f : (S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K₁) :
    adj.pointwiseDerivedHomEquiv S S' K₂ M (f ≫ rightDerivedValueMap S (F ⋙ S'.Q) k) =
      adj.pointwiseDerivedHomEquiv S S' K₁ M f ≫ S.Q.map k :=
by
  -- TODO: after identifying `pointwiseDerivedHomEquiv` with the canonical six-step comparison,
  -- prove right naturality by functoriality of the right-derived endpoint, the underived
  -- adjunction, and the localization comparison isomorphisms.
  sorry

end Adjunction

end

end CategoryTheory
