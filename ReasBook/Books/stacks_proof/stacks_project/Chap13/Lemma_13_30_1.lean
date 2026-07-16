import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.StacksAttribute
import stacks_proof.stacks_project.Chap04.Lemma_4_14_10
import stacks_proof.stacks_project.Chap04.Lemma_4_22_9
import stacks_proof.stacks_project.Chap04.Lemma_4_22_10
import stacks_proof.stacks_project.Chap04.Remark_4_27_7
import stacks_proof.stacks_project.Chap04.Remark_4_27_15
import stacks_proof.stacks_project.Chap04.Definition_4_27_20
import stacks_proof.stacks_project.Chap13.DerivedDefinedAt
import stacks_proof.stacks_project.Chap13.Lemma_13_14_3
import stacks_proof.stacks_project.Chap13.Lemma_13_14_16

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

/-- Helper for Lemma 13.30.1: the left-localization Hom-colimit comparison sends a coprojection
indexed by a denominator `s : Y ⟶ Y'` and a numerator `f : X ⟶ Y'` to the corresponding left
fraction in the localization. -/
theorem leftLocalizationHomColimit_hom_ι
    (W : MorphismProperty D) [W.HasLeftCalculusOfFractions] (X Y : D)
    (U : MorphismProperty.Under W ⊤ Y)
    (f : ((MorphismProperty.Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
      uliftCoyoneda.{u₁}.obj (Opposite.op X))).obj U) :
    (left_localization_hom_colimit W X Y).hom
        (colimit.ι
          (MorphismProperty.Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
            uliftCoyoneda.{u₁}.obj (Opposite.op X))
          U f) =
      LeftFraction.Localization.homMk (LeftFraction.mk f.down U.hom U.prop) := by
  let F : (MorphismProperty.Under W ⊤ Y) ⥤ Type (max u₁ v₁) :=
    MorphismProperty.Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
      uliftCoyoneda.{u₁}.obj (Opposite.op X)
  -- Proof comment: unfold the public colimit comparison and rewrite the coprojection formula in
  -- `Type`, where the cocone legs are actual functions.
  simp only [left_localization_hom_colimit]
  change
    (((colimit.ι F U) ≫ (id (id (colimit.isoColimitCocone (_ : ColimitCocone F)))).hom :
        F.obj U → ((const (MorphismProperty.Under W ⊤ Y)).obj
          (ColimitCocone.cocone (_ : ColimitCocone F)).pt).obj U) f) =
      (((ColimitCocone.cocone (_ : ColimitCocone F)).ι.app U :
        F.obj U → ((const (MorphismProperty.Under W ⊤ Y)).obj
          (ColimitCocone.cocone (_ : ColimitCocone F)).pt).obj U) f)
  exact congrFun (colimit.isoColimitCocone_ι_hom (_ : ColimitCocone F) U) f

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
open CategoryTheory.Limits.Cocone
open CategoryTheory.Limits.Cone

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

/-- Helper for Lemma 13.30.1: the morphism induced on homotopy categories is obtained by mapping
the chosen chain-level representative and then passing to the quotient. -/
private theorem mapHomotopyCategory_map_out_eq
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {H : C ⥤ D} [H.Additive]
    {L₁ L₂ : HomotopyCategory C (up ℤ)} (f : L₁ ⟶ L₂) :
    (HomotopyCategory.quotient D (up ℤ)).map ((H.mapHomologicalComplex (up ℤ)).map f.out) =
      (H.mapHomotopyCategory (up ℤ)).map f := by
  -- Proof comment: first replace `f` by the quotient of its chosen representative, then apply
  -- the defining computation rule for `mapHomotopyCategory`.
  rw [← HomotopyCategory.quotient_map_out f]
  simpa using (Functor.mapHomotopyCategory_map H f.out).symm

/-- Helper for Lemma 13.30.1: the descended chain-level adjunction is natural in the source
variable on homotopy categories. -/
private theorem mapHomotopyCategory_coreHomEquiv_naturality_left_symm
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F)
    {L₁ L₂ : HomotopyCategory D (up ℤ)} {K : HomotopyCategory C (up ℤ)}
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ (F.mapHomotopyCategory (up ℤ)).obj K) :
    (HomotopyCategory.quotient C (up ℤ)).map
        (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₁.as K.as).symm ((f ≫ g).out)) =
      (G.mapHomotopyCategory (up ℤ)).map f ≫
        (HomotopyCategory.quotient C (up ℤ)).map
          (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₂.as K.as).symm g.out) := by
  let qC := HomotopyCategory.quotient C (up ℤ)
  let qD := HomotopyCategory.quotient D (up ℤ)
  -- Proof comment: replace the chosen quotient representative of `f ≫ g` by the concrete
  -- representative `f.out ≫ g.out`, then descend the chain-level left naturality identity.
  have hqD :
      qD.map ((f ≫ g).out) = qD.map (f.out ≫ g.out) := by
    have hOut :
        qD.map ((f ≫ g).out) = f ≫ g := by
      simpa [qD] using HomotopyCategory.quotient_map_out (f ≫ g)
    have hComp :
        qD.map (f.out ≫ g.out) = f ≫ g := by
      simpa [qD] using HomotopyCategory.quotient_map_out_comp_out f g
    exact hOut.trans hComp.symm
  rcases
      quotient_map_eq_iff_homotopy.1 hqD with
    ⟨hout⟩
  rcases
      homotopy_mapHomologicalComplex_homEquiv_symm adj (up ℤ) hout with
    ⟨htransport⟩
  have hleft :
      qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₁.as K.as).symm ((f ≫ g).out)) =
        qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₁.as K.as).symm
          (f.out ≫ g.out)) :=
    quotient_map_eq_iff_homotopy.2 ⟨htransport⟩
  calc
    (qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₁.as K.as).symm ((f ≫ g).out))) =
        qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₁.as K.as).symm
          (f.out ≫ g.out)) := hleft
    _ = qC.map (((G.mapHomologicalComplex (up ℤ)).map f.out) ≫
          ((adj.mapHomologicalComplex (up ℤ)).homEquiv L₂.as K.as).symm g.out) := by
      exact congrArg qC.map
        ((adj.mapHomologicalComplex (up ℤ)).homEquiv_naturality_left_symm f.out g.out)
    _ = qC.map ((G.mapHomologicalComplex (up ℤ)).map f.out) ≫
          qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₂.as K.as).symm g.out) := by
      rw [Functor.map_comp]
    _ = (G.mapHomotopyCategory (up ℤ)).map f ≫
          qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L₂.as K.as).symm g.out) := by
      rw [mapHomotopyCategory_map_out_eq f]
      rfl

/-- Helper for Lemma 13.30.1: the descended chain-level adjunction is natural in the target
variable on homotopy categories. -/
private theorem mapHomotopyCategory_coreHomEquiv_naturality_right
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F)
    {L : HomotopyCategory D (up ℤ)} {K₁ K₂ : HomotopyCategory C (up ℤ)}
    (f : (G.mapHomotopyCategory (up ℤ)).obj L ⟶ K₁) (g : K₁ ⟶ K₂) :
    (HomotopyCategory.quotient D (up ℤ)).map
        (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₂.as) ((f ≫ g).out)) =
      (HomotopyCategory.quotient D (up ℤ)).map
          (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₁.as) f.out) ≫
        (F.mapHomotopyCategory (up ℤ)).map g := by
  let qC := HomotopyCategory.quotient C (up ℤ)
  let qD := HomotopyCategory.quotient D (up ℤ)
  -- Proof comment: replace the chosen representative of `f ≫ g` by `f.out ≫ g.out`, then
  -- descend the chain-level right naturality identity to the quotient.
  have hqC :
      qC.map ((f ≫ g).out) = qC.map (f.out ≫ g.out) := by
    have hOut :
        qC.map ((f ≫ g).out) = f ≫ g := by
      simpa [qC] using HomotopyCategory.quotient_map_out (f ≫ g)
    have hComp :
        qC.map (f.out ≫ g.out) = f ≫ g := by
      simpa [qC] using HomotopyCategory.quotient_map_out_comp_out f g
    exact hOut.trans hComp.symm
  rcases
      quotient_map_eq_iff_homotopy.1 hqC with
    ⟨hout⟩
  rcases
      homotopy_mapHomologicalComplex_homEquiv adj (up ℤ) hout with
    ⟨htransport⟩
  have hright :
      qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₂.as) ((f ≫ g).out)) =
        qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₂.as)
          (f.out ≫ g.out)) :=
    quotient_map_eq_iff_homotopy.2 ⟨htransport⟩
  calc
    qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₂.as) ((f ≫ g).out)) =
        qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₂.as)
          (f.out ≫ g.out)) := hright
    _ = qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₁.as) f.out ≫
          (F.mapHomologicalComplex (up ℤ)).map g.out) := by
      exact congrArg qD.map
        ((adj.mapHomologicalComplex (up ℤ)).homEquiv_naturality_right f.out g.out)
    _ = qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₁.as) f.out) ≫
          qD.map ((F.mapHomologicalComplex (up ℤ)).map g.out) := by
      rw [Functor.map_comp]
    _ = qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K₁.as) f.out) ≫
          (F.mapHomotopyCategory (up ℤ)).map g := by
      rw [mapHomotopyCategory_map_out_eq g]
      rfl

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
            quotient_map_eq_iff_homotopy.1 hqD with
          ⟨hout⟩
        rcases
            homotopy_mapHomologicalComplex_homEquiv_symm adj (up ℤ) hout with
          ⟨hback⟩
        have hqC :
            qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).symm
                ((qD.map htrans).out)) =
              qC.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as).symm htrans) :=
          quotient_map_eq_iff_homotopy.2 ⟨hback⟩
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
            quotient_map_eq_iff_homotopy.1 hqC with
          ⟨hout⟩
        rcases
            homotopy_mapHomologicalComplex_homEquiv adj (up ℤ) hout with
          ⟨hforward⟩
        have hqD :
            qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as)
                ((qC.map htrans).out)) =
              qD.map (((adj.mapHomologicalComplex (up ℤ)).homEquiv L.as K.as) htrans) :=
          quotient_map_eq_iff_homotopy.2 ⟨hforward⟩
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
    intro L₁ L₂ K f g
    exact mapHomotopyCategory_coreHomEquiv_naturality_left_symm adj f g
  homEquiv_naturality_right := by
    intro L K₁ K₂ f g
    exact mapHomotopyCategory_coreHomEquiv_naturality_right adj f g

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

/-- Helper for Lemma 13.30.1: the canonical colimit cocone whose point is the right-derived value
at `K`. -/
private noncomputable abbrev rightDerivedValueCocone
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D)
    [S.HasRightCalculusOfFractions]
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K] :
    Cocone (CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q)) :=
  let RK := CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q)
  let _ : HasColimit RK :=
    Functor.HasPointwiseRightDerivedFunctorAt.hasColimit (F ⋙ S'.Q) S.Q S K
  colimit.cocone RK

/-- Helper for Lemma 13.30.1: the canonical limit cone whose point is the left-derived value at
`M`. -/
private noncomputable abbrev leftDerivedValueCone
    (S : MorphismProperty D) (S' : MorphismProperty D') (G : D' ⥤ D) (M : D')
    [S'.HasLeftCalculusOfFractions]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    Cone (StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)) :=
  let LM := StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)
  let _ : HasLimit LM :=
    Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit (G ⋙ S.Q) S'.Q S' M
  limit.cone LM

/-- Helper for Lemma 13.30.1: any explicit colimit cocone on the right-derived indexing diagram
identifies its vertex with the canonical right-derived value. -/
private noncomputable def rightDerivedValueIsoOfColimitCoconeLocal
    (S : MorphismProperty D) (F : D ⥤ D') {X : D}
    [F.HasPointwiseRightDerivedFunctorAt S X]
    (cX : ColimitCocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)) :
    cX.cocone.pt ≅ rightDerivedValue S F X := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let _ : HasColimit RX := HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  -- Proof comment: compare the chosen colimit cocone with the canonical colimit presentation of
  -- `rightDerivedValue S F X`.
  change cX.cocone.pt ≅ colimit RX
  simpa [RX, rightDerivedValue] using (colimit.isoColimitCocone cX).symm

/-- Helper for Lemma 13.30.1: any explicit limit cone on the left-derived indexing diagram
identifies its vertex with the canonical left-derived value. -/
private noncomputable def leftDerivedValueIsoOfLimitConeLocal
    (S : MorphismProperty D) (F : D ⥤ D') {X : D}
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    (cX : LimitCone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)) :
    cX.cone.pt ≅ leftDerivedValue S F X := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let _ : HasLimit LX := HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  -- Proof comment: compare the chosen limit cone with the canonical limit presentation of
  -- `leftDerivedValue S F X`.
  change cX.cone.pt ≅ limit LX
  simpa [LX, leftDerivedValue] using (limit.isoLimitCone cX).symm

/-- Helper for Lemma 13.30.1: an essentially constant filtered cocone already satisfies the
Chapter 4 Hom-colimit comparison criterion. -/
private noncomputable def coconeHasHomColimitComparison_of_essentiallyConstant
    {I : Type*} {C : Type*} [Category I] [Category C]
    {M : I ⥤ C} {c : Cocone M} (hc : IsEssentiallyConstantFilteredCocone c) :
    Cocone.HasHomColimitComparison M c :=
  fun W ↦
    -- Proof comment: postcompose the essentially constant cocone with co-Yoneda; the resulting
    -- cocone in `Type` is still essentially constant, hence colimiting.
    (hc.mapCocone (uliftCoyoneda.obj (Opposite.op W))).isColimit

/-- Helper for Lemma 13.30.1: a cocone isomorphism transports Chapter 4 Hom-colimit comparison
data between cocones on the same diagram. -/
private noncomputable def coconeHasHomColimitComparison_ofIso
    {I : Type*} {C : Type*} [Category I] [Category C]
    {M : I ⥤ C} {c₁ c₂ : Cocone M} (e : c₁ ≅ c₂)
    (hc₁ : Cocone.HasHomColimitComparison M c₁) :
    Cocone.HasHomColimitComparison M c₂ :=
  fun W ↦
    -- Proof comment: map the cocone isomorphism through co-Yoneda and transport the colimit
    -- witness along the resulting cocone isomorphism in `Type`.
    IsColimit.ofIsoColimit (hc₁ W) <|
      (Cocone.functoriality M (uliftCoyoneda.obj (Opposite.op W))).mapIso e

/-- Helper for Lemma 13.30.1: extending an essentially constant filtered cocone along an
isomorphism of cocone points preserves essential constancy. -/
private theorem essentiallyConstantFilteredCocone_extendIso
    {I : Type*} {C : Type*} [Category I] [Category C]
    {M : I ⥤ C} {c : Cocone M} (hc : IsEssentiallyConstantFilteredCocone c)
    {X : C} (e : c.pt ≅ X) :
    IsEssentiallyConstantFilteredCocone (c.extend e.hom) := by
  rcases hc with ⟨i, σ, hfac⟩
  refine ⟨i, SplitEpi.comp σ ⟨e.inv, by simp⟩, ?_⟩
  intro j
  rcases hfac j with ⟨k, ik, jk, hjk⟩
  refine ⟨k, ik, jk, ?_⟩
  simpa [Category.assoc] using hjk

/-- Helper for Lemma 13.30.1: an essentially constant cofiltered cone already satisfies the dual
Chapter 4 Hom-colimit comparison criterion. -/
private theorem coneHasHomColimitComparison_of_essentiallyConstant
    {I : Type*} {C : Type*} [Category I] [Category C]
    {M : I ⥤ C} {c : Cone M} (hc : IsEssentiallyConstantCofilteredCone c) :
    Cone.HasHomColimitComparison M c := by
  intro W
  -- Proof comment: pass to the opposite filtered cocone, postcompose with Yoneda, and package
  -- the resulting colimit witness back into the dual Chapter 4 predicate.
  exact ⟨(show IsColimit ((uliftYoneda.obj W).mapCocone c.op) from
    (show IsEssentiallyConstantFilteredCocone c.op from hc).mapCocone (uliftYoneda.obj W) |>.isColimit)⟩

/-- Helper for Lemma 13.30.1: extending an essentially constant cofiltered cone along an
isomorphism of cone points preserves essential constancy. -/
private theorem essentiallyConstantCofilteredCone_extendIso
    {I : Type*} {C : Type*} [Category I] [Category C]
    {M : I ⥤ C} {c : Cone M} (hc : IsEssentiallyConstantCofilteredCone c)
    {X : C} (e : c.pt ≅ X) :
    IsEssentiallyConstantCofilteredCone (c.extend e.inv) := by
  let hcOp : IsEssentiallyConstantFilteredCocone c.op := hc
  let eOp : c.op.pt ≅ Opposite.op X := e.op.symm
  change IsEssentiallyConstantFilteredCocone ((c.extend e.inv).op)
  simpa using essentiallyConstantFilteredCocone_extendIso hcOp eOp

/-- Helper for Lemma 13.30.1: a cone isomorphism transports the dual Chapter 4 Hom-colimit
comparison data between cones on the same diagram. -/
private theorem coneHasHomColimitComparison_ofIso
    {I : Type*} {C : Type*} [Category I] [Category C]
    {M : I ⥤ C} {c₁ c₂ : Cone M} (e : c₁ ≅ c₂)
    (hc₁ : Cone.HasHomColimitComparison M c₁) :
    Cone.HasHomColimitComparison M c₂ := by
  intro W
  let eInvHom := e.inv.hom
  let eop : c₁.op ≅ c₂.op :=
    Cocone.ext ((asIso eInvHom).op)
      (fun j ↦ by
        cases j with
        | op unop =>
            exact
              (show (c₁.π.app unop).op ≫ eInvHom.op = (c₂.π.app unop).op from
                congrArg Quiver.Hom.op (e.inv.w unop)))
  -- Proof comment: turn the cone isomorphism into an isomorphism of opposite cocones and
  -- transport the colimit witness through Yoneda.
  exact ⟨IsColimit.ofIsoColimit (Classical.choice (hc₁ W)) <|
    (Cocone.functoriality M.op (uliftYoneda.obj W)).mapIso eop⟩

/-- Helper for Lemma 13.30.1: the canonical right-derived cocone must carry explicit Chapter 4
Hom-colimit comparison data in the source variable before the textbook colimit-swapping proof can
run. -/
private noncomputable def rightDerivedValueCocone_hasHomColimitComparison
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D)
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S'.HasRightCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K] :
    Cocone.HasHomColimitComparison
      (CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q))
      (rightDerivedValueCocone S S' F K) :=
  let RK := CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q)
  let FK := F ⋙ S'.Q
  let hK : RightDerivedDefinedAt FK S K := inferInstance
  let hC :=
    essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone RK
      hK.isEssentiallyConstant
  let cK : ColimitCocone RK := Classical.choose hC
  let hcK : IsEssentiallyConstantFilteredCocone cK.cocone := Classical.choose_spec hC
  let _ : HasColimit RK := HasColimit.mk cK
  let eK := rightDerivedValueIsoOfColimitCoconeLocal S FK cK
  let hcomp₀ :
      Cocone.HasHomColimitComparison RK cK.cocone :=
    coconeHasHomColimitComparison_of_essentiallyConstant hcK
  let hcomp₁ :
      Cocone.HasHomColimitComparison RK (cK.cocone.extend eK.hom) :=
    coconeHasHomColimitComparison_ofIso (Cocone.extendIso cK.cocone eK) hcomp₀
  let hcolim₁ : IsColimit (cK.cocone.extend eK.hom) :=
    IsColimit.extendIso eK.hom cK.isColimit
  let hIsoPt :
      (cK.cocone.extend eK.hom).pt ≅ (rightDerivedValueCocone S S' F K).pt :=
    hcolim₁.coconePointUniqueUpToIso (colimit.isColimit RK)
  let hIso :
      cK.cocone.extend eK.hom ≅ rightDerivedValueCocone S S' F K :=
    Cocone.ext hIsoPt
      (fun j ↦ by
        simpa using hcolim₁.comp_coconePointUniqueUpToIso_hom (colimit.isColimit RK) j)
  -- Proof comment: move the comparison from the essentially constant colimit cocone supplied by
  -- `RightDerivedDefinedAt` to the canonical colimit cocone defining `rightDerivedValue`.
  coconeHasHomColimitComparison_ofIso hIso hcomp₁

/-- Helper for Lemma 13.30.1: the canonical left-derived cone must satisfy the dual Chapter 4
Hom-colimit comparison in the target variable before the textbook colimit-swapping proof can
descend to `Hom(LG(M), K)`. -/
private theorem leftDerivedValueCone_hasHomColimitComparison
    (S : MorphismProperty D) (S' : MorphismProperty D') (G : D' ⥤ D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S.HasLeftCalculusOfFractions]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M] :
    Cone.HasHomColimitComparison
      (StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q))
      (leftDerivedValueCone S S' G M) := by
  let LM := StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)
  let GM := G ⋙ S.Q
  let hM : LeftDerivedDefinedAt GM S' M := inferInstance
  obtain ⟨cM, hcM⟩ :=
    essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone LM
      hM.isEssentiallyConstant
  let _ : HasLimit LM := HasLimit.mk cM
  let eM := leftDerivedValueIsoOfLimitConeLocal S' GM cM
  let hcomp₀ :
      Cone.HasHomColimitComparison LM cM.cone :=
    coneHasHomColimitComparison_of_essentiallyConstant hcM
  let hcM' :
      IsEssentiallyConstantCofilteredCone (cM.cone.extend eM.inv) :=
    essentiallyConstantCofilteredCone_extendIso hcM eM
  let hcomp₁ :
      Cone.HasHomColimitComparison LM (cM.cone.extend eM.inv) :=
    coneHasHomColimitComparison_of_essentiallyConstant hcM'
  let hlim₁ : IsLimit (cM.cone.extend eM.inv) :=
    IsLimit.extendIso eM.inv cM.isLimit
  let hIsoPt :
      (cM.cone.extend eM.inv).pt ≅ (leftDerivedValueCone S S' G M).pt :=
    hlim₁.conePointUniqueUpToIso (limit.isLimit LM)
  let hIso :
      cM.cone.extend eM.inv ≅ leftDerivedValueCone S S' G M :=
    Cone.ext hIsoPt
      (fun j ↦ by
        simpa using (hlim₁.conePointUniqueUpToIso_hom_comp (limit.isLimit LM) j).symm)
  -- Proof comment: dually, transport the comparison from the essentially constant limit cone
  -- supplied by `LeftDerivedDefinedAt` to the canonical cone defining `leftDerivedValue`.
  exact coneHasHomColimitComparison_ofIso hIso hcomp₁

/-- Helper for Lemma 13.30.1: a denominator `m : M ⟶ M'` transports pointwise left-derived
definedness from `M` to `M'`. -/
private theorem hasPointwiseLeftDerivedFunctorAt_of_mem
    (S : MorphismProperty D) (S' : MorphismProperty D') (G : D' ⥤ D)
    {M M' : D'} (m : M ⟶ M') (hm : S' m)
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M] :
    (G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M' := by
  let hM : (G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M := inferInstance
  -- Proof comment: `LeftDerivedDefinedAt` refines pointwise left-derived existence, and the
  -- standard Chapter 13 denominator transport lemma moves that pointwise hypothesis along `m`.
  exact (hasPointwiseLeftDerivedFunctorAt_iff_of_mem (G ⋙ S.Q) S' m hm).1 hM

/-- Helper for Lemma 13.30.1: a denominator `k : K ⟶ K'` transports pointwise right-derived
definedness from `K` to `K'`. -/
private theorem hasPointwiseRightDerivedFunctorAt_of_mem
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D')
    {K K' : D} (k : K ⟶ K') (hk : S k)
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K] :
    (F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K' := by
  let hK : (F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K := inferInstance
  -- Proof comment: dually, the pointwise right-derived existence hypothesis is invariant along
  -- denominators by the standard Chapter 13 transport lemma.
  exact (hasPointwiseRightDerivedFunctorAt_iff_of_mem (F ⋙ S'.Q) S k hk).1 hK

/-- Helper for Lemma 13.30.1: the inverse underived adjunction is natural in the source
variable, so precomposing a numerator by `m` can be moved across `adj.homEquiv`. -/
private theorem pointwiseDerivedHomAdjunction_symm_naturality_left
    (adj : G ⊣ F) {M₁ M₂ : D'} {K : D} (m : M₁ ⟶ M₂) (φ : M₂ ⟶ F.obj K) :
    (adj.homEquiv M₁ K).symm (m ≫ φ) =
      G.map m ≫ (adj.homEquiv M₂ K).symm φ := by
  -- Proof comment: this is the exact underived numerator rewrite needed in the middle four-step
  -- chain after the left denominator has been chosen.
  simpa using (adj.homEquiv_naturality_left_symm m φ)

/-- Helper for Lemma 13.30.1: the standard source generator is already the numerator composed
with the `k`-indexed right-derived leg, with only associativity normalization needed. -/
private theorem pointwiseDerivedHomSource_generator_assoc
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D')
    {K K' : D} (k : K ⟶ K') (hk : S k) {M M' : D'} (m : M ⟶ M')
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    (φ : M' ⟶ F.obj K') :
    S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk =
      (S'.Q.map m ≫ S'.Q.map φ) ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk := by
  -- Proof comment: record the only associativity rewrite needed before applying the source
  -- endpoint transport in the final witness construction.
  simpa using
    (Category.assoc (S'.Q.map m) (S'.Q.map φ) (rightDerivedValueLeg S (F ⋙ S'.Q) k hk)).symm

/- The semantic recall step for this source-facing owner was done with `lean_leansearch`; the
useful hit was `Equiv.existsUnique_congr`, but the local Stacks API still needs the explicit
canonicality predicate below because the canonical equivalence is characterized by denominator
formulas rather than by transport from a previously packaged equivalence owner. -/

/-- A Hom-equivalence for Lemma 13.30.1 is canonical when it satisfies the source-facing
denominator formula used in the Stacks proof. -/
def IsCanonicalPointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M]
    (e :
      ((S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) ≃
        (leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K)) : Prop :=
  ∀ {K' : D} {M' : D'} (m : M ⟶ M') (hm : S' m) (k : K ⟶ K') (hk : S k)
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M']
    (φ : M' ⟶ F.obj K'),
      e (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
        leftDerivedValueMap S' (G ⋙ S.Q) m ≫
          leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
          S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
          (Localization.isoOfHom S.Q S k hk).inv

/-- Helper for Lemma 13.30.1: on the source side, the mapped cocone leg at the denominator `k`
is literally postcomposition with `rightDerivedValueLeg`. -/
private theorem rightDerivedSourceMappedCocone_ι_app
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S'.HasRightCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    {K' : D} (k : K ⟶ K') (hk : S k)
    (ψ : S'.Q.obj M ⟶ S'.Q.obj (F.obj K')) :
    (((uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))).mapCocone
        (rightDerivedValueCocone S S' F K)).ι.app
        (CostructuredArrow.mk ((Localization.isoOfHom S.Q S k hk).inv)))
      (ULift.up ψ) =
        ULift.up (ψ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) := by
  -- Proof comment: for the mapped co-Yoneda cocone, the leg at `k` is definitionally the
  -- function sending a numerator to its composite with the canonical right-derived leg.
  rfl

/-- Helper for Lemma 13.30.1: on the target side, the mapped opposite cone leg at the denominator
`m : M' ⟶ M` is literally precomposition with `leftDerivedValueProjection`. -/
private theorem leftDerivedTargetMappedCocone_ι_app
    (S : MorphismProperty D) (S' : MorphismProperty D') (G : D' ⥤ D) (M : D') (K : D)
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S.HasLeftCalculusOfFractions]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M]
    {M' : D'} (m : M' ⟶ M) (hm : S' m)
    (ψ : S.Q.obj (G.obj M') ⟶ S.Q.obj K) :
    (((uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)).mapCocone
        (leftDerivedValueCone S S' G M).op).ι.app
        (Opposite.op
          (show StructuredArrow (S'.Q.obj M) S'.Q from
            StructuredArrow.mk ((Localization.isoOfHom S'.Q S' m hm).inv))))
      (ULift.up ψ) =
        ULift.up (leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫ ψ) := by
  -- Proof comment: dually, the mapped Yoneda cocone leg is definitionally the function given by
  -- precomposition with the canonical left-derived projection indexed by `m`.
  rfl

/-- Helper for Lemma 13.30.1: specializing the Chapter 4 source-point comparison to the canonical
right-derived cocone identifies `Hom(M, RF(K))` with the colimit over the right-derived
denominator diagram. -/
private noncomputable def rightDerivedSourceEndpointEquiv
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S'.HasRightCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K] :
    pointwiseDerivedHomSource F S S' K M ≃
      colimit
        (CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q) ⋙
          uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))) := by
  let RK := CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q)
  let c :
      Cocone (RK ⋙ uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))) :=
    (uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))).mapCocone
      (rightDerivedValueCocone S S' F K)
  let hc : IsColimit c :=
    rightDerivedValueCocone_hasHomColimitComparison S S' F K (S'.Q.obj M)
  let eIso :
      ULift (pointwiseDerivedHomSource F S S' K M) ≅
        colimit (RK ⋙ uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))) :=
    hc.coconePointUniqueUpToIso
      (colimit.isColimit
        (RK ⋙ uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))))
  -- Proof comment: the mapped co-Yoneda cocone already computes the colimit by Chapter 4, so the
  -- desired endpoint comparison is just the resulting cocone-point uniqueness isomorphism.
  refine
    { toFun := fun f ↦ eIso.hom (ULift.up f)
      invFun := fun x ↦ (eIso.inv x).down
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    simpa using congrArg ULift.down (eIso.hom_inv_id_apply (ULift.up f))
  · intro x
    simpa using eIso.inv_hom_id_apply x

/-- Helper for Lemma 13.30.1: the source endpoint comparison sends the standard generator indexed
by `k` to the corresponding coprojection in the explicit colimit. -/
private theorem rightDerivedSourceEndpointEquiv_apply_generator
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S'.HasRightCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    {K' : D} (k : K ⟶ K') (hk : S k)
    (ψ : S'.Q.obj M ⟶ S'.Q.obj (F.obj K')) :
    rightDerivedSourceEndpointEquiv S S' F K M
        (ψ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
      colimit.ι
        (CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q) ⋙
          uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M)))
        (CostructuredArrow.mk ((Localization.isoOfHom S.Q S k hk).inv))
        (ULift.up ψ) := by
  let RK := CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q)
  let c :
      Cocone (RK ⋙ uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))) :=
    (uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))).mapCocone
      (rightDerivedValueCocone S S' F K)
  let hc : IsColimit c :=
    rightDerivedValueCocone_hasHomColimitComparison S S' F K (S'.Q.obj M)
  let eIso :
      ULift (pointwiseDerivedHomSource F S S' K M) ≅
        colimit (RK ⋙ uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))) :=
    hc.coconePointUniqueUpToIso
      (colimit.isColimit
        (RK ⋙ uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))))
  -- Proof comment: rewrite the source generator as the mapped cocone leg and then apply the
  -- standard coprojection formula for cocone-point uniqueness.
  simpa [rightDerivedSourceEndpointEquiv, RK, c, hc, eIso,
      rightDerivedSourceMappedCocone_ι_app]
    using congrFun
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (colimit.isColimit
          (RK ⋙ uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))))
        (CostructuredArrow.mk ((Localization.isoOfHom S.Q S k hk).inv)))
      (ULift.up ψ)

/-- Helper for Lemma 13.30.1: specializing the Chapter 4 target-point comparison to the canonical
left-derived cone identifies `Hom(LG(M), K)` with the colimit over the opposite denominator
diagram for `M`. -/
private noncomputable def leftDerivedTargetEndpointEquiv
    (S : MorphismProperty D) (S' : MorphismProperty D') (G : D' ⥤ D) (M : D') (K : D)
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S.HasLeftCalculusOfFractions]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M] :
    pointwiseDerivedHomTarget G S S' M K ≃
      colimit
        ((StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)).op ⋙
          uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)) := by
  let LM := StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)
  let c :
      Cocone (LM.op ⋙ uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)) :=
    (uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)).mapCocone (leftDerivedValueCone S S' G M).op
  let hc : IsColimit c :=
    Classical.choice <|
      leftDerivedValueCone_hasHomColimitComparison S S' G M (S.Q.obj K)
  let eIso :
      ULift (pointwiseDerivedHomTarget G S S' M K) ≅
        colimit (LM.op ⋙ uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)) :=
    hc.coconePointUniqueUpToIso
      (colimit.isColimit (LM.op ⋙ uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)))
  -- Proof comment: the dual Chapter 4 comparison makes the mapped Yoneda cocone colimiting, so
  -- the target endpoint is again obtained by cocone-point uniqueness.
  refine
    { toFun := fun f ↦ eIso.hom (ULift.up f)
      invFun := fun x ↦ (eIso.inv x).down
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    simpa using congrArg ULift.down (eIso.hom_inv_id_apply (ULift.up f))
  · intro x
    simpa using eIso.inv_hom_id_apply x

/-- Helper for Lemma 13.30.1: the target endpoint comparison sends the standard generator indexed
by `m : M' ⟶ M` to the corresponding coprojection in the explicit opposite colimit. -/
private theorem leftDerivedTargetEndpointEquiv_apply_generator
    (S : MorphismProperty D) (S' : MorphismProperty D') (G : D' ⥤ D) (M : D') (K : D)
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S.HasLeftCalculusOfFractions]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M]
    {M' : D'} (m : M' ⟶ M) (hm : S' m)
    (ψ : S.Q.obj (G.obj M') ⟶ S.Q.obj K) :
    leftDerivedTargetEndpointEquiv S S' G M K
        (leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫ ψ) =
      colimit.ι
        ((StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)).op ⋙
          uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K))
        (Opposite.op (StructuredArrow.mk ((Localization.isoOfHom S'.Q S' m hm).inv)))
        (ULift.up ψ) := by
  let LM := StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)
  let c :
      Cocone (LM.op ⋙ uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)) :=
    (uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)).mapCocone (leftDerivedValueCone S S' G M).op
  let hc : IsColimit c :=
    Classical.choice <|
      leftDerivedValueCone_hasHomColimitComparison S S' G M (S.Q.obj K)
  let eIso :
      ULift (pointwiseDerivedHomTarget G S S' M K) ≅
        colimit (LM.op ⋙ uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)) :=
    hc.coconePointUniqueUpToIso
      (colimit.isColimit (LM.op ⋙ uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)))
  -- Proof comment: rewrite the target generator as the mapped opposite-cocone leg and then apply
  -- the same cocone-point uniqueness coprojection formula.
  simpa [leftDerivedTargetEndpointEquiv, LM, c, hc, eIso,
      leftDerivedTargetMappedCocone_ι_app]
    using congrFun
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (colimit.isColimit (LM.op ⋙ uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)))
        (Opposite.op (StructuredArrow.mk ((Localization.isoOfHom S'.Q S' m hm).inv))))
      (ULift.up ψ)

/-- Helper for Lemma 13.30.1: fix the raw numerator bifunctor whose value at a right denominator
for `K` and a right denominator for `M` is the underlying Hom-set `Hom_{D'}(P, F(K'))`. -/
private abbrev pointwiseDerivedHomNumeratorBifunctor
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D') :
    CostructuredArrow S.Q (S.Q.obj K) ⥤
      (MorphismProperty.Over S' ⊤ M)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂) where
  obj U :=
    { obj := fun V ↦ ULift.{max u₁ u₂ v₁ v₂} (V.unop.left ⟶ F.obj U.left)
      map := fun {V W} g ψ ↦ ULift.up (g.unop.left ≫ ψ.down)
      map_id := by
        intro V
        funext ψ
        simp
      map_comp := by
        intro V W X g h
        funext ψ
        simp [Category.assoc] }
  map f :=
    { app := fun V ψ ↦ ULift.up (ψ.down ≫ F.map f.left)
      naturality := by
        intro V W g
        funext ψ
        simp [Category.assoc] }
  map_id := by
    intro U
    ext V ψ
    simp
  map_comp := by
    intro U V W f g
    ext X ψ
    simp [Category.assoc]

/-- Helper for Lemma 13.30.1: after swapping the denominator order, apply the underived
adjunction pointwise to obtain the raw numerator bifunctor on `Hom_D(G(P), K')`. -/
private abbrev pointwiseDerivedHomAdjointedBifunctor
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    (MorphismProperty.Over S' ⊤ M)ᵒᵖ ⥤
      CostructuredArrow S.Q (S.Q.obj K) ⥤ Type (max u₁ u₂ v₁ v₂) where
  obj V :=
    { obj := fun U ↦ ULift.{max u₁ u₂ v₁ v₂} (G.obj V.unop.left ⟶ U.left)
      map := fun {U W} f ψ ↦ ULift.up (ψ.down ≫ f.left)
      map_id := by
        intro U
        funext ψ
        simp
      map_comp := by
        intro U W X f g
        funext ψ
        simp [Category.assoc] }
  map g :=
    { app := fun U ψ ↦ ULift.up (G.map g.unop.left ≫ ψ.down)
      naturality := by
        intro U W f
        funext ψ
        simp [Category.assoc] }
  map_id := by
    intro V
    ext U ψ
    simp
  map_comp := by
    intro U V W g h
    ext X ψ
    simp [Category.assoc]

/-- Helper for Lemma 13.30.1: the underived adjunction identifies the two raw numerator
bifunctors once the two denominator directions are swapped. -/
private noncomputable def pointwiseDerivedHomAdjunctionIso
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
        uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M) ≅
      uncurry.obj (pointwiseDerivedHomAdjointedBifunctor G S S' K M) :=
  NatIso.ofComponents
    (fun X ↦
      { hom := fun ψ ↦ ULift.up ((adj.homEquiv X.1.unop.left X.2.left).symm ψ.down)
        inv := fun ψ ↦ ULift.up (adj.homEquiv X.1.unop.left X.2.left ψ.down) })
    (by
      intro X Y f
      ext ψ
      -- Proof comment: after unpacking the product morphism, the two sides are exactly the
      -- left- and right-variable naturality rules for `adj.homEquiv.symm`.
      rcases X with ⟨V, U⟩
      rcases Y with ⟨W, Z⟩
      rcases f with ⟨g, h⟩
      simp [pointwiseDerivedHomNumeratorBifunctor, pointwiseDerivedHomAdjointedBifunctor,
        Category.assoc, pointwiseDerivedHomAdjunction_symm_naturality_left,
        ← adj.homEquiv_naturality_right_symm])

/-- Helper for Lemma 13.30.1: on a fixed pair of denominator generators, the middle adjunction
isomorphism is exactly the inverse underived adjunction map. -/
private theorem pointwiseDerivedHomAdjunctionIso_hom_app
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (U : CostructuredArrow S.Q (S.Q.obj K)) (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (ψ : ULift.{max u₁ u₂ v₁ v₂} (V.unop.left ⟶ F.obj U.left)) :
    (pointwiseDerivedHomAdjunctionIso adj S S' K M).hom.app (V, U) ψ =
      ULift.up ((adj.homEquiv V.unop.left U.left).symm ψ.down) := by
  -- Proof comment: the component of the middle adjunction isomorphism is definitionally the
  -- inverse `adj.homEquiv` on the raw numerator Hom-set.
  rfl

/-- Helper for Lemma 13.30.1: a commutative denominator square out of `K` gives the equality
needed to build the corresponding morphism in the target-side costructured-arrow indexing
category. -/
private theorem denominatorCostructuredArrowHomEq {K K' K'' : D}
    (s : K ⟶ K') (s' : K ⟶ K'') (hs : S s) (hs' : S s') (f : K' ⟶ K'')
    (hf : s ≫ f = s') :
    S.Q.map f ≫ (Localization.isoOfHom S.Q S s' hs').inv =
      (Localization.isoOfHom S.Q S s hs).inv := by
  -- Proof comment: localize the denominator square and cancel the denominator isomorphisms on
  -- both sides to isolate the costructured-arrow comparison.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
        (Localization.isoOfHom S.Q S s' hs').inv)
    (congrArg (fun k ↦ S.Q.map k) hf)
  simpa [Functor.map_comp, Category.assoc, Localization.isoOfHom_hom] using hsq

/-- Helper for Lemma 13.30.1: any ambient target-row indexing object first receives a map from
one coming from a plain arrow into that stage. -/
private theorem costructuredArrowExistsHomFromPlainMap {K : D}
    [S.HasRightCalculusOfFractions] (g : CostructuredArrow S.Q (S.Q.obj K)) :
    ∃ (K' : D) (s : K' ⟶ g.left) (_ : S s) (f : K' ⟶ K),
      S.Q.map s ≫ g.hom = S.Q.map f := by
  -- Proof comment: represent `g.hom` by a right fraction in the localization; its numerator gives
  -- the plain-map stage and its denominator gives the arrow into `g`.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ψ.f, ?_⟩
  simpa [hψ] using rfl

/-- Helper for Lemma 13.30.1: a right fraction out of `K` can be completed to a common-target
denominator square. -/
private theorem rightFractionExistsTargetDenominatorSquare {A K : D}
    [S.HasLeftCalculusOfFractions] (ψ : S.RightFraction A K) :
    ∃ (K' : D) (s : K ⟶ K') (_ : S s) (f : A ⟶ K'),
      ψ.s ≫ f = ψ.f ≫ s := by
  -- Proof comment: pass to the opposite category, build the right-fraction comparison there, and
  -- unop the resulting common-target square.
  obtain ⟨φ, hφ⟩ := ψ.op.exists_rightFraction
  refine ⟨Opposite.unop φ.X', φ.s.unop, φ.hs, φ.f.unop, ?_⟩
  simpa using (congrArg Quiver.Hom.unop hφ).symm

/-- Helper for Lemma 13.30.1: every ambient target-row indexing object maps to one indexed by an
actual denominator out of `K`. -/
private theorem costructuredArrowExistsHomToDenominator {K : D}
    [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions]
    (g : CostructuredArrow S.Q (S.Q.obj K)) :
    ∃ (K' : D) (s : K ⟶ K') (hs : S s),
      Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) := by
  -- Proof comment: first replace `g` by a plain-map stage, then complete that stage to a genuine
  -- denominator stage using the common-target Ore square.
  rcases costructuredArrowExistsHomFromPlainMap (S := S) g with ⟨A, t, ht, u, hu⟩
  rcases rightFractionExistsTargetDenominatorSquare (S := S)
      (MorphismProperty.RightFraction.mk t ht u) with ⟨K', s, hs, f, hsq⟩
  refine ⟨K', s, hs, ⟨CostructuredArrow.homMk f ?_⟩⟩
  have hcomp : g.hom ≫ S.Q.map s = S.Q.map f := by
    letI : IsIso (S.Q.map t) := Localization.inverts S.Q S t ht
    apply (cancel_epi (S.Q.map t)).1
    calc
      S.Q.map t ≫ (g.hom ≫ S.Q.map s) = (S.Q.map t ≫ g.hom) ≫ S.Q.map s := by
        simp [Category.assoc]
      _ = S.Q.map u ≫ S.Q.map s := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ S.Q.map s) hu
      _ = S.Q.map (u ≫ s) := by
        simp [Functor.map_comp]
      _ = S.Q.map (t ≫ f) := by
        rw [hsq]
      _ = S.Q.map t ≫ S.Q.map f := by
        simp [Functor.map_comp]
  letI : IsIso (S.Q.map s) := Localization.inverts S.Q S s hs
  apply (cancel_mono (S.Q.map s)).1
  calc
    (S.Q.map f ≫ (Localization.isoOfHom S.Q S s hs).inv) ≫ S.Q.map s = S.Q.map f := by
      simp [Category.assoc]
    _ = g.hom ≫ S.Q.map s := hcomp.symm

/-- Helper for Lemma 13.30.1: the ordinary denominator category for `K` maps to the ambient
target-row costructured-arrow indexing category by sending a denominator to its localized
inverse. -/
private noncomputable def targetDenominatorToCostructuredArrow (K : D) :
    MorphismProperty.Under S ⊤ K ⥤ CostructuredArrow S.Q (S.Q.obj K) where
  obj U := CostructuredArrow.mk ((Localization.isoOfHom S.Q S U.hom U.prop).inv)
  map := fun {U V} f ↦
    CostructuredArrow.homMk f.right
      (denominatorCostructuredArrowHomEq
        (S := S) U.hom V.hom U.prop V.prop f.right (MorphismProperty.Under.w f))

/-- Helper for Lemma 13.30.1: the target-side denominator functor into the ambient
costructured-arrow indexing category is final. -/
private theorem targetDenominatorToCostructuredArrow_final
    (K : D) [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions] :
    Functor.Final (targetDenominatorToCostructuredArrow (S := S) K) := by
  let T := targetDenominatorToCostructuredArrow (S := S) K
  -- Proof comment: every ambient stage refines to an actual denominator stage, and two such
  -- refinements into the same denominator equalize after refining that denominator once more.
  refine Functor.final_of_exists_of_isFiltered T ?_ ?_
  · intro g
    rcases costructuredArrowExistsHomToDenominator (S := S) (K := K) g with ⟨K', s, hs, ⟨α⟩⟩
    exact ⟨MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := K) s hs, ⟨α⟩⟩
  · intro g U α β
    have hα :
        S.Q.map α.left = g.hom ≫ S.Q.map U.hom := by
      have h := congrArg (fun k ↦ k ≫ S.Q.map U.hom) α.w
      simpa [T, targetDenominatorToCostructuredArrow, Category.assoc, Localization.isoOfHom_hom]
        using h
    have hβ :
        S.Q.map β.left = g.hom ≫ S.Q.map U.hom := by
      have h := congrArg (fun k ↦ k ≫ S.Q.map U.hom) β.w
      simpa [T, targetDenominatorToCostructuredArrow, Category.assoc, Localization.isoOfHom_hom]
        using h
    obtain ⟨Y, t, ht, hfac⟩ :=
      (MorphismProperty.map_eq_iff_postcomp (L := S.Q) (W := S) α.left β.left).1
        (hα.trans hβ.symm)
    let V : MorphismProperty.Under S ⊤ K :=
      MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := K) (U.hom ≫ t)
        (S.comp_mem _ _ U.prop ht)
    let γ : U ⟶ V :=
      MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := K) t rfl
    refine ⟨V, γ, ?_⟩
    apply CostructuredArrow.hom_ext
    simpa [T, targetDenominatorToCostructuredArrow, γ, V, Category.assoc] using hfac

/-- Helper for Lemma 13.30.1: a commutative denominator square in `S'` gives the equality needed
to build the corresponding morphism in `StructuredArrow (S'.Q.obj M) S'.Q`. -/
private theorem leftDenominatorStructuredArrowHomEq
    {M M' M'' : D'} (m : M' ⟶ M) (m' : M'' ⟶ M) (hm : S' m) (hm' : S' m')
    (f : M' ⟶ M'') (hf : f ≫ m' = m) :
    (Localization.isoOfHom S'.Q S' m hm).inv ≫ S'.Q.map f =
      (Localization.isoOfHom S'.Q S' m' hm').inv := by
  -- Proof comment: localize the commutative denominator square and cancel the two denominator
  -- isomorphisms to isolate the structured-arrow comparison morphism.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S'.Q S' m hm).inv ≫ k ≫
        (Localization.isoOfHom S'.Q S' m' hm').inv)
    (congrArg (fun k ↦ S'.Q.map k) hf)
  simpa [Functor.map_comp, Category.assoc, Localization.isoOfHom_hom] using hsq

/-- Helper for Lemma 13.30.1: the denominator category for `M` maps to the structured-arrow
indexing category of `LM` by sending a denominator to its localized inverse. -/
private noncomputable def leftDenominatorToStructuredArrow (M : D') :
    MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q where
  obj U := StructuredArrow.mk ((Localization.isoOfHom S'.Q S' U.hom U.prop).inv)
  map := fun {U V} f ↦
    StructuredArrow.homMk f.left
      (leftDenominatorStructuredArrowHomEq
        U.hom V.hom U.prop V.prop f.left (MorphismProperty.Over.w f))

/-- Helper for Lemma 13.30.1: every structured-arrow stage under `S'.Q.obj M` receives a
morphism from one coming from an actual denominator into `M`. -/
private theorem leftDenominatorStructuredArrow_existsHomFromDenominator
    (M : D') [S'.HasRightCalculusOfFractions]
    (g : StructuredArrow (S'.Q.obj M) S'.Q) :
    ∃ (M' : D') (m : M' ⟶ M) (hm : S' m),
      Nonempty (StructuredArrow.mk ((Localization.isoOfHom S'.Q S' m hm).inv) ⟶ g) := by
  -- Proof comment: a right-fraction presentation of `g.hom` already has the source-denominator
  -- orientation needed for a map from a denominator stage into `g`.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S'.Q S' g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ?_⟩
  refine ⟨StructuredArrow.homMk ψ.f ?_⟩
  calc
    (Localization.isoOfHom S'.Q S' ψ.s ψ.hs).inv ≫ S'.Q.map ψ.f =
        ψ.map S'.Q (Localization.inverts S'.Q S') := by
          rfl
    _ = g.hom := hψ.symm

/-- Helper for Lemma 13.30.1: the denominator functor
`Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q` is initial. -/
private theorem leftDenominatorToStructuredArrow_initial
    (M : D') [S'.HasRightCalculusOfFractions] :
    Functor.Initial
      (leftDenominatorToStructuredArrow M :
        MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q) := by
  let T : MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q :=
    leftDenominatorToStructuredArrow M
  -- Proof comment: every ambient structured-arrow stage receives a map from a denominator stage,
  -- and two such maps equalize after refining the source denominator once.
  refine Functor.initial_of_exists_of_isCofiltered T ?_ ?_
  · intro g
    rcases leftDenominatorStructuredArrow_existsHomFromDenominator M g with
      ⟨M', m, hm, ⟨α⟩⟩
    exact ⟨{
      left := M'
      right := ⟨⟨⟩⟩
      hom := m
      prop := hm
    }, ⟨α⟩⟩
  · intro g U α β
    have hα :
        S'.Q.map α.right = S'.Q.map U.hom ≫ g.hom := by
      apply (cancel_epi (Localization.isoOfHom S'.Q S' U.hom U.prop).inv).1
      simpa [T, leftDenominatorToStructuredArrow, Category.assoc] using α.w.symm
    have hβ :
        S'.Q.map β.right = S'.Q.map U.hom ≫ g.hom := by
      apply (cancel_epi (Localization.isoOfHom S'.Q S' U.hom U.prop).inv).1
      simpa [T, leftDenominatorToStructuredArrow, Category.assoc] using β.w.symm
    obtain ⟨M'', t, ht, hfac⟩ :=
      (MorphismProperty.map_eq_iff_precomp S'.Q S' α.right β.right).1
        (hα.trans hβ.symm)
    let V : MorphismProperty.Over S' ⊤ M :=
      {
        left := M''
        right := ⟨⟨⟩⟩
        hom := t ≫ U.hom
        prop := S'.comp_mem _ _ ht U.prop
      }
    let γ : V ⟶ U :=
      MorphismProperty.Over.homMk t rfl
    refine ⟨V, γ, ?_⟩
    apply StructuredArrow.hom_ext
    simpa [T, leftDenominatorToStructuredArrow, γ, V, Category.assoc] using hfac

/-- Helper for Lemma 13.30.1: the target-side denominator reindexing functor is initial in the
notation used by the final Hom-comparison proof. -/
private theorem pointwiseDerivedHomTargetReindex_initial
    (M : D') [S'.HasRightCalculusOfFractions] :
    Functor.Initial
      (leftDenominatorToStructuredArrow M :
        MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q) := by
  -- Proof comment: this is exactly the owner-level initiality statement proved just above.
  simpa using leftDenominatorToStructuredArrow_initial M

/-- Helper for Lemma 13.30.1: after taking opposites, the same target-side denominator
reindexing functor is final, which is the form needed for `Functor.Final.colimitIso`. -/
private theorem pointwiseDerivedHomTargetReindexOp_final
    (M : D') [S'.HasRightCalculusOfFractions] :
    Functor.Final
      ((leftDenominatorToStructuredArrow M :
          MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op) := by
  -- Proof comment: finality of the opposite is the standard transport of initiality.
  letI : Functor.Initial
      (leftDenominatorToStructuredArrow M :
        MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q) :=
    pointwiseDerivedHomTargetReindex_initial M
  infer_instance

/-- Helper for Lemma 13.30.1: the source rows must be lifted before taking the row colimit, so
this helper records the common-universe row diagram over right denominators of `K`. -/
private abbrev pointwiseDerivedHomSourceRowLifted
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions] :
    CostructuredArrow S.Q (S.Q.obj K) ⥤
      (MorphismProperty.Over S' ⊤ M)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂) :=
  pointwiseDerivedHomNumeratorBifunctor S S' F K M

/-- Helper for Lemma 13.30.1: at a fixed right denominator `U`, the lifted source row is exactly
the common-universe numerator row for `U`. -/
private theorem pointwiseDerivedHomSourceRowLifted_obj
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    (U : CostructuredArrow S.Q (S.Q.obj K)) :
    (pointwiseDerivedHomSourceRowLifted S S' F K M).obj U =
      (pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U := by
  -- Proof comment: after the common-universe refactor, the lifted source row is definitionally
  -- the raw numerator row.
  rfl

/-- Helper for Lemma 13.30.1: after moving all raw rows to one common large `Type` universe, the
source-side row bridge is just the identity comparison. -/
private noncomputable def pointwiseDerivedHomSourceRowUliftNatIso
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    (U : CostructuredArrow S.Q (S.Q.obj K)) :
    (pointwiseDerivedHomSourceRowLifted S S' F K M).obj U ≅
      (pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U := by
  -- Proof comment: the source lifted row was refactored to be the common-universe numerator row
  -- itself, so no additional transport remains here.
  exact Iso.refl _

/-- Helper for Lemma 13.30.1: the identity source-row bridge fixes each generator. -/
private theorem pointwiseDerivedHomSourceRowUliftNatIso_hom_app
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    (U : CostructuredArrow S.Q (S.Q.obj K))
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (ψ : ((pointwiseDerivedHomSourceRowLifted S S' F K M).obj U).obj V) :
    (pointwiseDerivedHomSourceRowUliftNatIso S S' F K M U).hom.app V ψ =
      ψ := by
  -- Proof comment: after the common-universe refactor, the source row bridge is literally the
  -- identity natural isomorphism.
  rfl

/-- Helper for Lemma 13.30.1: the raw source row is the large-universe lift of the Chapter 4
right-localization Hom diagram for `Hom(M, F(U.left))`. -/
private noncomputable def pointwiseDerivedHomSourceRightLocalizationNatIso
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    (U : CostructuredArrow S.Q (S.Q.obj K)) :
    (pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U ≅
      MorphismProperty.rightLocalizationHomDiagram S' M (F.obj U.left) ⋙
        CategoryTheory.uliftFunctor.{max u₁ v₁, max u₂ v₂} :=
  NatIso.ofComponents
    (fun V ↦
      Equiv.toIso
        { toFun := fun ψ ↦ ULift.up (ULift.up ψ.down)
          invFun := fun ψ ↦ ULift.up ψ.down.down
          left_inv := fun ψ ↦ by
            cases ψ
            rfl
          right_inv := fun ψ ↦ by
            cases ψ
            rfl })
    (fun g ↦ by
      ext ψ
      rfl)

/-- Helper for Lemma 13.30.1: taking the colimit of a fixed lifted source row recovers the
corresponding source endpoint stage in the large `Type` universe. -/
private noncomputable def pointwiseDerivedHomSourceRowColimitIsoApp
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    (U : CostructuredArrow S.Q (S.Q.obj K)) :
    colimit ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) ≅
      ((CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q) ⋙
          uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))).obj U) :=
  let Fsmall := MorphismProperty.rightLocalizationHomDiagram S' M (F.obj U.left)
  let G := CategoryTheory.uliftFunctor.{max u₁ v₁, max u₂ v₂}
  let e₁ :
      colimit ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) ≅
        colimit (Fsmall ⋙ G) :=
    HasColimit.isoOfNatIso (pointwiseDerivedHomSourceRightLocalizationNatIso S S' F K M U)
  let e₂ : colimit (Fsmall ⋙ G) ≅ G.obj (colimit Fsmall) :=
    ((preservesColimitNatIso G).app Fsmall).symm
  let e₃ : G.obj (colimit Fsmall) ≅ G.obj (S'.Q.obj M ⟶ S'.Q.obj (F.obj U.left)) :=
    G.mapIso (MorphismProperty.right_localization_hom_colimit S' M (F.obj U.left))
  -- Proof comment: compare the raw row with the Chapter 4 right-localization Hom diagram, pass
  -- the colimit through `uliftFunctor`, and finally lift the Chapter 4 endpoint comparison.
  e₁ ≪≫ e₂ ≪≫ e₃

/-- Helper for Lemma 13.30.1: the source rowwise colimit comparison sends a coprojection to the
corresponding localized roof in `Hom_{(S')^{-1}\mathcal D'}(M, F(U.left))`. -/
private theorem pointwiseDerivedHomSourceRowColimitIsoApp_hom_ι
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    (U : CostructuredArrow S.Q (S.Q.obj K))
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (ψ : ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U).obj V) :
    (pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U).hom
        (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ψ) =
      ULift.up
        ((RightFraction.mk V.unop.hom V.unop.prop ψ.down).map
          S'.Q (Localization.inverts S'.Q S')) := by
  let Fsmall := MorphismProperty.rightLocalizationHomDiagram S' M (F.obj U.left)
  let G := CategoryTheory.uliftFunctor.{max u₁ v₁, max u₂ v₂}
  let e₁ :
      colimit ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) ≅
        colimit (Fsmall ⋙ G) :=
    HasColimit.isoOfNatIso (pointwiseDerivedHomSourceRightLocalizationNatIso S S' F K M U)
  let e₂ : colimit (Fsmall ⋙ G) ≅ G.obj (colimit Fsmall) :=
    ((preservesColimitNatIso G).app Fsmall).symm
  let e₃ : G.obj (colimit Fsmall) ≅ G.obj (S'.Q.obj M ⟶ S'.Q.obj (F.obj U.left)) :=
    G.mapIso (MorphismProperty.right_localization_hom_colimit S' M (F.obj U.left))
  have h₁ :
      e₁.hom (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ψ) =
        colimit.ι (Fsmall ⋙ G) V (ULift.up (ULift.up ψ.down)) := by
    -- Proof comment: the source row comparison only adds the outer `ULift`.
    simpa [Fsmall, G, e₁, pointwiseDerivedHomSourceRightLocalizationNatIso] using
      congrFun
        (HasColimit.isoOfNatIso_ι_hom
          (pointwiseDerivedHomSourceRightLocalizationNatIso S S' F K M U) V)
        ψ
  have h₂ :
      e₂.hom (colimit.ι (Fsmall ⋙ G) V (ULift.up (ULift.up ψ.down))) =
        ULift.up (colimit.ι Fsmall V (ULift.up ψ.down)) := by
    -- Proof comment: the preserved-colimit comparison removes the outer `uliftFunctor`.
    simpa [Fsmall, G, e₂] using
      congrFun (ι_preservesColimitIso_inv G Fsmall V) (ULift.up (ULift.up ψ.down))
  have h₃ :
      e₃.hom (ULift.up (colimit.ι Fsmall V (ULift.up ψ.down))) =
        ULift.up
          ((MorphismProperty.right_localization_hom_colimit S' M (F.obj U.left)).hom
            (colimit.ι Fsmall V (ULift.up ψ.down))) := by
    -- Proof comment: mapping the Chapter 4 isomorphism through `uliftFunctor` is definitionally
    -- the outer `ULift` of its underlying function.
    rfl
  have h₄ :
      (MorphismProperty.right_localization_hom_colimit S' M (F.obj U.left)).hom
          (colimit.ι Fsmall V (ULift.up ψ.down)) =
        (RightFraction.mk V.unop.hom V.unop.prop ψ.down).map
          S'.Q (Localization.inverts S'.Q S') := by
    -- Proof comment: this is exactly the Chapter 4 coprojection formula for right fractions.
    simpa [Fsmall] using
      MorphismProperty.right_localization_hom_colimit_hom_ι S' M (F.obj U.left) V
        (ULift.up ψ.down)
  -- Proof comment: combine the row identification, the preserved-colimit comparison, and the
  -- Chapter 4 coprojection formula into one generator calculation.
  change e₃.hom (e₂.hom
      (e₁.hom (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ψ))) =
    _
  rw [h₁, h₂, h₃]
  exact congrArg ULift.up h₄

/-- Helper for Lemma 13.30.1: the inverse source outer transport is computed by the identity
denominator on `M`, with the actual left denominator absorbed into the numerator. -/
private theorem pointwiseDerivedHomSourceOuterInv_apply_idDenominator
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    (U : CostructuredArrow S.Q (S.Q.obj K))
    {M' : D'} (m : M ⟶ M') (φ : M' ⟶ F.obj U.left) :
    (pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U).inv
        (ULift.up (S'.Q.map m ≫ S'.Q.map φ)) =
      colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
        (Opposite.op
          ({
            left := M
            right := ⟨⟨⟩⟩
            hom := 𝟙 M
            prop := S'.id_mem M
          } : MorphismProperty.Over S' ⊤ M))
        (ULift.up (m ≫ φ)) := by
  let V :
      MorphismProperty.Over S' ⊤ M :=
    {
      left := M
      right := ⟨⟨⟩⟩
      hom := 𝟙 M
      prop := S'.id_mem M
    }
  have hV :
      (pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U).hom
          (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
            (Opposite.op V) (ULift.up (m ≫ φ))) =
        ULift.up (S'.Q.map m ≫ S'.Q.map φ) := by
    -- Proof comment: evaluate the source row comparison at the identity denominator stage, so the
    -- denominator contribution collapses and only the original numerator `m ≫ φ` remains.
    calc
      (pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U).hom
          (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
            (Opposite.op V) (ULift.up (m ≫ φ))) =
        ULift.up
          ((RightFraction.mk (𝟙 M) (S'.id_mem M) (m ≫ φ)).map
            S'.Q (Localization.inverts S'.Q S')) := by
        simpa [V] using
          pointwiseDerivedHomSourceRowColimitIsoApp_hom_ι S S' F K M U (Opposite.op V)
            (ULift.up (m ≫ φ))
      _ = ULift.up (S'.Q.map m ≫ S'.Q.map φ) := by
        simp [RightFraction.map, Functor.map_comp]
  -- Proof comment: apply the inverse source row comparison to the forward coprojection formula
  -- and simplify the resulting `inv_hom_id`.
  simpa using
    (congrArg
      (fun t ↦ (pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U).inv t) hV).symm

/-- Helper for Lemma 13.30.1: the target row is compared against the Chapter 4
`left_localization_hom_colimit` diagram by the explicit denominator category `Under S ⊤ K`. -/
private abbrev pointwiseDerivedHomTargetLeftLocalizationDiagram
    (S : MorphismProperty D) (X Y : D) :
    MorphismProperty.Under S ⊤ Y ⥤ Type (max u₁ v₁) :=
  MorphismProperty.Under.forget S ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
    uliftCoyoneda.{u₁}.obj (Opposite.op X)

/-- Helper for Lemma 13.30.1: the target rows must likewise be lifted before taking the row
colimit, so this helper records the already-lifted row diagram after the underived adjunction
rewrite. -/
private abbrev pointwiseDerivedHomTargetRowLifted
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    (MorphismProperty.Over S' ⊤ M)ᵒᵖ ⥤
      CostructuredArrow S.Q (S.Q.obj K) ⥤ Type (max u₁ u₂ v₁ v₂) :=
  pointwiseDerivedHomAdjointedBifunctor G S S' K M

/-- Helper for Lemma 13.30.1: at a fixed left denominator `V`, the lifted target row is the
common-universe adjointed row at `V`. -/
private theorem pointwiseDerivedHomTargetRowLifted_obj
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ) :
    (pointwiseDerivedHomTargetRowLifted G S S' K M).obj V =
      (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V := by
  -- Proof comment: after the common-universe refactor, the lifted target row is definitionally
  -- the raw adjointed row.
  rfl

/-- Helper for Lemma 13.30.1: after moving both target-side rows to one common large `Type`
universe, the target row bridge is just the identity comparison. -/
private noncomputable def pointwiseDerivedHomTargetRowUliftNatIso
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ) :
    (pointwiseDerivedHomTargetRowLifted G S S' K M).obj V ≅
      (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V := by
  -- Proof comment: the target lifted row was refactored to be the common-universe adjointed row
  -- itself, so no additional transport remains here.
  exact Iso.refl _

/-- Helper for Lemma 13.30.1: the identity target-row bridge fixes each generator. -/
private theorem pointwiseDerivedHomTargetRowUliftNatIso_hom_app
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (U : CostructuredArrow S.Q (S.Q.obj K))
    (ψ : ((pointwiseDerivedHomTargetRowLifted G S S' K M).obj V).obj U) :
    (pointwiseDerivedHomTargetRowUliftNatIso G S S' K M V).hom.app U ψ =
      ψ := by
  -- Proof comment: after the common-universe refactor, the target row bridge is literally the
  -- identity natural isomorphism.
  rfl

/-- Helper for Lemma 13.30.1: after reindexing the target row by actual denominators out of `K`,
the resulting diagram is the common-universe lift of the Chapter 4 left-localization Hom
diagram. -/
private noncomputable def pointwiseDerivedHomTargetLeftLocalizationNatIso
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ) :
    targetDenominatorToCostructuredArrow (S := S) K ⋙
        (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V ≅
      pointwiseDerivedHomTargetLeftLocalizationDiagram S (G.obj V.unop.left) K ⋙
        CategoryTheory.uliftFunctor.{max u₂ v₂, max u₁ v₁} :=
  NatIso.ofComponents
    (fun U ↦
      Equiv.toIso
        { toFun := fun ψ ↦ ULift.up (ULift.up ψ.down)
          invFun := fun ψ ↦ ULift.up ψ.down.down
          left_inv := fun ψ ↦ by
            cases ψ
            rfl
          right_inv := fun ψ ↦ by
            cases ψ
            rfl })
    (by
      intro U W f
      ext ψ
      rfl)

/-- Helper for Lemma 13.30.1: taking the colimit of a fixed lifted target row recovers the
corresponding target endpoint stage in the large `Type` universe after reindexing by the chosen
left denominator. -/
private noncomputable def pointwiseDerivedHomTargetRowColimitIsoApp
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ) :
    colimit ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) ≅
      ((((leftDenominatorToStructuredArrow M :
            MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op) ⋙
          (StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)).op ⋙
          uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)).obj V) := by
  let Fsmall := pointwiseDerivedHomTargetLeftLocalizationDiagram S (G.obj V.unop.left) K
  let G₁ := CategoryTheory.uliftFunctor.{max u₂ v₂, max u₁ v₁}
  let _ : Functor.Final (targetDenominatorToCostructuredArrow (S := S) K) :=
    targetDenominatorToCostructuredArrow_final (S := S) K
  let e₀ :
      colimit ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) ≅
        colimit
          (targetDenominatorToCostructuredArrow (S := S) K ⋙
            (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) :=
    (Functor.Final.colimitIso (targetDenominatorToCostructuredArrow (S := S) K)
      ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V)).symm
  let e₁ :
      colimit
          (targetDenominatorToCostructuredArrow (S := S) K ⋙
            (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) ≅
        colimit (Fsmall ⋙ G₁) :=
    HasColimit.isoOfNatIso (pointwiseDerivedHomTargetLeftLocalizationNatIso G S S' K M V)
  let e₂ : colimit (Fsmall ⋙ G₁) ≅ G₁.obj (colimit Fsmall) :=
    ((preservesColimitNatIso G₁).app Fsmall).symm
  let e₃ :
      G₁.obj (colimit Fsmall) ≅
        G₁.obj (S.Q.obj (G.obj V.unop.left) ⟶ S.Q.obj K) :=
    G₁.mapIso
      ((MorphismProperty.left_localization_hom_colimit S (G.obj V.unop.left) K) ≪≫
        Equiv.toIso
          (Localization.homEquiv S (LeftFraction.Localization.Q S) S.Q))
  -- Proof comment: first replace the ambient costructured-arrow row by actual denominators of `K`,
  -- then compare with the Chapter 4 left-localization diagram, remove the outer `ULift`, and
  -- finally apply the owner-level left-localization endpoint comparison.
  simpa [Fsmall, G₁, pointwiseDerivedHomTargetLeftLocalizationDiagram,
      leftDenominatorToStructuredArrow] using
    e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃

/-- Helper for Lemma 13.30.1: the target rowwise colimit comparison sends a coprojection to the
corresponding localized left fraction in `Hom_{S^{-1}\mathcal D}(G(V.left), K)`. -/
private theorem pointwiseDerivedHomTargetRowColimitIsoApp_hom_ι
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    {K' : D} (k : K ⟶ K') (hk : S k)
    (ψ : ULift.{max u₁ u₂ v₁ v₂} (G.obj V.unop.left ⟶ K')) :
    (pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M V).hom
        (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V)
          (CostructuredArrow.mk ((Localization.isoOfHom S.Q S k hk).inv)) ψ) =
      ULift.up (S.Q.map ψ.down ≫ (Localization.isoOfHom S.Q S k hk).inv) := by
  let Fsmall := pointwiseDerivedHomTargetLeftLocalizationDiagram S (G.obj V.unop.left) K
  let G₁ := CategoryTheory.uliftFunctor.{max u₂ v₂, max u₁ v₁}
  let U : MorphismProperty.Under S ⊤ K :=
    MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := K) k hk
  let _ : Functor.Final (targetDenominatorToCostructuredArrow (S := S) K) :=
    targetDenominatorToCostructuredArrow_final (S := S) K
  let e₀ :
      colimit ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) ≅
        colimit
          (targetDenominatorToCostructuredArrow (S := S) K ⋙
            (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) :=
    (Functor.Final.colimitIso (targetDenominatorToCostructuredArrow (S := S) K)
      ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V)).symm
  let e₁ :
      colimit
          (targetDenominatorToCostructuredArrow (S := S) K ⋙
            (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) ≅
        colimit (Fsmall ⋙ G₁) :=
    HasColimit.isoOfNatIso (pointwiseDerivedHomTargetLeftLocalizationNatIso G S S' K M V)
  let e₂ : colimit (Fsmall ⋙ G₁) ≅ G₁.obj (colimit Fsmall) :=
    ((preservesColimitNatIso G₁).app Fsmall).symm
  let e₃ :
      G₁.obj (colimit Fsmall) ≅
        G₁.obj (S.Q.obj (G.obj V.unop.left) ⟶ S.Q.obj K) :=
    G₁.mapIso
      ((MorphismProperty.left_localization_hom_colimit S (G.obj V.unop.left) K) ≪≫
        Equiv.toIso
          (Localization.homEquiv S (LeftFraction.Localization.Q S) S.Q))
  have h₀ :
      e₀.hom
          (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V)
            (CostructuredArrow.mk ((Localization.isoOfHom S.Q S k hk).inv)) ψ) =
        colimit.ι
          (targetDenominatorToCostructuredArrow (S := S) K ⋙
            (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V)
          U ψ := by
    -- Proof comment: finality rewrites the ambient costructured-arrow generator to the actual
    -- denominator stage `k : K ⟶ K'`.
    simpa [U, e₀, targetDenominatorToCostructuredArrow] using
      congrFun
        (Functor.Final.ι_colimitIso_inv
          (F := targetDenominatorToCostructuredArrow (S := S) K)
          (G := (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) (X := U))
        ψ
  have h₁ :
      e₁.hom
          (colimit.ι
            (targetDenominatorToCostructuredArrow (S := S) K ⋙
              (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V)
            U ψ) =
        colimit.ι (Fsmall ⋙ G₁) U (ULift.up (ULift.up ψ.down)) := by
    -- Proof comment: the row comparison only inserts the extra `ULift` needed to land in the
    -- Chapter 4 left-localization Hom diagram.
    simpa [Fsmall, G₁, e₁, pointwiseDerivedHomTargetLeftLocalizationNatIso] using
      congrFun
        (HasColimit.isoOfNatIso_ι_hom
          (pointwiseDerivedHomTargetLeftLocalizationNatIso G S S' K M V) U)
        ψ
  have h₂ :
      e₂.hom (colimit.ι (Fsmall ⋙ G₁) U (ULift.up (ULift.up ψ.down))) =
        ULift.up (colimit.ι Fsmall U (ULift.up ψ.down)) := by
    -- Proof comment: the preserved-colimit comparison removes the outer `uliftFunctor`.
    simpa [Fsmall, G₁, e₂] using
      congrFun (ι_preservesColimitIso_inv G₁ Fsmall U) (ULift.up (ULift.up ψ.down))
  have h₃ :
      e₃.hom (ULift.up (colimit.ι Fsmall U (ULift.up ψ.down))) =
        ULift.up
          ((Localization.homEquiv S (LeftFraction.Localization.Q S) S.Q)
            ((MorphismProperty.left_localization_hom_colimit S (G.obj V.unop.left) K).hom
              (colimit.ι Fsmall U (ULift.up ψ.down)))) := by
    -- Proof comment: mapping the Chapter 4 isomorphism through `uliftFunctor` is definitionally
    -- just the outer `ULift` of its underlying function.
    rfl
  have h₄ :
      (Localization.homEquiv S (LeftFraction.Localization.Q S) S.Q)
          ((MorphismProperty.left_localization_hom_colimit S (G.obj V.unop.left) K).hom
            (colimit.ι Fsmall U (ULift.up ψ.down))) =
        S.Q.map ψ.down ≫ (Localization.isoOfHom S.Q S k hk).inv := by
    -- Proof comment: the Chapter 4 coprojection theorem gives the localized left fraction, and
    -- `left_fraction_homMk_eq` rewrites that owner-level fraction to the published normal form.
    have hOwner :
        (MorphismProperty.left_localization_hom_colimit S (G.obj V.unop.left) K).hom
            (colimit.ι Fsmall U (ULift.up ψ.down)) =
          (LeftFraction.Localization.Q S).map ψ.down ≫
            (Localization.isoOfHom (LeftFraction.Localization.Q S) S k hk).inv := by
      calc
        (MorphismProperty.left_localization_hom_colimit S (G.obj V.unop.left) K).hom
            (colimit.ι Fsmall U (ULift.up ψ.down)) =
          LeftFraction.Localization.homMk (LeftFraction.mk ψ.down k hk) := by
            simpa [Fsmall, U] using
              MorphismProperty.leftLocalizationHomColimit_hom_ι S (G.obj V.unop.left) K U
                (ULift.up ψ.down)
        _ = (LeftFraction.mk ψ.down k hk).map (LeftFraction.Localization.Q S)
              (Localization.inverts (LeftFraction.Localization.Q S) S) := by
            simpa using MorphismProperty.left_fraction_homMk_eq S ψ.down k hk
        _ = (LeftFraction.Localization.Q S).map ψ.down ≫
              (Localization.isoOfHom (LeftFraction.Localization.Q S) S k hk).inv := by
            rfl
    calc
      (Localization.homEquiv S (LeftFraction.Localization.Q S) S.Q)
          ((MorphismProperty.left_localization_hom_colimit S (G.obj V.unop.left) K).hom
            (colimit.ι Fsmall U (ULift.up ψ.down))) =
        (Localization.homEquiv S (LeftFraction.Localization.Q S) S.Q)
          ((LeftFraction.Localization.Q S).map ψ.down ≫
            (Localization.isoOfHom (LeftFraction.Localization.Q S) S k hk).inv) := by
          exact congrArg (Localization.homEquiv S (LeftFraction.Localization.Q S) S.Q) hOwner
      _ = S.Q.map ψ.down ≫ (Localization.isoOfHom S.Q S k hk).inv := by
          rw [Localization.homEquiv_comp, Localization.homEquiv_map,
            Localization.homEquiv_isoOfHom_inv]
  -- Proof comment: combine the reindexing, row comparison, `ULift` removal, and the Chapter 4
  -- coprojection formula into the final target-side generator identity.
  change e₃.hom
      (e₂.hom
        (e₁.hom
          (e₀.hom
            (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V)
              (CostructuredArrow.mk ((Localization.isoOfHom S.Q S k hk).inv)) ψ)))) =
    _
  rw [h₀, h₁, h₂, h₃]
  exact congrArg ULift.up h₄

/-- Helper for Lemma 13.30.1: the target row colimit comparison is natural in the left
denominator once the ambient costructured-arrow row is first reindexed to actual denominators of
`K`. -/
private theorem pointwiseDerivedHomTargetRowColimitIsoApp_naturality
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    {V W : (MorphismProperty.Over S' ⊤ M)ᵒᵖ} (g : V ⟶ W) :
    ((pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim).map g) ≫
        (pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M W).hom =
      (pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M V).hom ≫
        ((((leftDenominatorToStructuredArrow M :
              MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op) ⋙
            (StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)).op ⋙
            uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)).map g) := by
  let Fden := targetDenominatorToCostructuredArrow (S := S) K
  let rowV := (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V
  let rowW := (pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj W
  let targetEndpoint :=
    (((leftDenominatorToStructuredArrow M :
          MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op) ⋙
        (StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)).op ⋙
        uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K))
  let _ : Functor.Final Fden :=
    targetDenominatorToCostructuredArrow_final (S := S) K
  let e₀V : colimit rowV ≅ colimit (Fden ⋙ rowV) :=
    (Functor.Final.colimitIso Fden rowV).symm
  -- Route correction: the denominator-stage coprojection formula only applies after moving the
  -- ambient `CostructuredArrow` row to the actual denominator category `Under S ⊤ K`.
  apply (cancel_epi e₀V.inv).1
  apply colimit.hom_ext
  intro U
  ext ψ
  have hV :
      e₀V.inv (colimit.ι (Fden ⋙ rowV) U ψ) =
        colimit.ι rowV (Fden.obj U) ψ := by
    -- Proof comment: the inverse finality isomorphism recovers the original row generator at the
    -- denominator stage represented by `U`.
    simpa [e₀V] using
      congrFun (Functor.Final.ι_colimitIso_hom (F := Fden) (G := rowV) (X := U)) ψ
  have hMap :
      ((pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim).map g)
          (colimit.ι rowV (Fden.obj U) ψ) =
        colimit.ι rowW (Fden.obj U)
          (((pointwiseDerivedHomAdjointedBifunctor G S S' K M).map g).app (Fden.obj U) ψ) := by
    -- Proof comment: once the denominator stage is fixed, the outer colimit map is the usual
    -- coprojection compatibility for the rowwise natural transformation induced by `g`.
    simpa [Functor.comp_map] using
      congrFun
        (IsColimit.ι_map
          (colimit.isColimit rowV)
          (colimit.cocone rowW)
          ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).map g)
          (Fden.obj U))
        ψ
  change
      (pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M W).hom
          (((pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim).map g)
            (e₀V.inv (colimit.ι (Fden ⋙ rowV) U ψ))) =
        targetEndpoint.map g
          ((pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M V).hom
            (e₀V.inv (colimit.ι (Fden ⋙ rowV) U ψ)))
  rw [hV, hMap]
  have hW :
      (pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M W).hom
          (colimit.ι rowW (Fden.obj U)
            (((pointwiseDerivedHomAdjointedBifunctor G S S' K M).map g).app (Fden.obj U) ψ)) =
        ULift.up
          (S.Q.map (G.map g.unop.left ≫ ψ.down) ≫
            (Localization.isoOfHom S.Q S U.hom U.prop).inv) := by
    -- Proof comment: after reindexing to the actual denominator `U`, the target row comparison is
    -- exactly the denominator-stage coprojection formula.
    simpa only [Fden] using
      pointwiseDerivedHomTargetRowColimitIsoApp_hom_ι G S S' K M (V := W)
        (k := U.hom) (hk := U.prop)
        (((pointwiseDerivedHomAdjointedBifunctor G S S' K M).map g).app (Fden.obj U) ψ)
  have hV' :
      (pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M V).hom
          (colimit.ι rowV (Fden.obj U) ψ) =
        ULift.up
          (S.Q.map ψ.down ≫ (Localization.isoOfHom S.Q S U.hom U.prop).inv) := by
    -- Proof comment: the same denominator-stage formula evaluates the right-hand row comparison.
    simpa [Fden, rowV] using
      pointwiseDerivedHomTargetRowColimitIsoApp_hom_ι G S S' K M (V := V)
        (k := U.hom) (hk := U.prop) ψ
  rw [hW, hV']
  -- Proof comment: after both row comparisons are rewritten on actual denominator generators,
  -- the square is exactly functoriality of `uliftYoneda` along the structured-arrow map from `g`.
  simp [targetEndpoint, leftDenominatorToStructuredArrow, Functor.map_comp, Category.assoc]

/-- Helper for Lemma 13.30.1: the published numerator outer-colimit functor is definitionally the
raw `curry/uncurry` row functor used in the middle comparison. -/
private theorem pointwiseDerivedHomMiddleSourceRows_eq
    (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim =
      curry.obj (uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙ colim := by
  -- Proof comment: this is exactly `Functor.curry_obj_uncurry_obj` after whiskering with the
  -- outer `colim` functor.
  simpa [Functor.curry_obj_uncurry_obj]

/-- Helper for Lemma 13.30.1: the published adjointed outer-colimit functor is definitionally the
raw `curry/uncurry` row functor used after the rowwise adjunction step. -/
private theorem pointwiseDerivedHomMiddleTargetRows_eq
    (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    curry.obj (uncurry.obj (pointwiseDerivedHomAdjointedBifunctor G S S' K M)) ⋙ colim =
      pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim := by
  -- Proof comment: the target side is the same normalization, now for the adjointed bifunctor.
  simpa [Functor.curry_obj_uncurry_obj]

/-- Helper for Lemma 13.30.1: the public source row-colimit functor reaches the swapped
denominator order by the symmetric Fubini comparison. -/
private noncomputable def pointwiseDerivedHomMiddleFubiniIso
    (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    colimit (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) ≅
      colimit
        (curry.obj
            (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
              uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙
          colim) := by
  -- Proof comment: type the symmetric Fubini isomorphism directly in the public source spelling
  -- by absorbing the `curry/uncurry` normalization into the stage definition.
  simpa [pointwiseDerivedHomMiddleSourceRows_eq (F := F) S S' K M] using
    (colimitCurrySwapCompColimIsoColimitCurryCompColim
      (uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).symm

/-- Helper for Lemma 13.30.1: after swapping denominators, the rowwise underived adjunction lands
directly in the public target row-colimit spelling. -/
private noncomputable def pointwiseDerivedHomMiddleAdjunctionRowsIso
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    colimit
        (curry.obj
            (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
              uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙
          colim) ≅
      colimit (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) := by
  -- Proof comment: absorb the target `curry/uncurry` normalization into the rowwise-adjunction
  -- stage as well, so all later generator formulas stay in the public target spelling.
  simpa [pointwiseDerivedHomMiddleTargetRows_eq (G := G) S S' K M] using
    (HasColimit.isoOfNatIso
      (Functor.isoWhiskerRight
        (Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M))
        colim))

/-- Helper for Lemma 13.30.1: after swapping the two denominator colimits, the underived
adjunction identifies the source and target raw numerator iterated colimits. -/
private noncomputable def pointwiseDerivedHomMiddleIteratedIso
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D') :
    colimit (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) ≅
      colimit (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) := by
  -- Route correction: the endpoint normalizations now live inside the two stage isomorphisms.
  -- Proof comment: compose the public-source Fubini stage with the public-target adjunction
  -- stage to obtain the final middle comparison.
  exact
    pointwiseDerivedHomMiddleFubiniIso (F := F) S S' K M ≪≫
      pointwiseDerivedHomMiddleAdjunctionRowsIso (G := G) adj S S' K M

/-- Helper for Lemma 13.30.1: in the raw `curry/uncurry` spelling, the symmetric Fubini
comparison swaps the two denominator coprojections. -/
private theorem pointwiseDerivedHomMiddleFubini_hom_ι_ι
    (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (U : CostructuredArrow S.Q (S.Q.obj K)) (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (ψ : ULift.{max u₁ u₂ v₁ v₂} (V.unop.left ⟶ F.obj U.left)) :
    ((colimitCurrySwapCompColimIsoColimitCurryCompColim
          (uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).symm).hom
        (colimit.ι
          (curry.obj (uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙ colim)
          U
          (colimit.ι
            ((curry.obj (uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).obj U)
            V ψ)) =
      colimit.ι
        (curry.obj
            (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
              uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙
          colim)
        V
        (colimit.ι
          ((curry.obj
                (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ)
                  (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                    uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).obj
            V)
          U ψ) := by
  -- Proof comment: the raw middle source is exactly the symmetric Fubini comparison from mathlib,
  -- so the `_inv` generator formula swaps the outer and inner denominator indices.
  simpa using
    congrFun
      (colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_inv
        (G := uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))
        (j := U) (k := V))
      ψ

/-- Helper for Lemma 13.30.1: in the raw `curry/uncurry` spelling, the rowwise adjunction
comparison sends the swapped double coprojection to the adjointed double coprojection. -/
private theorem pointwiseDerivedHomMiddleAdjunctionRows_hom_ι_ι
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (U : CostructuredArrow S.Q (S.Q.obj K)) (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (ψ : ULift.{max u₁ u₂ v₁ v₂} (V.unop.left ⟶ F.obj U.left)) :
    (HasColimit.isoOfNatIso
        (Functor.isoWhiskerRight
          (Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M))
          colim)).hom
        (colimit.ι
          (curry.obj
              (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙
            colim)
          V
          (colimit.ι
            ((curry.obj
                  (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ)
                    (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                      uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).obj
              V)
            U ψ)) =
      colimit.ι
        (curry.obj (uncurry.obj (pointwiseDerivedHomAdjointedBifunctor G S S' K M)) ⋙ colim)
        V
        (colimit.ι
          ((curry.obj (uncurry.obj (pointwiseDerivedHomAdjointedBifunctor G S S' K M))).obj V)
          U
          (ULift.up ((adj.homEquiv V.unop.left U.left).symm ψ.down))) := by
  let Fswap :=
    curry.obj
      (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
        uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))
  let Grows := curry.obj (uncurry.obj (pointwiseDerivedHomAdjointedBifunctor G S S' K M))
  have hInner :
      colimit.ι (Fswap.obj V) U ≫
          (HasColimit.isoOfNatIso
            ((Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M)).app V)).hom =
        (pointwiseDerivedHomAdjunctionIso adj S S' K M).hom.app (V, U) ≫
          colimit.ι (Grows.obj V) U := by
    -- Proof comment: on the fixed outer row `V`, the inner comparison is the standard colimit
    -- transport induced by the rowwise adjunction natural isomorphism.
    simpa [Fswap, Grows] using
      (HasColimit.isoOfNatIso_ι_hom_assoc
        ((Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M)).app V)
        U
        (𝟙 _))
  have hOuter :
      colimit.ι (Fswap ⋙ colim) V ≫
          (HasColimit.isoOfNatIso
            (Functor.isoWhiskerRight
              (Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M))
              colim)).hom =
        (Functor.isoWhiskerRight
            (Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M))
            colim).hom.app V ≫
          colimit.ι (Grows ⋙ colim) V := by
    -- Proof comment: the outer comparison is the same transport formula, now for the whiskered
    -- natural isomorphism between the row-colimit functors.
    simpa [Fswap, Grows] using
      (HasColimit.isoOfNatIso_ι_hom_assoc
        (Functor.isoWhiskerRight
          (Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M))
          colim)
        V
        (𝟙 _))
  -- Proof comment: evaluate the outer coprojection formula on the swapped generator and then
  -- rewrite the inner transported generator with the component formula of the underived adjunction.
  calc
    (HasColimit.isoOfNatIso
        (Functor.isoWhiskerRight
          (Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M))
          colim)).hom
        (colimit.ι (Fswap ⋙ colim) V (colimit.ι (Fswap.obj V) U ψ)) =
      colimit.ι (Grows ⋙ colim) V
        ((Functor.isoWhiskerRight
            (Functor.curry.mapIso (pointwiseDerivedHomAdjunctionIso adj S S' K M))
            colim).hom.app V
          (colimit.ι (Fswap.obj V) U ψ)) := by
            simpa using congrFun hOuter (colimit.ι (Fswap.obj V) U ψ)
    _ = colimit.ι (Grows ⋙ colim) V
          (colimit.ι (Grows.obj V) U
            (ULift.up ((adj.homEquiv V.unop.left U.left).symm ψ.down))) := by
              exact congrArg (colimit.ι (Grows ⋙ colim) V) <|
                by simpa [pointwiseDerivedHomAdjunctionIso_hom_app] using congrFun hInner ψ

/-- Helper for Lemma 13.30.1: the published Fubini stage sends a double coprojection in the
source spelling to the swapped double coprojection. -/
-- TODO: Prove this by transporting `pointwiseDerivedHomMiddleFubini_hom_ι_ι` through the
-- `Eq.mpr` cast inserted by `pointwiseDerivedHomMiddleFubiniIso` when the public source row
-- functor is identified with the raw `curry/uncurry` row functor.
private theorem pointwiseDerivedHomMiddleFubiniIso_hom_ι_ι
    (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (U : CostructuredArrow S.Q (S.Q.obj K)) (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (ψ : ULift.{max u₁ u₂ v₁ v₂} (V.unop.left ⟶ F.obj U.left)) :
    (pointwiseDerivedHomMiddleFubiniIso (F := F) S S' K M).hom
        (colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
          (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ψ)) =
      colimit.ι
        (curry.obj
            (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
              uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙
          colim)
        V
        (colimit.ι
          ((curry.obj
                (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ)
                  (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                    uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).obj
            V)
          U ψ) :=
  sorry

/-- Helper for Lemma 13.30.1: the published rowwise-adjunction stage sends the swapped double
coprojection to the published target double coprojection. -/
-- TODO: Prove this by transporting `pointwiseDerivedHomMiddleAdjunctionRows_hom_ι_ι` through the
-- `Eq.mp` cast inserted by `pointwiseDerivedHomMiddleAdjunctionRowsIso` when the raw target row
-- functor is normalized back to `pointwiseDerivedHomAdjointedBifunctor ⋙ colim`.
private theorem pointwiseDerivedHomMiddleAdjunctionRowsIso_hom_ι_ι
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    (U : CostructuredArrow S.Q (S.Q.obj K)) (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ)
    (ψ : ULift.{max u₁ u₂ v₁ v₂} (V.unop.left ⟶ F.obj U.left)) :
    (pointwiseDerivedHomMiddleAdjunctionRowsIso (G := G) adj S S' K M).hom
        (colimit.ι
          (curry.obj
              (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ) (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙
            colim)
          V
          (colimit.ι
            ((curry.obj
                  (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ)
                    (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                      uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).obj
              V)
            U ψ)) =
      colimit.ι (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) V
        (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj V) U
          (ULift.up ((adj.homEquiv V.unop.left U.left).symm ψ.down))) :=
  sorry

-- Proof sketch: construct the comparison family by transporting the Chapter 4 left/right
-- localization Hom descriptions through the underived adjunction `adj.homEquiv`, then descend
-- through the pointwise right/left derived-value presentations. The same denominator formulas
-- give the naturality laws and the normalization on basic fraction generators.
/-- Helper for Lemma 13.30.1: there exists a canonical Hom-equivalence between the localized
source and target Hom-sets. -/
private theorem exists_pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M] :
  ∃ e : pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K,
      IsCanonicalPointwiseDerivedHomEquiv adj S S' K M e := by
  let sourceEndpoint :=
    CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ (F ⋙ S'.Q) ⋙
      uliftCoyoneda.{max u₁ v₁}.obj (Opposite.op (S'.Q.obj M))
  let targetEndpoint :=
    ((leftDenominatorToStructuredArrow M :
        MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op) ⋙
      (StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)).op ⋙
      uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K)
  let sourceRows :
      pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim ≅ sourceEndpoint :=
    NatIso.ofComponents
      (fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U)
      (by
        intro U W f
        apply colimit.hom_ext
        intro V
        ext ψ
        -- Proof comment: both sides send the source generator to the same localized right roof,
        -- with the extra numerator map `F.map f.left` appearing only by associativity.
        have hColim :
            colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ≫
                (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim).map f =
              ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).map f).app V ≫
                colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj W) V := by
          simpa [Functor.comp_map] using
            (IsColimit.ι_map
              (colimit.isColimit ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U))
              (colimit.cocone ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj W))
              ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).map f)
              V)
        have hColimApp :
            (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ≫
                  (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim).map f ≫
                    ((fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U) W).hom)
                ψ =
              ((((pointwiseDerivedHomNumeratorBifunctor S S' F K M).map f).app V ≫
                    colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj W) V ≫
                      ((fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U) W).hom)
                  ψ) := by
          exact congrFun
            (congrArg
              (fun t ↦ t ≫ ((fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U) W).hom)
              hColim)
            ψ
        have hTransport :
            ((((pointwiseDerivedHomNumeratorBifunctor S S' F K M).map f).app V ≫
                  colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj W) V ≫
                    ((fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U) W).hom)
                ψ) =
              (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ≫
                  ((fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U) U).hom ≫
                    sourceEndpoint.map f)
                ψ := by
          change
            ((fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U) W).hom
                (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj W) V
                  (((pointwiseDerivedHomNumeratorBifunctor S S' F K M).map f).app V ψ)) =
              sourceEndpoint.map f
                (((fun U ↦ pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U) U).hom
                  (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U) V ψ))
          rw [pointwiseDerivedHomSourceRowColimitIsoApp_hom_ι,
            pointwiseDerivedHomSourceRowColimitIsoApp_hom_ι]
          simp [sourceEndpoint, pointwiseDerivedHomNumeratorBifunctor, RightFraction.map,
            Functor.map_comp, Category.assoc]
        exact (hColimApp.trans hTransport))
  let sourceOuter :
      colimit sourceEndpoint ≅ colimit (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) :=
    (HasColimit.isoOfNatIso sourceRows).symm
  let targetRows :
      pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim ≅ targetEndpoint :=
    NatIso.ofComponents
      (fun V ↦ pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M V)
      (by
        intro V W g
        -- Route correction: prove the row naturality square only after reindexing the target row
        -- to actual denominators of `K`, where the denominator-stage generator formula applies.
        simpa [targetEndpoint] using
          pointwiseDerivedHomTargetRowColimitIsoApp_naturality G S S' K M g)
  let targetOuter :
      colimit (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) ≅ colimit targetEndpoint :=
    HasColimit.isoOfNatIso targetRows
  let targetEndpointDirect :=
    ((StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ (G ⋙ S.Q)).op ⋙
      uliftYoneda.{max u₂ v₂}.obj (S.Q.obj K))
  let _ :
      Functor.Final
        ((leftDenominatorToStructuredArrow M :
            MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op) :=
    pointwiseDerivedHomTargetReindexOp_final (S' := S') M
  let targetReindex :
      colimit targetEndpoint ≅ colimit targetEndpointDirect :=
    Functor.Final.colimitIso
      ((leftDenominatorToStructuredArrow M :
          MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op)
      targetEndpointDirect
  let targetOuterDirect :
      colimit (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) ≅
        colimit targetEndpointDirect :=
    targetOuter ≪≫ targetReindex
  let e :
      pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K :=
    (rightDerivedSourceEndpointEquiv S S' F K M).trans
      (sourceOuter.toEquiv.trans
        ((pointwiseDerivedHomMiddleIteratedIso adj S S' K M).toEquiv.trans
          (targetOuterDirect.toEquiv.trans
            (leftDerivedTargetEndpointEquiv S S' G M K).symm)))
  refine ⟨e, ?_⟩
  intro K' M' m hm k hk _ φ
  let U : CostructuredArrow S.Q (S.Q.obj K) :=
    CostructuredArrow.mk ((Localization.isoOfHom S.Q S k hk).inv)
  let V :
      MorphismProperty.Over S' ⊤ M :=
    {
      left := M
      right := ⟨⟨⟩⟩
      hom := 𝟙 M
      prop := S'.id_mem M
    }
  have hProjection :
      leftDerivedValueMap S' (G ⋙ S.Q) m ≫ leftDerivedValueProjection S' (G ⋙ S.Q) m hm =
        leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) := by
    let sq : CommSq (𝟙 M) (𝟙 M) m m := ⟨by simp⟩
    -- Proof comment: specialize the standard left-derived square compatibility to the square whose
    -- top edge is the identity on `M`, so the identity-denominator projection is recovered.
    simpa using
      (leftDerivedValueMap_comp_of_square S' (G ⋙ S.Q) m
        (𝟙 M) m (S'.id_mem M) hm (𝟙 M) sq).w
  have hSourceOuter :
      sourceOuter.hom
          (colimit.ι sourceEndpoint U (ULift.up (S'.Q.map m ≫ S'.Q.map φ))) =
        colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
          (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
            (Opposite.op V) (ULift.up (m ≫ φ))) := by
    -- Proof comment: invert the rowwise source comparison at the fixed denominator `k`, then
    -- absorb the actual left denominator `m` into the numerator while keeping the identity stage.
    calc
      sourceOuter.hom
          (colimit.ι sourceEndpoint U (ULift.up (S'.Q.map m ≫ S'.Q.map φ))) =
        colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
          ((pointwiseDerivedHomSourceRowColimitIsoApp S S' F K M U).inv
            (ULift.up (S'.Q.map m ≫ S'.Q.map φ))) := by
          simpa [sourceOuter, sourceRows, U, sourceEndpoint] using
            congrFun (HasColimit.isoOfNatIso_ι_inv sourceRows U)
              (ULift.up (S'.Q.map m ≫ S'.Q.map φ))
      _ = colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
            (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
              (Opposite.op V) (ULift.up (m ≫ φ))) := by
          rw [pointwiseDerivedHomSourceOuterInv_apply_idDenominator S S' F K M U m φ]
  have hTargetOuter :
      targetOuterDirect.hom
          (colimit.ι (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) (Opposite.op V)
            (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
              U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ))))) =
        colimit.ι targetEndpointDirect
          (Opposite.op
            (StructuredArrow.mk
              ((Localization.isoOfHom S'.Q S' (𝟙 M) (S'.id_mem M)).inv)))
          (ULift.up
            (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
              (Localization.isoOfHom S.Q S k hk).inv)) := by
    -- Proof comment: push the target raw generator through the outer row comparison at the
    -- identity denominator on `M`, keeping the right denominator `k` explicit.
    have hTargetReindex :
        targetReindex.hom
            (colimit.ι targetEndpoint (Opposite.op V)
              (ULift.up
                (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
                  (Localization.isoOfHom S.Q S k hk).inv))) =
          colimit.ι targetEndpointDirect
            (((leftDenominatorToStructuredArrow M :
                MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op).obj
              (Opposite.op V))
            (ULift.up
              (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
                (Localization.isoOfHom S.Q S k hk).inv)) := by
      simpa [targetReindex] using
        congrFun
          (Functor.Final.ι_colimitIso_hom
            ((leftDenominatorToStructuredArrow M :
                MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op)
            targetEndpointDirect
            (Opposite.op V))
          (ULift.up
            (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
              (Localization.isoOfHom S.Q S k hk).inv))
    calc
      targetOuterDirect.hom
          (colimit.ι (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) (Opposite.op V)
            (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
              U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ))))) =
        targetReindex.hom
          (colimit.ι targetEndpoint (Opposite.op V)
            ((pointwiseDerivedHomTargetRowColimitIsoApp G S S' K M (Opposite.op V)).hom
              (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
                U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ)))))) := by
          simpa [targetOuterDirect, targetOuter, targetRows] using
            congrArg targetReindex.hom <|
              congrFun (HasColimit.isoOfNatIso_ι_hom targetRows (Opposite.op V))
                (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
                  U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ))))
      _ = targetReindex.hom
            (colimit.ι targetEndpoint (Opposite.op V)
              (ULift.up
                (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
                  (Localization.isoOfHom S.Q S k hk).inv))) := by
          exact congrArg
            (fun t ↦ targetReindex.hom (colimit.ι targetEndpoint (Opposite.op V) t))
            (pointwiseDerivedHomTargetRowColimitIsoApp_hom_ι G S S' K M (Opposite.op V) k hk
              (ULift.up ((adj.homEquiv M K').symm (m ≫ φ))))
      _ = colimit.ι targetEndpointDirect
            (((leftDenominatorToStructuredArrow M :
                MorphismProperty.Over S' ⊤ M ⥤ StructuredArrow (S'.Q.obj M) S'.Q).op).obj
              (Opposite.op V))
            (ULift.up
              (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
                (Localization.isoOfHom S.Q S k hk).inv)) := hTargetReindex
      _ = colimit.ι targetEndpointDirect
            (Opposite.op
              (StructuredArrow.mk
                ((Localization.isoOfHom S'.Q S' (𝟙 M) (S'.id_mem M)).inv)))
            (ULift.up
              (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
                (Localization.isoOfHom S.Q S k hk).inv)) := by
          simp [leftDenominatorToStructuredArrow, V]
  have hTargetEndpoint :
      (leftDerivedTargetEndpointEquiv S S' G M K).symm
          (colimit.ι targetEndpointDirect
            (Opposite.op
              (StructuredArrow.mk
                ((Localization.isoOfHom S'.Q S' (𝟙 M) (S'.id_mem M)).inv)))
            (ULift.up
              (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
                (Localization.isoOfHom S.Q S k hk).inv))) =
        leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) ≫
          S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
          (Localization.isoOfHom S.Q S k hk).inv := by
    -- Proof comment: evaluate the target endpoint equivalence at the identity denominator object,
    -- so the opposite colimit generator becomes the identity-denominator projection on `M`.
    simpa [targetEndpointDirect, V, Category.assoc, Localization.isoOfHom_id_inv] using
      (congrArg (leftDerivedTargetEndpointEquiv S S' G M K).symm
        (leftDerivedTargetEndpointEquiv_apply_generator S S' G M K (𝟙 M) (S'.id_mem M)
          (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
            (Localization.isoOfHom S.Q S k hk).inv))).symm
  have hSourceGenerator :
      sourceOuter.hom
          (rightDerivedSourceEndpointEquiv S S' F K M
            (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk)) =
        sourceOuter.hom (colimit.ι sourceEndpoint U (ULift.up (S'.Q.map m ≫ S'.Q.map φ))) := by
    rw [pointwiseDerivedHomSource_generator_assoc S S' F k hk m φ]
    exact congrArg sourceOuter.hom <|
      rightDerivedSourceEndpointEquiv_apply_generator S S' F K M k hk
        (S'.Q.map m ≫ S'.Q.map φ)
  have hMiddle :
      (pointwiseDerivedHomMiddleIteratedIso adj S S' K M).hom
          (colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
            (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
              (Opposite.op V) (ULift.up (m ≫ φ)))) =
        colimit.ι (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) (Opposite.op V)
          (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
            U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ)))) := by
    -- Proof comment: pass first through the published Fubini stage and then through the published
    -- rowwise-adjunction stage, both on the explicit double coprojection.
    calc
      (pointwiseDerivedHomMiddleIteratedIso adj S S' K M).hom
          (colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
            (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
              (Opposite.op V) (ULift.up (m ≫ φ)))) =
        (pointwiseDerivedHomMiddleAdjunctionRowsIso (G := G) adj S S' K M).hom
          ((pointwiseDerivedHomMiddleFubiniIso (F := F) S S' K M).hom
            (colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
              (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
                (Opposite.op V) (ULift.up (m ≫ φ))))) := by
          rfl
      _ =
        (pointwiseDerivedHomMiddleAdjunctionRowsIso (G := G) adj S S' K M).hom
          (colimit.ι
            (curry.obj
                (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ)
                  (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                    uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M)) ⋙
              colim)
            (Opposite.op V)
            (colimit.ι
              ((curry.obj
                    (Prod.swap ((MorphismProperty.Over S' ⊤ M)ᵒᵖ)
                      (CostructuredArrow S.Q (S.Q.obj K)) ⋙
                        uncurry.obj (pointwiseDerivedHomNumeratorBifunctor S S' F K M))).obj
                (Opposite.op V))
              U
              (ULift.up (m ≫ φ)))) := by
          rw [pointwiseDerivedHomMiddleFubiniIso_hom_ι_ι (F := F) S S' K M U
            (Opposite.op V) (ULift.up (m ≫ φ))]
          rfl
      _ = colimit.ι (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) (Opposite.op V)
            (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
              U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ)))) := by
          exact
            pointwiseDerivedHomMiddleAdjunctionRowsIso_hom_ι_ι (G := G) adj S S' K M U
              (Opposite.op V) (ULift.up (m ≫ φ))
  let throughMiddle := fun t ↦
    (leftDerivedTargetEndpointEquiv S S' G M K).symm
      (targetOuterDirect.hom ((pointwiseDerivedHomMiddleIteratedIso adj S S' K M).hom t))
  let throughTarget := fun t ↦
    (leftDerivedTargetEndpointEquiv S S' G M K).symm (targetOuterDirect.hom t)
  have hStart :
      e (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
        throughMiddle
          (sourceOuter.hom
            (rightDerivedSourceEndpointEquiv S S' F K M
              (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk))) := by
    rfl
  have hAfterSourceGenerator :
      throughMiddle
          (sourceOuter.hom
            (rightDerivedSourceEndpointEquiv S S' F K M
              (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk))) =
        throughMiddle (sourceOuter.hom (colimit.ι sourceEndpoint U (ULift.up (S'.Q.map m ≫ S'.Q.map φ)))) := by
    exact congrArg throughMiddle hSourceGenerator
  have hAfterSourceOuter :
      throughMiddle (sourceOuter.hom (colimit.ι sourceEndpoint U (ULift.up (S'.Q.map m ≫ S'.Q.map φ)))) =
        throughMiddle
          (colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
            (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
              (Opposite.op V) (ULift.up (m ≫ φ)))) := by
    exact congrArg throughMiddle hSourceOuter
  have hAfterMiddle :
      throughMiddle
          (colimit.ι (pointwiseDerivedHomNumeratorBifunctor S S' F K M ⋙ colim) U
            (colimit.ι ((pointwiseDerivedHomNumeratorBifunctor S S' F K M).obj U)
              (Opposite.op V) (ULift.up (m ≫ φ)))) =
        throughTarget
          (colimit.ι (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) (Opposite.op V)
            (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
              U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ))))) := by
    exact congrArg throughTarget hMiddle
  have hAfterTargetOuter :
      throughTarget
          (colimit.ι (pointwiseDerivedHomAdjointedBifunctor G S S' K M ⋙ colim) (Opposite.op V)
            (colimit.ι ((pointwiseDerivedHomAdjointedBifunctor G S S' K M).obj (Opposite.op V))
              U (ULift.up ((adj.homEquiv M K').symm (m ≫ φ))))) =
        (leftDerivedTargetEndpointEquiv S S' G M K).symm
          (colimit.ι targetEndpointDirect
            (Opposite.op
              (StructuredArrow.mk
                ((Localization.isoOfHom S'.Q S' (𝟙 M) (S'.id_mem M)).inv)))
            (ULift.up
              (S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
                (Localization.isoOfHom S.Q S k hk).inv))) := by
    exact congrArg (leftDerivedTargetEndpointEquiv S S' G M K).symm hTargetOuter
  have hNaturality :
      leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) ≫
          S.Q.map ((adj.homEquiv M K').symm (m ≫ φ)) ≫
          (Localization.isoOfHom S.Q S k hk).inv =
        leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) ≫
          S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
          (Localization.isoOfHom S.Q S k hk).inv := by
    simpa using congrArg
      (fun t ↦
        leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) ≫
          S.Q.map t ≫ (Localization.isoOfHom S.Q S k hk).inv)
      (pointwiseDerivedHomAdjunction_symm_naturality_left adj m φ)
  have hProjection' :
      leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) ≫
          S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
          (Localization.isoOfHom S.Q S k hk).inv =
        leftDerivedValueMap S' (G ⋙ S.Q) m ≫
          leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
          S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
          (Localization.isoOfHom S.Q S k hk).inv := by
    rw [← hProjection]
    simp [Category.assoc]
  -- Proof comment: propagate the source generator through the source row comparison, the middle
  -- adjunction comparison, and the target row comparison, then simplify the resulting endpoint.
  exact hStart.trans <|
    hAfterSourceGenerator.trans <|
      hAfterSourceOuter.trans <|
        hAfterMiddle.trans <|
          hAfterTargetOuter.trans <|
            hTargetEndpoint.trans <|
              hNaturality.trans hProjection'

section SourceStatement

variable [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- Lemma 13.30.1: in the Chapter 13 situation of exact functors between triangulated categories
and multiplicative systems compatible with the triangulated structures, if `F` is right adjoint
to `G`, if the Chapter 4 source notion saying the right derived functor of `F ⋙ S'.Q` is defined
at `K`, namely that the denominator diagram `CostructuredArrow.proj S.Q (S.Q.obj K) ⋙ F ⋙ S'.Q`
is essentially constant, holds, and if the dual source notion saying the left derived functor of
`G ⋙ S.Q` is defined at `M`, namely that `StructuredArrow.proj (S'.Q.obj M) S'.Q ⋙ G ⋙ S.Q` is
essentially constant, holds, then the localized Hom-sets
`Hom_{(S')⁻¹\mathcal D'}(M, RF(K))` and `Hom_{S⁻¹\mathcal D}(LG(M), K)` are canonically
equivalent. Here the Stacks phrase “multiplicative system” is formalized by the left and right
calculus-of-fractions assumptions on `S` and `S'`. -/
@[stacks 0FND]
noncomputable def pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    [S'.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [S.IsCompatibleWithTriangulation] [S'.IsCompatibleWithTriangulation]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M] :
    ((S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) ≃
      (leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K) :=
  Classical.choose <|
    exists_pointwiseDerivedHomEquiv adj S S' K M

/-- Companion for Lemma 13.30.1: the chosen Hom-equivalence is canonical in the source-facing
denominator sense. -/
@[stacks 0FND]
theorem pointwiseDerivedHomEquiv_isCanonical
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    [S'.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [S.IsCompatibleWithTriangulation] [S'.IsCompatibleWithTriangulation]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M] :
    IsCanonicalPointwiseDerivedHomEquiv adj S S' K M
      (pointwiseDerivedHomEquiv adj S S' K M) := by
  change IsCanonicalPointwiseDerivedHomEquiv adj S S' K M
    (Classical.choose <|
      exists_pointwiseDerivedHomEquiv adj S S' K M)
  exact Classical.choose_spec <|
    exists_pointwiseDerivedHomEquiv adj S S' K M

/-- Companion for Lemma 13.30.1: the chosen Hom-equivalence satisfies the full denominator
formula used in the Stacks proof. -/
@[stacks 0FND]
theorem pointwiseDerivedHomEquiv_spec
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    [S'.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [S.IsCompatibleWithTriangulation] [S'.IsCompatibleWithTriangulation]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M]
    {K' : D} {M' : D'} (m : M ⟶ M') (hm : S' m) (k : K ⟶ K') (hk : S k)
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M']
    (φ : M' ⟶ F.obj K') :
    pointwiseDerivedHomEquiv adj S S' K M
        (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
      leftDerivedValueMap S' (G ⋙ S.Q) m ≫
        leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
        S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
        (Localization.isoOfHom S.Q S k hk).inv := by
  exact pointwiseDerivedHomEquiv_isCanonical adj S S' K M m hm k hk φ

/-- Helper for Lemma 13.30.1: the canonical equivalence evaluated on a generator coming from a
left denominator is exactly the source-facing formula with the identity denominator on `K`
collapsed. -/
private theorem pointwiseDerivedHomEquiv_onLeftDenominator
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M]
    {e :
      ((S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) ≃
        (leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K)}
    (he : IsCanonicalPointwiseDerivedHomEquiv adj S S' K M e)
    {M' : D'} (m : M ⟶ M') (hm : S' m)
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M']
    (φ : M' ⟶ F.obj K) :
    e
        (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) (𝟙 K) (S.id_mem K)) =
      leftDerivedValueMap S' (G ⋙ S.Q) m ≫
        leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
        S.Q.map (G.map m ≫ (adj.homEquiv M' K).symm φ) := by
  -- Proof comment: specialize the canonical denominator formula to the identity arrow on `K`,
  -- then simplify the terminal localization isomorphism and the resulting identity composites.
  simpa [Category.assoc, Functor.map_id, Localization.isoOfHom_id_inv] using
    he m hm (𝟙 K) (S.id_mem K) φ

/-- Helper for Lemma 13.30.1: the canonical equivalence evaluated on a generator coming from a
right denominator is exactly the source-facing formula with the identity denominator on `M`
collapsed. -/
private theorem pointwiseDerivedHomEquiv_onRightDenominator
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasRightCalculusOfFractions] [S'.HasLeftCalculusOfFractions]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M]
    {e :
      ((S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) ≃
        (leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K)}
    (he : IsCanonicalPointwiseDerivedHomEquiv adj S S' K M e)
    {K' : D} (k : K ⟶ K') (hk : S k)
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K']
    (φ : M ⟶ F.obj K') :
    e
        (S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
      leftDerivedValueMap S' (G ⋙ S.Q) (𝟙 M) ≫
        leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) ≫
        S.Q.map ((adj.homEquiv M K').symm φ) ≫
        (Localization.isoOfHom S.Q S k hk).inv := by
  -- Proof comment: specialize the canonical denominator formula to the identity arrow on `M`,
  -- then simplify the left localization factor down to the remaining right denominator term.
  simpa [Category.assoc, Functor.map_id, Localization.isoOfHom_id_inv] using
    he (𝟙 M) (S'.id_mem M) k hk φ

/-- Helper for Lemma 13.30.1: left-derived maps carry the identity-denominator projection through
the plain map `G.map m` after localization. -/
private theorem leftDerivedValueMap_comp_leftDerivedValueProjection_id
    (S : MorphismProperty D) (S' : MorphismProperty D') (G : D' ⥤ D)
    [S'.HasLeftCalculusOfFractions]
    {M₁ M₂ : D'} (m : M₁ ⟶ M₂)
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₁]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₂] :
    leftDerivedValueMap S' (G ⋙ S.Q) m ≫
        leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M₂) (S'.id_mem M₂) =
      leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M₁) (S'.id_mem M₁) ≫
        S.Q.map (G.map m) := by
  let sq : CommSq (𝟙 M₁) m m (𝟙 M₂) := ⟨by simp⟩
  -- Proof comment: specialize the square-compatibility theorem to the identity denominators on
  -- `M₁` and `M₂`, so the remaining comparison is the plain map `G.map m`.
  simpa using
    (leftDerivedValueMap_comp_of_square S' (G ⋙ S.Q) m
      (𝟙 M₁) (𝟙 M₂) (S'.id_mem M₁) (S'.id_mem M₂) m sq).w

/-- Helper for Lemma 13.30.1: the right-derived map of `k` is detected on the identity
denominator leg by the localized map `F.map k`. -/
private theorem rightDerivedValueLeg_id_comp_rightDerivedValueMap
    (S : MorphismProperty D) (S' : MorphismProperty D') (F : D ⥤ D')
    [S.ContainsIdentities]
    {K₁ K₂ : D} (k : K₁ ⟶ K₂)
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₁]
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₂] :
    rightDerivedValueLeg S (F ⋙ S'.Q) (𝟙 K₁) (S.id_mem K₁) ≫
        rightDerivedValueMap S (F ⋙ S'.Q) k =
      S'.Q.map (F.map k) ≫
        rightDerivedValueLeg S (F ⋙ S'.Q) (𝟙 K₂) (S.id_mem K₂) := by
  let sq : CommSq k (𝟙 K₁) (𝟙 K₂) k := ⟨by simp⟩
  -- Proof comment: specialize the right-derived square formula to identity denominators, which
  -- leaves only the localized image of the original map `k`.
  simpa using
    (rightDerivedValueMap_comp_of_square S (F ⋙ S'.Q) k
      (𝟙 K₁) (𝟙 K₂) (S.id_mem K₁) (S.id_mem K₂) k sq).w

/-- Companion for Lemma 13.30.1: the canonical Hom-equivalence is natural on the left-denominator
generators in the source variable. -/
@[stacks 0FND]
theorem pointwiseDerivedHomEquiv_naturality_left
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    [S'.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [S.IsCompatibleWithTriangulation] [S'.IsCompatibleWithTriangulation]
    {K : D} {M₁ M₂ : D'}
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M₁]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M₂]
    (m : M₁ ⟶ M₂) (hm : S' m) (φ : M₂ ⟶ F.obj K) :
    pointwiseDerivedHomEquiv adj S S' K M₁
        (S'.Q.map m ≫
          S'.Q.map φ ≫
          rightDerivedValueLeg S (F ⋙ S'.Q) (𝟙 K) (S.id_mem K)) =
      leftDerivedValueMap S' (G ⋙ S.Q) m ≫
        leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
        S.Q.map (G.map m ≫ (adj.homEquiv M₂ K).symm φ) := by
  -- Proof comment: specialize the canonical denominator formula to the identity denominator on
  -- `K`, so the left-variable behavior is read off directly on the standard source generators.
  exact pointwiseDerivedHomEquiv_onLeftDenominator adj S S' K M₁
    (pointwiseDerivedHomEquiv_isCanonical adj S S' K M₁) m hm φ

/-- Companion for Lemma 13.30.1: the canonical Hom-equivalence is natural on the right-denominator
generators in the target variable. -/
@[stacks 0FND]
theorem pointwiseDerivedHomEquiv_naturality_right
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    [S'.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [S.IsCompatibleWithTriangulation] [S'.IsCompatibleWithTriangulation]
    {K₁ K₂ : D} {M : D'}
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K₁]
    [RightDerivedDefinedAt (F ⋙ S'.Q) S K₂]
    [LeftDerivedDefinedAt (G ⋙ S.Q) S' M]
    (k : K₁ ⟶ K₂) (hk : S k) (φ : M ⟶ F.obj K₂) :
    pointwiseDerivedHomEquiv adj S S' K₁ M
        (S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
      leftDerivedValueMap S' (G ⋙ S.Q) (𝟙 M) ≫
        leftDerivedValueProjection S' (G ⋙ S.Q) (𝟙 M) (S'.id_mem M) ≫
        S.Q.map ((adj.homEquiv M K₂).symm φ) ≫
        (Localization.isoOfHom S.Q S k hk).inv := by
  -- Proof comment: this is the right-denominator specialization of the canonical denominator
  -- formula, so the right-variable behavior is already built into `pointwiseDerivedHomEquiv_spec`.
  exact pointwiseDerivedHomEquiv_onRightDenominator adj S S' K₁ M
    (pointwiseDerivedHomEquiv_isCanonical adj S S' K₁ M) k hk φ

end SourceStatement

end Adjunction

end

end CategoryTheory
