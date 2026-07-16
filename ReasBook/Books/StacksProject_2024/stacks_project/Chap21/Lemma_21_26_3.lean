import Mathlib.Algebra.Category.Grp.Abelian
import StacksProject_2024.stacks_project.Chap07.Lemma_7_12_4
import StacksProject_2024.stacks_project.Chap18.Lemma_18_5_2
import StacksProject_2024.stacks_project.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.stacks_project.Chap21.Lemma_21_26_1
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 21.26.3:
- primary domain: Mayer-Vietoris triangles in the derived category of abelian sheaves on a
  Grothendieck site, extracted from pushout squares of sheafified representables;
- inspected canonical declarations:
  `IsPushout`,
  `GrothendieckTopology.sheafifiedRepresentableMap`,
  `h[U]^#[J]`,
  `siteAbelianSectionsDerived`,
  the functor-category biproduct object
  `siteAbelianSectionsDerived J Z ⊞ siteAbelianSectionsDerived J Y`,
  `DerivedCategory.mappingCocone_triangle_distinguished`,
  `derived_mayer_vietoris_triangle_of_comparison_distinguished`;
- best owner abstraction: the pushout hypothesis is canonically owned by `IsPushout` with vertex
  already fixed to `h[X]^#[J]`, and the middle Mayer-Vietoris term is the canonical pointwise
  product functor `siteAbelianSectionsDerived J Z ⊞ siteAbelianSectionsDerived J Y`; the section
  terms themselves are owned by `siteAbelianSectionsDerived J U`;
- primitive data: the four site objects `X`, `Y`, `Z`, `E`, the two object morphisms out of `E`,
  the two comparison morphisms into `X`, the pushout square witness after sheafification, and the
  monomorphism hypothesis;
- derived API: the two natural transformations into and out of the canonical middle term, the
  connecting morphism, and the distinguished-triangle conclusion.

Source/core/bridge triage:
- `source-facing`: the functorial Mayer-Vietoris triangle for `RΓ(X,-)`, `RΓ(Y,-)`, `RΓ(Z,-)`,
  and `RΓ(E,-)`;
- `core/canonical`: `siteAbelianSectionsDerived`, the functor-category biproduct for the middle
  term, and `derived_mayer_vietoris_triangle_of_comparison_distinguished` for distinguishedness;
- `bridge/view`: the comparison from K-injective section complexes to the mapping cocone.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.GrothendieckTopology

open scoped GrothendieckTopologyDerivedSections SheafifiedRepresentable

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)]
variable {X Y Z E : C}

local notation "DSh" => DerivedCategory (SiteAbelianSheafCat J)
local notation "DAb" => DerivedCategory AddCommGrpCat
local notation "QSh" =>
  (DerivedCategory.Q :
    CochainComplex (SiteAbelianSheafCat J) ℤ ⥤ DSh)
local notation "QisSh" =>
  HomologicalComplex.quasiIso (SiteAbelianSheafCat J) (ComplexShape.up ℤ)

private abbrev siteAbelianSectionsToDerived (U : C) :
    CochainComplex (SiteAbelianSheafCat J) ℤ ⥤ DAb :=
  (siteAbelianSectionsFunctor J U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Helper for Lemma 21.26.3: the sections functor `Γ(U,-)` preserves zero morphisms because it
is additive. -/
private instance siteAbelianSectionsFunctor_preservesZeroMorphisms
    (U : C) :
    (siteAbelianSectionsFunctor J U).PreservesZeroMorphisms := by
  let _ : (siteAbelianSectionsFunctor J U).Additive := by infer_instance
  infer_instance

private instance siteAbelianSectionsToDerived_hasRightDerivedFunctor (U : C) :
    (siteAbelianSectionsToDerived J U).HasRightDerivedFunctor QisSh := by
  simpa [siteAbelianSectionsToDerived] using
    (mapHomologicalComplexQ_hasRightDerivedFunctor
      (siteAbelianSectionsFunctor J U))

/-- The canonical underived restriction natural transformation
`Γ(V, -) ⟶ Γ(U, -)` induced by `φ : U ⟶ V`. -/
abbrev siteAbelianSectionsRestrictionNatTrans {U V : C} (φ : U ⟶ V) :
    siteAbelianSectionsFunctor J V ⟶ siteAbelianSectionsFunctor J U :=
  Functor.whiskerLeft
    (sheafToPresheaf J AddCommGrpCat.{max u v})
    ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).map φ.op)

private abbrev siteAbelianSectionsRestrictionToDerivedNatTrans {U V : C} (φ : U ⟶ V) :
    siteAbelianSectionsToDerived J V ⟶ siteAbelianSectionsToDerived J U :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex
      (J.siteAbelianSectionsRestrictionNatTrans φ)
      (ComplexShape.up ℤ))
    DerivedCategory.Q

/-- The canonical derived restriction natural transformation
`RΓ[J](V) ⟶ RΓ[J](U)` induced by `φ : U ⟶ V`. -/
abbrev siteAbelianSectionsDerivedRestrictionNatTrans {U V : C} (φ : U ⟶ V) :
    RΓ[J](V) ⟶ RΓ[J](U) :=
  Functor.rightDerivedNatTrans
    (RΓ[J](V))
    (RΓ[J](U))
    (Functor.totalRightDerivedUnit (siteAbelianSectionsToDerived J V) QSh QisSh)
    (Functor.totalRightDerivedUnit (siteAbelianSectionsToDerived J U) QSh QisSh)
    QisSh
    (siteAbelianSectionsRestrictionToDerivedNatTrans J φ)

-- Proof sketch: pass to the set-valued underlying sheaf and identify sections with maps out of
-- the sheafified representable. Equality of the sheafified-representable maps then forces the two
-- pullback maps on sections to agree.
omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: equal sheafified-representable maps induce equal pullback maps on
sections of any set-valued sheaf. -/
private theorem sections_restriction_eq_of_sheafifiedRepresentableMap_eq
    {U V : C} (ℱ : Sheaf J (Type (max u v))) {φ ψ : U ⟶ V}
    (hφψ : J.sheafifiedRepresentableMap φ = J.sheafifiedRepresentableMap ψ) :
    ℱ.obj.map φ.op = ℱ.obj.map ψ.op := by
  ext x
  let α : h[V]^#[J] ⟶ ℱ := (J.uliftSheafifiedRepresentableHomEquiv ℱ V).symm x
  -- Rewrite both pullbacks through the canonical `Hom(h[V]^#, ℱ) ≃ ℱ(V)` bridge.
  calc
    ℱ.obj.map φ.op x =
        J.uliftSheafifiedRepresentableHomEquiv ℱ U
          (J.sheafifiedRepresentableMap φ ≫ α) := by
            rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ V).apply_symm_apply x]
            symm
            simpa [α, GrothendieckTopology.sheafifiedRepresentableMap,
              GrothendieckTopology.sheafifiedRepresentableFunctor] using
              J.uliftSheafifiedRepresentableHomEquiv_naturality φ ℱ α
    _ = J.uliftSheafifiedRepresentableHomEquiv ℱ U
          (J.sheafifiedRepresentableMap ψ ≫ α) := by
            rw [hφψ]
    _ = ℱ.obj.map ψ.op x := by
          rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ V).apply_symm_apply x]
          simpa [α, GrothendieckTopology.sheafifiedRepresentableMap,
            GrothendieckTopology.sheafifiedRepresentableFunctor] using
            J.uliftSheafifiedRepresentableHomEquiv_naturality ψ ℱ α

-- Proof sketch: the abelian-valued restriction map has the same underlying function as the
-- set-valued restriction on the forgotten sheaf, so the previous set-valued lemma applies
-- componentwise.
omit [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: equal sheafified-representable maps induce the same natural
transformation on abelian-group-valued sections. -/
theorem siteAbelianSectionsRestriction_eq_of_sheafifiedRepresentableMap_eq
    {U V : C} {φ ψ : U ⟶ V}
    (hφψ : J.sheafifiedRepresentableMap φ = J.sheafifiedRepresentableMap ψ) :
    J.siteAbelianSectionsRestrictionNatTrans φ =
      J.siteAbelianSectionsRestrictionNatTrans ψ := by
  ext 𝒜 x
  -- Forget to the underlying sheaf of sets, where the previous bridge lemma applies directly.
  let x' : ((sheafForget J).obj 𝒜).obj.obj (Opposite.op V) := x
  simpa [siteAbelianSectionsRestrictionNatTrans, siteAbelianSectionsFunctor] using
    congrFun
      (J.sections_restriction_eq_of_sheafifiedRepresentableMap_eq
        ((sheafForget J).obj 𝒜) hφψ) x'

omit [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
private theorem siteAbelianSectionsRestrictionToDerivedNatTrans_eq_of_sheafifiedRepresentableMap_eq
    {U V : C} {φ ψ : U ⟶ V}
    (hφψ : J.sheafifiedRepresentableMap φ = J.sheafifiedRepresentableMap ψ) :
    siteAbelianSectionsRestrictionToDerivedNatTrans J φ =
      siteAbelianSectionsRestrictionToDerivedNatTrans J ψ := by
  simp [siteAbelianSectionsRestrictionToDerivedNatTrans,
    J.siteAbelianSectionsRestriction_eq_of_sheafifiedRepresentableMap_eq hφψ]

/-- Equal sheafified-representable maps induce the same derived restriction natural
transformation on abelian-group-valued sections. -/
theorem siteAbelianSectionsDerivedRestrictionNatTrans_eq_of_sheafifiedRepresentableMap_eq
    {U V : C} {φ ψ : U ⟶ V}
    (hφψ : J.sheafifiedRepresentableMap φ = J.sheafifiedRepresentableMap ψ) :
    J.siteAbelianSectionsDerivedRestrictionNatTrans φ =
      J.siteAbelianSectionsDerivedRestrictionNatTrans ψ := by
  simp [
    siteAbelianSectionsDerivedRestrictionNatTrans,
    J.siteAbelianSectionsRestrictionToDerivedNatTrans_eq_of_sheafifiedRepresentableMap_eq hφψ]

-- Proof sketch: the derived restriction is defined from the underived restriction by
-- `Functor.rightDerivedNatTrans`, so once the underived transformation is identified, the derived
-- one follows by the same rewrite.
-- Proof sketch: the underived restriction natural transformations come from evaluation on the
-- presheaf side, so contravariant composition is just functoriality of the evaluation map.
omit [HasWeakSheafify J (Type (max u v))]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: underived section restrictions compose contravariantly. -/
theorem siteAbelianSectionsRestriction_comp
    {U V W : C} (φ : U ⟶ V) (ψ : V ⟶ W) :
    J.siteAbelianSectionsRestrictionNatTrans ψ ≫ J.siteAbelianSectionsRestrictionNatTrans φ =
      J.siteAbelianSectionsRestrictionNatTrans (φ ≫ ψ) := by
  -- Evaluate on a sheaf and use functoriality of the underlying presheaf restriction maps.
  ext 𝒜 x
  simp [siteAbelianSectionsRestrictionNatTrans]

omit [HasWeakSheafify J (Type (max u v))]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
private theorem siteAbelianSectionsRestrictionToDerivedNatTrans_comp
    {U V W : C} (φ : U ⟶ V) (ψ : V ⟶ W) :
    siteAbelianSectionsRestrictionToDerivedNatTrans J ψ ≫
      siteAbelianSectionsRestrictionToDerivedNatTrans J φ =
        siteAbelianSectionsRestrictionToDerivedNatTrans J (φ ≫ ψ) := by
  ext K
  have hmap :
      ((NatTrans.mapHomologicalComplex
            (J.siteAbelianSectionsRestrictionNatTrans ψ)
            (ComplexShape.up ℤ)).app K) ≫
          ((NatTrans.mapHomologicalComplex
            (J.siteAbelianSectionsRestrictionNatTrans φ)
            (ComplexShape.up ℤ)).app K) =
        (NatTrans.mapHomologicalComplex
          (J.siteAbelianSectionsRestrictionNatTrans (φ ≫ ψ))
          (ComplexShape.up ℤ)).app K := by
    apply HomologicalComplex.hom_ext _ _
    intro n
    simp
  simpa [siteAbelianSectionsRestrictionToDerivedNatTrans, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.map_comp] using
      congrArg (fun η ↦ DerivedCategory.Q.map η) hmap

omit [HasWeakSheafify J (Type (max u v))] in
/-- Derived section restrictions compose contravariantly. -/
theorem siteAbelianSectionsDerivedRestrictionNatTrans_comp
    {U V W : C} (φ : U ⟶ V) (ψ : V ⟶ W) :
    J.siteAbelianSectionsDerivedRestrictionNatTrans ψ ≫
      J.siteAbelianSectionsDerivedRestrictionNatTrans φ =
        J.siteAbelianSectionsDerivedRestrictionNatTrans (φ ≫ ψ) := by
  simp [
    siteAbelianSectionsDerivedRestrictionNatTrans,
    J.siteAbelianSectionsRestrictionToDerivedNatTrans_comp φ ψ,
    Functor.rightDerivedNatTrans_comp]

omit [HasWeakSheafify J (Type (max u v))] in
/-- The canonical first Mayer-Vietoris map
`RΓ[J](X) ⟶ RΓ[J](Z) ⊞ RΓ[J](Y)` induced by the two comparison morphisms into `X`. -/
abbrev siteAbelianSectionsDerivedMayerVietorisToBiprod
    {X Y Z : C} (inY : Y ⟶ X) (inZ : Z ⟶ X) :
    RΓ[J](X) ⟶ (RΓ[J](Z) ⊞ RΓ[J](Y)) :=
  biprod.lift
    (J.siteAbelianSectionsDerivedRestrictionNatTrans inZ)
    (J.siteAbelianSectionsDerivedRestrictionNatTrans inY)

omit [HasWeakSheafify J (Type (max u v))] in
/-- The canonical second Mayer-Vietoris map
`RΓ[J](Z) ⊞ RΓ[J](Y) ⟶ RΓ[J](E)` given by the overlap difference. -/
abbrev siteAbelianSectionsDerivedMayerVietorisDifference
    {Y Z E : C} (f : E ⟶ Y) (g : E ⟶ Z) :
    (RΓ[J](Z) ⊞ RΓ[J](Y)) ⟶ RΓ[J](E) :=
  biprod.desc
    (J.siteAbelianSectionsDerivedRestrictionNatTrans g)
    (-J.siteAbelianSectionsDerivedRestrictionNatTrans f)

-- Proof sketch: the pushout square says that the two restrictions from `X` to `E` through `Y`
-- and `Z` agree after sheafification. The Mayer-Vietoris difference map subtracts these two
-- restrictions, so the composite vanishes.
/-- The canonical first two Mayer-Vietoris maps compose to zero. -/
theorem mayerVietorisToBiprod_comp_mayerVietorisDifference
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ)) :
    J.siteAbelianSectionsDerivedMayerVietorisToBiprod inY inZ ≫
      J.siteAbelianSectionsDerivedMayerVietorisDifference f g = 0 := by
  -- First rewrite the biproduct composite as the difference of the two restrictions to `E`.
  rw [biprod.lift_desc]
  -- The pushout square identifies the two sheafified maps `E ⟶ X`, so the two derived
  -- restrictions agree after composing through `Y` and `Z`.
  have hcomp :
      J.sheafifiedRepresentableMap (f ≫ inY) =
        J.sheafifiedRepresentableMap (g ≫ inZ) := by
    simpa [GrothendieckTopology.sheafifiedRepresentableMap,
      GrothendieckTopology.sheafifiedRepresentableFunctor] using hpushout.w
  have hderived :
      J.siteAbelianSectionsDerivedRestrictionNatTrans (f ≫ inY) =
        J.siteAbelianSectionsDerivedRestrictionNatTrans (g ≫ inZ) :=
    J.siteAbelianSectionsDerivedRestrictionNatTrans_eq_of_sheafifiedRepresentableMap_eq hcomp
  calc
    J.siteAbelianSectionsDerivedRestrictionNatTrans inZ ≫
        J.siteAbelianSectionsDerivedRestrictionNatTrans g +
      J.siteAbelianSectionsDerivedRestrictionNatTrans inY ≫
        (-J.siteAbelianSectionsDerivedRestrictionNatTrans f) =
          J.siteAbelianSectionsDerivedRestrictionNatTrans (g ≫ inZ) +
            -J.siteAbelianSectionsDerivedRestrictionNatTrans (f ≫ inY) := by
            rw [show J.siteAbelianSectionsDerivedRestrictionNatTrans inZ ≫
                  J.siteAbelianSectionsDerivedRestrictionNatTrans g =
                    J.siteAbelianSectionsDerivedRestrictionNatTrans (g ≫ inZ) by
                  simpa using J.siteAbelianSectionsDerivedRestrictionNatTrans_comp g inZ]
            simp [CategoryTheory.Preadditive.comp_neg,
              show J.siteAbelianSectionsDerivedRestrictionNatTrans inY ≫
                    J.siteAbelianSectionsDerivedRestrictionNatTrans f =
                  J.siteAbelianSectionsDerivedRestrictionNatTrans (f ≫ inY) by
                simpa using J.siteAbelianSectionsDerivedRestrictionNatTrans_comp f inY]
    _ = J.siteAbelianSectionsDerivedRestrictionNatTrans (f ≫ inY) +
          -J.siteAbelianSectionsDerivedRestrictionNatTrans (f ≫ inY) := by
          rw [hderived]
    _ = 0 := by
          simp

-- Proof sketch: a section on `X` is the same as a morphism `h[X]^# ⟶ ℱ`. Under the pushout
-- hypothesis, morphisms out of `h[X]^#` are exactly compatible pairs of morphisms out of
-- `h[Y]^#` and `h[Z]^#`, so compatible sections on `Y` and `Z` glue uniquely to `X`.
omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: under the sheafified pushout hypothesis, compatible sections on
`Y` and `Z` glue uniquely to a section on `X`. -/
private theorem exists_unique_section_of_compatible_sections_of_sheafifiedRepresentable_pushout
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (ℱ : Sheaf J (Type (max u v)))
    (sY : ℱ.obj.obj (Opposite.op Y))
    (sZ : ℱ.obj.obj (Opposite.op Z))
    (hcompat : ℱ.obj.map f.op sY = ℱ.obj.map g.op sZ) :
    ∃! sX : ℱ.obj.obj (Opposite.op X),
      ℱ.obj.map inY.op sX = sY ∧ ℱ.obj.map inZ.op sX = sZ := by
  let αY : h[Y]^#[J] ⟶ ℱ := (J.uliftSheafifiedRepresentableHomEquiv ℱ Y).symm sY
  let αZ : h[Z]^#[J] ⟶ ℱ := (J.uliftSheafifiedRepresentableHomEquiv ℱ Z).symm sZ
  have hdesc :
      J.sheafifiedRepresentableMap f ≫ αY =
        J.sheafifiedRepresentableMap g ≫ αZ := by
    -- Translate the section compatibility to equality of the corresponding morphisms out of
    -- `h[E]^#[J]`.
    apply (J.uliftSheafifiedRepresentableHomEquiv ℱ E).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv ℱ E
          (J.sheafifiedRepresentableMap f ≫ αY) =
          ℱ.obj.map f.op sY := by
            rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ Y).apply_symm_apply sY]
            simpa [αY, GrothendieckTopology.sheafifiedRepresentableMap,
              GrothendieckTopology.sheafifiedRepresentableFunctor] using
              J.uliftSheafifiedRepresentableHomEquiv_naturality f ℱ αY
      _ = ℱ.obj.map g.op sZ := hcompat
      _ =
          J.uliftSheafifiedRepresentableHomEquiv ℱ E
            (J.sheafifiedRepresentableMap g ≫ αZ) := by
              rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ Z).apply_symm_apply sZ]
              symm
              simpa [αZ, GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor] using
                J.uliftSheafifiedRepresentableHomEquiv_naturality g ℱ αZ
  let αX : h[X]^#[J] ⟶ ℱ := hpushout.desc αY αZ hdesc
  refine ⟨J.uliftSheafifiedRepresentableHomEquiv ℱ X αX, ?_, ?_⟩
  · constructor
    · -- The glued morphism restricts to the given section on `Y`.
      calc
        ℱ.obj.map inY.op (J.uliftSheafifiedRepresentableHomEquiv ℱ X αX) =
            J.uliftSheafifiedRepresentableHomEquiv ℱ Y
              (J.sheafifiedRepresentableMap inY ≫ αX) := by
                symm
                simpa [GrothendieckTopology.sheafifiedRepresentableMap,
                  GrothendieckTopology.sheafifiedRepresentableFunctor] using
                  J.uliftSheafifiedRepresentableHomEquiv_naturality inY ℱ αX
        _ = J.uliftSheafifiedRepresentableHomEquiv ℱ Y αY := by
              rw [hpushout.inl_desc]
        _ = sY := by
              change
                J.uliftSheafifiedRepresentableHomEquiv ℱ Y
                    ((J.uliftSheafifiedRepresentableHomEquiv ℱ Y).symm sY) = sY
              exact (J.uliftSheafifiedRepresentableHomEquiv ℱ Y).apply_symm_apply sY
    · -- The glued morphism restricts to the given section on `Z`.
      calc
        ℱ.obj.map inZ.op (J.uliftSheafifiedRepresentableHomEquiv ℱ X αX) =
            J.uliftSheafifiedRepresentableHomEquiv ℱ Z
              (J.sheafifiedRepresentableMap inZ ≫ αX) := by
                symm
                simpa [GrothendieckTopology.sheafifiedRepresentableMap,
                  GrothendieckTopology.sheafifiedRepresentableFunctor] using
                  J.uliftSheafifiedRepresentableHomEquiv_naturality inZ ℱ αX
        _ = J.uliftSheafifiedRepresentableHomEquiv ℱ Z αZ := by
              rw [hpushout.inr_desc]
        _ = sZ := by
              change
                J.uliftSheafifiedRepresentableHomEquiv ℱ Z
                    ((J.uliftSheafifiedRepresentableHomEquiv ℱ Z).symm sZ) = sZ
              exact (J.uliftSheafifiedRepresentableHomEquiv ℱ Z).apply_symm_apply sZ
  · intro sX hsX
    -- Convert the competing section back to a morphism out of `h[X]^#[J]` and use pushout
    -- uniqueness.
    let βX : h[X]^#[J] ⟶ ℱ := (J.uliftSheafifiedRepresentableHomEquiv ℱ X).symm sX
    have hβY :
        J.sheafifiedRepresentableMap inY ≫ βX = αY := by
      apply (J.uliftSheafifiedRepresentableHomEquiv ℱ Y).injective
      calc
        J.uliftSheafifiedRepresentableHomEquiv ℱ Y
            (J.sheafifiedRepresentableMap inY ≫ βX) =
            ℱ.obj.map inY.op sX := by
              rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ X).apply_symm_apply sX]
              simpa [βX, GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor] using
                J.uliftSheafifiedRepresentableHomEquiv_naturality inY ℱ βX
        _ = sY := hsX.1
        _ = J.uliftSheafifiedRepresentableHomEquiv ℱ Y αY := by
              symm
              exact (J.uliftSheafifiedRepresentableHomEquiv ℱ Y).apply_symm_apply sY
    have hβZ :
        J.sheafifiedRepresentableMap inZ ≫ βX = αZ := by
      apply (J.uliftSheafifiedRepresentableHomEquiv ℱ Z).injective
      calc
        J.uliftSheafifiedRepresentableHomEquiv ℱ Z
            (J.sheafifiedRepresentableMap inZ ≫ βX) =
            ℱ.obj.map inZ.op sX := by
              rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ X).apply_symm_apply sX]
              simpa [βX, GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor] using
                J.uliftSheafifiedRepresentableHomEquiv_naturality inZ ℱ βX
        _ = sZ := hsX.2
        _ = J.uliftSheafifiedRepresentableHomEquiv ℱ Z αZ := by
              symm
              exact (J.uliftSheafifiedRepresentableHomEquiv ℱ Z).apply_symm_apply sZ
    have hβ :
        βX = αX := hpushout.hom_ext
          (hβY.trans (hpushout.inl_desc αY αZ hdesc).symm)
          (hβZ.trans (hpushout.inr_desc αY αZ hdesc).symm)
    have hsβ :
        J.uliftSheafifiedRepresentableHomEquiv ℱ X βX =
          J.uliftSheafifiedRepresentableHomEquiv ℱ X αX :=
      congrArg (J.uliftSheafifiedRepresentableHomEquiv ℱ X) hβ
    calc
      sX = J.uliftSheafifiedRepresentableHomEquiv ℱ X βX := by
            symm
            change
              J.uliftSheafifiedRepresentableHomEquiv ℱ X
                  ((J.uliftSheafifiedRepresentableHomEquiv ℱ X).symm sX) = sX
            exact (J.uliftSheafifiedRepresentableHomEquiv ℱ X).apply_symm_apply sX
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ X αX := hsβ

-- Proof sketch: unwrap `freeAbelianSheafifiedRepresentableHomEquivSections` into the sheaf
-- adjunction followed by the usual sheafified-representable equivalence, then use naturality of
-- each owner equivalence in turn.
omit [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: the free-abelian sheafified-representable Hom/sections equivalence
is natural in the source object. -/
private theorem freeAbelianSheafifiedRepresentableHomEquivSections_naturality
    {U V : C} (φ : U ⟶ V) (𝒜 : SiteAbelianSheafCat J)
    (α : (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[V]^#[J] ⟶ 𝒜) :
    freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜
        (((Sheaf.composeAndSheafify J AddCommGrpCat.free).map
          (J.sheafifiedRepresentableMap φ)) ≫ α) =
      𝒜.obj.map φ.op
        (freeAbelianSheafifiedRepresentableHomEquivSections J V 𝒜 α) := by
  let β : h[V]^#[J] ⟶ (sheafForget J).obj 𝒜 :=
    (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[V]^#[J] 𝒜 α
  -- First rewrite through the free-forgetful sheaf adjunction, then apply the source naturality
  -- of `uliftSheafifiedRepresentableHomEquiv`.
  change
    J.uliftSheafifiedRepresentableHomEquiv ((sheafForget J).obj 𝒜) U
      (((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] 𝒜)
        (((Sheaf.composeAndSheafify J AddCommGrpCat.free).map
          (J.sheafifiedRepresentableMap φ)) ≫ α)) =
      _
  rw [show
      ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] 𝒜)
          (((Sheaf.composeAndSheafify J AddCommGrpCat.free).map
            (J.sheafifiedRepresentableMap φ)) ≫ α) =
        J.sheafifiedRepresentableMap φ ≫ β by
          dsimp [β]
          exact (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv_naturality_left
            (J.sheafifiedRepresentableMap φ) α]
  simpa [β] using
    J.uliftSheafifiedRepresentableHomEquiv_naturality φ ((sheafForget J).obj 𝒜) β

/-- Helper for Lemma 21.26.3: the free abelian sheafified representable over `U`. -/
private abbrev freeAbelianSheafifiedRepresentable
    (U : C) : SiteAbelianSheafCat J :=
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J]

/-- Helper for Lemma 21.26.3: the free-abelian sheafified-representable Hom/sections equivalence
is natural in the codomain sheaf. -/
private theorem freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right
    (U : C) {𝒜 ℬ : SiteAbelianSheafCat J} (f : 𝒜 ⟶ ℬ)
    (α : J.freeAbelianSheafifiedRepresentable U ⟶ 𝒜) :
    freeAbelianSheafifiedRepresentableHomEquivSections J U ℬ (α ≫ f) =
      f.hom.app (Opposite.op U)
        (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 α) := by
  let β : h[U]^#[J] ⟶ (sheafForget J).obj 𝒜 :=
    (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] 𝒜 α
  -- Rewrite through the sheaf adjunction, then use right naturality of the representable
  -- sections equivalence.
  change
    J.uliftSheafifiedRepresentableHomEquiv ((sheafForget J).obj ℬ) U
      (((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] ℬ) (α ≫ f)) =
      _
  rw [show
      ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] ℬ) (α ≫ f) =
        β ≫ (sheafForget J).map f by
          dsimp [β]
          exact (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv_naturality_right
            α f]
  simpa [β] using
    J.uliftSheafifiedRepresentableHomEquiv_comp β ((sheafForget J).map f)

/-- Helper for Lemma 21.26.3: the free-abelian sheafified-representable Hom/sections equivalence
sends the zero morphism to the zero section. -/
private theorem freeAbelianSheafifiedRepresentableHomEquivSections_zero
    (U : C) (𝒜 : SiteAbelianSheafCat J) :
    freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜
        (0 : J.freeAbelianSheafifiedRepresentable U ⟶ 𝒜) = 0 := by
  let G := J.freeAbelianSheafifiedRepresentable U
  calc
    freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜
        (0 : G ⟶ 𝒜) =
      (0 : G ⟶ 𝒜).hom.app (Opposite.op U)
        (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G)) := by
          simpa [G] using
            J.freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right U
              (0 : G ⟶ 𝒜) (𝟙 G)
    _ = 0 := by
      change (0 : G.obj.obj (Opposite.op U) ⟶ 𝒜.obj.obj (Opposite.op U))
          (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G)) = 0
      rfl

/-- Helper for Lemma 21.26.3: the free-abelian sheafified-representable Hom/sections equivalence
is additive. -/
private theorem freeAbelianSheafifiedRepresentableHomEquivSections_add
    (U : C) (𝒜 : SiteAbelianSheafCat J)
    (a b : J.freeAbelianSheafifiedRepresentable U ⟶ 𝒜) :
    freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 (a + b) =
      freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 a +
        freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 b := by
  let G := J.freeAbelianSheafifiedRepresentable U
  calc
    freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 (a + b) =
      (a + b).hom.app (Opposite.op U)
        (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G)) := by
          simpa [G] using
            J.freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right U
              (a + b) (𝟙 G)
    _ = a.hom.app (Opposite.op U)
          (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G)) +
        b.hom.app (Opposite.op U)
          (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G)) := by
            change ((a.hom.app (Opposite.op U)) + (b.hom.app (Opposite.op U)))
                (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G)) =
              a.hom.app (Opposite.op U)
                (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G)) +
                b.hom.app (Opposite.op U)
                  (freeAbelianSheafifiedRepresentableHomEquivSections J U G (𝟙 G))
            rfl
    _ = freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 (𝟙 G ≫ a) +
        freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 (𝟙 G ≫ b) := by
          rw [← J.freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right U a (𝟙 G)]
          rw [← J.freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right U b (𝟙 G)]
    _ = freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 a +
          freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 b := by
            simpa [G] using congrArg₂ HAdd.hAdd
              (congrArg
                (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜)
                (Category.id_comp a))
              (congrArg
                (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜)
                (Category.id_comp b))

/-- Helper for Lemma 21.26.3: morphisms from the free abelian sheafified representable identify
additively with sections over `U`. -/
private noncomputable def freeAbelianSheafifiedRepresentableHomAddEquivSections
    (U : C) (𝒜 : SiteAbelianSheafCat J) :
    (J.freeAbelianSheafifiedRepresentable U ⟶ 𝒜) ≃+
      ((siteAbelianSectionsFunctor J U).obj 𝒜) where
  toEquiv := freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜
  map_add' := J.freeAbelianSheafifiedRepresentableHomEquivSections_add U 𝒜

/-- Helper for Lemma 21.26.3: sections over `U` identify additively with morphisms from the free
abelian sheafified representable on `U`. -/
private noncomputable def siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom
    (U : C) (𝒜 : SiteAbelianSheafCat J) :
    ((siteAbelianSectionsFunctor J U).obj 𝒜) ≃+
      (J.freeAbelianSheafifiedRepresentable U ⟶ 𝒜) :=
  (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U 𝒜).symm

/-- Helper for Lemma 21.26.3: the additive sections/free-sheafified-representable comparison is
natural in the sheaf variable. -/
private theorem siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom_naturality
    {U : C} {𝒜 ℬ : SiteAbelianSheafCat J} (f : 𝒜 ⟶ ℬ)
    (s : (siteAbelianSectionsFunctor J U).obj 𝒜) :
    J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U ℬ
        ((siteAbelianSectionsFunctor J U).map f s) =
      J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜 s ≫ f := by
  -- Proof comment: apply the forward additive equivalence, so the claim becomes the already
  -- proved right-naturality of `freeAbelianSheafifiedRepresentableHomEquivSections`.
  apply (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U ℬ).injective
  calc
    (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U ℬ)
        (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U ℬ
          ((siteAbelianSectionsFunctor J U).map f s)) =
      (siteAbelianSectionsFunctor J U).map f s := by
        exact (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U ℬ).apply_symm_apply _
    _ = (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U ℬ)
          (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜 s ≫ f) := by
          symm
          have hRight :
              (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U ℬ)
                  (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜 s ≫ f) =
                f.hom.app (Opposite.op U)
                  ((J.freeAbelianSheafifiedRepresentableHomAddEquivSections U 𝒜)
                    (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜 s)) := by
            simpa [freeAbelianSheafifiedRepresentableHomAddEquivSections] using
              J.freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right U f
                (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜 s)
          have hMap :
              f.hom.app (Opposite.op U)
                  ((J.freeAbelianSheafifiedRepresentableHomAddEquivSections U 𝒜)
                    (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜 s)) =
                (siteAbelianSectionsFunctor J U).map f s := by
            have hs :
                (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U 𝒜)
                    (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜 s) = s := by
              exact (J.freeAbelianSheafifiedRepresentableHomAddEquivSections U 𝒜).apply_symm_apply s
            simpa [siteAbelianSectionsFunctor] using
              congrArg (f.hom.app (Opposite.op U)) hs
          exact hRight.trans hMap

/-- Helper for Lemma 21.26.3: `Γ(U,-)` is naturally isomorphic to `Hom(FreeAb(h[U]^#), -)`. -/
private noncomputable def siteAbelianSectionsIsoSheafifiedRepresentableFreeHom
    (U : C) :
    siteAbelianSectionsFunctor J U ≅
      preadditiveCoyoneda.obj (Opposite.op (J.freeAbelianSheafifiedRepresentable U)) :=
  NatIso.ofComponents
    (fun 𝒜 ↦
      (J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom U 𝒜).toAddCommGrpIso)
    (fun f ↦ by
      ext s
      exact J.siteAbelianSectionsAddEquivSheafifiedRepresentableFreeHom_naturality f s)

-- Proof sketch: `composeAndSheafify` is the composite "forget to presheaves, whisker with
-- `AddCommGrpCat.free`, then sheafify", so its map on a sheaf morphism is exactly the sheafified
-- whiskered free presheaf map.
omit [HasWeakSheafify J (Type (max u v))]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: the map induced by `composeAndSheafify` is the sheafification of the
free-abelian whiskering of the underlying set-valued sheaf map. -/
private theorem composeAndSheafify_map_eq_presheafToSheaf_map
    {𝒢₁ 𝒢₂ : Sheaf J (Type (max u v))} (φ : 𝒢₁ ⟶ 𝒢₂) :
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map φ =
      (presheafToSheaf J AddCommGrpCat.{max u v}).map
        (Functor.whiskerRight
          ((sheafToPresheaf J (Type (max u v))).map φ)
          AddCommGrpCat.free) := by
  -- Route correction: keep the normalization at the owner definition of `composeAndSheafify`
  -- instead of introducing an extra sheafification layer.
  rfl

-- Proof sketch: check monomorphy objectwise on the underlying natural transformation of
-- presheaves. Each component is the free abelian group map induced by an injective map of sets,
-- so the Chapter 20 left-inverse argument applies verbatim.
omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: whiskering the underlying set-valued sheaf map with the free
abelian group functor preserves monomorphisms. -/
private theorem free_whisker_map_mono_of_mono
    {𝒢₁ 𝒢₂ : Sheaf J (Type (max u v))} (φ : 𝒢₁ ⟶ 𝒢₂) [Mono φ] :
    Mono (Functor.whiskerRight
      ((sheafToPresheaf J (Type (max u v))).map φ)
      AddCommGrpCat.free) := by
  classical
  -- Reduce to injectivity of each free-abelian-group map on generators.
  refine (NatTrans.mono_iff_mono_app _).2 ?_
  intro U
  rw [AddCommGrpCat.mono_iff_injective]
  let f :
      (((sheafToPresheaf J (Type (max u v))).obj 𝒢₁).obj U) →
        (((sheafToPresheaf J (Type (max u v))).obj 𝒢₂).obj U) :=
    (((sheafToPresheaf J (Type (max u v))).map φ).app U)
  have hf : Function.Injective f := by
    have hφhom :
        Mono ((sheafToPresheaf J (Type (max u v))).map φ) :=
      (sheafToPresheaf J (Type (max u v))).map_mono φ
    exact (mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app _).1 hφhom U)
  intro x y hxy
  let r :
      (((sheafToPresheaf J (Type (max u v))).obj 𝒢₂).obj U) →
        FreeAbelianGroup (((sheafToPresheaf J (Type (max u v))).obj 𝒢₁).obj U) :=
    fun h ↦
      if hh : ∃ g : (((sheafToPresheaf J (Type (max u v))).obj 𝒢₁).obj U), f g = h then
        FreeAbelianGroup.of (Classical.choose hh)
      else
        0
  have hr :
      ∀ g : (((sheafToPresheaf J (Type (max u v))).obj 𝒢₁).obj U),
        r (f g) = FreeAbelianGroup.of g := by
    intro g
    dsimp [r]
    split_ifs with hh
    · apply congrArg FreeAbelianGroup.of
      exact hf (Classical.choose_spec hh)
    · exact (hh ⟨g, rfl⟩).elim
  have hmap :
      Function.LeftInverse
        (FreeAbelianGroup.lift r)
        (AddCommGrpCat.free.map f) := by
    intro z
    change FreeAbelianGroup.lift r (FreeAbelianGroup.map f z) = z
    rw [← FreeAbelianGroup.lift_comp f r z]
    have hrf : r ∘ f = FreeAbelianGroup.of := by
      ext g
      exact hr g
    rw [hrf]
    simpa [FreeAbelianGroup.map] using (FreeAbelianGroup.map_id_apply z)
  exact hmap.injective hxy

-- Proof sketch: normalize the `composeAndSheafify` map to a `presheafToSheaf.map`, prove the
-- whiskered free presheaf map is mono objectwise, and then use that abelian sheafification
-- preserves monomorphisms because it is exact.
/-- Helper for Lemma 21.26.3: if `h_E^# ⟶ h_Y^#` is mono, then the induced map on free abelian
sheafified representables is also mono. -/
private theorem freeAbelian_sheafifiedRepresentableMap_mono_of_mono
    {U V : C} (φ : U ⟶ V)
    (hmono : Mono (J.sheafifiedRepresentableMap φ)) :
    Mono ((Sheaf.composeAndSheafify J AddCommGrpCat.free).map
      (J.sheafifiedRepresentableMap φ)) := by
  let _ := (inferInstance : HasWeakSheafify J (Type (max u v)))
  let _ := (inferInstance : IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J))
  let F := presheafToSheaf J AddCommGrpCat.{max u v}
  let hExact : exactFunctor _ _ F :=
    (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩
  letI : PreservesFiniteLimits F := (exactFunctor_iff F).1 hExact |>.1
  letI : Mono (Functor.whiskerRight
      ((sheafToPresheaf J (Type (max u v))).map (J.sheafifiedRepresentableMap φ))
      AddCommGrpCat.free) := by
    letI : Mono (J.sheafifiedRepresentableMap φ) := hmono
    exact J.free_whisker_map_mono_of_mono (J.sheafifiedRepresentableMap φ)
  -- Normalize once to the explicit sheafified free presheaf map, then apply exactness.
  rw [J.composeAndSheafify_map_eq_presheafToSheaf_map (J.sheafifiedRepresentableMap φ)]
  exact F.map_mono (Functor.whiskerRight
    ((sheafToPresheaf J (Type (max u v))).map (J.sheafifiedRepresentableMap φ))
    AddCommGrpCat.free)

-- Proof sketch: represent the chosen section of `ℐ(U)` by a morphism out of the free abelian
-- sheafified representable on `U`, extend it across the mono from the previous lemma by
-- injectivity of `ℐ`, and translate the factorization identity back to sections by naturality.
/-- Helper for Lemma 21.26.3: if `h_U^# ⟶ h_V^#` is mono, then every section of an injective
abelian sheaf over `U` extends to a section over `V`. -/
private lemma injective_sheaf_sections_surjective_of_mono_sheafifiedRepresentableMap
    {U V : C} (φ : U ⟶ V)
    (hmono : Mono (J.sheafifiedRepresentableMap φ))
    (ℐ : SiteAbelianSheafCat J) (hℐ : Injective ℐ) :
    Function.Surjective (((J.siteAbelianSectionsRestrictionNatTrans φ).app ℐ).hom) := by
  letI : Injective ℐ := hℐ
  let ψ := (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (J.sheafifiedRepresentableMap φ)
  letI : Mono ψ :=
    freeAbelian_sheafifiedRepresentableMap_mono_of_mono J φ hmono
  intro s
  let γ :
      (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J] ⟶ ℐ :=
    (freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ).symm s
  let δ :
      (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[V]^#[J] ⟶ ℐ :=
    Injective.factorThru γ ψ
  refine ⟨freeAbelianSheafifiedRepresentableHomEquivSections J V ℐ δ, ?_⟩
  have hδ : ψ ≫ δ = γ := by
    simpa [δ, ψ] using Injective.comp_factorThru γ ψ
  have hs :
      ((J.siteAbelianSectionsRestrictionNatTrans φ).app ℐ).hom
          (freeAbelianSheafifiedRepresentableHomEquivSections J V ℐ δ) =
        freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ γ := by
    calc
      ((J.siteAbelianSectionsRestrictionNatTrans φ).app ℐ).hom
          (freeAbelianSheafifiedRepresentableHomEquivSections J V ℐ δ) =
        freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ (ψ ≫ δ) := by
          simpa [ψ, siteAbelianSectionsRestrictionNatTrans, siteAbelianSectionsFunctor] using
            (J.freeAbelianSheafifiedRepresentableHomEquivSections_naturality φ ℐ δ).symm
      _ = freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ γ := by
        rw [hδ]
  exact hs.trans ((freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ).apply_symm_apply s)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- The canonical first underived Mayer-Vietoris map
`Γ(X,-) ⟶ Γ(Z,-) ⊞ Γ(Y,-)`. -/
private abbrev siteAbelianSectionsMayerVietorisToBiprod
    {X Y Z : C} (inY : Y ⟶ X) (inZ : Z ⟶ X) :
    siteAbelianSectionsFunctor J X ⟶
      siteAbelianSectionsFunctor J Z ⊞ siteAbelianSectionsFunctor J Y :=
  biprod.lift
    (J.siteAbelianSectionsRestrictionNatTrans inZ)
    (J.siteAbelianSectionsRestrictionNatTrans inY)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- The canonical second underived Mayer-Vietoris map
`Γ(Z,-) ⊞ Γ(Y,-) ⟶ Γ(E,-)`. -/
private abbrev siteAbelianSectionsMayerVietorisDifference
    {Y Z E : C} (f : E ⟶ Y) (g : E ⟶ Z) :
    siteAbelianSectionsFunctor J Z ⊞ siteAbelianSectionsFunctor J Y ⟶
      siteAbelianSectionsFunctor J E :=
  biprod.desc
    (J.siteAbelianSectionsRestrictionNatTrans g)
    (-J.siteAbelianSectionsRestrictionNatTrans f)

-- Proof sketch: this is the underived version of
-- `mayerVietorisToBiprod_comp_mayerVietorisDifference`; the pushout relation identifies the two
-- restrictions from `X` to `E`, so their difference is zero already on ordinary sections.
/-- Helper for Lemma 21.26.3: the ordinary section maps
`Γ(X,-) ⟶ Γ(Z,-) ⊞ Γ(Y,-) ⟶ Γ(E,-)` attached to the pushout square compose to zero. -/
private theorem sectionsToBiprod_comp_sectionsDifference
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ)) :
    J.siteAbelianSectionsMayerVietorisToBiprod inY inZ ≫
      J.siteAbelianSectionsMayerVietorisDifference f g = 0 := by
  let _ := (inferInstance : HasWeakSheafify J (Type (max u v)))
  let _ := (inferInstance : IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J))
  rw [biprod.lift_desc]
  -- The pushout equation identifies the two composites `E ⟶ X`.
  have hcomp :
      J.sheafifiedRepresentableMap (f ≫ inY) =
        J.sheafifiedRepresentableMap (g ≫ inZ) := by
    simpa [GrothendieckTopology.sheafifiedRepresentableMap,
      GrothendieckTopology.sheafifiedRepresentableFunctor] using hpushout.w
  have hunderived :
      J.siteAbelianSectionsRestrictionNatTrans (f ≫ inY) =
        J.siteAbelianSectionsRestrictionNatTrans (g ≫ inZ) :=
    J.siteAbelianSectionsRestriction_eq_of_sheafifiedRepresentableMap_eq hcomp
  calc
    J.siteAbelianSectionsRestrictionNatTrans inZ ≫
        J.siteAbelianSectionsRestrictionNatTrans g +
      J.siteAbelianSectionsRestrictionNatTrans inY ≫
        (-J.siteAbelianSectionsRestrictionNatTrans f) =
          J.siteAbelianSectionsRestrictionNatTrans (g ≫ inZ) +
            -J.siteAbelianSectionsRestrictionNatTrans (f ≫ inY) := by
              simp [CategoryTheory.Preadditive.comp_neg,
                siteAbelianSectionsRestriction_comp]
    _ = J.siteAbelianSectionsRestrictionNatTrans (f ≫ inY) +
          -J.siteAbelianSectionsRestrictionNatTrans (f ≫ inY) := by
            rw [← hunderived]
    _ = 0 := by
          simp

-- Proof sketch: the two restrictions of a section on `X` to `E` coincide because the two
-- composites `E ⟶ X` agree after sheafification.
omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] in
/-- Helper for Lemma 21.26.3: any section on `X` restricts compatibly to `Y` and `Z` over `E`. -/
private theorem compatible_restrictions_of_section_of_sheafifiedRepresentable_pushout
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (ℱ : Sheaf J (Type (max u v)))
    (sX : ℱ.obj.obj (Opposite.op X)) :
    ℱ.obj.map f.op (ℱ.obj.map inY.op sX) =
      ℱ.obj.map g.op (ℱ.obj.map inZ.op sX) := by
  have hcomp :
      J.sheafifiedRepresentableMap (f ≫ inY) =
        J.sheafifiedRepresentableMap (g ≫ inZ) := by
    simpa [GrothendieckTopology.sheafifiedRepresentableMap,
      GrothendieckTopology.sheafifiedRepresentableFunctor] using hpushout.w
  have hres :
      ℱ.obj.map (f ≫ inY).op =
        ℱ.obj.map (g ≫ inZ).op :=
    J.sections_restriction_eq_of_sheafifiedRepresentableMap_eq ℱ hcomp
  -- Rewrite both sides as restriction along the two composites out of `E`.
  calc
    ℱ.obj.map f.op (ℱ.obj.map inY.op sX) = ℱ.obj.map (f ≫ inY).op sX := by
      simp
    _ = ℱ.obj.map (g ≫ inZ).op sX := by
      simpa using congrFun hres sX
    _ = ℱ.obj.map g.op (ℱ.obj.map inZ.op sX) := by
      simp

-- Proof sketch: specialize the already-proved natural-transformation vanishing to a fixed sheaf.
/-- Helper for Lemma 21.26.3: the ordinary Mayer-Vietoris composite is zero after evaluating at a
fixed abelian sheaf. -/
private theorem sectionsToBiprod_comp_sectionsDifference_app
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (ℐ : SiteAbelianSheafCat J) :
    ((J.siteAbelianSectionsMayerVietorisToBiprod inY inZ).app ℐ) ≫
        ((J.siteAbelianSectionsMayerVietorisDifference f g).app ℐ) =
      0 := by
  -- Proof comment: this is just the pointwise form of the natural-transformation identity above.
  exact congrArg (fun η ↦ η.app ℐ)
    (J.sectionsToBiprod_comp_sectionsDifference f g inY inZ hpushout)

/-- Helper for Lemma 21.26.3: evaluating the functor-category biproduct of sections at `ℐ`
identifies it with the product of the two evaluated section groups. -/
private noncomputable abbrev siteAbelianSectionsBiprodAppIso
    (ℐ : SiteAbelianSheafCat J) :
    ((siteAbelianSectionsFunctor J Z ⊞ siteAbelianSectionsFunctor J Y).obj ℐ) ≅
      AddCommGrpCat.of
        (((siteAbelianSectionsFunctor J Z).obj ℐ) ×
          ((siteAbelianSectionsFunctor J Y).obj ℐ)) := by
  -- TODO: compare the evaluated functor-category biproduct at `ℐ` with the objectwise biproduct
  -- via a stable owner-level iso, then compose with `AddCommGrpCat.biprodIsoProd`.
  sorry

/-- Helper for Lemma 21.26.3: evaluating the first Mayer-Vietoris natural transformation gives the
expected biproduct lift on section groups. -/
private theorem siteAbelianSectionsRestrictionNatTrans_app_hom
    {U V : C} (φ : U ⟶ V) (ℐ : SiteAbelianSheafCat J) :
    ((J.siteAbelianSectionsRestrictionNatTrans φ).app ℐ).hom = (ℐ.obj.map φ.op).hom := rfl

/-- Helper for Lemma 21.26.3: after evaluating at an abelian sheaf, the first Mayer-Vietoris map
becomes the pair of restriction maps under the standard biproduct/product comparison. -/
private theorem siteAbelianSectionsMayerVietorisToBiprod_apply
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (ℐ : SiteAbelianSheafCat J)
    (s : (siteAbelianSectionsFunctor J X).obj ℐ) :
    ((J.siteAbelianSectionsMayerVietorisToBiprod inY inZ).app ℐ).hom s =
      (J.siteAbelianSectionsBiprodAppIso (Y := Y) (Z := Z) ℐ).inv
        ⟨((J.siteAbelianSectionsRestrictionNatTrans inZ).app ℐ).hom s,
          ((J.siteAbelianSectionsRestrictionNatTrans inY).app ℐ).hom s⟩ := by
  -- TODO: once `siteAbelianSectionsBiprodAppIso` is proved, transport the element to product
  -- coordinates and use the two projection lemmas just above.
  sorry

/-- Helper for Lemma 21.26.3: after evaluating at an abelian sheaf, the second Mayer-Vietoris map
is the difference of the two restriction maps in product coordinates. -/
private theorem siteAbelianSectionsMayerVietorisDifference_biprodIsoProd_inv_apply
    (f : E ⟶ Y)
    (g : E ⟶ Z)
    (ℐ : SiteAbelianSheafCat J)
    (sZ : (siteAbelianSectionsFunctor J Z).obj ℐ)
    (sY : (siteAbelianSectionsFunctor J Y).obj ℐ) :
    ((J.siteAbelianSectionsMayerVietorisDifference f g).app ℐ).hom
        ((J.siteAbelianSectionsBiprodAppIso (Y := Y) (Z := Z) ℐ).inv ⟨sZ, sY⟩) =
      ((J.siteAbelianSectionsRestrictionNatTrans g).app ℐ).hom sZ -
        ((J.siteAbelianSectionsRestrictionNatTrans f).app ℐ).hom sY := by
  -- Proof comment: after rewriting the input through the product comparison, the second map is
  -- exactly the biproduct `desc` of the two restriction maps.
  -- TODO: after the same evaluated-biproduct/product comparison is available, rewrite the input
  -- through `siteAbelianSectionsBiprodAppIso` and apply the two inclusion lemmas above.
  sorry

/-- Helper for Lemma 21.26.3: for an injective abelian sheaf `ℐ`, the ordinary Mayer-Vietoris
row `Γ(X, ℐ) ⟶ Γ(Z, ℐ) ⊞ Γ(Y, ℐ) ⟶ Γ(E, ℐ)` is short exact under the sheafified pushout and
monomorphism hypotheses. -/
private theorem injectiveSheafSectionsMayerVietorisShortExact
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (hmono : Mono (J.sheafifiedRepresentableMap f))
    (ℐ : SiteAbelianSheafCat J) (hℐ : Injective ℐ) :
    (ShortComplex.mk
      ((J.siteAbelianSectionsMayerVietorisToBiprod inY inZ).app ℐ)
      ((J.siteAbelianSectionsMayerVietorisDifference f g).app ℐ)
      (J.sectionsToBiprod_comp_sectionsDifference_app f g inY inZ hpushout ℐ)).ShortExact := by
  -- TODO: once `siteAbelianSectionsBiprodAppIso` and the two pair-formula lemmas above are
  -- proved, show exactness by gluing compatible pairs, monicity by uniqueness of gluing, and
  -- epimorphy by extending `-t` along the mono `h[E]^# ⟶ h[Y]^#`.
  sorry

/-- Helper for Lemma 21.26.3: the cochain Mayer-Vietoris composite on a complex `I` is zero. -/
private theorem mayerVietorisCochainComposite_zero
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    [((siteAbelianSectionsFunctor J Z ⊞
        siteAbelianSectionsFunctor J Y).PreservesZeroMorphisms)]
    (I : CochainComplex (SiteAbelianSheafCat J) ℤ) :
    ((NatTrans.mapHomologicalComplex
        (J.siteAbelianSectionsMayerVietorisToBiprod inY inZ)
        (ComplexShape.up ℤ)).app I) ≫
      ((NatTrans.mapHomologicalComplex
        (J.siteAbelianSectionsMayerVietorisDifference f g)
        (ComplexShape.up ℤ)).app I) =
        0 := by
  -- Proof comment: `mapHomologicalComplex` is checked degreewise, where the ordinary
  -- Mayer-Vietoris composite already vanishes.
  apply HomologicalComplex.hom_ext
  intro n
  simpa using
    J.sectionsToBiprod_comp_sectionsDifference_app f g inY inZ hpushout (I.X n)

/-- Helper for Lemma 21.26.3: if `I` is termwise injective, then the cochain Mayer-Vietoris row
of section complexes is short exact degreewise and hence short exact as a short complex of
cochain complexes. -/
private theorem mayerVietorisCochainShortExact_of_termwiseInjective
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (hmono : Mono (J.sheafifiedRepresentableMap f))
    [((siteAbelianSectionsFunctor J Z ⊞
        siteAbelianSectionsFunctor J Y).PreservesZeroMorphisms)]
    (I : CochainComplex (SiteAbelianSheafCat J) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    (let α :=
        (NatTrans.mapHomologicalComplex
          (J.siteAbelianSectionsMayerVietorisToBiprod inY inZ)
          (ComplexShape.up ℤ)).app I
      let β :=
        (NatTrans.mapHomologicalComplex
          (J.siteAbelianSectionsMayerVietorisDifference f g)
          (ComplexShape.up ℤ)).app I
      ShortComplex.mk α β
        (J.mayerVietorisCochainComposite_zero f g inY inZ hpushout I)).ShortExact := by
  -- Proof comment: short exactness of the cochain row is degreewise short exactness of the
  -- injective sheaf row already proved above.
  dsimp
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n ↦ by
      simpa using
        J.injectiveSheafSectionsMayerVietorisShortExact
          f g inY inZ hpushout hmono (I.X n) (hI n))

/-- Helper for Lemma 21.26.3: the short exact cochain Mayer-Vietoris model coming from a
termwise-injective complex yields a quasi-isomorphism from the mapping cone of the first map to
the overlap complex. -/
private theorem mayerVietorisMappingConeQuasiIso_of_termwiseInjective
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (hmono : Mono (J.sheafifiedRepresentableMap f))
    [((siteAbelianSectionsFunctor J Z ⊞
        siteAbelianSectionsFunctor J Y).PreservesZeroMorphisms)]
    (I : CochainComplex (SiteAbelianSheafCat J) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    let α :=
      (NatTrans.mapHomologicalComplex
        (J.siteAbelianSectionsMayerVietorisToBiprod inY inZ)
        (ComplexShape.up ℤ)).app I
    let β :=
      (NatTrans.mapHomologicalComplex
        (J.siteAbelianSectionsMayerVietorisDifference f g)
        (ComplexShape.up ℤ)).app I
    let hαβ := J.mayerVietorisCochainComposite_zero f g inY inZ hpushout I
    QuasiIso (CochainComplex.mappingCone.descShortComplex (ShortComplex.mk α β hαβ)) := by
  -- Proof comment: once the cochain Mayer-Vietoris row is short exact, the mapping-cone owner
  -- theorem supplies the quasi-isomorphism automatically.
  dsimp
  have hShort :
      (ShortComplex.mk
        ((NatTrans.mapHomologicalComplex
          (J.siteAbelianSectionsMayerVietorisToBiprod inY inZ)
          (ComplexShape.up ℤ)).app I)
        ((NatTrans.mapHomologicalComplex
          (J.siteAbelianSectionsMayerVietorisDifference f g)
          (ComplexShape.up ℤ)).app I)
        (J.mayerVietorisCochainComposite_zero f g inY inZ hpushout I)).ShortExact := by
    simpa using
      J.mayerVietorisCochainShortExact_of_termwiseInjective
        f g inY inZ hpushout hmono I hI
  simpa using CochainComplex.mappingCone.quasiIso_descShortComplex hShort

/-- Helper for Lemma 21.26.3: fix a functorial K-injective replacement on cochain complexes of
abelian sheaves on `J`. -/
private noncomputable abbrev siteAbelianSectionsKInjectiveResolution :
    CochainComplex.FunctorialComplexApproximation (SiteAbelianSheafCat J) :=
  Classical.choose
    (CochainComplex.exists_functorial_kInjective_resolution
      (SiteAbelianSheafCat J))

/-- Helper for Lemma 21.26.3: the chosen functorial replacement lands in K-injective complexes. -/
private theorem siteAbelianSectionsKInjectiveResolution_isKInjective
    (K : CochainComplex (SiteAbelianSheafCat J) ℤ) :
    ((J.siteAbelianSectionsKInjectiveResolution).toFunctor.obj K).IsKInjective := by
  -- Proof comment: the Chapter 19 functorial replacement theorem records K-injectivity
  -- objectwise for the chosen approximation.
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution
        (SiteAbelianSheafCat J))).2 K

/-- Helper for Lemma 21.26.3: the chosen functorial replacement has injective terms in every
degree. -/
private theorem siteAbelianSectionsKInjectiveResolution_termwiseInjective
    (K : CochainComplex (SiteAbelianSheafCat J) ℤ) (n : ℤ) :
    Injective (((J.siteAbelianSectionsKInjectiveResolution).toFunctor.obj K).X n) := by
  -- Proof comment: the same Chapter 19 package records termwise injectivity together with
  -- K-injectivity for the chosen approximation functor.
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution
        (SiteAbelianSheafCat J))).1 K n

/-- Helper for Lemma 21.26.3: a K-injective complex computes the homotopy-side derived sections
functor attached to `Γ(U,-)`. -/
private theorem siteAbelianSectionsHomotopy_hasPointwiseRightDerivedFunctor
    (U : C) :
    Functor.HasPointwiseRightDerivedFunctor
      (((siteAbelianSectionsFunctor J U).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (SiteAbelianSheafCat J)
        (ComplexShape.up ℤ)) := by
  let F :
      HomotopyCategory (SiteAbelianSheafCat J) (ComplexShape.up ℤ) ⥤ DAb :=
    ((siteAbelianSectionsFunctor J U).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Qh
  let Qish :
      MorphismProperty
        (HomotopyCategory (SiteAbelianSheafCat J) (ComplexShape.up ℤ)) :=
    HomotopyCategory.quasiIso
      (SiteAbelianSheafCat J)
      (ComplexShape.up ℤ)
  -- Proof comment: every homotopy object is connected by a quasi-isomorphism to the chosen
  -- K-injective replacement of a representative, and that replacement computes the derived
  -- functor by the Chapter 13 owner theorem.
  refine F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt Qish ?_
  intro K
  obtain ⟨Kres, _, hKinj⟩ :=
    CochainComplex.exists_functorial_kInjective_resolution
      (SiteAbelianSheafCat J)
  refine
    ⟨(HomotopyCategory.quotient
        (SiteAbelianSheafCat J)
        (ComplexShape.up ℤ)).obj
        (Kres.toFunctor.obj K.as), ?_, ?_, ?_⟩
  · -- Proof comment: the quotient of the chosen replacement arrow gives the required denominator.
    simpa [HomotopyCategory.quotient_obj_as] using
      (HomotopyCategory.quotient
        (SiteAbelianSheafCat J)
        (ComplexShape.up ℤ)).map
        (Kres.ι.app K.as)
  · -- Proof comment: the chosen replacement arrow is a quasi-isomorphism by construction.
    exact
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (Kres.ι.app K.as)).2
        (Kres.quasiIso_app K.as)
  · letI : (Kres.toFunctor.obj K.as).IsKInjective := hKinj K.as
    simpa [F, Qish] using
      (kInjective_computesRightDerivedFunctorAt
        F
        (Kres.toFunctor.obj K.as))

/-- Helper for Lemma 21.26.3: a K-injective complex computes the homotopy-side derived sections
functor attached to `Γ(U,-)`. -/
private theorem siteAbelianSectionsHomotopy_computesRightDerivedAt_of_isKInjective
    (U : C)
    (I : CochainComplex (SiteAbelianSheafCat J) ℤ) [I.IsKInjective] :
    let F :
        HomotopyCategory (SiteAbelianSheafCat J) (ComplexShape.up ℤ) ⥤ DAb :=
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh
    let Qish :
        MorphismProperty
          (HomotopyCategory (SiteAbelianSheafCat J) (ComplexShape.up ℤ)) :=
      HomotopyCategory.quasiIso
        (SiteAbelianSheafCat J)
        (ComplexShape.up ℤ)
    F.ComputesRightDerivedAt
      Qish
      ((HomotopyCategory.quotient (SiteAbelianSheafCat J) (ComplexShape.up ℤ)).obj I) := by
  let F :
      HomotopyCategory (SiteAbelianSheafCat J) (ComplexShape.up ℤ) ⥤ DAb :=
    ((siteAbelianSectionsFunctor J U).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Qh
  let Qish :
      MorphismProperty
        (HomotopyCategory (SiteAbelianSheafCat J) (ComplexShape.up ℤ)) :=
    HomotopyCategory.quasiIso
      (SiteAbelianSheafCat J)
      (ComplexShape.up ℤ)
  -- Proof comment: this is the Chapter 13 computation owner specialized to the sections functor.
  simpa [F, Qish] using
    (kInjective_computesRightDerivedFunctorAt
      F
      I)

/-- Helper for Lemma 21.26.3: the Chapter 19 exact-model derived sections owner is already
computed by a K-injective complex. -/
private theorem siteAbelianSectionsAdditiveDerivedUnit_app_isIso_of_isKInjective
    (U : C)
    (I : CochainComplex (SiteAbelianSheafCat J) ℤ) [I.IsKInjective] :
    IsIso ((additiveFunctorTotalRightDerivedUnit (siteAbelianSectionsFunctor J U)).app I) := by
  -- TODO: factor the Chapter 19 unit through the homotopy-side unit exactly as in
  -- `Lemma_21_21_1.pushforwardDerivedUnit_app_isIso_of_isKInjective`, then apply
  -- `Functor.computesRightDerivedAt_iff` only to that middle factor.
  sorry

/-- Helper for Lemma 21.26.3: the Chapter 19 exact-model owner at `K` is obtained by applying
ordinary sections to the chosen K-injective representative of `K`. -/
private noncomputable def siteAbelianSectionsAdditiveDerivedObjIso
    (U : C) (K : DSh) :
    (additiveFunctorTotalRightDerived (siteAbelianSectionsFunctor J U)).obj K ≅
      (siteAbelianSectionsToDerived J U).obj
        ((J.siteAbelianSectionsKInjectiveResolution).toFunctor.obj
          (DerivedCategory.Q.objPreimage K)) := by
  -- TODO: after the previous unit-is-iso lemma is in place, compare `K` with the chosen
  -- K-injective representative via `Q.objObjPreimageIso K` and the derived image of the chosen
  -- resolution arrow, then invert the cochain-level unit at that representative.
  sorry

-- Proof sketch: use the pushout description of `h_X^#` together with the monomorphism
-- `h_E^# ⟶ h_Y^#` to show that for every injective abelian sheaf `ℐ`, the sequence
-- `0 ⟶ ℐ(X) ⟶ ℐ(Z) ⊞ ℐ(Y) ⟶ ℐ(E) ⟶ 0` is short exact. Applying this to a K-injective
-- representative of each `K : DerivedCategory (SiteAbelianSheafCat J)` gives comparison morphisms
-- to the mapping cocone
-- from Lemma `21.26.1`, and those comparisons are quasi-isomorphisms. Lemma `21.26.1` then
-- yields the distinguished triangle, while the construction is natural in `K`.
/-- Lemma 21.26.3: if the sheafified representable `h_X^#` is a pushout of
`h_E^# ⟶ h_Y^#` and `h_E^# ⟶ h_Z^#` through the sheafified maps of a commutative square
`Y ⟶ X`, `Z ⟶ X`, and if `h_E^# ⟶ h_Y^#` is a monomorphism, then there is a functorial
Mayer-Vietoris triangle on `DerivedCategory (SiteAbelianSheafCat J)` whose terms are the canonical
derived sections functors `RΓ[J](X)`, `RΓ[J](Z) ⊞ RΓ[J](Y)`, and `RΓ[J](E)`, and this triangle is
distinguished for every `K`. In Lean these are the owner functors `RΓ[J](X)`, `RΓ[J](Y)`,
`RΓ[J](Z)`, and `RΓ[J](E)`, with canonical middle term `RΓ[J](Z) ⊞ RΓ[J](Y)`, the canonical
maps `siteAbelianSectionsDerivedMayerVietorisToBiprod inY inZ` and
`siteAbelianSectionsDerivedMayerVietorisDifference f g`, and an
existential boundary morphism. -/
@[stacks 0EVY]
theorem exists_functorial_mayerVietoris_triangle_of_sheafifiedRepresentable_pushout
    (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X)
    (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (hmono : Mono (J.sheafifiedRepresentableMap f)) :
    ∃ delta : RΓ[J](E) ⟶ RΓ[J](X) ⋙ shiftFunctor DAb (1 : ℤ),
      ∀ K : DSh,
        Triangle.mk
            ((J.siteAbelianSectionsDerivedMayerVietorisToBiprod inY inZ).app K)
            ((J.siteAbelianSectionsDerivedMayerVietorisDifference f g).app K)
            (delta.app K) ∈
          distTriang DAb := by
  -- TODO: the underived ingredients are now isolated: the ordinary Mayer-Vietoris composite
  -- vanishes pointwise, compatible sections glue uniquely across the sheafified pushout, and
  -- injective sheaves give surjective restriction along the mono `h[E]^# ⟶ h[Y]^#`. The
  -- remaining work is to turn the new exact-model owner bridge into a functor-level comparison
  -- with the public owners `RΓ[J](U)`, then transport the exact-model distinguished triangle
  -- across that comparison before defining the boundary natural transformation.
  sorry

end

end CategoryTheory.GrothendieckTopology
