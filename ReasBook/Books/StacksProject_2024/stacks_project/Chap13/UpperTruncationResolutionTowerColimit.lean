import StacksProject_2024.stacks_project.Chap13.Lemma_13_29_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_10.ColimitHomology

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Opposite TopCat TopologicalSpace

noncomputable section

universe v u

namespace CategoryTheory.UpperTruncationResolutionTower

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasColimitsOfShape ℕ C]
variable {P : ObjectProperty C} {K : CochainComplex C ℤ}

/-- Once the truncation cutoff contains degree `i`, the stage map from an upper-truncation
resolution tower to the target complex is a quasi-isomorphism in degree `i`. -/
theorem toTarget_quasiIsoAt_of_le_stage
    (T : UpperTruncationResolutionTower P K)
    (i : ℤ) {n : ℕ} (h : i ≤ (n : ℤ) + 1) :
    QuasiIsoAt (T.toTarget n) i := by
  change QuasiIsoAt (T.comparison.app n ≫ K.ιTruncLE ((n : ℤ) + 1)) i
  have hcomparison : QuasiIsoAt (T.comparison.app n) i :=
    (T.isResolutionStage n).quasiIso.quasiIsoAt i
  have htrunc : QuasiIsoAt (K.ιTruncLE ((n : ℤ) + 1)) i := by
    simpa using CochainComplex.quasiIsoAt_ιTruncLE K ((n : ℤ) + 1) i h
  rw [quasiIsoAt_iff_isIso_homologyMap] at hcomparison htrunc ⊢
  let e₁ : _ ≅ _ := asIso (HomologicalComplex.homologyMap (T.comparison.app n) i)
  let e₂ : _ ≅ _ := asIso (HomologicalComplex.homologyMap (K.ιTruncLE ((n : ℤ) + 1)) i)
  refine ⟨⟨e₂.inv ≫ e₁.inv, ?_, ?_⟩⟩
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]

/-- After a stage whose cutoff contains degree `i`, the induced diagram on `i`th homology is
eventually constant. -/
theorem homologyDiagram_isEventuallyConstantFrom_of_le_stage
    (T : UpperTruncationResolutionTower P K)
    (i : ℤ) {n : ℕ} (h : i ≤ (n : ℤ) + 1) :
    Functor.IsEventuallyConstantFrom
      (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) n := by
  intro j f
  have hnj : n ≤ j := leOfHom f
  have hsource : QuasiIsoAt (T.toTarget n) i :=
    toTarget_quasiIsoAt_of_le_stage T i h
  have htarget : QuasiIsoAt (T.toTarget j) i :=
    toTarget_quasiIsoAt_of_le_stage T i (by omega)
  have hcomp : T.diagram.map f ≫ T.toTarget j = T.toTarget n := by
    change T.diagram.map f ≫ T.cocone.ι.app j = T.cocone.ι.app n
    exact T.cocone.w f
  have hstep : QuasiIsoAt (T.diagram.map f) i := by
    letI : QuasiIsoAt (T.diagram.map f ≫ T.toTarget j) i := by
      simpa [hcomp] using hsource
    exact quasiIsoAt_of_comp_right (T.diagram.map f) (T.toTarget j) i
  rw [quasiIsoAt_iff_isIso_homologyMap] at hstep
  simpa [Functor.comp_map] using hstep

/-- For each fixed degree, the homology cocone of an upper-truncation resolution tower is
colimiting because the stage maps to the target become isomorphisms on that homology group after
the cutoff passes the degree. -/
noncomputable def toTarget_homologyCocone_isColimit
    (T : UpperTruncationResolutionTower P K)
    (i : ℤ) :
    IsColimit
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone T.cocone) := by
  let n0 : ℕ := Int.toNat i
  have hle : i ≤ (n0 : ℤ) + 1 := by
    by_cases hnonneg : 0 ≤ i
    · rw [Int.toNat_of_nonneg hnonneg]
      omega
    · have hnonpos : i ≤ 0 := le_of_not_ge hnonneg
      dsimp [n0]
      rw [Int.toNat_of_nonpos hnonpos]
      omega
  let hstable :
      Functor.IsEventuallyConstantFrom
        (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) n0 :=
    homologyDiagram_isEventuallyConstantFrom_of_le_stage T i hle
  have hstage : QuasiIsoAt (T.toTarget n0) i :=
    toTarget_quasiIsoAt_of_le_stage T i hle
  rw [quasiIsoAt_iff_isIso_homologyMap] at hstage
  haveI :
      IsIso
        (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone
          T.cocone).ι.app n0) := by
    simpa [n0] using hstage
  exact hstable.isColimitOfIsIso
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone T.cocone)

/-- If degreewise homology commutes with sequential colimits for the ambient category, then the
canonical map from the sequential colimit of an upper-truncation resolution tower to the target
complex is a quasi-isomorphism. -/
theorem fromColimit_quasiIso_of_colimit_homology_iso
    (colimit_homology_iso :
      ∀ (S : ℕ ⥤ CochainComplex C ℤ) (i : ℤ),
        colimit (S ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) ≅
          (colimit S).homology i)
    (colimit_homology_iso_hom_ι :
      ∀ (S : ℕ ⥤ CochainComplex C ℤ) (i : ℤ) (n : ℕ),
        colimit.ι (S ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) n ≫
            (colimit_homology_iso S i).hom =
          HomologicalComplex.homologyMap (colimit.ι S n) i)
    (T : UpperTruncationResolutionTower P K) :
    QuasiIso T.fromColimit := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hdesc :
      IsIso
        (colimit.desc
          (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i)
          ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone
            T.cocone)) := by
    let hcocone :
        Cocone (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) :=
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone T.cocone
    let f :
        colimit.cocone
            (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) ⟶
          hcocone :=
      { hom := colimit.desc _ hcocone
        w n := colimit.ι_desc hcocone n }
    let hcolim := toTarget_homologyCocone_isColimit T i
    haveI : IsIso f :=
      IsColimit.hom_isIso
        (colimit.isColimit
          (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i))
        hcolim f
    let e :
        colimit.cocone
            (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) ≅
          hcocone := asIso f
    refine ⟨⟨e.inv.hom, ?_, ?_⟩⟩
    · exact congrArg CoconeMorphism.hom e.hom_inv_id
    · exact congrArg CoconeMorphism.hom e.inv_hom_id
  have hcomp :
      IsIso
        ((colimit_homology_iso T.diagram i).hom ≫
          HomologicalComplex.homologyMap T.fromColimit i) := by
    rw [show
      (colimit_homology_iso T.diagram i).hom ≫
          HomologicalComplex.homologyMap T.fromColimit i =
        colimit.desc
          (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i)
          ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone
            T.cocone) by
      apply colimit.hom_ext
      intro n
      have hmapcomp :
          HomologicalComplex.homologyMap (colimit.ι T.diagram n) i ≫
              HomologicalComplex.homologyMap T.fromColimit i =
            HomologicalComplex.homologyMap (colimit.ι T.diagram n ≫ T.fromColimit) i := by
        rw [HomologicalComplex.homologyMap_comp]
      have hleft :
          colimit.ι
              (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) n ≫
              (colimit_homology_iso T.diagram i).hom ≫
                HomologicalComplex.homologyMap T.fromColimit i =
            HomologicalComplex.homologyMap (colimit.ι T.diagram n) i ≫
              HomologicalComplex.homologyMap T.fromColimit i := by
        rw [← Category.assoc, colimit_homology_iso_hom_ι]
        rfl
      have htarget :
          HomologicalComplex.homologyMap (colimit.ι T.diagram n ≫ T.fromColimit) i =
            colimit.ι
              (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) n ≫
                colimit.desc
                  (T.diagram ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i)
                  ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone
                    T.cocone) := by
        rw [UpperTruncationResolutionTower.ι_comp_fromColimit]
        rw [colimit.ι_desc
          (c := (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone T.cocone)
          (j := n)]
        change HomologicalComplex.homologyMap (T.cocone.ι.app n) i =
          ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).mapCocone T.cocone).ι.app n
        rfl
      exact hleft.trans (hmapcomp.trans htarget)]
    exact hdesc
  exact
    (isIso_comp_left_iff
      ((colimit_homology_iso T.diagram i).hom)
      (HomologicalComplex.homologyMap T.fromColimit i)).1 hcomp

end

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- For an upper-truncation resolution tower of `𝒪`-modules, the canonical map from the
sequential colimit of the tower to the target complex is a quasi-isomorphism. -/
theorem fromColimit_quasiIso_of_ringedSite
    {P : ObjectProperty Mod} {K : CochainComplex Mod ℤ}
    (T : UpperTruncationResolutionTower P K) :
    QuasiIso T.fromColimit :=
  fromColimit_quasiIso_of_colimit_homology_iso
    (C := Mod)
    (P := P)
    (K := K)
    (fun S i ↦
      SheafOfModules.RingedSite.colimit_homology_iso_of_exact_sequential (𝒪 := 𝒪) S i)
    (fun S i n ↦
      SheafOfModules.RingedSite.colimit_homology_iso_of_exact_sequential_hom_ι
        (𝒪 := 𝒪) S i n)
    T

end

end CategoryTheory.UpperTruncationResolutionTower
