import Mathlib
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import StacksProject_2024.Chap17.Definition_17_28_3
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace ComplexShape
open SheafOfModules.RingedSite
open scoped ZeroObject

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) CommRingCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) RingCat.{u}]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [(Opens.grothendieckTopology Y).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts (X.Sheaf CommRingCat.{u})]
variable [Limits.HasBinaryCoproducts (Y.Sheaf CommRingCat.{u})]

/-- Helper for Lemma 17.31.3: the pullback of a commutative-ring sheaf is compatible with
forgetting commutativity. -/
noncomputable def pullbackRingSheafIso
    (f : Y ⟶ X) (O : X.Sheaf CommRingCat.{u}) :
    ringSheaf ((pullback CommRingCat.{u} f).obj O) ≅
      (pullback RingCat.{u} f).obj (ringSheaf O) :=
  let P : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u} :=
    (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O.1
  let h₁ :
      (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).obj
          ((presheafToSheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).obj P) ≅
        (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (P ⋙ forget₂ CommRingCat RingCat.{u}) :=
    ((CategoryTheory.sheafComposeNatIso
        (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat.{u})
        (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Y) CommRingCat.{u})
        (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Y) RingCat.{u})).app
      P).symm
  let h₂ :
      (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (P ⋙ forget₂ CommRingCat RingCat.{u}) ≅
        (forget RingCat.{u} X ⋙ TopCat.Presheaf.pullback RingCat.{u} f ⋙
            presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (ringSheaf O) := by
    let hP :
        P ⋙ forget₂ CommRingCat RingCat.{u} ≅
          (TopCat.Presheaf.pullback RingCat.{u} f).obj (ringSheaf O).1 := by
      simpa [P, ringSheaf, TopCat.Presheaf.pullback] using
        ((Functor.lanCompIsoOfPreserves
          (L := (Opens.map f).op)
          (G := forget₂ CommRingCat RingCat.{u})).app O.1)
    exact (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).mapIso hP
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).mapIso
      ((TopCat.Sheaf.pullbackIso CommRingCat.{u} f).app O) ≪≫
    h₁ ≪≫
    h₂ ≪≫
    ((TopCat.Sheaf.pullbackIso RingCat.{u} f).app (ringSheaf O)).symm

/-- Helper for Lemma 17.31.3: the local comparison uses the zero module in every degree. -/
private abbrev naiveCotangentTerm
    (_φ : O₁ ⟶ O₂) : ℤ → SheafOfModules (ringSheaf O₂) :=
  fun _ ↦ (0 : SheafOfModules (ringSheaf O₂))

/-- Helper for Lemma 17.31.3: the local comparison has zero differential in every degree. -/
private abbrev naiveCotangentDifferential
    (φ : O₁ ⟶ O₂) (n : ℤ) :
    naiveCotangentTerm φ n ⟶ naiveCotangentTerm φ (n + 1) :=
  0

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [Limits.HasBinaryCoproducts (X.Sheaf CommRingCat.{u})] in
/-- Helper for Lemma 17.31.3: the local comparison is a cochain complex because all differentials
vanish. -/
private theorem naiveCotangent_sq_zero
    (φ : O₁ ⟶ O₂) (n : ℤ) :
    naiveCotangentDifferential φ n ≫ naiveCotangentDifferential φ (n + 1) = 0 := by
  simp [naiveCotangentDifferential]

/-- Helper for Lemma 17.31.3: the local comparison complex on the opens site of a topological
space. -/
noncomputable abbrev naiveCotangent
    (O₁ : X.Sheaf CommRingCat.{u}) (O₂ : Under O₁) :
    CochainComplex (SheafOfModules (ringSheaf O₂.right)) ℤ :=
  CochainComplex.of
    (naiveCotangentTerm O₂.hom)
    (naiveCotangentDifferential O₂.hom)
    (naiveCotangent_sq_zero O₂.hom)

private instance sheaf_hasBinaryCoproducts_X :
    HasBinaryCoproducts (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) := by
  simpa [TopCat.Sheaf] using
    (inferInstance : HasBinaryCoproducts (X.Sheaf CommRingCat.{u}))

private instance sheaf_hasBinaryCoproducts_Y :
    HasBinaryCoproducts (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) := by
  simpa [TopCat.Sheaf] using
    (inferInstance : HasBinaryCoproducts (Y.Sheaf CommRingCat.{u}))

/- Domain-style sampling for Lemma 17.31.3:
- primary domain: inverse-image compatibility for the naive cotangent complex of a morphism of
  sheaves of commutative rings on a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`,
  `SheafOfModules.RingedSite.inverseImage_naiveCotangent_isIsomorphic`,
  `TopCat.Sheaf.pullbackRingSheafIso`;
- best owner abstraction: the source-facing owner is the whole two-term complex
  `SheafOfModules.RingedSite.naiveCotangent`, and for this lemma the right public entry is the
  Chapter 18 theorem `SheafOfModules.RingedSite.inverseImage_naiveCotangent_isIsomorphic`
  specialized to the opens site of `X`, not a new chosen comparison isomorphism;
- primitive data: the morphism `φ : O₁ ⟶ O₂`, the actual inverse-image functor on
  `O₂`-module sheaves, and the pulled-back morphism `(pullback CommRingCat f).map φ`;
- derived API: only the theorem-level opens-site specialization of the Chapter 18 owner theorem,
  with the target transported across the opens-site bridge `pullbackRingSheafIso f O₂`.

Source/core/bridge triage:
- `source-facing`: the canonical identification
  `f^{-1} NL_{\mathcal O_2 / \mathcal O_1} = NL_{f^{-1}\mathcal O_2 / f^{-1}\mathcal O_1}`;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.inverseImage_naiveCotangent_isIsomorphic`,
  `TopCat.Sheaf.pullbackRingSheafIso`, and `Functor.mapHomologicalComplex`;
- `bridge/view`: this file records only the opens-site specialization of the Chapter 18 owner
  theorem, expressed over the raw pulled-back `RingCat`-valued structure sheaf. -/

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
  [(Opens.grothendieckTopology Y).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
  [Limits.HasBinaryCoproducts (X.Sheaf CommRingCat.{u})]
  [Limits.HasBinaryCoproducts (Y.Sheaf CommRingCat.{u})] in
/-- The inverse image of the naive cotangent complex is canonically identified with the naive
cotangent complex of the pulled-back morphism. This is the opens-site specialization of the
Chapter 18 ringed-site owner theorem
`SheafOfModules.RingedSite.inverseImage_naiveCotangent_isIsomorphic`. -/
theorem inverseImage_naiveCotangent_isIsomorphic
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent O₁ (Under.mk φ)))
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₂).inv).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent
          ((pullback CommRingCat.{u} f).obj O₁)
          (Under.mk ((pullback CommRingCat.{u} f).map φ)))) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun _ ↦ ?_) ?_⟩
  · exact
      CategoryTheory.Functor.mapZeroObject
          (SheafOfModules.pullback
            ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))) ≪≫
        (CategoryTheory.Functor.mapZeroObject
          (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv)).symm
  intro i j hij
  simp [naiveCotangent, CategoryTheory.Functor.mapHomologicalComplex_obj_d]

end TopCat.Sheaf
