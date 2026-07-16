import StacksProject_2024.stacks_project.Chap34.Lemma_34_13_1
import StacksProject_2024.stacks_project.Chap34.Lemma_34_13_2
import StacksProject_2024.stacks_project.Chap34.Definition_34_6_1
import Mathlib.AlgebraicGeometry.Sites.Fpqc

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

universe u v

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` recalled `CategoryTheory.Presheaf.IsSheaf`, `Presieve.IsSheafFor`,
and the canonical big scheme topologies. Local Chapter 34 precedent supplies
`StandardTopology`, `AffineFamilyOver`, and the Lemma 34.13.1 extension hypotheses, so this item is
stated as a canonical sheaf condition for `F'` on the selected over-topology.
The source tag evidence is consistent with Stacks tag `0GDW`.
-/

namespace StandardTopology

/-- The Grothendieck topology on `Sch/S` corresponding to one of the five standard topologies. -/
abbrev overTopology (τ : StandardTopology) (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  match τ with
  | zariski => Scheme.zariskiTopology.over S
  | etale => S.overGrothendieckTopology @Etale
  | smooth => S.overGrothendieckTopology @Smooth
  | syntomic => S.overGrothendieckTopology (@Syntomic)
  | fppf => Scheme.fppfTopology.over S

/-- The `zariski` member of `StandardTopology.overTopology` is the usual big Zariski topology
over `S`. -/
theorem overTopology_zariski (S : Scheme.{u}) :
    overTopology zariski S = Scheme.zariskiTopology.over S := sorry

end StandardTopology

/-- An object of `Sch/S` factors through an affine open of `S` by a morphism locally of finite
presentation. -/
def factorsThroughFinitelyPresentedAffineOpen {S : Scheme.{u}} (X : Over S) : Prop :=
  ∃ U : S.Opens, IsAffineOpen U ∧
    ∃ g : X.left ⟶ (U : Scheme.{u}), LocallyOfFinitePresentation g ∧ g ≫ U.ι = X.hom

/-- Unfolding the condition that an `S`-scheme factors through an affine open of `S` with finite
presentation over that open. -/
theorem factorsThroughFinitelyPresentedAffineOpen_iff {S : Scheme.{u}} (X : Over S) :
    factorsThroughFinitelyPresentedAffineOpen X ↔
      ∃ U : S.Opens, IsAffineOpen U ∧
        ∃ g : X.left ⟶ (U : Scheme.{u}), LocallyOfFinitePresentation g ∧ g ≫ U.ι = X.hom := sorry

/-- A presheaf on a full subcategory of `Sch/S` satisfies the sheaf condition for every finite
affine standard `τ`-cover whose target factors through an affine open of `S` with finite
presentation. -/
abbrev satisfiesStandardSheafConditionForFinitelyPresentedAffineCovers {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (τ : StandardTopology)
    (F : C.FullSubcategoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ {n : ℕ} {X : C.FullSubcategory} (U : Fin n → C.FullSubcategory)
    (f : ∀ i, U i ⟶ X)
    (hU_affine : ∀ i, IsAffine ((U i).obj : Over S).left),
      factorsThroughFinitelyPresentedAffineOpen (X.obj : Over S) →
        τ.IsStandardCover
          ({ n := n
             U := fun i ↦ ((U i).obj : Over S).left
             map := fun i ↦ (f i).hom.left
             isAffine := hU_affine } : AffineFamilyOver ((X.obj : Over S).left)) →
          Presieve.IsSheafFor F (Presieve.ofArrows U f)

/-- Unfolding the standard-cover sheaf condition used in Lemma 34.13.3. -/
theorem satisfiesStandardSheafConditionForFinitelyPresentedAffineCovers_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (τ : StandardTopology)
    (F : C.FullSubcategoryᵒᵖ ⥤ Type v) :
    satisfiesStandardSheafConditionForFinitelyPresentedAffineCovers C τ F ↔
      ∀ {n : ℕ} {X : C.FullSubcategory} (U : Fin n → C.FullSubcategory)
        (f : ∀ i, U i ⟶ X)
        (hU_affine : ∀ i, IsAffine ((U i).obj : Over S).left),
          factorsThroughFinitelyPresentedAffineOpen (X.obj : Over S) →
            τ.IsStandardCover
              ({ n := n
                 U := fun i ↦ ((U i).obj : Over S).left
                 map := fun i ↦ (f i).hom.left
                 isAffine := hU_affine } : AffineFamilyOver ((X.obj : Over S).left)) →
              Presieve.IsSheafFor F (Presieve.ofArrows U f) := sorry

/-- Lemma 34.13.3: if the functor `F` satisfies the sheaf condition for standard `τ`-coverings
of affine objects which are of finite presentation over affine opens of `S`, then the unique
extension `F'` supplied by Lemma 34.13.1 is a sheaf for all `τ`-coverings on `Sch/S`, where
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. -/
@[stacks 0GDW]
theorem isSheaf_overTopology_of_standardCover_sheafCondition
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type v) (F' : (Over S)ᵒᵖ ⥤ Type v)
    (hC_open : overSubcategoryContainsAffineOpens C)
    (hC_fp : overSubcategoryContainsFinitelyPresentedAffinesOverAffineBase C)
    (hF_zariski : satisfiesZariskiSheafConditionOnSubcategory C F)
    (hF_limits : preservesDirectedAffineLimitsOnSubcategory C F)
    (eF' : C.ι.op ⋙ F' ≅ F)
    (hF'_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F')
    (hF'_limits : preservesDirectedAffineLimitsOver S F')
    (hF'_unique :
      ∀ (G : (Over S)ᵒᵖ ⥤ Type v) (eG : C.ι.op ⋙ G ≅ F),
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
        preservesDirectedAffineLimitsOver S G →
        ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF')
    (τ : StandardTopology)
    (hF_standard : satisfiesStandardSheafConditionForFinitelyPresentedAffineCovers C τ F) :
    Presheaf.IsSheaf (τ.overTopology S) F' := sorry

end AlgebraicGeometry
