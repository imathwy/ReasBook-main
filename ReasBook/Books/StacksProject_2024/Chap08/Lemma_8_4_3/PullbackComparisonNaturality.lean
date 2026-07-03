import stacks_project.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import stacks_project.Chap08.Lemma_8_4_3.PullbackComparisonIso

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)
variable [p.IsFibered]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: the inclusion pullback-comparison isomorphism intertwines pullback
of vertical morphisms with the image of the pulled-back morphism in the ambient fiber. -/
theorem fullSubcategory_inclusion_pullbackComparison_naturality_over_vertical
    (J : GrothendieckTopology C)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U V : C} (f : V ⟶ U) {x y : (P.ι ⋙ p).Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((((fullSubcategory_inclusion_fibredMor
            (J := J) (p := p) (P := P) hpullback).toHom).fiberFunctor U).map φ)) ≫
      (FibredCategoryMor.pullbackComparison
        (fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback) f y).hom =
    (FibredCategoryMor.pullbackComparison
        (fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback) f x).hom ≫
      ((((fullSubcategory_inclusion_fibredMor
            (J := J) (p := p) (P := P) hpullback).toHom).fiberFunctor V).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f.op.toLoc).toFunctor.map φ)) := by
  let H := fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback
  -- Route correction: the specialized fixed-cover square is exactly the generic fibred-morphism
  -- naturality square for the inclusion morphism `H`.
  simpa [H] using
    (FibredCategoryMor.pullbackComparison_naturality_over_vertical
      (F := H) (f := f) (φ := φ))

/-- Helper for Lemma 8.4.3: moving the hom-side inclusion comparison square across the inverse
comparison isomorphisms gives the inverse-side naturality used in the reverse descent bridge. -/
theorem fullSubcategory_inclusion_pullbackComparison_inv_naturality_over_vertical
    (J : GrothendieckTopology C)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U V : C} (f : V ⟶ U) {x y : (P.ι ⋙ p).Fiber U} (φ : x ⟶ y) :
    ((((fullSubcategory_inclusion_fibredMor
          (J := J) (p := p) (P := P) hpullback).toHom).fiberFunctor V).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f.op.toLoc).toFunctor.map φ)) ≫
      (FibredCategoryMor.pullbackComparison
        (fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback) f y).inv =
    (FibredCategoryMor.pullbackComparison
        (fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback) f x).inv ≫
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((((fullSubcategory_inclusion_fibredMor
            (J := J) (p := p) (P := P) hpullback).toHom).fiberFunctor U).map φ) := by
  let H := fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback
  -- Route correction: the inverse-side transport square is the generic inverse naturality square
  -- specialized to the inclusion fibred morphism.
  simpa [H] using
    (FibredCategoryMor.pullbackComparison_inv_naturality_over_vertical
      (F := H) (f := f) (φ := φ))

/-- Helper for Lemma 8.4.3: postcomposing the hom part of the restricted/ambient pullback
comparison with the chosen ambient pullback arrow recovers the image of the restricted chosen
pullback arrow. -/
theorem restricted_pullback_vs_ambient_pullback_comparison_hom_postcompose
    (J : GrothendieckTopology C)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U V : C} (f : V ⟶ U) (x : (P.ι ⋙ p).Fiber U) :
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f x).hom.1 ≫
      (canonicalPullbackChoice p).map f
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj =
    ((canonicalPullbackChoice (P.ι ⋙ p)).map f x).hom := by
  let H := fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback
  -- The local comparison is the inverse of the owner pullback comparison for the inclusion.
  simpa [restricted_pullback_vs_ambient_pullback_comparison, H] using
    (FibredCategoryMor.pullbackComparison_inv_postcompose_owner
      (F := H) (f := f) (x := x))

/-- Helper for Lemma 8.4.3: postcomposing the inverse part of the restricted/ambient pullback
comparison with the image of the restricted chosen pullback arrow recovers the chosen ambient
pullback arrow. -/
theorem restricted_pullback_vs_ambient_pullback_comparison_inv_postcompose
    (J : GrothendieckTopology C)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U V : C} (f : V ⟶ U) (x : (P.ι ⋙ p).Fiber U) :
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f x).inv.1 ≫
      ((canonicalPullbackChoice (P.ι ⋙ p)).map f x).hom =
    (canonicalPullbackChoice p).map f
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj := by
  let H := fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback
  -- This is the dual owner identity, translated through the local `symm` convention.
  simpa [restricted_pullback_vs_ambient_pullback_comparison, H] using
    (FibredCategoryMor.pullbackComparison_hom_postcompose
      (F := H) (f := f) (x := x))

end RestrictedFibered

end
