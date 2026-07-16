import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite
open scoped CategoryTheory.SemiRepresentableFamily

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{max u v} C]

-- Semantic search note: `lean_leansearch` recalled mathlib's
-- `CategoryTheory.Sheaf.cohomologyPresheafFunctor` and `CategoryTheory.Sheaf.H` as the
-- objectwise sheaf-cohomology owners. Local Chapter 25 precedent supplies
-- `hypercoveringCechCohomology` for fixed hypercoverings, so the hypercover Čech functor is
-- presented below by its refinement-compatible colimit cocone.

/-- The objectwise sheaf-cohomology functor `ℱ ↦ H^i(X, ℱ)`. -/
def sheafCohomologyOverObjectFunctor (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    (X : C) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
  Sheaf.cohomologyPresheafFunctor J i ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op X)

/-- The category of hypercoverings of `X` with arrows oriented as refinements: a morphism
`K ⟶ L` is a simplicial morphism from the underlying simplicial object of `L` to that of `K`. -/
abbrev Hypercovering.RefinementCategory (J : GrothendieckTopology C) [HasPullbacks C] (X : C) :=
  InducedCategory (SimplicialObject (SR(C, X)))ᵒᵖ
    (fun K : @Hypercovering C _ J X ↦ op K.toSimplicialObject)

namespace Hypercovering

variable {J : GrothendieckTopology C} [HasPullbacks C]
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable {X : C}

/-- A refinement morphism, viewed as a morphism of the underlying simplicial objects. -/
def refinementHomToSimplicial {K L : RefinementCategory J X} (f : K ⟶ L) :
    (L : @Hypercovering C _ J X).toSimplicialObject ⟶
      (K : @Hypercovering C _ J X).toSimplicialObject :=
  unop f.hom

/-- The map of Čech complexes induced by a refinement of hypercoverings. -/
noncomputable def cechComplexMap
    {K L : RefinementCategory J X} (f : K ⟶ L)
    (ℱ : Sheaf J AddCommGrpCat.{max u v}) :
    hypercoveringCechComplex (K : @Hypercovering C _ J X) ℱ ⟶
      hypercoveringCechComplex (L : @Hypercovering C _ J X) ℱ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max u v}).map
    (Functor.whiskerRight
      ((Functor.whiskerRight (refinementHomToSimplicial f)
        (SemiRepresentableFamily.Over.forget ⋙ SemiRepresentableFamily.toPresheaf)).rightOp)
      (hypercoveringCechSectionsFunctor ℱ))

/-- The map on Čech cohomology induced by a refinement of hypercoverings. -/
noncomputable def cechCohomologyMap
    {K L : RefinementCategory J X} (f : K ⟶ L)
    (ℱ : Sheaf J AddCommGrpCat.{max u v}) (i : ℕ) :
    hypercoveringCechCohomology (K : @Hypercovering C _ J X) ℱ i ⟶
      hypercoveringCechCohomology (L : @Hypercovering C _ J X) ℱ i :=
  HomologicalComplex.homologyMap (cechComplexMap f ℱ) i

/-- The objectwise colimit universal property for a presented hypercover Čech cohomology functor.
This records that `checkH.obj ℱ` is the colimit of fixed-hypercovering Čech cohomology groups over
the refinement category. -/
def IsCechCohomologyHCColimit
    (X : C) (i : ℕ)
    (checkH : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v})
    (ι : ∀ (K : RefinementCategory J X) (ℱ : Sheaf J AddCommGrpCat.{max u v}),
      hypercoveringCechCohomology (K : @Hypercovering C _ J X) ℱ i ⟶ checkH.obj ℱ) : Prop :=
  ∀ (ℱ : Sheaf J AddCommGrpCat.{max u v}) (A : AddCommGrpCat.{max u v})
    (s : ∀ K : RefinementCategory J X,
      hypercoveringCechCohomology (K : @Hypercovering C _ J X) ℱ i ⟶ A),
    (∀ ⦃K L : RefinementCategory J X⦄ (f : K ⟶ L),
      cechCohomologyMap f ℱ i ≫ s L = s K) →
    ∃! t : checkH.obj ℱ ⟶ A, ∀ K : RefinementCategory J X, ι K ℱ ≫ t = s K

/-- Theorem 25.10.1: let `C` be a site with fibre products and let `X` be an object of `C`.
For every `i ≥ 0`, the functors `ℱ ↦ H^i(X, ℱ)` and
`ℱ ↦ \check H^i_{HC}(X, ℱ)` from abelian sheaves on `C` to abelian groups are canonically
isomorphic. Here the hypercover Čech cohomology functor is represented by its natural
refinement-compatible colimit cocone from the fixed-hypercovering Čech cohomology groups. -/
@[stacks 01H0]
theorem cechCohomologyHC_isIsomorphic_sheafCohomology
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    (X : C) (i : ℕ)
    (checkH : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v})
    (cechMap : ∀ (K : RefinementCategory J X)
      ⦃ℱ 𝒢 : Sheaf J AddCommGrpCat.{max u v}⦄, (ℱ ⟶ 𝒢) →
        (hypercoveringCechCohomology (K : @Hypercovering C _ J X) ℱ i ⟶
          hypercoveringCechCohomology (K : @Hypercovering C _ J X) 𝒢 i))
    (ι : ∀ (K : RefinementCategory J X) (ℱ : Sheaf J AddCommGrpCat.{max u v}),
      hypercoveringCechCohomology (K : @Hypercovering C _ J X) ℱ i ⟶ checkH.obj ℱ)
    (ι_natural : ∀ (K : RefinementCategory J X)
      ⦃ℱ 𝒢 : Sheaf J AddCommGrpCat.{max u v}⦄ (φ : ℱ ⟶ 𝒢),
      cechMap K φ ≫ ι K 𝒢 = ι K ℱ ≫ checkH.map φ)
    (ι_refinement : ∀ ⦃K L : RefinementCategory J X⦄ (f : K ⟶ L)
      (ℱ : Sheaf J AddCommGrpCat.{max u v}), cechCohomologyMap f ℱ i ≫ ι L ℱ = ι K ℱ)
    (isColimit_obj : IsCechCohomologyHCColimit X i checkH ι) :
    IsIsomorphic checkH (sheafCohomologyOverObjectFunctor J X i) := sorry

end Hypercovering

end CategoryTheory
