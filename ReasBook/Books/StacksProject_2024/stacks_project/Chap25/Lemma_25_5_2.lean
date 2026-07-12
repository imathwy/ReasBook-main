import Mathlib
import StacksProject_2024.Chap25.Lemma_25_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C]
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable {X : C}

-- Semantic search note: `lean_leansearch` recalled mathlib's sheaf-cohomology owner
-- `CategoryTheory.Sheaf.H` and one-hypercover APIs. This item stays with the local Chapter 25
-- fixed-target `Hypercovering` owner and the alternating-coface sections complex.

/-- The contravariant sections functor used to evaluate a simplicial presheaf against an abelian
sheaf: first form the free abelian sheaf on a set-valued presheaf, then take morphisms into the
coefficient sheaf. -/
abbrev hypercoveringCechSectionsFunctor
    (I : Sheaf J AddCommGrpCat.{max u v}) :
    (Cᵒᵖ ⥤ Type (max u v))ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  ((((Functor.whiskeringRight Cᵒᵖ (Type (max u v)) AddCommGrpCat.{max u v}).obj
      AddCommGrpCat.free) ⋙
    presheafToSheaf J AddCommGrpCat.{max u v}).op) ⋙
      preadditiveYoneda.obj I

/-- The sections functor is the represented functor out of the free abelian sheafification. -/
theorem hypercoveringCechSectionsFunctor_def
    (I : Sheaf J AddCommGrpCat.{max u v}) :
    hypercoveringCechSectionsFunctor I =
      ((((Functor.whiskeringRight Cᵒᵖ (Type (max u v)) AddCommGrpCat.{max u v}).obj
          AddCommGrpCat.free) ⋙
        presheafToSheaf J AddCommGrpCat.{max u v}).op) ⋙
          preadditiveYoneda.obj I := sorry

/-- The Čech cochain complex attached to a hypercovering of `X` and an abelian sheaf `I`. -/
abbrev hypercoveringCechComplex
    (K : @Hypercovering C _ J X)
    (I : Sheaf J AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max u v}).obj
    ((hypercoveringSimplicialPresheaf K).rightOp ⋙ hypercoveringCechSectionsFunctor I)

/-- The Čech cochain complex is the alternating-coface complex of the degreewise sections
groups attached to `K`. -/
theorem hypercoveringCechComplex_def
    (K : @Hypercovering C _ J X)
    (I : Sheaf J AddCommGrpCat.{max u v}) :
    hypercoveringCechComplex K I =
      (alternatingCofaceMapComplex AddCommGrpCat.{max u v}).obj
        ((hypercoveringSimplicialPresheaf K).rightOp ⋙ hypercoveringCechSectionsFunctor I) := sorry

/-- The Čech cohomology group of a hypercovering `K` with coefficients in `I`. -/
abbrev hypercoveringCechCohomology
    (K : @Hypercovering C _ J X)
    (I : Sheaf J AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  (hypercoveringCechComplex K I).homology p

/-- Unfolding the Čech cohomology of a hypercovering gives the homology of the associated
alternating-coface sections complex. -/
theorem hypercoveringCechCohomology_def
    (K : @Hypercovering C _ J X)
    (I : Sheaf J AddCommGrpCat.{max u v}) (p : ℕ) :
    hypercoveringCechCohomology K I p =
      (hypercoveringCechComplex K I).homology p := sorry

/-- Lemma 25.5.2 (1): for a hypercovering `K` of `X` and an injective abelian sheaf `I`, the
degree-zero Čech cohomology identifies with the section group `I(X)`. -/
@[stacks 01GW]
theorem hypercoveringCechCohomology_zero_isomorphic_sections_of_injective
    (K : @Hypercovering C _ J X)
    (I : Sheaf J AddCommGrpCat.{max u v}) [Injective I] :
    IsIsomorphic (hypercoveringCechCohomology K I 0) (I.1.obj (op X)) := sorry

/-- Lemma 25.5.2 (2): for a hypercovering `K` of `X` and an injective abelian sheaf `I`, the
positive-degree Čech cohomology groups vanish. -/
@[stacks 01GW]
theorem hypercoveringCechCohomology_isZero_of_injective_pos
    (K : @Hypercovering C _ J X)
    (I : Sheaf J AddCommGrpCat.{max u v}) [Injective I]
    {p : ℕ} (hp : 0 < p) :
    IsZero (hypercoveringCechCohomology K I p) := sorry

end

end CategoryTheory
