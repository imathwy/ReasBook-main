import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Sites.Abelian
import StacksProject_2024.Chap18.Definition_18_5_1

open CategoryTheory
open AlgebraicTopology
open scoped FreeAbelianSheaf

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]

-- Semantic search tool unavailable in this runner; the owner/API below follows the canonical
-- degreewise free-abelian-sheaf construction and the alternating-face-map complex precedent.

/-- The degreewise free-abelian-sheaf functor on presheaves of sets over the fixed site. -/
abbrev simplicialPresheafFreeAbelianSheafFunctor :
    (Cᵒᵖ ⥤ Type (max w v)) ⥤ Sheaf J AddCommGrpCat.{max w v} :=
  ((Functor.whiskeringRight Cᵒᵖ (Type (max w v)) AddCommGrpCat.{max w v}).obj
      AddCommGrpCat.free) ⋙
    presheafToSheaf J AddCommGrpCat.{max w v}

/-- The simplicial free abelian sheaf `\mathbf Z_K^\#` attached degreewise to a simplicial
presheaf `K`. -/
abbrev simplicialPresheafFreeAbelianSheaf
    (K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))) :
    SimplicialObject (Sheaf J AddCommGrpCat.{max w v}) :=
  K ⋙ simplicialPresheafFreeAbelianSheafFunctor J

/-- Degreewise, the simplicial free abelian sheaf is the free abelian sheaf on the corresponding
presheaf of simplices. -/
@[simp]
theorem simplicialPresheafFreeAbelianSheaf_obj
    (K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))) (Δ : SimplexCategoryᵒᵖ) :
    (simplicialPresheafFreeAbelianSheaf J K).obj Δ =
      ((ℤ_ K.obj Δ)^#[J] : Sheaf J AddCommGrpCat.{max w v}) := rfl

/-- The associated chain complex of abelian sheaves attached to a simplicial presheaf, obtained by
applying the free abelian sheaf construction degreewise and then taking the alternating face map
complex. -/
abbrev simplicialPresheafHomologyComplex
    (K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))) :
    ChainComplex (Sheaf J AddCommGrpCat.{max w v}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{max w v})).obj
    (simplicialPresheafFreeAbelianSheaf J K)

/-- The associated complex is obtained from the simplicial free abelian sheaf `\mathbf Z_K^\#` by
the canonical alternating-face-map-complex construction. -/
@[simp]
theorem simplicialPresheafHomologyComplex_def
    (K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))) :
    simplicialPresheafHomologyComplex J K =
      (AlgebraicTopology.alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{max w v})).obj
        (simplicialPresheafFreeAbelianSheaf J K) := rfl

/-- Definition 25.4.1: for a simplicial presheaf `K` on the site `(\mathcal C, J)`, the
degree-`n` homology of `K` is the degree-`n` homology sheaf of the associated complex of abelian
sheaves `s(\mathbf Z_K^\#)`. -/
abbrev simplicialPresheafHomology
    (K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))) (n : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} :=
  (simplicialPresheafHomologyComplex J K).homology n

/-- The homology of a simplicial presheaf is, by definition, the homology of its associated
complex of abelian sheaves. -/
@[simp]
theorem simplicialPresheafHomology_def
    (K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))) (n : ℕ) :
    simplicialPresheafHomology J K n =
      (simplicialPresheafHomologyComplex J K).homology n := rfl

/-- The chain map between the associated complexes induced by a morphism of simplicial
presheaves. -/
abbrev simplicialPresheafHomologyComplexMap
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))} (f : L ⟶ K) :
    simplicialPresheafHomologyComplex J L ⟶ simplicialPresheafHomologyComplex J K :=
  (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{max w v})).map
    (Functor.whiskerRight f (simplicialPresheafFreeAbelianSheafFunctor J))

/-- The induced chain map is the alternating-face-map-complex image of the degreewise free
abelian sheaf map. -/
@[simp]
theorem simplicialPresheafHomologyComplexMap_def
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))} (f : L ⟶ K) :
    simplicialPresheafHomologyComplexMap J f =
      (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{max w v})).map
        (Functor.whiskerRight f (simplicialPresheafFreeAbelianSheafFunctor J)) := rfl

/-- The map on homology sheaves induced by a morphism of simplicial presheaves. -/
abbrev simplicialPresheafHomologyMap
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))} (f : L ⟶ K) (n : ℕ) :
    simplicialPresheafHomology J L n ⟶ simplicialPresheafHomology J K n :=
  HomologicalComplex.homologyMap (simplicialPresheafHomologyComplexMap J f) n

/-- The induced map on homology sheaves is obtained by applying `homologyMap` to the canonical
chain map between the associated alternating-face-map complexes. -/
@[simp]
theorem simplicialPresheafHomologyMap_def
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))} (f : L ⟶ K) (n : ℕ) :
    simplicialPresheafHomologyMap J f n =
      HomologicalComplex.homologyMap (simplicialPresheafHomologyComplexMap J f) n := rfl

end

end CategoryTheory
