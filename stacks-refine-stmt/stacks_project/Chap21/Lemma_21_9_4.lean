import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite

noncomputable section

universe w u

namespace CategoryTheory

/-- The functor from formal coproducts in `C` to abelian presheaves sending a family to the
coproduct of the free abelian representables of its components. -/
abbrev freeAbelianRepresentableFormalCoproductFunctor {C : Type u} [Category.{u} C]
    [HasFiniteProducts C] [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}] :
    FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (FormalCoproduct.eval.{w} C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free.{u})

/-- The simplicial abelian presheaf whose degree-`n` term is the coproduct of the free abelian
representables on the `(n + 1)`-fold Čech intersections of the family `family`. -/
abbrev cechCoverSimplicialObject {C : Type u} [Category.{u} C] [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → C) : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ((SimplicialObject.whiskering (FormalCoproduct.{w} C) (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    freeAbelianRepresentableFormalCoproductFunctor).obj ((FormalCoproduct.mk ι family).cech)

/-- The chain complex of abelian presheaves on `Over U` obtained by applying the alternating face
map construction to the simplicial free-abelian representable Čech object attached to `family`. -/
abbrev freeAbelianCechCoverChainComplex {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)] [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}] {ι : Type w} (family : ι → Over U) :
    ChainComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (alternatingFaceMapComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (cechCoverSimplicialObject family)

-- Proof sketch: evaluate the chain complex on an object `V ⟶ U` of `Over U` and decompose the
-- resulting complex as a direct sum over maps `V ⟶ U` of bar-resolution complexes on the sets of
-- lifts to the cover. For each summand, choose a lift when the indexing set is nonempty and use
-- the induced extra degeneracy, equivalently the standard contracting homotopy on
-- `ℤ[S^{\bullet + 1}]`, to kill positive homology.
/-- Lemma 21.9.4: the free-abelian Čech cover chain complex of a family with fixed target has zero
homology presheaves in every positive degree. -/
theorem freeAbelianCechCoverChainComplex_homology_isZero_of_pos {C : Type u} [Category.{u} C]
    (U : C) [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    [CategoryWithHomology ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    {ι : Type w} (family : ι → Over U) :
    ∀ i : ℕ, 0 < i →
      IsZero (((HomologicalComplex.homologyFunctor ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
        (ComplexShape.down ℕ) i).obj (freeAbelianCechCoverChainComplex U family))) := sorry

end CategoryTheory
