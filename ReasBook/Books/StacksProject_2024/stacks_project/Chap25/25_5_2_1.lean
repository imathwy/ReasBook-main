import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import StacksProject_2024.stacks_project.Chap18.Definition_18_5_1

open CategoryTheory Opposite
open AlgebraicTopology

noncomputable section

universe u v w

namespace CategoryTheory

-- Semantic search note: no `lean_leansearch` tool was available in this run; the owner choice
-- follows the existing Chapter 21 `H^0(-, F)` and Hom-complex patterns for free abelian
-- sheafification on sheaves of sets.

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v w}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]

/-- The represented Hom functor on abelian sheaves preserves zero morphisms, so it lifts to
homological complexes. -/
local instance preadditiveYonedaObjPreservesZeroMorphisms
    (𝒜 : Sheaf J AddCommGrpCat.{max u v w}) :
    (preadditiveYoneda.obj 𝒜).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (preadditiveYoneda.obj 𝒜)

/-- The degree-zero cohomology functor `K ↦ Hom((ℤ K)^#, 𝒜)` on sheaves of sets, written in the
canonical sheaf-level owner form used below. -/
abbrev h0OverSheafFunctor (𝒜 : Sheaf J AddCommGrpCat.{max u v w}) :
    (Sheaf J (Type (max u v w)))ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).op ⋙ preadditiveYoneda.obj 𝒜

/-- The left-hand side `s(𝒜(K))` of 25.5.2.1, realized as the alternating coface complex of the
degreewise `H^0(-, 𝒜)` functor on the simplicial sheaf `K`. -/
abbrev simplicialSheafSectionsComplex
    (K : SimplicialObject (Sheaf J (Type (max u v w))))
    (𝒜 : Sheaf J AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).obj
    (K.rightOp ⋙ h0OverSheafFunctor 𝒜)

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})] in
/-- 25.5.2.1: for a simplicial sheaf of sets `K` and an abelian sheaf `𝒜`, the cochain complex
`s(𝒜(K))` is the alternating coface complex of the represented Hom functor
`K ↦ Hom((\mathbf Z_K)^\#, 𝒜)`, formalized by `h0OverSheafFunctor`. -/
theorem simplicialSheafSectionsComplex_def
    (K : SimplicialObject (Sheaf J (Type (max u v w))))
    (𝒜 : Sheaf J AddCommGrpCat.{max u v w}) :
    simplicialSheafSectionsComplex K 𝒜 =
      (alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).obj
        (K.rightOp ⋙ h0OverSheafFunctor 𝒜) := rfl

end CategoryTheory
