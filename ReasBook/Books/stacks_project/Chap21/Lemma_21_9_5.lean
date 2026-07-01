import Mathlib
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u w

namespace CategoryTheory

/-- The functor from formal coproducts in `C` to abelian presheaves sending a family to the
coproduct of the free abelian representables of its components. -/
abbrev sliceFreeAbelianRepresentableFormalCoproductFunctor {C : Type u} [Category.{u} C]
    [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}] :
    FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (FormalCoproduct.eval.{w} C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free.{u})

/-- The simplicial abelian presheaf on the slice category whose degree-`n` term is the coproduct
of the free abelian representables on the `(n + 1)`-fold Čech intersections of the family
`family`. -/
abbrev sliceCechCoverSimplicialObject {C : Type u} [Category.{u} C]
    [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → C) :
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ((SimplicialObject.whiskering (FormalCoproduct.{w} C) (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    sliceFreeAbelianRepresentableFormalCoproductFunctor).obj
      ((FormalCoproduct.mk ι family).cech)

/-- The chain complex of free abelian representable presheaves attached to a Čech family. -/
abbrev sliceFreeAbelianCechCoverChainComplex {C : Type u} [Category.{u} C]
    [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → C) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (sliceCechCoverSimplicialObject family)

/-- The restriction of a commutative-ring-valued presheaf on `C` to the slice category
`Over U`. -/
abbrev restrictedCommRingPresheaf {C : Type u} [Category.{u} C] (U : C)
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) : (Over U)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget U).op ⋙ 𝒪

/-- The equivalence inverse sending an additive commutative group to the corresponding
`ℤ`-module. -/
abbrev addCommGrpToIntModule : AddCommGrpCat.{u} ⥤ ModuleCat.{u, 0} ℤ :=
  (forget₂ (ModuleCat.{u, 0} ℤ) AddCommGrpCat.{u}).asEquivalence.inverse

/-- The chain complex of `ℤ`-modules obtained by evaluating the free-abelian Čech cover chain
complex at `V : Over U`. -/
abbrev cechCoverSectionChainComplex {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → Over U) (V : Over U) :
    ChainComplex (ModuleCat.{u, 0} ℤ) ℕ :=
  (((CategoryTheory.evaluation (Over U)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) ⋙
      addCommGrpToIntModule).mapHomologicalComplex (ComplexShape.down ℕ) |>.obj
    (sliceFreeAbelianCechCoverChainComplex family)

/-- The sectionwise tensor of the evaluated free-abelian Čech cover chain complex with the
commutative ring of sections of `𝒪` over `V`, realized as extension of scalars from `ℤ`. -/
abbrev cechCoverSectionTensorChainComplex {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) {ι : Type w} (family : ι → Over U) (V : Over U) :
    ChainComplex (ModuleCat ((restrictedCommRingPresheaf U 𝒪).obj (op V))) ℕ :=
  ((ModuleCat.extendScalars
      (Int.castRingHom ((restrictedCommRingPresheaf U 𝒪).obj (op V)))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cechCoverSectionChainComplex U family V)

-- Proof sketch: for each `V : Over U`, evaluate Lemma `21.9.4` at `V` and identify the resulting
-- complex with a direct sum of bar-resolution summands. Tensoring that evaluated complex over `ℤ`
-- with the section ring `𝒪(V)` preserves exactness in positive degrees by the flatness argument of
-- Lemma `18.28.11`, exactly as in the textbook proof.
/-- Lemma 21.9.5: after restricting a ring-valued presheaf `\mathcal O` to `Over U`, tensoring
the evaluated free-abelian Čech cover chain complex with the ring of sections over any object
`V : Over U` yields a complex with zero homology in every positive degree. -/
theorem cechCoverSectionTensorChainComplex_homology_isZero_of_pos
    {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → Over U) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    ∀ V : Over U, ∀ i : ℕ, 0 < i →
      IsZero (((HomologicalComplex.homologyFunctor
        (ModuleCat ((restrictedCommRingPresheaf U 𝒪).obj (op V)))
        (ComplexShape.down ℕ) i).obj
          (cechCoverSectionTensorChainComplex U 𝒪 family V))) := sorry

end CategoryTheory
