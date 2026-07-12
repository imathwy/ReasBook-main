import StacksProject_2024.Chap21.Definition_21_8_1

open CategoryTheory.Limits
open AlgebraicTopology

universe w v v' u u'

noncomputable section

namespace CategoryTheory

section Bridge

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable [HasFiniteProducts C]

/- Domain-style sampling for 21.8.2.1:
- primary domain: refinement functoriality of Čech complexes, first for formal coproducts in an
  arbitrary category with finite products and then for covering families in `Over U`;
- sampled owner declarations:
  `FormalCoproduct.cosimplicialObjectFunctor`,
  `FormalCoproduct.cochainComplexFunctor`,
  `cechComplexFunctor`,
  `cechComplex`;
- best owner abstraction:
  `source-facing`: the Chapter 21 map on `cechComplex U family F` for families in `Over U`;
  `core/canonical`: `cechComplexFunctor`;
  `bridge/view`: the induced morphisms on the underlying Čech cosimplicial objects and cochain
    complexes attached to formal coproducts.

The generic formal-coproduct refinement maps remain public as the bridge layer, but the tagged
Chapter 21 declaration below is the source-facing owner on `Over U`.
-/

/- A refinement morphism of formal coproducts first gives a natural transformation of the
associated Čech cosimplicial-object functors. -/
private noncomputable abbrev formalCoproductCechCosimplicialNatTransOfRefinement {ι κ : Type w}
    (refinement : ι → C) (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C)) :=
  Functor.whiskerLeft (FormalCoproduct.evalOp C A)
    ((Functor.whiskeringLeft SimplexCategory ((FormalCoproduct C)ᵒᵖ) A).map
      ((FormalCoproduct.cechFunctor.map σ).rightOp))

/-- Bridge/view: a morphism of formal coproducts induces the corresponding morphism of Čech
cosimplicial objects after evaluation against `F`. -/
abbrev formalCoproductCechCosimplicialMapOfRefinement {ι κ : Type w} (refinement : ι → C)
    (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.cech (FormalCoproduct.mk κ family))).obj F ⟶
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.cech (FormalCoproduct.mk ι refinement))).obj F :=
  (formalCoproductCechCosimplicialNatTransOfRefinement refinement family σ).app F

/- Applying `alternatingCofaceMapComplex` to that natural transformation gives the induced
natural transformation of formal-coproduct Čech complexes. -/
private noncomputable abbrev formalCoproductCechComplexNatTransOfRefinement {ι κ : Type w}
    (refinement : ι → C)
    (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C)) :=
  Functor.whiskerRight
    (formalCoproductCechCosimplicialNatTransOfRefinement refinement family σ)
    (alternatingCofaceMapComplex A)

/-- Bridge/view: applying `alternatingCofaceMapComplex` to the Čech cosimplicial refinement map
gives the induced morphism of Čech complexes for formal coproducts. -/
abbrev formalCoproductCechComplexMapOfRefinement {ι κ : Type w} (refinement : ι → C)
    (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor family).obj F ⟶
      (cechComplexFunctor refinement).obj F :=
  (formalCoproductCechComplexNatTransOfRefinement refinement family σ).app F

/-- In degree `n`, the formal-coproduct Čech refinement map is the corresponding component of its
underlying cosimplicial morphism. -/
@[simp] theorem formalCoproductCechComplexMapOfRefinement_f {ι κ : Type w}
    (refinement : ι → C) (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    (formalCoproductCechComplexMapOfRefinement refinement family σ F).f n =
      (formalCoproductCechCosimplicialMapOfRefinement refinement family σ F).app
        (SimplexCategory.mk n) := by
  simp [formalCoproductCechComplexMapOfRefinement,
    formalCoproductCechCosimplicialMapOfRefinement, alternatingCofaceMapComplex_map]

end Bridge

section

variable {C : Type u} [Category.{v} C]
variable (U : C) [HasFiniteProducts (Over U)]
variable [HasProducts AddCommGrpCat.{v}]
variable {ι κ : Type w}

/-- Bridge/view: the Chapter 21 refinement morphism induces the corresponding natural
transformation on Čech-complex functors after restricting presheaves to `Over U`. -/
abbrev cechComplexMapOfRefinementNatTrans (family : κ → Over U) (refinement : ι → Over U)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct (Over U)) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct (Over U))) :
    (restrictPresheafToOver U ⋙ cechComplexFunctor family) ⟶
      (restrictPresheafToOver U ⋙ cechComplexFunctor refinement) :=
  Functor.whiskerLeft (restrictPresheafToOver U)
    (formalCoproductCechComplexNatTransOfRefinement refinement family σ)

/-- 21.8.2.1: a refinement morphism of covering families of `U` induces the canonical map from
the Čech complex of the coarser family to the Čech complex of the refinement. -/
@[stacks 03F4]
abbrev cechComplexMapOfRefinement (family : κ → Over U) (refinement : ι → Over U)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct (Over U)) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct (Over U)))
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    cechComplex U family F ⟶ cechComplex U refinement F :=
  (cechComplexMapOfRefinementNatTrans U family refinement σ).app F

/-- In degree `n`, the Chapter 21 Čech refinement map is induced by the corresponding component
of the underlying formal-coproduct Čech cosimplicial morphism on the restricted presheaf. -/
@[simp] theorem cechComplexMapOfRefinement_f (family : κ → Over U) (refinement : ι → Over U)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct (Over U)) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct (Over U)))
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (n : ℕ) :
    (cechComplexMapOfRefinement U family refinement σ F).f n =
      (formalCoproductCechCosimplicialMapOfRefinement refinement family σ
        ((restrictPresheafToOver U).obj F)).app (SimplexCategory.mk n) := by
  simpa [cechComplexMapOfRefinement] using
    formalCoproductCechComplexMapOfRefinement_f refinement family σ
      ((restrictPresheafToOver U).obj F) n

end

end CategoryTheory
