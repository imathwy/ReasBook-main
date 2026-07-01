import Mathlib

open CategoryTheory.Limits
open AlgebraicTopology

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable [HasFiniteProducts C]

/-- The natural transformation of cosimplicial objects induced by a refinement morphism of formal
coproducts. -/
noncomputable abbrev cechCosimplicialNatTransOfRefinement {ι κ : Type w} (U : ι → C) (V : κ → C)
    (σ : (FormalCoproduct.mk ι U : FormalCoproduct C) ⟶ (FormalCoproduct.mk κ V : FormalCoproduct C)) :=
  Functor.whiskerLeft (FormalCoproduct.evalOp C A)
    ((Functor.whiskeringLeft SimplexCategory ((FormalCoproduct C)ᵒᵖ) A).map
      ((FormalCoproduct.cechFunctor.map σ).rightOp))

/-- The cosimplicial morphism induced by a refinement morphism of formal coproducts. -/
noncomputable abbrev cechCosimplicialMapOfRefinement {ι κ : Type w} (U : ι → C) (V : κ → C)
    (σ : (FormalCoproduct.mk ι U : FormalCoproduct C) ⟶ (FormalCoproduct.mk κ V : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.cech (FormalCoproduct.mk κ V))).obj F ⟶
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.cech (FormalCoproduct.mk ι U))).obj F :=
  (cechCosimplicialNatTransOfRefinement U V σ).app F

/-- The natural transformation of Čech complexes induced by a refinement morphism of formal
coproducts. -/
noncomputable abbrev cechComplexNatTransOfRefinement {ι κ : Type w} (U : ι → C) (V : κ → C)
    (σ : (FormalCoproduct.mk ι U : FormalCoproduct C) ⟶ (FormalCoproduct.mk κ V : FormalCoproduct C)) :=
  Functor.whiskerRight (cechCosimplicialNatTransOfRefinement U V σ) (alternatingCofaceMapComplex A)

/-- 21.8.2.1: a refinement morphism of coverings induces the canonical map from the Čech complex
of the coarser covering to the Čech complex of the finer covering. -/
noncomputable abbrev cechComplexMapOfRefinement {ι κ : Type w} (U : ι → C) (V : κ → C)
    (σ : (FormalCoproduct.mk ι U : FormalCoproduct C) ⟶ (FormalCoproduct.mk κ V : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor V).obj F ⟶
      (cechComplexFunctor U).obj F :=
  (cechComplexNatTransOfRefinement U V σ).app F

/-- The degreewise component of the Čech complex refinement map is the corresponding component of
its underlying cosimplicial morphism. -/
-- Proof sketch: unfold `cechComplexMapOfRefinement` and use the definition of
-- `AlgebraicTopology.AlternatingCofaceMapComplex.map`, whose degree-`n` component is evaluation of
-- the underlying cosimplicial morphism on `SimplexCategory.mk n`.
theorem cechComplexMapOfRefinement_f {ι κ : Type w} (U : ι → C) (V : κ → C)
    (σ : (FormalCoproduct.mk ι U : FormalCoproduct C) ⟶ (FormalCoproduct.mk κ V : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplexMapOfRefinement U V σ F).f n =
      (cechCosimplicialMapOfRefinement U V σ F).app (SimplexCategory.mk n) := by
  simp [cechComplexMapOfRefinement, cechComplexNatTransOfRefinement,
    cechCosimplicialMapOfRefinement, cechCosimplicialNatTransOfRefinement,
    alternatingCofaceMapComplex_map]

end CategoryTheory
