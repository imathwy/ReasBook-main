import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})]

-- Proof sketch: the example identifies the explicit complex attached to
-- `(GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A` with the cochains of a
-- contractible simplicial set. The resulting chain homotopy makes the associated cohomology
-- groups vanish in every positive degree, which is exactly the acyclicity input used later in the
-- computation theorem.
/-- Point skyscraper sheaves for the chaotic topology are acyclic for positive global
cohomology. -/
theorem pointBot_skyscraperSheaf_H_isZero_of_pos
    [LocallySmall.{max u v} C]
    (U : C) (A : AddCommGrpCat.{max u v}) {n : ℕ} (hn : 0 < n) :
    IsZero
      (AddCommGrpCat.of
        (((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A).H n)) := sorry

-- Proof sketch: replace the explicit complex `K^•(F)` from the text by a chosen injective
-- resolution `I` of `F` in the abelian sheaf category for the chaotic topology. The global
-- sections complex `Γ(I^•)` computes the right derived functors of `Γ`, hence its degree-`n`
-- cohomology is canonically `H^n(C, F)`. The example's acyclicity argument for products of point
-- skyscraper sheaves explains why the ad hoc complex `K^•(F)` is another model for the same
-- derived functor computation.
/-- Example 21.42.1 (Computing cohomology): for an abelian sheaf `\mathcal F` on the chaotic site
associated to a category `\mathcal C`, the cohomology object `H^n(\mathcal C, \mathcal F)` is
computed by the degree-`n` cohomology of the global-sections complex of any injective resolution
of `\mathcal F`. This is the canonical injective-resolution form of the explicit cochain complex
`K^\bullet(\mathcal F)` constructed in the text. -/
theorem categoryCohomology_iso_homology_of_injectiveResolution
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
    (I : InjectiveResolution F) (n : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (F.H n))
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) n).obj
        (((Sheaf.Γ (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end

end CategoryTheory
