import Mathlib
import StacksProject_2024.Chap21.Lemma_21_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for 20.54.2.1:
- primary domain: projection-formula morphisms built from the relative cup product in derived
  monoidal categories.
- sampled project declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `RingedSite.Hom.projectionFormulaMorphism`,
  `CategoryTheory.CommSq`,
  `Functor.homEquiv`.
- owner abstraction:
  `source-facing`: the projection-formula morphism attached to an adjunction on monoidal source and
  target categories;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct` from `Lemma_21_33_1`;
  `bridge/view`: the tensor-with-unit morphism feeding the relative cup product.
- primitive data: `Lf`, `Rf`, the adjunction `adj`, and the pullback-tensor comparison.
- derived API: ringed-space and ringed-site specializations, plus base-change compatibility. -/

section

variable {SourceDerived : Type u} [Category.{v} SourceDerived] [MonoidalCategory SourceDerived]
variable {TargetDerived : Type u} [Category.{v} TargetDerived] [MonoidalCategory TargetDerived]

variable
  (Lf : TargetDerived ⥤ SourceDerived)
  (Rf : SourceDerived ⥤ TargetDerived)
  (adj : Lf ⊣ Rf)

variable
  (pullbackTensorIso : ∀ (K L : TargetDerived), Lf.obj (K ⊗ L) ≅ (Lf.obj K ⊗ Lf.obj L))

/-- 20.54.2.1: the projection-formula morphism
`K ⊗ Rf E ⟶ Rf (Lf K ⊗ E)` obtained by tensoring the adjunction unit
`K ⟶ Rf (Lf K)` with `Rf E` and then applying the relative cup product. -/
noncomputable def projectionFormulaMorphism
    (E : SourceDerived) (K : TargetDerived) :
    K ⊗ Rf.obj E ⟶ Rf.obj (Lf.obj K ⊗ E) :=
  (adj.unit.app K ⊗ₘ 𝟙 (Rf.obj E)) ≫
    relativeDerivedCupProduct
      Lf
      Rf
      adj
      (curriedTensor SourceDerived)
      (curriedTensor TargetDerived)
      (fun A B ↦ pullbackTensorIso B A)
      E
      (Lf.obj K)

end

end CategoryTheory
