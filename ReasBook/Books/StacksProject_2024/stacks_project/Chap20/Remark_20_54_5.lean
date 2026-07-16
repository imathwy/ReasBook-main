import StacksProject_2024.stacks_project.Chap20.«20_54_2_1»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory

section

/- Domain-style sampling for Remark 20.54.5:
- primary domain: projection-formula morphisms and derived base-change maps in monoidal derived
  categories;
- sampled owner declarations:
  `CategoryTheory.projectionFormulaMorphism`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `CategoryTheory.relativeDerivedCupProduct_baseChange_commSq`,
  `CategoryTheory.CommSq`;
- source/core/bridge triage:
  `source-facing`: the abstract derived-category compatibility square for the projection-formula
    morphism;
  `core/canonical`: `projectionFormulaMorphism`, `IsDerivedBaseChangeMap`, and
    `relativeDerivedCupProduct_baseChange_commSq`;
  `bridge/view`: ringed-space and ringed-site specializations obtained by instantiating the
    ambient monoidal categories.
- primitive data: the four functors, the two adjunctions, the commutativity isomorphism, the four
  pullback-tensor comparison isomorphisms, the tensor-compatibility square for `squareIso`, and
  the two chosen base-change morphisms.
- derived API: the named left and right comparison morphisms in the square together with the
  commutative-square statement below.

This item is already completely generic in the ambient monoidal categories, so the refined owner
belongs in `CategoryTheory` rather than in a ringed-space specialization namespace.
-/

variable {DX DX' DY DY' : Type u}
variable [Category.{v} DX] [Category.{v} DX'] [Category.{v} DY] [Category.{v} DY']

variable
  (Lf : DY ⥤ DX)
  (Lf' : DY' ⥤ DX')
  (Lg : DY ⥤ DY')
  (Lg' : DX ⥤ DX')
  (Rf : DX ⥤ DY)
  (Rf' : DX' ⥤ DY')

variable [MonoidalCategory DX]
variable [MonoidalCategory DX']
variable [MonoidalCategory DY]
variable [MonoidalCategory DY']

variable
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

variable
  (pullbackTensorIso_f :
    ∀ (A B : DY),
      Lf.obj (A ⊗ B) ≅
        (Lf.obj A ⊗ Lf.obj B))
  (pullbackTensorIso_f' :
    ∀ (A B : DY'),
      Lf'.obj (A ⊗ B) ≅
        (Lf'.obj A ⊗ Lf'.obj B))
  (pullbackTensorIso_g :
    ∀ (A B : DY),
      Lg.obj (A ⊗ B) ≅
        (Lg.obj A ⊗ Lg.obj B))
  (pullbackTensorIso_g' :
    ∀ (A B : DX),
      Lg'.obj (A ⊗ B) ≅
        (Lg'.obj A ⊗ Lg'.obj B))
  (squareIsoTensorCommSq :
    ∀ (A B : DY),
      CommSq
        (Lf'.map (pullbackTensorIso_g A B).hom)
        (squareIso.hom.app (A ⊗ B))
        (pullbackTensorIso_f' (Lg.obj A) (Lg.obj B)).hom
        (Lg'.map (pullbackTensorIso_f A B).hom ≫
          (pullbackTensorIso_g' (Lf.obj A) (Lf.obj B)).hom ≫
          ((𝟙 (Lg'.obj (Lf.obj A))) ⊗ₘ squareIso.inv.app B) ≫
          (squareIso.inv.app A ⊗ₘ 𝟙 (Lf'.obj (Lg.obj B)))))

/-- Remark 20.54.5: for a commutative square of monoidal derived categories whose square
isomorphism is compatible with the pullback-tensor comparisons, the projection-formula morphism of
`20.54.2.1` is compatible with derived base change. If `ηE` and `ηTensor` are the base-change
maps for `E` and for `Lf.obj K ⊗ E`, then the square comparing the pullback of the
projection-formula morphism for `f` with the projection-formula morphism for `f'` commutes. -/
@[stacks 0B6B]
theorem projectionFormulaMorphism_baseChange_commSq
    (E : DX)
    (K : DY)
    (ηE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (ηTensor :
      Lg.obj (Rf.obj (Lf.obj K ⊗ E)) ⟶
        Rf'.obj (Lg'.obj (Lf.obj K ⊗ E)))
    (hηE : IsDerivedBaseChangeMap
      Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso E ηE)
    (hηTensor : IsDerivedBaseChangeMap
      Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso (Lf.obj K ⊗ E) ηTensor) :
    CommSq
      (Lg.map (projectionFormulaMorphism Lf Rf adj_f pullbackTensorIso_f E K))
      ((pullbackTensorIso_g K (Rf.obj E)).hom ≫
        (𝟙 (Lg.obj K) ⊗ₘ ηE))
      (ηTensor ≫
        Rf'.map
          ((pullbackTensorIso_g' (Lf.obj K) E).hom ≫
            (squareIso.inv.app K ⊗ₘ 𝟙 (Lg'.obj E))))
      (projectionFormulaMorphism Lf' Rf' adj_f' pullbackTensorIso_f' (Lg'.obj E) (Lg.obj K)) :=
by
  sorry

end

end CategoryTheory
