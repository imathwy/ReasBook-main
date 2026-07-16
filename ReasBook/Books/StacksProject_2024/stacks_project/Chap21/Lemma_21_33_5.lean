import Mathlib.CategoryTheory.CommSq
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1_core
import StacksProject_2024.stacks_project.Chap21.Remark_21_19_3_core

open CategoryTheory

noncomputable section

universe u u' v v'

namespace CategoryTheory

section

variable {DX DY : Type u} {DX' DY' : Type u'}
variable [Category.{v} DX] [Category.{v'} DX'] [Category.{v} DY] [Category.{v'} DY']

/- Domain-style sampling for Lemma 21.33.5:
- primary domain: compatibility between `relativeDerivedCupProduct` and canonical derived
  base-change maps across a commutative square of adjunctions;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the compatibility square between the relative derived cup product and the
    canonical base-change maps;
  `core/canonical`: `relativeDerivedCupProduct`, `derivedBaseChangeMap`, and `CommSq`;
  `bridge/view`: none should survive as a second public owner in this file.

Primitive data are the square isomorphism together with the four pullback-tensor comparison
isomorphisms and their compatibility with the square isomorphism. The public statement should
therefore be the single canonical `CommSq` theorem.
-/

/-- Lemma 21.33.5: the relative cup product is compatible with canonical derived base-change
maps when the square isomorphism is compatible with the pullback-tensor comparisons. -/
@[stacks 0H9A]
theorem relativeDerivedCupProduct_baseChange_commSq
    (Lf : DY ⥤ DX) (Lf' : DY' ⥤ DX') (Lg : DY ⥤ DY') (Lg' : DX ⥤ DX')
    (Rf : DX ⥤ DY) (Rf' : DX' ⥤ DY')
    (tensorX : DX ⥤ DX ⥤ DX) (tensorX' : DX' ⥤ DX' ⥤ DX')
    (tensorY : DY ⥤ DY ⥤ DY) (tensorY' : DY' ⥤ DY' ⥤ DY')
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')
    (pullbackTensorIso_f :
      ∀ A B : DY,
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (pullbackTensorIso_f' :
      ∀ A B : DY',
        Lf'.obj ((tensorY'.obj B).obj A) ≅
          ((tensorX'.obj (Lf'.obj B)).obj (Lf'.obj A)))
    (pullbackTensorIso_g :
      ∀ A B : DY,
        Lg.obj ((tensorY.obj B).obj A) ≅
          ((tensorY'.obj (Lg.obj B)).obj (Lg.obj A)))
    (pullbackTensorIso_g' :
      ∀ A B : DX,
        Lg'.obj ((tensorX.obj B).obj A) ≅
          ((tensorX'.obj (Lg'.obj B)).obj (Lg'.obj A)))
    (squareIsoTensorCommSq :
      ∀ A B : DY,
        CommSq
          (Lf'.map (pullbackTensorIso_g A B).hom)
          (squareIso.hom.app ((tensorY.obj B).obj A))
          (pullbackTensorIso_f' (Lg.obj A) (Lg.obj B)).hom
          (Lg'.map (pullbackTensorIso_f A B).hom ≫
            (pullbackTensorIso_g' (Lf.obj A) (Lf.obj B)).hom ≫
            (tensorX'.map (squareIso.inv.app B)).app (Lg'.obj (Lf.obj A)) ≫
            (tensorX'.obj (Lf'.obj (Lg.obj B))).map (squareIso.inv.app A)))
    (K L : DX) :
    let ηK := derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K
    let ηL := derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso L
    let ηKL :=
      derivedBaseChangeMap
        Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso ((tensorX.obj L).obj K)
    CommSq
      (Lg.map
        (relativeDerivedCupProduct
          Lf Rf adj_f tensorX tensorY pullbackTensorIso_f K L))
      ((pullbackTensorIso_g (Rf.obj K) (Rf.obj L)).hom ≫
        (tensorY'.map ηL).app (Lg.obj (Rf.obj K)) ≫
        (tensorY'.obj (Rf'.obj (Lg'.obj L))).map ηK)
      (ηKL ≫ Rf'.map (pullbackTensorIso_g' K L).hom)
      (relativeDerivedCupProduct
        Lf' Rf' adj_f' tensorX' tensorY' pullbackTensorIso_f' (Lg'.obj K) (Lg'.obj L)) := by
  sorry

end

end CategoryTheory
