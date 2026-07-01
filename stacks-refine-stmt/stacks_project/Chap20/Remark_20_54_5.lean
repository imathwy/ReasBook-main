import Mathlib
import stacks_project.Chap20.Lemma_20_31_8
import stacks_project.Chap20.«20_54_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X X' Y Y' : RingedSpace.{u}}

variable
  (Lf : ModuleDerived Y ⥤ ModuleDerived X)
  (Lf' : ModuleDerived Y' ⥤ ModuleDerived X')
  (Lg : ModuleDerived Y ⥤ ModuleDerived Y')
  (Lg' : ModuleDerived X ⥤ ModuleDerived X')
  (Rf : ModuleDerived X ⥤ ModuleDerived Y)
  (Rf' : ModuleDerived X' ⥤ ModuleDerived Y')

variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')]
variable [MonoidalCategory (ModuleDerived Y)]
variable [MonoidalCategory (ModuleDerived Y')]

variable
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

variable
  (pullbackTensorIso_f :
    ∀ (A B : ModuleDerived Y),
      Lf.obj (A ⊗ B) ≅
        (Lf.obj A ⊗ Lf.obj B))
  (pullbackTensorIso_f' :
    ∀ (A B : ModuleDerived Y'),
      Lf'.obj (A ⊗ B) ≅
        (Lf'.obj A ⊗ Lf'.obj B))
  (pullbackTensorIso_g :
    ∀ (A B : ModuleDerived Y),
      Lg.obj (A ⊗ B) ≅
        (Lg.obj A ⊗ Lg.obj B))
  (pullbackTensorIso_g' :
    ∀ (A B : ModuleDerived X),
      Lg'.obj (A ⊗ B) ≅
        (Lg'.obj A ⊗ Lg'.obj B))

local notation "DModX" => ModuleDerived X
local notation "DModX'" => ModuleDerived X'
local notation "DModY" => ModuleDerived Y
local notation "DModY'" => ModuleDerived Y'

/-- A morphism `Lg^* Rf_* A ⟶ R(f')_* L(g')^* A` is the base-change map for the square if its
transpose across `Lf' ⊣ Rf'` is the pullback of the counit `Lf^* Rf_* A ⟶ A` transported through
the commutativity isomorphism `Lg ⋙ Lf' ≅ Lf ⋙ Lg'`. -/
def IsBaseChangeMapInDerivedSquare
    (A : DModX)
    (η : Lg.obj (Rf.obj A) ⟶ Rf'.obj (Lg'.obj A)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj A)) (Lg'.obj A)).symm η) =
    (squareIso.hom.app (Rf.obj A) ≫ Lg'.map (adj_f.counit.app A))

-- Proof sketch: expand the top and bottom arrows by the definition of
-- `projectionFormulaMorphism`.
-- Naturality of the
-- adjunction units makes the tensor-with-unit part commute with the base-change map for `E`, and
-- Lemma `20.31.8` gives the corresponding compatibility for the relative cup-product part. The
-- final comparison `c` is the tensor-level transport induced by `squareIso.inv.app K`.
/-- Remark 20.54.5: for a commutative square of ringed spaces, the projection-formula morphism
`(20.54.2.1)` is compatible with the base-change morphism of Remark `20.28.3`. In the abstract
derived-category formulation, if `ηE` and `ηTensor` are the base-change maps for `E` and for
`Lf^* K \otimes_{\mathcal O_X}^{\mathbf L} E`, then the rectangle comparing the pullback of the
projection-formula map for `f` with the projection-formula map for `f'` commutes. -/
theorem projectionFormulaMorphism_baseChange_commSq
    (E : DModX)
    (K : DModY)
    (ηE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (ηTensor :
      Lg.obj (Rf.obj (Lf.obj K ⊗ E)) ⟶
        Rf'.obj (Lg'.obj (Lf.obj K ⊗ E)))
    (hηE :
      IsBaseChangeMapInDerivedSquare Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso E ηE)
    (hηTensor :
      IsBaseChangeMapInDerivedSquare
        Lf
        Lf'
        Lg
        Lg'
        Rf
        Rf'
        adj_f
        adj_f'
        squareIso
        (Lf.obj K ⊗ E)
        ηTensor) :
    CommSq
      (Lg.map (projectionFormulaMorphism Lf Rf adj_f pullbackTensorIso_f E K))
      ((pullbackTensorIso_g K (Rf.obj E)).hom ≫
        (𝟙 (Lg.obj K) ⊗ₘ ηE))
      (ηTensor ≫
        Rf'.map
          ((pullbackTensorIso_g' (Lf.obj K) E).hom ≫
            (squareIso.inv.app K ⊗ₘ 𝟙 (Lg'.obj E))))
      (projectionFormulaMorphism Lf' Rf' adj_f' pullbackTensorIso_f' (Lg'.obj E) (Lg.obj K)) :=
  sorry

end

end AlgebraicGeometry.RingedSpace
