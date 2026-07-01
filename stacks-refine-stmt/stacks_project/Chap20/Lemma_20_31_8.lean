import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of not-necessarily-commutative
rings. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules on a
ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

section

variable {X X' Y Y' : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DModX'" => ModuleDerived X'
local notation "DModY" => ModuleDerived Y
local notation "DModY'" => ModuleDerived Y'

variable
  (Lf : DModY ⥤ DModX)
  (Lf' : DModY' ⥤ DModX')
  (Lg : DModY ⥤ DModY')
  (Lg' : DModX ⥤ DModX')
  (Rf : DModX ⥤ DModY)
  (Rf' : DModX' ⥤ DModY')

variable
  (tensorX : DModX ⥤ DModX ⥤ DModX)
  (tensorX' : DModX' ⥤ DModX' ⥤ DModX')
  (tensorY : DModY ⥤ DModY ⥤ DModY)
  (tensorY' : DModY' ⥤ DModY' ⥤ DModY')

variable
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is a derived base-change map if, after
transposing across the adjunction `L(f')^* ⊣ R(f')_*`, it is the pullback of the counit
`Lf^* Rf_* K ⟶ K` transported through the commutativity isomorphism
`L(g)^* \circ L(f')^* \cong L(f)^* \circ L(g')^*`. -/
def IsDerivedBaseChangeMap
    (K : DModX)
    (η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm η) =
    (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K))

/-- The adjoint-side morphism whose transpose is the relative cup product. -/
noncomputable def relativeDerivedCupProductAdjoint
    (pullbackTensorIso :
      ∀ (A B : DModY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DModX) :
    Lf.obj ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      ((tensorX.obj L).obj K) :=
  (pullbackTensorIso (Rf.obj K) (Rf.obj L)).hom ≫
    ((tensorX.map (adj_f.counit.app L)).app (Lf.obj (Rf.obj K))) ≫
    ((tensorX.obj L).map (adj_f.counit.app K))

/-- The relative cup product attached to an adjunction `Lf^* ⊣ Rf_*` and a pullback-tensor
comparison for `Lf^*`. -/
noncomputable def relativeDerivedCupProduct
    (pullbackTensorIso :
      ∀ (A B : DModY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DModX) :
    ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      Rf.obj ((tensorX.obj L).obj K) :=
  (adj_f.homEquiv
      ((tensorY.obj (Rf.obj L)).obj (Rf.obj K))
      ((tensorX.obj L).obj K))
    (relativeDerivedCupProductAdjoint
      Lf
      Rf
      tensorX
      tensorY
      adj_f
      pullbackTensorIso
      K
      L)

-- Proof sketch: transpose both routes across `adj_f'`. The three base-change hypotheses identify
-- the vertical maps with the pullback of the counits via `squareIso`, while the two cup-product
-- maps are, by definition, the transposes of the pullback-tensor comparisons followed by those
-- same counits. After rewriting the pullbacks of the tensor products with `pullbackTensorIso_g`
-- and `pullbackTensorIso_g'`, both transposes are the same morphism from
-- `Lf' Lg (Rf K \otimes^{\mathbf L} Rf L)` to `Lg' (K \otimes^{\mathbf L} L)`.
/-- Lemma 20.31.8: for a commutative square of ringed spaces, the relative cup product is
compatible with base change. Formally, given derived pullback and pushforward functors for the
four corners, adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ R(f')_*`, pullback-tensor comparison
isomorphisms for the horizontal and vertical maps, and base-change morphisms for `K`, `L`, and
`K \otimes_{\mathcal O_X}^{\mathbf L} L`, the resulting square comparing the relative cup product
for `f` with the relative cup product for `f'` commutes in `D(\mathcal O_{Y'})`. -/
theorem relativeDerivedCupProduct_baseChange_commutes
    (pullbackTensorIso_f :
      ∀ (A B : DModY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (pullbackTensorIso_f' :
      ∀ (A B : DModY'),
        Lf'.obj ((tensorY'.obj B).obj A) ≅
          ((tensorX'.obj (Lf'.obj B)).obj (Lf'.obj A)))
    (pullbackTensorIso_g :
      ∀ (A B : DModY),
        Lg.obj ((tensorY.obj B).obj A) ≅
          ((tensorY'.obj (Lg.obj B)).obj (Lg.obj A)))
    (pullbackTensorIso_g' :
      ∀ (A B : DModX),
        Lg'.obj ((tensorX.obj B).obj A) ≅
          ((tensorX'.obj (Lg'.obj B)).obj (Lg'.obj A)))
    (K L : DModX)
    (ηK : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K))
    (ηL : Lg.obj (Rf.obj L) ⟶ Rf'.obj (Lg'.obj L))
    (ηKL : Lg.obj (Rf.obj ((tensorX.obj L).obj K)) ⟶
      Rf'.obj (Lg'.obj ((tensorX.obj L).obj K)))
    (hηK : IsDerivedBaseChangeMap K ηK)
    (hηL : IsDerivedBaseChangeMap L ηL)
    (hηKL : IsDerivedBaseChangeMap ((tensorX.obj L).obj K) ηKL) :
    Lg.map
        (relativeDerivedCupProduct pullbackTensorIso_f K L) ≫
      ηKL ≫
      Rf'.map ((pullbackTensorIso_g' K L).hom) =
    ((pullbackTensorIso_g (Rf.obj K) (Rf.obj L)).hom) ≫
      ((tensorY'.map ηL).app (Lg.obj (Rf.obj K))) ≫
      ((tensorY'.obj (Rf'.obj (Lg'.obj L))).map ηK) ≫
      relativeDerivedCupProduct pullbackTensorIso_f' (Lg'.obj K) (Lg'.obj L) := sorry

end

end AlgebraicGeometry.RingedSpace
