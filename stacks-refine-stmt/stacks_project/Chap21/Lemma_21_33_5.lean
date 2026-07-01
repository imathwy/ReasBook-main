import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {DX DX' DY DY' : Type u}
variable [Category.{v} DX] [Category.{v} DX'] [Category.{v} DY] [Category.{v} DY']

variable
  (Lf : DY ⥤ DX)
  (Lf' : DY' ⥤ DX')
  (Lg : DY ⥤ DY')
  (Lg' : DX ⥤ DX')
  (Rf : DX ⥤ DY)
  (Rf' : DX' ⥤ DY')

variable
  (tensorX : DX ⥤ DX ⥤ DX)
  (tensorX' : DX' ⥤ DX' ⥤ DX')
  (tensorY : DY ⥤ DY ⥤ DY)
  (tensorY' : DY' ⥤ DY' ⥤ DY')

variable
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/-- The adjoint-side morphism whose transpose is the relative cup product. -/
noncomputable def relativeDerivedCupProductAdjoint
    (pullbackTensorIso :
      ∀ (A B : DY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DX) :
    Lf.obj ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      ((tensorX.obj L).obj K) :=
  (pullbackTensorIso (Rf.obj K) (Rf.obj L)).hom ≫
    ((tensorX.map (adj_f.counit.app L)).app (Lf.obj (Rf.obj K))) ≫
    ((tensorX.obj L).map (adj_f.counit.app K))

/-- The relative cup product obtained by transposing the pullback-side morphism across the
adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def relativeDerivedCupProduct
    (pullbackTensorIso :
      ∀ (A B : DY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DX) :
    ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      Rf.obj ((tensorX.obj L).obj K) :=
  (adj_f.homEquiv
      ((tensorY.obj (Rf.obj L)).obj (Rf.obj K))
      ((tensorX.obj L).obj K))
    (relativeDerivedCupProductAdjoint
      Lf Rf tensorX tensorY adj_f pullbackTensorIso K L)

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is a derived base-change map if, after
transposing across the adjunction `L(f')^* ⊣ R(f')_*`, it is the pullback of the counit
`Lf^* Rf_* K ⟶ K` transported through the commutativity isomorphism
`Lg^* \circ L(f')^* ≅ Lf^* \circ L(g')^*`. -/
def IsDerivedBaseChangeMap
    (K : DX)
    (η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm η) =
    (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K))

-- Proof sketch: transpose both routes across `adj_f'`. The hypotheses `hηK`, `hηL`, and `hηKL`
-- identify the three base-change morphisms with pullbacks of the counit for `adj_f` through
-- `squareIso`. Unfolding `relativeDerivedCupProduct` on both horizontal arrows then reduces both
-- transposes to the same morphism built from the pullback-tensor comparisons for `f`, `f'`, `g`,
-- and `g'` together with the two counits of `adj_f`.
/-- Lemma 21.33.5: for a commutative square of ringed topoi, the relative cup product is
compatible with base change. In the abstract derived-category formulation used here, after choosing
derived pullback and pushforward functors for the four corners, pullback-tensor comparison
isomorphisms for the four sides, and base-change morphisms for `K`, `L`, and
`K \otimes^{\mathbf L} L`, the two induced morphisms
`Lg^*(Rf_* K \otimes^{\mathbf L} Rf_* L) ⟶ R(f')_*(L(g')^* K \otimes^{\mathbf L} L(g')^* L)`
agree. -/
theorem relativeDerivedCupProduct_baseChange_commutes
    (pullbackTensorIso_f :
      ∀ (A B : DY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (pullbackTensorIso_f' :
      ∀ (A B : DY'),
        Lf'.obj ((tensorY'.obj B).obj A) ≅
          ((tensorX'.obj (Lf'.obj B)).obj (Lf'.obj A)))
    (pullbackTensorIso_g :
      ∀ (A B : DY),
        Lg.obj ((tensorY.obj B).obj A) ≅
          ((tensorY'.obj (Lg.obj B)).obj (Lg.obj A)))
    (pullbackTensorIso_g' :
      ∀ (A B : DX),
        Lg'.obj ((tensorX.obj B).obj A) ≅
          ((tensorX'.obj (Lg'.obj B)).obj (Lg'.obj A)))
    (K L : DX)
    (ηK : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K))
    (ηL : Lg.obj (Rf.obj L) ⟶ Rf'.obj (Lg'.obj L))
    (ηKL : Lg.obj (Rf.obj ((tensorX.obj L).obj K)) ⟶
      Rf'.obj (Lg'.obj ((tensorX.obj L).obj K)))
    (hηK :
      IsDerivedBaseChangeMap
        Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K ηK)
    (hηL :
      IsDerivedBaseChangeMap
        Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso L ηL)
    (hηKL :
      IsDerivedBaseChangeMap
        Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso
        ((tensorX.obj L).obj K) ηKL) :
    Lg.map
        (relativeDerivedCupProduct
          Lf Rf tensorX tensorY adj_f pullbackTensorIso_f K L) ≫
      ηKL ≫
      Rf'.map ((pullbackTensorIso_g' K L).hom) =
    ((pullbackTensorIso_g (Rf.obj K) (Rf.obj L)).hom) ≫
      ((tensorY'.map ηL).app (Lg.obj (Rf.obj K))) ≫
      ((tensorY'.obj (Rf'.obj (Lg'.obj L))).map ηK) ≫
      relativeDerivedCupProduct
        Lf' Rf' tensorX' tensorY' adj_f' pullbackTensorIso_f'
        (Lg'.obj K) (Lg'.obj L) := sorry

end

end CategoryTheory
