import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` did not surface a pre-existing category whose morphisms are
finite-order differential operators. The local owner predicate is
`SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`, and Lemma 29.33.2 supplies the
tensoring construction used for the external product. The tag evidence is consistent:
item tag `0G46` matches the source URL `/tag/0G46`. -/

/-- The inverse-image structure-sheaf map used to regard `\mathcal O_X`-modules as modules
relative to a morphism `a : X ⟶ S`. -/
noncomputable abbrev relativeStructureSheafMap {X S : Scheme.{u}} (a : X ⟶ S) :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom

/-- Remark 29.33.3 (1): for morphisms `a : X ⟶ S` and `b : Y ⟶ S`, the external tensor product
of an `\mathcal O_X`-module `\mathcal F` and an `\mathcal O_Y`-module `\mathcal G` is
`p^*\mathcal F ⊗ q^*\mathcal G` on `X ×_S Y`, where `p` and `q` are the two projections. -/
@[stacks 0G46]
abbrev externalTensorProduct
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [MonoidalCategory (Limits.pullback a b).Modules]
    (ℱ : X.Modules) (𝒢 : Y.Modules) : (Limits.pullback a b).Modules :=
  (tensorObj ((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj ℱ)
    ((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj 𝒢) :
      (Limits.pullback a b).Modules)

/-- Remark 29.33.3 (2): a morphism in the category `\mathcal A_{X/S}` is a finite-order
differential operator between the corresponding `\mathcal O_X`-modules, expressed through the
ringed-site differential-operator predicate. -/
@[stacks 0G46]
structure RelativeFiniteOrderDifferentialOperator
    {X S : Scheme.{u}} (a : X ⟶ S) (ℱ 𝒢 : X.Modules) where
  /-- The underlying morphism after restriction of scalars along `a`. -/
  hom :
    (restrictionAlong (relativeStructureSheafMap a)).obj ℱ ⟶
      (restrictionAlong (relativeStructureSheafMap a)).obj 𝒢
  /-- The underlying morphism is a differential operator of some finite order. -/
  finiteOrder :
    ∃ k : ℕ, IsDifferentialOperatorOfOrder.{u, u} (relativeStructureSheafMap a) hom k

/-- Coerce a relative finite-order differential operator to its underlying restricted morphism. -/
instance instCoeRelativeFiniteOrderDifferentialOperator
    {X S : Scheme.{u}} {a : X ⟶ S} {ℱ 𝒢 : X.Modules} :
    Coe (RelativeFiniteOrderDifferentialOperator a ℱ 𝒢)
      ((restrictionAlong (relativeStructureSheafMap a)).obj ℱ ⟶
        (restrictionAlong (relativeStructureSheafMap a)).obj 𝒢) where
  coe D := D.hom

/-- The source-facing specification of a relative finite-order differential operator: it is its
underlying restricted morphism together with a finite order bound. -/
@[stacks 0G46]
theorem RelativeFiniteOrderDifferentialOperator.finiteOrder.spec
    {X S : Scheme.{u}} {a : X ⟶ S} {ℱ 𝒢 : X.Modules}
    (D : RelativeFiniteOrderDifferentialOperator a ℱ 𝒢) :
    (((D :
      (restrictionAlong (relativeStructureSheafMap a)).obj ℱ ⟶
        (restrictionAlong (relativeStructureSheafMap a)).obj 𝒢) = D.hom) ∧
      (∃ k : ℕ,
        IsDifferentialOperatorOfOrder.{u, u} (relativeStructureSheafMap a)
          (D :
            (restrictionAlong (relativeStructureSheafMap a)).obj ℱ ⟶
              (restrictionAlong (relativeStructureSheafMap a)).obj 𝒢) k)) := sorry

/-- A restricted morphism underlies a relative finite-order differential operator exactly when it
has some finite order as a differential operator. -/
@[stacks 0G46]
theorem relativeFiniteOrderDifferentialOperator_iff
    {X S : Scheme.{u}} {a : X ⟶ S} {ℱ 𝒢 : X.Modules}
    (f :
      (restrictionAlong (relativeStructureSheafMap a)).obj ℱ ⟶
        (restrictionAlong (relativeStructureSheafMap a)).obj 𝒢) :
    (∃ D : RelativeFiniteOrderDifferentialOperator a ℱ 𝒢, D.hom = f) ↔
      ∃ k : ℕ,
        IsDifferentialOperatorOfOrder.{u, u} (relativeStructureSheafMap a) f k := sorry

/-- Remark 29.33.3 (3): the construction of Lemma 29.33.2 determines the morphism action of the
external tensor product on finite-order differential operators. Given operators `D` on `X/S` and
`E` on `Y/S` with respective order bounds `k` and `l`, there is an induced operator on
`(\mathcal F \boxtimes \mathcal G) ⟶ (\mathcal F' \boxtimes \mathcal G')` over `X ×_S Y/S`,
whose order is bounded by `k + l`. -/
@[stacks 0G46]
theorem exists_externalTensorProductDifferentialOperator
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [MonoidalCategory (Limits.pullback a b).Modules]
    {ℱ ℱ' : X.Modules} [ℱ.IsQuasicoherent] [ℱ'.IsQuasicoherent]
    {𝒢 𝒢' : Y.Modules} [𝒢.IsQuasicoherent] [𝒢'.IsQuasicoherent]
    (D : RelativeFiniteOrderDifferentialOperator a ℱ ℱ')
    (E : RelativeFiniteOrderDifferentialOperator b 𝒢 𝒢')
    {k l : ℕ}
    (hD : IsDifferentialOperatorOfOrder.{u, u} (relativeStructureSheafMap a) D.hom k)
    (hE : IsDifferentialOperatorOfOrder.{u, u} (relativeStructureSheafMap b) E.hom l) :
    ∃ DE : RelativeFiniteOrderDifferentialOperator (Limits.pullback.fst a b ≫ a)
        (externalTensorProduct a b ℱ 𝒢)
        (externalTensorProduct a b ℱ' 𝒢'),
      IsDifferentialOperatorOfOrder.{u, u}
        (relativeStructureSheafMap (Limits.pullback.fst a b ≫ a)) DE.hom (k + l) := sorry

/-- Remark 29.33.3 (4): in the affine case `X = Spec(A)`, `Y = Spec(B)`, and `S = Spec(R)`,
the morphism part of the external tensor product functor is the usual tensor product of
`R`-linear maps. -/
@[stacks 0G46]
abbrev affineExternalTensorProductMap
    {R M M' N N' : Type u}
    [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (D : M →ₗ[R] M') (E : N →ₗ[R] N') :
    TensorProduct R M N →ₗ[R] TensorProduct R M' N' :=
  TensorProduct.map D E

/-- Remark 29.33.3 (5): on pure tensors, the affine morphism formula is
`(D ⊗ D') (m ⊗ n) = D(m) ⊗ D'(n)`. -/
@[stacks 0G46]
theorem affineExternalTensorProductMap_tmul
    {R A B M M' N N' : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    [Module A M] [Module A M'] [IsScalarTower R A M] [IsScalarTower R A M']
    [Module B N] [Module B N'] [IsScalarTower R B N] [IsScalarTower R B N']
    {k l : ℕ}
    (D : differential_operators_order_le R A M k M')
    (E : differential_operators_order_le R B N l N')
    (m : M) (n : N) :
    affineExternalTensorProductMap D.1 E.1 (m ⊗ₜ[R] n) = D.1 m ⊗ₜ[R] E.1 n := sorry

end AlgebraicGeometry.Scheme.Modules
