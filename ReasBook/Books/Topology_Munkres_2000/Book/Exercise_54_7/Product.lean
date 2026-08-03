module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section

universe u v

open CategoryTheory
open FundamentalGroupoidFunctor

namespace FundamentalGroup

/-- The projections from `X × Y` induce the canonical product decomposition of
the fundamental group. -/
def prodMulEquiv {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (x₀ : X) (y₀ : Y) :
    FundamentalGroup (X × Y) (x₀, y₀) ≃* FundamentalGroup X x₀ × FundamentalGroup Y y₀ where
  toFun p :=
    ((projLeft (TopCat.of X) (TopCat.of Y)).map p,
      (projRight (TopCat.of X) (TopCat.of Y)).map p)
  invFun p := Path.Homotopic.prod p.1 p.2
  left_inv := Path.Homotopic.prod_projLeft_projRight
  right_inv p := by ext <;> simp
  map_mul' p q := by
    apply Prod.ext
    · exact (projLeft (TopCat.of X) (TopCat.of Y)).map_comp q p
    · exact (projRight (TopCat.of X) (TopCat.of Y)).map_comp q p

/-- The fundamental group of a product with a trivial second fundamental group is the
fundamental group of the first factor. -/
noncomputable def prodMulEquivLeftOfSubsingleton {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y)
    (hY : Subsingleton (FundamentalGroup Y y₀)) :
    FundamentalGroup (X × Y) (x₀, y₀) ≃* FundamentalGroup X x₀ :=
  (prodMulEquiv x₀ y₀).trans <|
    MulEquiv.mk'
      { toFun := MonoidHom.fst _ _
        invFun := MonoidHom.inl _ _
        left_inv := by
          intro p
          ext
          · rfl
          · exact hY.elim _ _
        right_inv := by
          intro p
          rfl }
      (MonoidHom.fst _ _).map_mul

/-- Forgetting a trivial second fundamental-group factor sends a loop to its first
projection. -/
@[simp]
theorem prodMulEquivLeftOfSubsingleton_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y)
    (hY : Subsingleton (FundamentalGroup Y y₀))
    (p : FundamentalGroup (X × Y) (x₀, y₀)) :
    prodMulEquivLeftOfSubsingleton x₀ y₀ hY p = Path.Homotopic.projLeft p := by
  rfl

/-- The product decomposition sends a loop to the pair of its projected loops. -/
@[simp]
theorem prodMulEquiv_apply {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (x₀ : X) (y₀ : Y) (p : FundamentalGroup (X × Y) (x₀, y₀)) :
    prodMulEquiv x₀ y₀ p = (Path.Homotopic.projLeft p, Path.Homotopic.projRight p) := by
  change
    ((projLeft (TopCat.of X) (TopCat.of Y)).map p,
      (projRight (TopCat.of X) (TopCat.of Y)).map p) = _
  rfl

/-- The inverse product decomposition forms the product of two loops. -/
@[simp]
theorem prodMulEquiv_symm_apply {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (x₀ : X) (y₀ : Y) (p : FundamentalGroup X x₀ × FundamentalGroup Y y₀) :
    (prodMulEquiv x₀ y₀).symm p = Path.Homotopic.prod p.1 p.2 := by
  change Path.Homotopic.prod p.1 p.2 = _
  rfl

end FundamentalGroup
