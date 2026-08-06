import Mathlib.LinearAlgebra.TensorProduct.Map
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory
open SpacePair
open scoped TensorProduct

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced general graded tensor-product APIs, not a
-- ready-made cohomology-ring owner for the current Chapter 18 pair-theory interface. This file
-- therefore records the source-faithful absolute cup-product structure directly on
-- `PairCohomologyTheory`.

/-- The absolute-pair functor `X ↦ (X, ∅)`. -/
private def absolutePairFunctor : TopCat.{u} ⥤ SpacePair.{u} where
  obj X := SpacePair.absolute X
  map f :=
    { hom := f
      map_subspace' := by
        intro x hx
        cases hx }
  map_id := by
    intro X
    apply SpacePair.hom_ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply SpacePair.hom_ext
    rfl

namespace PairCohomologyTheory

variable {π : Type u} [AddCommGroup π]

/-- The absolute cohomology functor `X ↦ H^q(X, ∅; π)` underlying a pair cohomology theory `H`. -/
abbrev absoluteCohomology (H : PairCohomologyTheory π) (q : ℤ) :
    TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  absolutePairFunctor.op ⋙ H.cohomology q

/-- Evaluating `H.absoluteCohomology q` at `X` gives `H^q(X, ∅; π)`. -/
@[simp] theorem absoluteCohomology_obj (H : PairCohomologyTheory π) (q : ℤ) (X : TopCat.{u}) :
    (H.absoluteCohomology q).obj (Opposite.op X) =
      (H.cohomology q).obj (Opposite.op (SpacePair.absolute X)) :=
  rfl

end PairCohomologyTheory

/-- Definition 18.3.1. An absolute cup product on a pair cohomology theory with commutative
coefficients `R` is a natural pairing `H^p(X; R) ⊗ H^q(X; R) → H^(p + q)(X; R)` together with a
unit in degree `0`, making the graded family `H^*(X; R)` into a graded ring for each space `X`.
-/
structure AbsoluteCupProduct {R : Type u} [CommRing R] (H : PairCohomologyTheory R) where
  /-- The degreewise bilinear pairing `H^p(X; R) ⊗ H^q(X; R) → H^(p + q)(X; R)`. -/
  cup (X : TopCat.{u}) (p q : ℤ) :
      (H.absoluteCohomology p).obj (Opposite.op X) ⊗[ℤ]
        (H.absoluteCohomology q).obj (Opposite.op X) →ₗ[ℤ]
          (H.absoluteCohomology (p + q)).obj (Opposite.op X)
  /-- Pullback along a map of spaces is multiplicative for the cup product. -/
  naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (p q : ℤ) :
      (cup X p q).comp
          (TensorProduct.map
            (((H.absoluteCohomology p).map f.op).hom.toIntLinearMap)
            (((H.absoluteCohomology q).map f.op).hom.toIntLinearMap)) =
        (((H.absoluteCohomology (p + q)).map f.op).hom.toIntLinearMap).comp
          (cup Y p q)
  /-- The degree-zero unit class in `H^0(X; R)`. -/
  oneClass (X : TopCat.{u}) : (H.absoluteCohomology 0).obj (Opposite.op X)
  /-- The degree-zero unit class acts as a left unit for the cup product. -/
  left_unit {X : TopCat.{u}} (p : ℤ) (α : (H.absoluteCohomology p).obj (Opposite.op X)) :
      cast (by simp) (cup X 0 p (TensorProduct.tmul ℤ (oneClass X) α)) = α
  /-- The degree-zero unit class acts as a right unit for the cup product. -/
  right_unit {X : TopCat.{u}} (p : ℤ) (α : (H.absoluteCohomology p).obj (Opposite.op X)) :
      cast (by simp) (cup X p 0 (TensorProduct.tmul ℤ α (oneClass X))) = α
  /-- The cup product is associative on homogeneous classes. -/
  assoc {X : TopCat.{u}} (p q r : ℤ)
      (α : (H.absoluteCohomology p).obj (Opposite.op X))
      (β : (H.absoluteCohomology q).obj (Opposite.op X))
      (γ : (H.absoluteCohomology r).obj (Opposite.op X)) :
      cup X (p + q) r
          (TensorProduct.tmul ℤ (cup X p q (TensorProduct.tmul ℤ α β)) γ) =
        cast (by simp [add_assoc])
          (cup X p (q + r)
            (TensorProduct.tmul ℤ α (cup X q r (TensorProduct.tmul ℤ β γ))))

/-- An absolute cup product coerces to its underlying family of bilinear pairings. -/
instance absoluteCupProductCoeFun {R : Type u} [CommRing R] (H : PairCohomologyTheory R) :
    CoeFun (AbsoluteCupProduct H) (fun _ ↦
      ∀ (X : TopCat.{u}) (p q : ℤ),
        (H.absoluteCohomology p).obj (Opposite.op X) ⊗[ℤ]
          (H.absoluteCohomology q).obj (Opposite.op X) →ₗ[ℤ]
            (H.absoluteCohomology (p + q)).obj (Opposite.op X)) where
  coe cupProduct := cupProduct.cup
