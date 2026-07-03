import Mathlib
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Opposites
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_19_extra_1 (from Chap03/Sec03_19) -/
open CategoryTheory

/- Definition 3.19-extra-1: a category is the canonical mathlib typeclass
`Category C`, whose underlying hom-types, identity morphisms, and composition
come from `CategoryStruct`, and whose axioms are the identity laws
`Category.id_comp`, `Category.comp_id`, and associativity `Category.assoc`. -/
recall Category

/-! ### Definition_3_19_extra_2 (from Chap03/Sec03_19) -/
/- Definition 3.19-extra-2: the canonical notion that a morphism in a category is an
isomorphism is `CategoryTheory.IsIso f`, meaning that `f` admits a two-sided inverse. -/
recall CategoryTheory.IsIso

/-! ### Definition_3_19_extra_3 (from Chap03/Sec03_19) -/
open CategoryTheory

/- Definition 3.19-extra-3 (1): `SmallCategory C` is the canonical notion of a small category. -/
recall SmallCategory

/- Definition 3.19-extra-3 (2): `LocallySmall C` is the canonical notion that each hom-type
`Hom_C(X,Y)` is small. -/
recall LocallySmall

/-! ### Definition_3_19_extra_4 (from Chap03/Sec03_19) -/
/- Definition 3.19-extra-4: a covariant functor from a category `C` to a category `D` is
canonically an element of `C ⥤ D`, i.e. of `CategoryTheory.Functor C D`; its primitive data are
the object assignment `obj` and morphism assignment `map`, and its functoriality axioms are
`map_id` and `map_comp`. -/
#check (C ⥤ D)

/-! ### Definition_3_19_extra_5 (from Chap03/Sec03_19) -/
open CategoryTheory

section

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Definition 3.19-extra-5: a contravariant functor from `C` to `D` is canonically a functor
`Cᵒᵖ ⥤ D`. -/
#check (Cᵒᵖ ⥤ D)

end

/-! ### Exercise_3_19 (from Chap03/Sec03_16) -/
open scoped Manifold

noncomputable section

universe u

variable {n : ℕ} [NeZero n]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ⊤ M]

/- Exercise 3.19: if `M` is a smooth manifold with boundary, then its tangent bundle carries the
canonical topology and smooth structure coming from the tangent-bundle model with corners
`(𝓡∂ n).tangent`. -/
#synth TopologicalSpace (TangentBundle (𝓡∂ n) M)
#synth IsManifold (𝓡∂ n).tangent ⊤ (TangentBundle (𝓡∂ n) M)

-- Proof sketch: compose the canonical tangent-bundle chart with the product-swap homeomorphism;
-- its coordinate expression is then the tuple `(v, x)` obtained from the natural `(x, v)` chart
-- by permuting the two factors.
/-- Exercise 3.19: the canonical tangent-bundle topology and smooth structure on `TM` for a smooth
manifold with boundary have the property that swapping the factors in the natural chart
`(x, v)` gives the boundary-chart coordinate expression `(v, x)` described in the exercise. -/
theorem tangentBundleBoundaryChart_apply
    (p q : TangentBundle (𝓡∂ n) M) :
    ((chartAt (ModelProd (EuclideanHalfSpace n) (EuclideanSpace ℝ (Fin n))) p).transHomeomorph
      (Homeomorph.prodComm (EuclideanHalfSpace n) (EuclideanSpace ℝ (Fin n))) q) =
      Prod.swap ((chartAt (ModelProd (EuclideanHalfSpace n) (EuclideanSpace ℝ (Fin n))) p) q) := rfl
