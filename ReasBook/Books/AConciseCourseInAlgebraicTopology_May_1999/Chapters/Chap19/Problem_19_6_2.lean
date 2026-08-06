import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Definition_18_3_1

open CategoryTheory
open SpacePair
open scoped TensorProduct

universe u v

-- Semantic recall via `lean_leansearch` only surfaced unrelated general cohomology APIs. Local
-- Chapter 14/18 precedent already fixes the pair owner `subsetPair` together with the canonical
-- ambient context `PairCohomologyTheory` and `AbsoluteCupProduct`, while the abstract
-- `E`-parameterized family of relative cup-product maps remains useful helper infrastructure for
-- downstream problems.

section

variable (E : ℤ → (X : TopCat.{u}) → Set X → Type v)
variable [∀ q (X : TopCat.{u}) (A : Set X), AddCommGroup (E q X A)]
variable [∀ q (X : TopCat.{u}) (A : Set X), Module ℤ (E q X A)]

/-- Families of bilinear maps `H^p(X, A) ⊗ H^q(X, B) → H^(p + q)(X, A ∪ B)`. -/
abbrev RelativeCupProductMap :=
  ∀ {X : TopCat.{u}} (A B : Set X) (p q : ℤ),
    E p X A ⊗[ℤ] E q X B →ₗ[ℤ] E (p + q) X (A ∪ B)

namespace PairCohomologyTheory

/-- The Chapter 19 relative-cohomology groups of a pair cohomology theory, evaluated on the
explicit pair `(X, A)`. -/
abbrev relativeCohomology {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) :
    ℤ → (X : TopCat.{u}) → Set X → Type u :=
  fun q X A ↦ (H.cohomology q).obj (Opposite.op (subsetPair X A))

/-- The canonical map `H^q(X, A) → H^q(X)` induced by `absoluteToRelative (subsetPair X A)` and
the contravariance of `H.cohomology q`. -/
abbrev relativeToAbsolute {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : TopCat.{u}) (A : Set X) (q : ℤ) :
    H.relativeCohomology q X A →ₗ[ℤ] (H.absoluteCohomology q).obj (Opposite.op X) :=
  ((H.cohomology q).map (absoluteToRelative (subsetPair X A)).op).hom.toIntLinearMap

/-- The tensor product of the canonical maps `H^p(X, A) → H^p(X)` and `H^q(X, B) → H^q(X)`. -/
abbrev relativeToAbsoluteTensor {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : TopCat.{u}) (A B : Set X) (p q : ℤ) :
    H.relativeCohomology p X A ⊗[ℤ] H.relativeCohomology q X B →ₗ[ℤ]
      (H.absoluteCohomology p).obj (Opposite.op X) ⊗[ℤ]
        (H.absoluteCohomology q).obj (Opposite.op X) :=
  TensorProduct.map (H.relativeToAbsolute X A p) (H.relativeToAbsolute X B q)

/-- The family of relative cup-product maps attached to a Chapter 18 pair cohomology theory. -/
abbrev RelativeCupProductMap {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) :=
  _root_.RelativeCupProductMap H.relativeCohomology

end PairCohomologyTheory

namespace AbsoluteCupProduct

/-- Compatibility of a relative cup-product family on `H` with the chosen absolute cup product
after forgetting from relative to absolute cohomology by the canonical maps
`H^*(X, A; R) → H^*(X; R)`. -/
def IsCompatibleWithRelativeCup {R : Type u} [CommRing R] {H : PairCohomologyTheory R}
    (absoluteCup : AbsoluteCupProduct H)
    (cup : PairCohomologyTheory.RelativeCupProductMap H) : Prop :=
  ∀ {X : TopCat.{u}} (A B : Set X) (p q : ℤ),
    (absoluteCup.cup X p q).comp (H.relativeToAbsoluteTensor X A B p q) =
      (H.relativeToAbsolute X (A ∪ B) (p + q)).comp (cup A B p q)

end AbsoluteCupProduct

namespace AbsoluteCupProduct

/-- Problem 19.6.2. Compatibility with the absolute cup product means that after applying the
canonical maps `H^*(X, A; R) → H^*(X; R)` and `H^*(X, B; R) → H^*(X; R)`, the relative cup
product agrees with the absolute cup product in `H^(p + q)(X; R)`. -/
theorem relativeCupProduct_compatible {R : Type u} [CommRing R] {H : PairCohomologyTheory R}
    (absoluteCup : AbsoluteCupProduct H)
    (cup : PairCohomologyTheory.RelativeCupProductMap H)
    (hcompat : absoluteCup.IsCompatibleWithRelativeCup cup)
    {X : TopCat.{u}} (A B : Set X) (p q : ℤ) :
    (absoluteCup.cup X p q).comp (H.relativeToAbsoluteTensor X A B p q) =
      (H.relativeToAbsolute X (A ∪ B) (p + q)).comp
        (cup A B p q) :=
  hcompat A B p q

end AbsoluteCupProduct

end
