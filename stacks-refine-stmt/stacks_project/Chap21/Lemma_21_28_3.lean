import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]

/-- The bounded-below condition on an object of a derived category. -/
def DerivedCategoryIsBoundedBelow (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n →
    IsZero ((DerivedCategory.homologyFunctor A i).obj K)

/-- The degree-zero derived object attached to the `q`-th cohomology object of `K`. -/
abbrev cohomologyObjectAsDerived (K : DerivedCategory A) (q : ℤ) :
    DerivedCategory A :=
  (DerivedCategory.singleFunctor A (0 : ℤ)).obj
    ((DerivedCategory.homologyFunctor A q).obj K)

variable (F : DerivedCategory B ⥤ DerivedCategory A)
variable (G : DerivedCategory A ⥤ DerivedCategory B)
variable (adj : F ⊣ G)

-- Proof sketch: let `D'` be the triangulated subcategory from Lemma `21.28.2` cut out by the
-- counit-isomorphism condition. The hypothesis says that each cohomology object `H^q(K)[0]`
-- lies in this subcategory. Using bounded-belowness, rebuild bounded truncations of `K` from
-- these cohomology objects through the standard distinguished triangles; closure under shifts
-- and triangles then implies every truncation, and hence `K` itself, lies in the same
-- subcategory.
/-- Lemma 21.28.3: if `K ∈ D(\mathcal O_{\mathcal C})` is bounded below and every degree-zero
derived object attached to a cohomology sheaf `H^q(K)` satisfies the counit isomorphism
condition for an adjunction `F ⊣ G` on derived categories, then `K` itself satisfies that
condition. Applied to `F = Lf^*` and `G = Rf_*`, this is the canonical derived-category form of
the Stacks statement that, for a flat morphism of ringed topoi, if every
`f^* Rf_* H^q(K) ⟶ H^q(K)` is an isomorphism, then so is `Lf^* Rf_* K ⟶ K`. -/
theorem counit_isIso_of_boundedBelow_of_cohomology
    (K : DerivedCategory A)
    (hK : DerivedCategoryIsBoundedBelow K)
    (hH : ∀ q : ℤ, IsIso (adj.counit.app (cohomologyObjectAsDerived K q))) :
    IsIso (adj.counit.app K) := sorry

end

end CategoryTheory
