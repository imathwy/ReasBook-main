import Mathlib
import stacks_project.Chap15.Lemma_15_60_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "CpxB" => CochainComplex (ModuleCat B) ℤ
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat B)
local notation "QA" => (DerivedCategory.Q : CpxA ⥤ DModA)
local notation "QB" => (DerivedCategory.Q : CpxB ⥤ DModB)
local notation "Res" =>
  (Functor.mapHomologicalComplex (ModuleCat.restrictScalars (algebraMap A B)) (up ℤ) :
    CpxB ⥤ CpxA)

/- Domain-style sampling for Lemma 15.103.5:
- primary domain: derived base change along `A → B` for cochain complexes of modules, together
  with compatible subcomplex inclusions and the induced maps on cohomology;
- sampled owner declarations:
  `CochainComplex`,
  `derivedTensorWithAlgebraAdjunction`,
  `DerivedCategory.Q`,
  `Functor.mapDerivedCategoryFactors`,
  `Subobject.factorThru`;
- best owner abstraction: the canonical owner of the comparison
  `M^• ⊗_A^{\mathbf L} B ⟶ N^•` attached to a complex map
  `a : M ⟶ ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj N`
  is the adjunction
  `derivedTensorWithAlgebraAdjunction`, together with the standard `Q`/restriction comparison
  isomorphism `Functor.mapDerivedCategoryFactors`, here specialized to the restriction functor
  on cochain complexes;
- primitive vs. derived:
  primitive data are the complex map `a`, the subobjects `M'`, `N'`, and the factorization witness
  expressing that `a` carries `M'` into `N'` after restricting scalars;
  the induced maps on derived base change and on cohomology are derived API and should not be
  stored as primitive wrapper fields;
- source/core/bridge triage:
  `source-facing`: the enlargement theorem for actual subcomplexes `M₁ ⊆ M₂ ⊆ M` and
    `N₁ ⊆ N₂ ⊆ N`;
  `core/canonical`: `derivedTensorWithAlgebraAdjunction`, `DerivedCategory.Q`,
  `Functor.mapDerivedCategoryFactors`, and `Subobject.factorThru`;
  `bridge/view`: the canonical comparison maps below, obtained by transposing the corresponding
    complex maps under the derived extension/restriction adjunction, together with the standard
    cardinality owner `CochainComplex.termCardinal` for the size bounds in the source statement.
-/

namespace CochainComplex

/-- The total cardinality of the terms of a cochain complex of modules. -/
def termCardinal {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat R) ℤ) : Cardinal :=
  Cardinal.mk (Σ i : ℤ, (K.X i : Type _))

end CochainComplex

/-- The canonical derived base-change morphism attached to a complex map
`f : M ⟶ Res.obj N`. -/
noncomputable def derivedTensorWithAlgebraComparison {M : CpxA} {N : CpxB}
    (f : M ⟶ (Res).obj N) :
    (((QA).obj M) ⊗[A]^L[B]) ⟶ (QB).obj N :=
  (derivedTensorWithAlgebraAdjunction.homEquiv _ _).symm
    ((QA).map f ≫
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.inv.app N)

/-- Given compatible subcomplexes `M' ⊆ M` and `N' ⊆ N`, the map `a : M ⟶ Res N` restricts to a
map `M' ⟶ Res N'`. -/
private def restrictToSubcomplexes {M : CpxA} {N : CpxB}
    (M' : Subobject M) (N' : Subobject N)
    (a : M ⟶ (Res).obj N)
    (h : (Subobject.mk ((Res).map N'.arrow)).Factors (M'.arrow ≫ a)) :
    (M' : CpxA) ⟶ (Res).obj (N' : CpxB) :=
  (Subobject.mk ((Res).map N'.arrow)).factorThru (M'.arrow ≫ a) h ≫
    (Subobject.underlyingIso ((Res).map N'.arrow)).hom

/-- The induced homology map on the derived base-change comparison for compatible subcomplexes. -/
noncomputable def derivedTensorWithAlgebraSubcomplexHomologyMap {M : CpxA} {N : CpxB}
    (M' : Subobject M) (N' : Subobject N)
    (a : M ⟶ (Res).obj N)
    (h : (Subobject.mk ((Res).map N'.arrow)).Factors (M'.arrow ≫ a))
    (i : ℤ) :
    (H i).obj (((QA).obj (M' : CpxA)) ⊗[A]^L[B]) ⟶ (H i).obj ((QB).obj (N' : CpxB)) :=
  (H i).map (derivedTensorWithAlgebraComparison (restrictToSubcomplexes M' N' a h))

-- Proof sketch: choose a cardinal bounding the sizes of `A`, `B`, and a free `A`-resolution of
-- `B`; then enlarge the initial subcomplexes by adjoining small stable subcomplexes that kill the
-- relevant kernel classes and realize the relevant image classes after derived base change.
/-- Lemma 15.103.5: for a ring map `A → B`, there exists a cardinal `κ` such that whenever
`a : M^• ⟶ N^•` induces an isomorphism
`M^• \otimes_A^{\mathbf L} B \to N^•` in `D(B)`, every compatible pair of subcomplexes
`M₁^• ⊆ M^•` and `N₁^• ⊆ N^•` admits enlargements `M₂^•` and `N₂^•` through which the kernel and
image conditions on cohomology hold in every degree, with total cardinality bounded by
`max(κ, |M₁^•|, |N₁^•|)`. -/
theorem exists_cardinal_for_derivedTensor_subcomplex_approximation :
    ∃ κ : Cardinal,
        ∀ ⦃M : CpxA⦄ ⦃N : CpxB⦄
        (a : M ⟶ (Res).obj N)
        (haIso : IsIso (derivedTensorWithAlgebraComparison a))
        (M₁ : Subobject M) (N₁ : Subobject N)
        (h₁ : (Subobject.mk ((Res).map N₁.arrow)).Factors (M₁.arrow ≫ a)),
        ∃ (M₂ : Subobject M) (N₂ : Subobject N)
          (hM : M₁ ≤ M₂) (hN : N₁ ≤ N₂)
          (h₂ : (Subobject.mk ((Res).map N₂.arrow)).Factors (M₂.arrow ≫ a)),
          (∀ i : ℤ,
              (kernelSubobject (derivedTensorWithAlgebraSubcomplexHomologyMap M₁ N₁ a h₁ i)).arrow ≫
                (H i).map
                    ((derivedTensorWithAlgebra (algebraMap A B)).map
                      ((QA).map (Subobject.ofLE M₁ M₂ hM))) = 0) ∧
          (∀ i : ℤ,
              imageSubobject ((H i).map ((QB).map (Subobject.ofLE N₁ N₂ hN))) ≤
                imageSubobject (derivedTensorWithAlgebraSubcomplexHomologyMap M₂ N₂ a h₂ i)) ∧
          max ((M₂ : CpxA).termCardinal)
              ((N₂ : CpxB).termCardinal) ≤
            max κ
              (max ((M₁ : CpxA).termCardinal)
                ((N₁ : CpxB).termCardinal)) := sorry

end

end CategoryTheory
