import StacksProject_2024.Chap12.Lemma_12_26_1
import StacksProject_2024.Chap12.Lemma_12_26_2

open CategoryTheory Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v u
open scoped HomologicalComplex₂

/-
Domain-style sampling for Lemma 15.104.1 in the product-total domain:
- primary domain: product total complexes of cochain complexes of cochain complexes in an abelian
  category with countable products;
- sampled owner declarations:
  * `coaugmentedColumnBicomplex` from `Chap12.Lemma_12_26_1` for the canonical bridge from a
    cochain sequence to its associated bicomplex;
  * `HomologicalComplex₂.productTotal` from `Chap12.Lemma_12_26_2` as the shared owner for
    product total complexes of cohomological bicomplexes;
  * `HomologicalComplex.homology` as the canonical owner of the degreewise cohomology objects of a
    cochain complex in an abelian category.
- source/core/bridge triage:
  * `source-facing`: the acyclicity statement for the product total of the associated bicomplex;
  * `core/canonical`: `HomologicalComplex₂.productTotal` on the reindexed bicomplex;
  * `bridge/view`: the exported row-to-bicomplex bridge `coaugmentedColumnBicomplex A`.

Primitive data are only the cochain sequence `A`; the product total complex is derived owner API
from the Chapter 12 bicomplex abstraction. This file therefore reuses the canonical upstream
row-to-bicomplex bridge and the Chapter 12 product-total owner directly.
-/

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]

local notation "CochainComplexSequence" => CochainComplex (CochainComplex 𝒜 ℤ) ℕ

-- Proof sketch: view `A` as the bicomplex with horizontal degree `p` and vertical degree `q`,
-- so that the antidiagonal of total degree `0` is `A_p^{-p}`. A cocycle in degree `0` of the
-- product total is a family `(x_p)` with `x_p ∈ A_p^{-p}` whose total differential vanishes.
-- Using `H^{-p}(A_p^•) = 0`, recursively choose primitives in degrees `-p-1` that kill the
-- antidiagonal components one column at a time; these assemble to a degree `-1` element whose
-- total differential is the original cocycle.
-- Route correction: the textbook argument is valid for abelian groups because countable products
-- are exact there. In the present generalized statement over an arbitrary abelian category with
-- countable products, taking all horizontal differentials to be zero and each column to be a
-- two-term complex `B_p ⟶ C_p` with epi differential would identify `H^0` of the product total
-- with the cokernel of `∏ B_p ⟶ ∏ C_p`. Hence the statement would force countable products of
-- epimorphisms to be epimorphisms, which is false in general abelian categories with products.
/-- Lemma 15.104.1: if `A₀^• ⟶ A₁^• ⟶ A₂^• ⟶ ⋯` is a cochain complex of cochain complexes in an
abelian category with countable products and `H^{-p}(A_p^•) = 0` for every `p ≥ 0`, then the
degree-`0` cohomology of the associated product total complex
`Tot_π(coaugmentedColumnBicomplex A)` is zero.
-/
theorem isZero_homology_zero_productTotal_of_isZero_diagonal_homology
    (A : CochainComplexSequence)
    (hA : ∀ p : ℕ, IsZero ((A.X p).homology (-(p : ℤ)))) :
    IsZero ((Tot_π(coaugmentedColumnBicomplex A)).homology 0) := sorry

end
