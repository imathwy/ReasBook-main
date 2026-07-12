import StacksProject_2024.Chap12.Lemma_12_26_1
import StacksProject_2024.Chap12.Lemma_12_26_2

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]

local notation "CochainComplexSequence" => CochainComplex (CochainComplex 𝒜 ℤ) ℕ

/-
Domain-style sampling for Lemma 15.104.2:
- primary domain: functoriality of product total complexes for cochain complexes of cochain
  complexes in an abelian category with countable products;
- sampled owner declarations:
  * `coaugmentedColumnBicomplex` from `Chap12.Lemma_12_26_1` for the source-facing owner that
    turns a cochain sequence into the associated bicomplex;
  * `HomologicalComplex₂.productTotal` and `HomologicalComplex₂.productTotalFunctor` from
    `Chap12.Lemma_12_26_2` as the shared owner of the product total and its functoriality;
  * `CochainComplex.mappingCone` as the canonical owner of the mapping cone used in the proof
    sketch.
- source/core/bridge triage:
  * `source-facing`: the columnwise quasi-isomorphism criterion for the induced map on the
    product totals of the associated bicomplexes;
  * `core/canonical`: the product total owner `Tot_π(coaugmentedColumnBicomplex A)`;
  * `bridge/view`: functoriality of the reindexing functor
    `(ComplexShape.embeddingUpNat).extendFunctor (CochainComplex 𝒜 ℤ)` followed by the canonical
    owner `productTotalFunctor`.

Primitive data are only the morphism `f : A ⟶ B`. The induced map on product totals is derived
owner API from the Chapter 12 owner `coaugmentedColumnBicomplex` together with
`productTotalFunctor`. The public statement should therefore use that induced map directly rather
than exporting a parallel local helper name for it.
-/

-- Proof sketch: form the double complex of mapping cones of the column maps `A_p^• ⟶ B_p^•`; its
-- product total complex is the mapping cone of the induced map on product totals, and the
-- product-total acyclicity
-- argument from the preceding item applies
-- because each column cone is acyclic when `f.f p` is a quasi-isomorphism.
/-- Lemma 15.104.2: if a morphism of cochain complexes of cochain complexes in an abelian category
with countable products is a quasi-isomorphism in every column, then the induced
map
`Tot_π(coaugmentedColumnBicomplex A) ⟶ Tot_π(coaugmentedColumnBicomplex B)`
on the product total complexes is a quasi-isomorphism. -/
theorem productTotal_map_quasiIso_of_columnwise
    {A B : CochainComplexSequence} (f : A ⟶ B)
    (hf : ∀ p : ℕ, QuasiIso (f.f p)) :
    QuasiIso
      (productTotalFunctor.map ((embeddingUpNat.extendFunctor (CochainComplex 𝒜 ℤ)).map f)) := by
  sorry

end
