import Mathlib
import StacksProject_2024.Chap15.Lemma_15_91_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {R' : Type w} [CommRing R'] [Algebra R R']
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (f : R)

/-
Domain-style sampling:
- primary domain: commutative algebra of tensor base change along completion/localization, together
  with the canonical tensor-product/product comparison;
- sampled owner declarations:
  `principalPowerIdealImageQuotientMap`,
  `principalAdicCompletion_quotientMap_bijective`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `TensorProduct.prodRight`;
- best owner abstraction: the source-facing statement is nontriviality after base change to the
  product ring `R' × R_f`; its core support comes from the canonical quotient-map owner
  `principalPowerIdealImageQuotientMap` on the powers of `(f)`, the ideal-power-torsion
  base-change theorem from Lemma `15.89.9`, the principal completion specialization
  `principalAdicCompletion_quotientMap_bijective`, and the product tensor equivalence
  `TensorProduct.prodRight`;
- primitive data: the algebra map `R → R'`, the element `f`, the `R`-module `M`, and the
  quotient-map bijectivity hypothesis for `(f)^n`;
- derived API: the completion specialization and the decomposition of the tensor product with a
  product algebra into the corresponding product of tensor products;
- triage: the first theorem is `source-facing`, the completion specialization is a `bridge/view`,
  and the tensor-product/product equivalence is the `core/canonical` owner abstraction.
-/

-- Proof sketch: if `M ⊗[R] Localization.Away f` were trivial, then every element of `M` would be
-- killed by a power of `f`. Lemma `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`
-- then identifies `M ⊗[R] R'` with `M`, so the `R'`-summand stays nontrivial. Finally, tensoring
-- with the finite direct sum `R' ⊕ R_f` decomposes into the corresponding product of tensor
-- products.
/-- Lemma 15.91.2: if the canonical maps `R / (f)^n → R' / (f)^n R'` are bijective for every
positive integer `n`, then tensoring any nontrivial `R`-module with `R' × R_f` remains
nontrivial. -/
theorem tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective
    [Nontrivial M]
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Nontrivial (M ⊗[R] (R' × Localization.Away f)) := sorry

-- Proof sketch: apply
-- `tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, and use
-- `principalAdicCompletion_quotientMap_bijective` to verify the quotient-map hypothesis in the
-- principal-image form used above.
/-- The `(f)`-adic completion and the localization away from `f` jointly detect nontrivial
`R`-modules. -/
theorem tensorProduct_completion_prod_localizationAway_nontrivial
    [Nontrivial M] :
    Nontrivial
      (M ⊗[R] (principalAdicCompletion f × Localization.Away f)) := sorry

end
