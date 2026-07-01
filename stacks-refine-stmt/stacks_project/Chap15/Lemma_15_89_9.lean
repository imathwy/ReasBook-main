import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import stacks_project.Chap10.Lemma_10_96_3
import stacks_project.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {R' : Type w} [CommRing R'] [Algebra R R']
variable (I : Ideal R)

/- Domain-style sampling for the tensor base-change statement:
- primary domain: commutative algebra of ideal-power torsion modules under scalar extension and
  tensor products;
- sampled owners: `Module.IsIdealPowerTorsion`, `Ideal.quotientMap`, `TensorProduct.mk`;
- best owner abstraction: the canonical tensor-base-change unit `TensorProduct.mk R R' M 1 :
  M →ₗ[R] R' ⊗[R] M`; the symmetric map `M → M ⊗[R] R'` is only its tensor-symmetry view;
- primitive data: the ideal `I`, the algebra map `R → R'`, the module `M`, the torsion
  hypothesis, and the quotient-map bijectivity family;
- derived API: bijectivity of the base-change unit on `I`-power torsion modules.

Layer triage:
- `source-facing`: the tensor-base-change bijectivity statement below;
- `core/canonical`: `Ideal.quotientMap` and `TensorProduct.mk`;
- `bridge/view`: the tensor-symmetry reinterpretation `M → M ⊗[R] R'`.
-/

variable {M : Type v} [AddCommMonoid M] [Module R M]

-- Proof sketch: if `I ^ n` annihilates `M`, then `M` is naturally an `R ⧸ I ^ n`-module, so
-- base change along `R → R'` factors through `R ⧸ I ^ n → R' ⧸ I ^ n R'`, which is bijective by
-- hypothesis. For a general `I`-power torsion module, write `M` as the directed union of its
-- `I ^ n`-annihilated submodules and use that tensor products commute with direct limits.
/-- Lemma 15.89.9: if the canonical maps `R ⧸ I^n → R' ⧸ I^n R'` are isomorphisms for all positive
`n`, then for every `I`-power torsion `R`-module `M` the canonical base-change unit
`M → R' ⊗[R] M` is bijective. -/
theorem tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective (TensorProduct.mk R R' M 1) := sorry

end

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Domain-style sampling for the adic-completion quotient statement:
- primary domain: `I`-adic completion and quotient comparison for commutative rings;
- sampled owners: `Ideal.quotientMap`, `AdicCompletion.evalₐ`,
  `completionIdeal_pow_eq_ker_evalₐ`;
- best owner abstraction: the canonical completion-side map is
  `AdicCompletion.evalₐ I n : AdicCompletion I R →ₐ[R] R ⧸ I ^ n`; the quotient comparison below is
  its source-facing `Ideal.quotientMap` presentation, with the Chapter 10 bridge
  `completionIdeal_pow_eq_ker_evalₐ` identifying the kernel with the extended ideal
  `((I ^ n).map (algebraMap R (AdicCompletion I R)))`;
- primitive data: the ideal `I`, the ring `R`, the finite-generation hypothesis on `I`, and the
  exponent `n`, together with an `I`-power torsion `R`-module when specializing the tensor
  base-change theorem to completion;
- derived API: bijectivity of the induced quotient map to the completion quotient, and the
  completion-specialized tensor base-change statement for `I`-power torsion modules.

Layer triage:
- `source-facing`: the completion-specialized tensor base-change statement below;
- `core/canonical`: `AdicCompletion.evalₐ` and `completionIdeal_pow_eq_ker_evalₐ`;
- `bridge/view`: the quotient-comparison statement below, and its principal-ideal specialization
  `principalAdicCompletion_quotientMap_bijective` in Lemma `15.91.1`.
-/

-- Proof sketch: `AdicCompletion.evalₐ I n` is surjective, and
-- `completionIdeal_pow_eq_ker_evalₐ` identifies its kernel with the extended ideal
-- `(I^n) (AdicCompletion I R)`. The displayed `Ideal.quotientMap` is therefore the quotient-side
-- presentation of `evalₐ`.
/-- If `I` is finitely generated, then for every `n : ℕ` the canonical quotient map
`R ⧸ I^n → AdicCompletion I R ⧸ I^n AdicCompletion I R` is bijective. -/
theorem adicCompletion_quotientMap_bijective
    (hI : I.FG) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        ((I ^ n).map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R))
        Ideal.le_comap_map) := sorry

-- Proof sketch: specialize the general tensor base-change bijectivity theorem to the algebra
-- map `R → AdicCompletion I R`, and supply its quotient-map hypothesis via
-- `adicCompletion_quotientMap_bijective`.
/-- Lemma 15.89.9: if `I` is finitely generated, then for every `I`-power torsion `R`-module `M`
the canonical base-change unit `M → AdicCompletion I R ⊗[R] M` is bijective. This is the direct
completion specialization of the main base-change statement. -/
theorem tensorAdicCompletion_bijective_of_isIdealPowerTorsion
    (hI : I.FG) (hM : Module.IsIdealPowerTorsion I M) :
    Function.Bijective (TensorProduct.mk R (AdicCompletion I R) M 1) := by
  let hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R))
        Ideal.le_comap_map) :=
    fun n ↦ adicCompletion_quotientMap_bijective I hI n
  exact tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective I hM hquot

end
