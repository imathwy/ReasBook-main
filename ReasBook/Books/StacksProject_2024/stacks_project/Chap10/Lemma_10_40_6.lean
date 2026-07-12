import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PrimeSpectrum
open TensorProduct.AlgebraTensorModule Module.FaithfullyFlat

universe u v w

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

/-
Domain triage: this item lies in the commutative-algebra support/base-change domain.
- sampled canonical declarations: `Module.support`, `Module.support_subset_preimage_comap`,
  `Module.mem_support_iff_nontrivial_residueField_tensorProduct`, and
  `AlgebraTensorModule.cancelBaseChange`;
- layer: `source-facing`, since the theorem identifies the support of the base-changed finite
  module inside the owner API `Module.support`.

Primitive data are only the algebra map `R → R'` and the finite `R`-module `M`. The forward
support equality itself is not yet present upstream, so the file keeps the minimal local bridge
that compares residue-field fibers after passing from `p = q.comap` to `q`.
-/

/-- Lemma 10.40.6 (Tag `0BUR`): let `R → R'` be a ring map and let `M` be a finite `R`-module.
Then the support of the canonical base change `R' ⊗[R] M` is the inverse image of
`support R M` along the induced map `Spec R' → Spec R`. -/
@[stacks 0BUR]
theorem Lemma_10_40_6 :
    support R' (R' ⊗[R] M) = comap (algebraMap R R') ⁻¹' support R M := by
  ext q
  change q ∈ support R' (R' ⊗[R] M) ↔ comap (algebraMap R R') q ∈ support R M
  let p : PrimeSpectrum R := comap (algebraMap R R') q
  let K := p.asIdeal.ResidueField
  let L := q.asIdeal.ResidueField
  let e : L ⊗[R'] (R' ⊗[R] M) ≃ₗ[L] L ⊗[K] (K ⊗[R] M) :=
    (cancelBaseChange R R' L L M).trans (cancelBaseChange R K L L M).symm
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  rw [mem_support_iff_nontrivial_residueField_tensorProduct,
    mem_support_iff_nontrivial_residueField_tensorProduct]
  simpa [p] using e.nontrivial_congr.trans (nontrivial_tensorProduct_iff_right K L)

end Module

end
