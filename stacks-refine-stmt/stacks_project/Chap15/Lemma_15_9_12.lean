import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Kaehler.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]
variable {m : ℕ}

local notation "C" => SymmetricAlgebra A M

variable (q : (Fin m →₀ A) →ₗ[A] M)

/- Domain-style sampling:
- primary domain: symmetric-algebra presentations, tensor base change, and the conormal/Kähler
  exact sequence;
- sampled owner declarations:
  `LinearMap.lTensor`,
  `LinearMap.lTensor_surjective`,
  `lTensor_exact`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`;
- best owner abstraction: the canonical tensorized presentation maps attached to the kernel
  inclusion `i : q.ker →ₗ[A] Fin m →₀ A`, namely `i.lTensor C` and `q.lTensor C`, with the
  right-exactness of tensor product as the owner for the tensor sequence; the Kähler map is the
  source-facing specialization obtained by composing `q.lTensor C`,
  `(SymmetricAlgebra.ι A M).lTensor C`, and `Derivation.tensorProductTo` for the universal
  derivation on `C`;
- primitive data: the surjective module map `q` and the kernel inclusion
  `i : q.ker →ₗ[A] Fin m →₀ A`;
- derived API: the source-facing description of that canonical Kähler map on the standard basis of
  `Fin m →₀ A`.

Layer triage:
- `source-facing`: the conormal/Kähler exact sequence attached to the presentation `q`;
- `core/canonical`: the tensorized presentation maps `i.baseChange C` and `q.baseChange C`,
  together with the generic right-exactness owners `lTensor_exact` and
  `LinearMap.lTensor_surjective`;
- `bridge/view`: the identification of `C ⊗[A] A^{⊕ m}` with `⨁_{j=1}^m C \, dy_j`. -/

-- Proof sketch: identify the polynomial presentation `A[y₁, \ldots, y_m] → Sym_A(M)` determined
-- by `q` with the standard free presentation on the images of the basis vectors. The degree-`1`
-- term of the conormal sequence is `C ⊗_A ker(q)` by Lemma `10.13.2`, the degree-`0` term is the
-- free `C`-module on the `dy_j`, and the conormal sequence for Kähler differentials gives the
-- exactness and surjectivity.
/-- Lemma 15.9.12: if `q : A^{⊕ m} → M` is surjective and `C = Sym_A(M)`, then the polynomial
presentation of `C` induced by `q` has naive cotangent differential
`C ⊗_A ker(q) → C ⊗_A A^{⊕ m}`, and after the canonical identification
`C ⊗_A A^{⊕ m} ≃ \bigoplus_j C \, dy_j` the resulting sequence
`C ⊗_A ker(q) → \bigoplus_j C \, dy_j → Ω_{C/A} → 0`
is exact. This is the textbook complex `NL(α) = (K ⊗_A C → \bigoplus_j C \, dy_j)` written in the
equivalent library-facing tensor order `C ⊗_A K`. -/
theorem symmetricAlgebra_presentation_conormal_sequence
    (hq : Function.Surjective q) :
    let i : q.ker →ₗ[A] (Fin m →₀ A) := q.ker.subtype
    let toKaehler :
        C ⊗[A] (Fin m →₀ A) →ₗ[C] Ω[C⁄A] :=
      (KaehlerDifferential.D A C).tensorProductTo ∘ₗ
        (SymmetricAlgebra.ι A M).baseChange C ∘ₗ
        q.baseChange C
    Function.Exact (i.baseChange C) toKaehler ∧
      Function.Surjective toKaehler :=
  sorry

end
