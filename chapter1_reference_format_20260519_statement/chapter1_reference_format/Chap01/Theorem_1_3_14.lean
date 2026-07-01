import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Function Polynomial

universe u

section

open Ideal

variable {R : Type*} [CommRing R] {ι : Type u} [Fintype ι]
variable (f : ι → R[X]) (hf : Pairwise (IsCoprime on f))

/- Theorem 1.3.14 (1): at the source-facing polynomial-quotient layer, the canonical owner is
`AdjoinRoot`, while the core ring-theoretic content is the chapter's `Ideal.quotientInfRingEquivPiQuotient`
specialized to the principal ideals `(f i)`. Since `AdjoinRoot f = R[X] / (f)`, the result is
expressed directly on `AdjoinRoot`. The textbook's `𝔽_p[X]` presentation is a downstream
specialization; the ring-theoretic statement is canonical over an arbitrary commutative
coefficient ring. -/
#check
  (show AdjoinRoot (∏ i, f i) ≃+* Π i, AdjoinRoot (f i) from
    (quotEquivOfEq ((iInf_span_singleton (fun _ _ hij ↦ hf hij)).symm)).trans
      (quotientInfRingEquivPiQuotient
        (fun i ↦ span {f i})
        (fun _ _ hij ↦ (isCoprime_span_singleton_iff _ _).mpr (hf hij))))

/- Theorem 1.3.14 (2): the corresponding multiplicative-group equivalence is derived canonically
from the ring equivalence above via `Units.mapEquiv`, followed by the standard product-units
equivalence `MulEquiv.piUnits`. -/
#check
  (let e :
      AdjoinRoot (∏ i, f i) ≃+* Π i, AdjoinRoot (f i) :=
        (show AdjoinRoot (∏ i, f i) ≃+* Π i, AdjoinRoot (f i) from
          (quotEquivOfEq ((iInf_span_singleton (fun _ _ hij ↦ hf hij)).symm)).trans
            (quotientInfRingEquivPiQuotient
              (fun i ↦ span {f i})
              (fun _ _ hij ↦ (isCoprime_span_singleton_iff _ _).mpr (hf hij))));
    (((Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits) :
      (AdjoinRoot (∏ i, f i))ˣ ≃* Π i, (AdjoinRoot (f i))ˣ))

end
