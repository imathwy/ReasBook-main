import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Lemma 1.1.101 (1): in a commutative ring, the product of two coprime ideals equals their
intersection. This is the canonical ideal-theoretic owner theorem
`Ideal.mul_eq_inf_of_isCoprime`. -/
recall Ideal.mul_eq_inf_of_isCoprime {R : Type u} [CommSemiring R] {I J : Ideal R}
    (coprime : IsCoprime I J) : I * J = I ⊓ J

/- Lemma 1.1.101 (2): if `I` and `J` are both coprime to `N`, then the product ideal `I * J` is
also coprime to `N`. The source-facing ideal statement is the specialization of the canonical
multiplicativity theorem `IsCoprime.mul_left` to ideals. -/
theorem isCoprime_mul_left {R : Type u} [CommSemiring R] {I J N : Ideal R}
    (hI : IsCoprime I N) (hJ : IsCoprime J N) : IsCoprime (I * J) N :=
  IsCoprime.mul_left hI hJ
