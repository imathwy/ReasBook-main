import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.123.3: for an `R`-algebra `S`, if `φ : R[X] →ₐ[R] S`, `t : S` is integral over
`R[X]`, and `φ p * t` lies in the image of `φ`, then after multiplying `t` by a power of
`p.leadingCoeff`, one can subtract `φ q` for some `q : R[X]` and obtain an element integral over
`R`. This is exactly the canonical mathlib theorem
`exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range`. -/
recall exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
