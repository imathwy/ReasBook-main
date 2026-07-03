import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.147.4: if `R → S` is smooth, `A = integralClosure R B`, and
`A' = integralClosure S (S ⊗[R] B)`, then the canonical map
`S ⊗[R] A → A'` is bijective, hence an isomorphism. This is exactly the canonical theorem
`TensorProduct.toIntegralClosure_bijective_of_smooth`. -/
recall TensorProduct.toIntegralClosure_bijective_of_smooth
