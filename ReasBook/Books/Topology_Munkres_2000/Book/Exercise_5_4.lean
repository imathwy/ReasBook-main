module

public import Topology_Munkres_2000.Book.Exercise_5_4.Power

public section

universe u v

open scoped Book

/- Exercise 5.4 (1): If `m ≤ n`, extension by a fixed coordinate gives an
embedding `X^m ↪ X^n`. -/
#check fun {X : Type u} (x : X) {m n : ℕ+} (h : m ≤ n) ↦
  Power.tupleEmbedding x h

/- Exercise 5.4 (2): Concatenation gives a bijection
`X^m × X^n ≃ X^(m + n)`. -/
#check fun {X : Type u} (m n : ℕ+) ↦
  (Power.tupleAppendEquiv m n : (X ^ m × X ^ n) ≃ X ^ (m + n))

/- Exercise 5.4 (3): Adjoining a fixed constant tail gives an embedding
`X^n ↪ X^ω`. -/
#check fun {X : Type u} (x : X) (n : ℕ+) ↦
  Power.tupleSequenceEmbedding x n

/- Exercise 5.4 (4): A finite power times a positive-integer-indexed power is
equivalent to one positive-integer-indexed power. -/
#check fun {X : Type u} (n : ℕ+) ↦
  (Power.tupleProdSequenceEquiv n : (X ^ n × X ^ω) ≃ X ^ω)

/- Exercise 5.4 (5): Two positive-integer-indexed powers can be interleaved to
give one positive-integer-indexed power. -/
#check fun (X : Type u) ↦
  (Power.sequenceProdEquiv : (X ^ω × X ^ω) ≃ X ^ω)

/- Exercise 5.4 (6): If `A ⊆ B`, extension by a fixed coordinate gives an
embedding `X^A ↪ X^B`. -/
#check fun {X : Type u} {ι : Type v} (x : X) {A B : Set ι} (h : A ⊆ B) ↦
  Power.subsetEmbedding x h
