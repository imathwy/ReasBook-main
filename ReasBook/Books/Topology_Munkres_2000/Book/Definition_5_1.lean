module

import Mathlib.Data.Set.Image

/- Definition 5.1: An indexed family of sets is represented by a function
`A : J → Set X`, with `A α` denoting the set `A_α`. Its collection of values is
`Set.range A`, and `Set.rangeFactorization A` is the canonical surjective
indexing function onto that collection. Munkres's requirement that the
collection be nonempty is `(Set.range A).Nonempty`, equivalently `Nonempty J`. -/
#check Set.range
#check Set.rangeFactorization
#check Set.rangeFactorization_surjective
#check Set.coe_comp_rangeFactorization
#check Set.range_nonempty_iff_nonempty
