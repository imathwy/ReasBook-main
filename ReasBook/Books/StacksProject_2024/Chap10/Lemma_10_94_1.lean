import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_84_1
import StacksProject_2024.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: base change for module-theoretic properties over commutative rings;
- sampled owner declarations of the same kind:
  `Module.Flat.baseChange`,
  `Projective.tensorProduct`,
  `Module.CountablyGenerated`,
  `Module.IsDirectSumOfCountablyGenerated`,
  `Module.MittagLeffler`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective`;
- best owner abstraction: the chapter owners above, together with the existing mathlib typeclass
  owners `Module.Flat` and `Module.Projective`;
- primitive data: the ring map `R → S` and the `R`-module `M`;
- derived API: canonical recalls for flatness and projectivity under base change, together with the
  genuinely new base-change lemmas for `MittagLeffler` and
  `IsDirectSumOfCountablyGenerated`.

Layering:
- this numbered item is `bridge/view`: it records closure of the existing owner properties under
  base change, and does not define new owners.
-/

section

variable [Flat R M]

/- Lemma 10.94.1 (1): if `M` is flat over `R`, then its base change `S ⊗[R] M` is flat over `S`.
This is exactly the canonical owner instance `Module.Flat.baseChange` for the standard mathlib
model of the textbook module `M ⊗_R S`. -/
recall Module.Flat.baseChange

end

-- Proof sketch: use the tensor-product injectivity characterization of Mittag-Leffler modules from
-- Proposition `10.89.5`; after base change, commute tensor products with products and tensoring
-- over `S` to transfer injectivity to `S ⊗[R] M`.
/-- Lemma 10.94.1 (2): if `M` is Mittag-Leffler over `R`, then its base change `S ⊗[R] M` is
Mittag-Leffler over `S`. This is the canonical Lean form of the textbook statement for
`M ⊗_R S`. -/
theorem mittagLeffler_tensorProduct (hM : MittagLeffler R M) :
    MittagLeffler S (S ⊗[R] M) := by
  sorry

-- Proof sketch: choose an internal direct-sum decomposition of `M` by countably generated
-- `R`-submodules, tensor the whole decomposition with `S`, and use that tensor products commute
-- with direct sums while countable generating sets base change to countable generating sets.
/-- Lemma 10.94.1 (3): if `M` is a direct sum of countably generated `R`-modules, then
`S ⊗[R] M` is a direct sum of countably generated `S`-modules. This is the canonical Lean form of
the textbook statement for `M ⊗_R S`. -/
theorem isDirectSumOfCountablyGenerated_tensorProduct
    (hM : IsDirectSumOfCountablyGenerated R M) :
    IsDirectSumOfCountablyGenerated S (S ⊗[R] M) := by
  sorry

section

variable [Projective R M]

/- Lemma 10.94.1 (4): if `M` is projective over `R`, then its base change `S ⊗[R] M` is
projective over `S`. This is exactly the canonical owner instance `Projective.tensorProduct`,
specialized to the base-changed module `S ⊗[R] M`. -/
recall Projective.tensorProduct

end

end

end Module
