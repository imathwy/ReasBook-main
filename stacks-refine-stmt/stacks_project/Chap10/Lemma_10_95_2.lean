import Mathlib
import stacks_project.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

namespace Module

/-- Lemma 10.95.2: if the faithfully flat base change `S ⊗[R] M` is spanned over `S` by a
countable subset, then `M` is spanned over `R` by a countable subset. This is the canonical Lean
form of the textbook statement that countable generation descends from `M ⊗_R S`. -/
theorem countablyGenerated_of_countablyGenerated_tensorProduct_of_faithfullyFlat
    (h : CountablyGenerated S (S ⊗[R] M)) :
    CountablyGenerated R M := sorry

end Module

end
