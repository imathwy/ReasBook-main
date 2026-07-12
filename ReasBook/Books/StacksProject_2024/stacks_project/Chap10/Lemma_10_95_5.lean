import Mathlib
import StacksProject_2024.Chap10.Lemma_10_95_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule

universe u v w x

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {I : Type x}

-- Proof sketch: start with `N'_0 = N` and inductively enlarge to countably generated submodules
-- `N'_ℓ` so that each next base change contains every summand `Q i` that meets the current image.
-- Apply Lemma `10.95.4` to the countable sum of those summands at each step, then take the union
-- over the countable iteration to obtain `N'` and the corresponding subset `I'`.
/-- Lemma 10.95.5: if `S ⊗[R] M` is the sum of an independent family of countably generated
`S`-submodules `Q i`, equivalently an internal direct-sum decomposition by countably generated
summands, then every countably generated `R`-submodule `N` of `M` is contained in a countably
generated `R`-submodule whose base change is the sum of a subfamily of the `Q i`. This is the
canonical Lean form of the statement that the image of `N' ⊗_R S → M ⊗_R S` is `⨁_{i ∈ I'} Q i`.
-/
theorem exists_countablyGenerated_supermodule_with_baseChange_eq_iSup_subfamily
    (Q : I → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q)
    (hQtop : iSup Q = ⊤)
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    {N : Submodule R M}
    (hN : N.CountablyGenerated) :
    ∃ (N' : Submodule R M) (_ : N ≤ N') (_ : N'.CountablyGenerated) (I' : Set I),
      N'.baseChange S = ⨆ i : I', Q i.1 := sorry

end
