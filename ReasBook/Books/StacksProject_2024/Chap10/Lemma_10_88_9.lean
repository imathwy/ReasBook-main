import Mathlib
import stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Source/core/bridge triage:
* source-facing: the tensor-product stability statement from Lemma `10.88.9`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: none; the theorem is a derived closure property of the owner abstraction.
-/
-- Proof sketch: choose directed colimit presentations of `M` and `N` by finitely presented
-- modules with eventual factorization of transition maps, as in Proposition `10.88.6`. The
-- tensor-product presentation indexed by pairs `(i, j)` has finitely presented stages by Lemma
-- `10.12.14`, and the tensor products of the eventual factorization maps give the same eventual
-- factorization property for the tensor-product system. Therefore `M ⊗[R] N` is Mittag-Leffler.
/-- Lemma 10.88.9: if `M` and `N` are Mittag-Leffler modules over `R`, then `M ⊗[R] N` is a
Mittag-Leffler `R`-module. -/
theorem mittagLeffler_tensorProduct_of_mittagLeffler
    (hM : MittagLeffler R M) (hN : MittagLeffler R N) :
    MittagLeffler R (M ⊗[R] N) := sorry

end

end Module
