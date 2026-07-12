import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

/- Domain-style sampling:
- primary domain: faithfully flat descent for finiteness conditions on modules;
- sampled owner declarations of the same kind:
  `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`,
  `Module.Flat.of_flat_tensorProduct`,
  `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`;
- best owner abstraction: the predicate `Module.FinitePresentation R M`;
- primitive data: the rings `R`, `S`, the `R`-module `M`, and the faithfully flat base change
  `R → S`;
- derived API: descent lemmas for finiteness predicates after tensor base change.

Layering:
- this numbered item is `core/canonical`: unlike the finite and flat clauses, there is no
  upstream owner theorem for module finite-presentation descent, so the theorem below is the owner
  declaration rather than a bridge or compatibility wrapper.
-/

/- Companion recall: if the base-changed `S`-module `S ⊗[R] M` is finite, then `M` is finite.
This is exactly the canonical faithfully flat descent theorem
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`. -/
recall Module.Finite.of_finite_tensorProduct_of_faithfullyFlat

-- Proof sketch: first descend finite generation of `M` from part (1). Choose a finite free
-- presentation of `M`, identify the kernel after tensoring with `S` using flatness of the faithful
-- base change, use finite presentation of `S ⊗[R] M` to show the base-changed kernel is finite,
-- and then descend that finite generation again via faithfully flat descent.
/-- Lemma 10.83.2: if the base-changed `S`-module `S ⊗[R] M` is finitely presented over `S`,
then `M` is finitely presented over `R`. -/
theorem Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := sorry

/- Companion recall: if the base-changed `S`-module `S ⊗[R] M` is flat over `S`, then `M` is
flat over `R`. This is exactly the canonical faithfully flat descent theorem
`Module.Flat.of_flat_tensorProduct`. -/
recall Module.Flat.of_flat_tensorProduct

end
