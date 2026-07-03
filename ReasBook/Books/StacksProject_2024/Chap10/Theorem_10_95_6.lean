import Mathlib
import StacksProject_2024.Chap10.Lemma_10_95_3
import StacksProject_2024.Chap10.Theorem_10_84_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module.Projective

section

variable {R : Type u} [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: faithfully flat descent for projective modules over commutative rings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.countablyGenerated_projective_of_countablyGenerated_projective_tensorProduct_of_faithfullyFlat`,
  `projective_isDirectSumOfCountablyGeneratedProjective`,
  and the direct-sum owner instance `Module.Projective R (Π₀ i, A i)`;
- best owner abstraction: the owner predicate `Module.Projective R M`;
- primitive data: the faithfully flat `R`-algebra `S`, the `R`-module `M`, and the projective
  base change `S ⊗[R] M`;
- derived API: descent of the owner predicate `Module.Projective` from the base-changed module
  back to `M`.

Layering:
- this numbered item is `core/canonical` in the owner namespace `Module.Projective`: there is no
  upstream exact-interface descent theorem to recall, so the theorem below remains the chapter's
  canonical owner-level entry rather than a local wrapper.
-/
-- Proof sketch: decompose the projective `S`-module `S ⊗[R] M` as a direct sum of countably
-- generated projective summands using Theorem `10.84.5`; then descend countably generated
-- projective pieces by Lemma `10.95.3` along a transfinite Kaplansky dévissage as in the
-- textbook proof, and conclude that `M` is a direct sum of projective modules, hence projective.
/-- Theorem 10.95.6: if `R → S` is faithfully flat and the base change `S ⊗[R] M` is projective
as an `S`-module, then `M` is projective as an `R`-module. -/
theorem of_projective_tensorProduct_of_faithfullyFlat
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] :
    Module.Projective R M := sorry

end

end Module.Projective
