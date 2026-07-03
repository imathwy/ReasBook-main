import Mathlib
import StacksProject_2024.Chap10.Lemma_10_78_6
import StacksProject_2024.Chap15.Definition_15_32_1
import StacksProject_2024.Chap15.Lemma_15_32_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

namespace Ideal

open RingTheory

variable {R : Type u} [CommRing R] {I : Ideal R}

/- Domain triage:
- primary domain: quasi-regular ideals and their conormal module `I / I²` in commutative algebra;
- sampled owner declarations of the same kind:
  `Ideal.IsQuasiRegularIdeal`,
  `Ideal.Cotangent`,
  `Module.FiniteProjective`,
  `fg_of_isQuasiRegularIdeal`;
- best owner abstraction in this file: the source-facing theorem should use the canonical owner
  predicate `Module.FiniteProjective` for the conormal module `I.Cotangent`;
- layer triage:
  `source-facing`: the finite-projective statement for `I.Cotangent`;
  `core/canonical`: `Ideal.Cotangent` and `Module.FiniteProjective`;
- primitive data: the ideal `I`, the source-facing hypothesis `hI : I.IsQuasiRegularIdeal`, and
  the canonical cotangent owner `I.Cotangent`;
- derived API: finite generation of `I` comes from `fg_of_isQuasiRegularIdeal`, while the theorem
  below packages the resulting finiteness and projectivity of `I.Cotangent` in the owner
  predicate `Module.FiniteProjective`. -/

-- Proof sketch: combine Lemma `15.32.2` with the canonical cotangent owner `I.Cotangent` to show
-- that `I / I²` is finite and projective over `R ⧸ I`, then package the result in
-- `Module.FiniteProjective`.
/-- Lemma 15.32.3: if `I` is a quasi-regular ideal of a commutative ring `R`, then the cotangent
module `I.Cotangent = I / I²` is a finite projective `(R ⧸ I)`-module. -/
theorem cotangent_finite_projective_of_isQuasiRegularIdeal
    (hI : I.IsQuasiRegularIdeal) :
    Module.FiniteProjective (R ⧸ I) I.Cotangent := by
  sorry

end Ideal

end
