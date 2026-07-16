import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {R' : Type v} [CommSemiring R] [CommSemiring R']

namespace Ideal

/-
Domain triage:
- primary domain: commutative algebra of ideals, nilradicals, and extension along ring maps;
- sampled owner declarations: `Ideal.IsLocallyNilpotent`, `Ideal.map_radical_le`,
  `Ideal.map_mono`;
- best owner abstraction: local nilpotence is the canonical containment `I ≤ nilradical R`, so the
  source-facing statement here is a `bridge/view` theorem transporting that containment across
  `Ideal.map`;
- primitive data: a ring homomorphism `f : R →+* R'` and an ideal `I : Ideal R`;
  derived API: `I.IsLocallyNilpotent`.
-/
/-- Lemma 10.32.3: the extension of a locally nilpotent ideal along a ring map is again locally
nilpotent. This is a `bridge/view` theorem from the chapter vocabulary
`Ideal.IsLocallyNilpotent` to the canonical owner lemma `Ideal.map_radical_le`. -/
@[stacks 0544]
theorem map_isLocallyNilpotent (f : R →+* R') {I : Ideal R}
    (hI : I.IsLocallyNilpotent) : (I.map f).IsLocallyNilpotent :=
  (map_mono hI).trans <| by
    simpa using (⊥ : Ideal R).map_radical_le f

end Ideal

end
