import Mathlib
import stacks_project.Chap10.Definition_10_160_1
import stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

namespace RingHom

/- Domain-style sampling:
- primary domain: formal smoothness of adic ring maps and extension of absolute derivations across
  square-zero thickenings.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.exists_continuous_lift_of_formally_smooth_for_adic`
  * `Derivation`
  * `Derivation.liftOfDerivationToSquareZero`
- best owner abstraction: an arbitrary ring map `f : A →+* B` together with the ideal
  `I : Ideal B` controlling the adic topology; the local/maximal-ideal case is a specialization.
- source/core/bridge triage:
  * `source-facing`: extension of an absolute derivation across a formally smooth adic map;
  * `core/canonical`: the owner lifting theorem
    `RingHom.exists_continuous_lift_of_formally_smooth_for_adic` together with the standard
    derivation/square-zero-extension API;
  * `bridge/view`: the complete-local maximal-ideal specialization below.
- primitive data: the ring map `f : A →+* B`, the ideal `I : Ideal B`, `I`-adic completeness of
  `B`, and the derivation `D : Derivation ℤ A A`.
- derived API: existence of an absolute derivation on `B` restricting to `D` along `f`.
-/

-- Proof sketch: form the square-zero thickening `B[ε]` and the map `A → B[ε]` sending
-- `a` to `f a + ε • f (D a)`. Because `B` is `I`-adically complete and `f` is formally smooth
-- for the `I`-adic topology, Lemma `15.37.5` provides a lift `B → B[ε]`. Taking the
-- `ε`-coefficient of that lift yields the required derivation on `B`, and the commutative square
-- forces it to agree with `D` on the image of `A`.
/-- A formally smooth adic ring map into an adically complete target extends absolute derivations
from the source to the target. -/
theorem exists_derivation_extension_of_formally_smooth_for_adic
    (f : A →+* B) (I : Ideal B) [IsAdicComplete I B]
    (hfs : f.formally_smooth_for_adic I)
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (f a) = f (D a) := sorry

end RingHom

section

open IsLocalRing

variable [Algebra A B] [IsCompleteLocalRing B]

/-- Lemma 15.49.1: if `B` is a complete local ring and `algebraMap A B` is formally smooth for
the `maximalIdeal B`-adic topology, then every absolute derivation `D : A → A` extends to an
absolute derivation `D' : B → B`. -/
theorem exists_derivation_extension_of_formally_smooth_for_completeLocal
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B))
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (algebraMap A B a) = algebraMap A B (D a) := by
  simpa using
    (algebraMap A B).exists_derivation_extension_of_formally_smooth_for_adic
      (maximalIdeal B) hfs D

end

end
