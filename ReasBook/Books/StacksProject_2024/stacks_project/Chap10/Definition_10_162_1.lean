import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of Japanese and Nagata finiteness conditions on rings;
- sampled owner abstractions of the same kind in the project:
  - `IsN1Ring` and `IsN2Ring` from `Definition_10_161_1`,
  - `UniversallyCatenaryRing` from `Definition_10_105_3`,
  - `IsJ2Ring` from `Chap15/Definition_15_47_1`,
  - `IsQuasiExcellentRing` from `Chap15/Definition_15_52_1`.

Best owner abstraction:
- `UniversallyJapaneseRing` is the source-facing owner for the finite-type-domain `N-2` property;
- `NagataRing` is the source-facing owner for the Noetherian-plus-prime-quotient `N-2` property;
- `IsN2Ring` remains the core/canonical owner reused inside those two definitions.

Primitive data vs derived API:
- primitive data for `UniversallyJapaneseRing`: the `N-2` owner on each finite type domain
  `R`-algebra;
- primitive data for `NagataRing`: Noetherianity together with the `N-2` owner on each prime
  quotient;
- derived API: all later bridges such as `[NagataRing R] → [UniversallyJapaneseRing R]` and
  finite-type stability belong downstream, not as extra fields here.
-/

/-- Definition 10.162.1 (1): A ring is universally Japanese if every finite type `R`-algebra
that is a domain is `N-2`, i.e. Japanese. -/
class UniversallyJapaneseRing : Prop where
  /-- Every finite type domain over a universally Japanese ring is `N-2`. -/
  finiteType_algebra_isN2Ring {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [IsDomain S] : IsN2Ring S

attribute [instance] UniversallyJapaneseRing.finiteType_algebra_isN2Ring

/-- Definition 10.162.1 (2): A Nagata ring is a Noetherian ring whose quotient by every prime
ideal is `N-2`. -/
class NagataRing : Prop extends IsNoetherianRing R where
  /-- The quotient of a Nagata ring by any prime ideal is `N-2`. -/
  quotient_isN2Ring (p : Ideal R) [p.IsPrime] : IsN2Ring (R ⧸ p)

attribute [instance] NagataRing.quotient_isN2Ring

end
