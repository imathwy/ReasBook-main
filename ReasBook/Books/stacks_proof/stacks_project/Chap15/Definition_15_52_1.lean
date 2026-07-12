import Mathlib
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap15.Definition_15_47_1
import StacksProject_2024.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling in the commutative-algebra excellence API:
- source-facing owners introduced here: `IsQuasiExcellentRing`, `IsExcellentRing`
- sampled project owners of the same kind:
  - `IsGRing` from `Definition_15_50_1`,
  - `IsJ2Ring` from `Definition_15_47_1`,
  - `UniversallyCatenaryRing` from `Chap10/Definition_10_105_3`,
  - `NagataRing` from `Chap10/Definition_10_162_1` as downstream derived API

Layer triage:
- `source-facing`: the textbook notions of quasi-excellent and excellent rings
- `core/canonical`: the existing owner predicates `IsGRing`, `IsJ2Ring`, and
  `UniversallyCatenaryRing`
- `bridge/view`: downstream consequences such as the Nagata-property instance belong in later
  files, not as primitive fields here

Primitive data vs derived API:
- primitive data for quasi-excellence are exactly the already-canonical owners `IsGRing` and
  `IsJ2Ring`;
- primitive data for excellence are exactly quasi-excellence together with
  `UniversallyCatenaryRing`;
- derived API should come from inherited instances, so this file should not introduce wrapper
  aliases or extra fields restating those owners.
-/

/-- Definition 15.52.1 (1): a ring `R` is quasi-excellent if it is Noetherian, a `G`-ring, and
`J-2`. -/
@[stacks 07QT]
class IsQuasiExcellentRing : Prop extends IsGRing R, IsJ2Ring.{u, v} R

/-- Definition 15.52.1 (2): a ring `R` is excellent if it is quasi-excellent and universally
catenary. -/
@[stacks 07QT]
class IsExcellentRing : Prop extends IsQuasiExcellentRing.{u, v} R, UniversallyCatenaryRing.{u, v} R

end
