import Mathlib
import stacks_project.Chap17.Definition_17_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable (f : X ⟶ Y) (i : ℕ)

/- Domain-style sampling for Definition 17.30.4:
- primary domain: relative de Rham complexes on a morphism of ringed spaces;
- sampled owner declarations:
  `deRhamComplex`,
  `deRhamComplex_X`,
  `IsDeRhamComplex`,
  `CochainComplex.d`;
- best owner abstraction: the source-facing differential already lives as the degree-`i`
  differential of the canonical owner `deRhamComplex f` from `Definition_17_30_1`;
- primitive data in this file: none;
- derived API in this file: none.

Source/core/bridge triage:
- `source-facing`: the differential `d : Ω^i_{X/Y} → Ω^{i + 1}_{X/Y}`;
- `core/canonical`: `deRhamComplex f` and its differential field `.d`;
- `bridge/view`: this file is recall-only, so it keeps no parallel bridge owner. -/

/- Definition 17.30.4: the degree-`i` relative de Rham differential
`d : Ω^i_{X/Y} → Ω^{i + 1}_{X/Y}` is the degree-`i` differential of the canonical relative de Rham
complex `deRhamComplex f`. -/
#check (deRhamComplex f).d i (i + 1)

end AlgebraicGeometry.RingedSpace
