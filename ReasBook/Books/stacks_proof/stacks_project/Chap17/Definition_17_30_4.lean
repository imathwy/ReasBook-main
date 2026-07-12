import Mathlib
import StacksProject_2024.Chap17.Definition_17_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable (f : X ⟶ Y) (i : ℕ)

/- Domain-style sampling for Definition 17.30.4:
- primary domain: relative de Rham complexes on a morphism of ringed spaces;
- sampled owner declarations:
  `TopCat.Sheaf.deRhamComplex_obj`,
  `deRhamComplex_d_basicForm`,
  `CochainComplex.d`;
- best owner abstraction: the source-facing differential already lives as the degree-`i`
  differential of the canonical owner `Ω^•[f]` from `Definition_17_30_1`;
- primitive data in this file: none;
- derived API in this file: none.

Source/core/bridge triage:
- `source-facing`: the differential `d : Ω^i_{X/Y} → Ω^{i + 1}_{X/Y}`;
- `core/canonical`: the sheaf-level owner
  `TopCat.Sheaf.deRhamComplex (RingedSpace.Hom.inverseImageStructureSheafHomComm f)` and its
  differential field `.d`;
- `bridge/view`: this file is recall-only, so it keeps no parallel bridge owner. -/

/- Definition 17.30.4: the degree-`i` relative de Rham differential
`d : Ω^i_{X/Y} → Ω^{i + 1}_{X/Y}` is the degree-`i` differential of the canonical relative de Rham
complex `Ω^•[f]`. -/
#check (Ω^•[f]).d i (i + 1)

end AlgebraicGeometry.RingedSpace
