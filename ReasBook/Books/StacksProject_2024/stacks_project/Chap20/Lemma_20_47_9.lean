import StacksProject_2024.Chap15.Lemma_15_65_3
import StacksProject_2024.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open DerivedCategory.TStructure
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

namespace ModuleDerived

section

/- Domain-style sampling for Lemma 20.47.9:
- primary domain: cohomology sheaves of `m`-pseudo-coherent derived `𝒪_X`-modules;
- sampled owner declarations:
  `ModuleDerived`,
  `DerivedCategory.homologyFunctor`,
  `K.IsMPseudoCoherent m`,
  `DerivedCategory.IsLE`,
  `CochainComplex.homology_finite_of_isMPseudoCoherent`,
  `CochainComplex.homology_finitePresentation_of_isMPseudoCoherent`;
- best owner abstraction: the intrinsic Chapter 20 owners
  `ModuleDerived` and `K.IsMPseudoCoherent m` are already owned by
  `Definition_20_47_1`, while the cohomology sheaf itself is the canonical owner
  `((H^i).obj K)` from the chapter-wide `H^i` notation and the bounded-above hypothesis belongs
  to the chapter/mathlib `t`-structure owner `K.IsLE n`; the actual finiteness mechanism is the
  Chapter 15 core pair
  `homology_finite_of_isMPseudoCoherent` and
  `homology_finitePresentation_of_isMPseudoCoherent`, so this file is only the ringed-space
  consequence layer transporting those top-cohomology conclusions to `D(𝒪_X)`;
- primitive data: a derived object `K`, the owner witness `K.IsMPseudoCoherent m`, and the
  canonical bounded-above hypothesis `K.IsLE m` or `K.IsLE (m + 1)`;
- derived API: the finite-type and finite-presentation conclusions for the top surviving
  cohomology sheaves.

Source/core/bridge triage:
- `source-facing`: the finite-type and finite-presentation consequences below;
- `core/canonical`: `ModuleDerived`, `H^i`, `K.IsMPseudoCoherent m`, and
  `DerivedCategory.IsLE`, together with the Chapter 15 homology-finiteness owners;
- `bridge/view`: the pointwise vanishing reformulation extracted from `K.IsLE n`. -/

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.carrier).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ U : Opens X.carrier,
  HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  ((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  ((Opens.grothendieckTopology X.carrier).over U).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]

local notation "DModX" => ModuleDerived X
local notation "ModX" => RingedSpace.Modules X
local notation:max "H^" q:max => DerivedCategory.homologyFunctor ModX q

variable {K : DModX} {m : ℤ}

/-- Lemma 20.47.9 (1): if `K` is `m`-pseudo-coherent and belongs to `D^{≤ m}`, then `H^m(K)` is
a finite type `𝒪_X`-module. The `IsLE` hypothesis is the canonical way to encode
`H^i(K) = 0` for `i > m`. -/
@[stacks 08DN]
theorem IsMPseudoCoherent.topCohomology_isFiniteType
    (hK : K.IsMPseudoCoherent m)
    (hLE : K.IsLE m) :
    ((H^m).obj K).IsFiniteType := sorry

/-- Lemma 20.47.9 (2): if `K` is `m`-pseudo-coherent and belongs to `D^{≤ m + 1}`, then
`H^{m + 1}(K)` is a finitely presented `𝒪_X`-module. The `IsLE` hypothesis is the canonical way
to encode `H^i(K) = 0` for `i > m + 1`. -/
@[stacks 08DN]
theorem IsMPseudoCoherent.nextCohomology_isFinitePresentation
    (hK : K.IsMPseudoCoherent m)
    (hLE : K.IsLE (m + 1)) :
    ((H^(m + 1)).obj K).IsFinitePresentation := sorry

end

end ModuleDerived

end AlgebraicGeometry.RingedSpace
