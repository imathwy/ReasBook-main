import StacksProject_2024.stacks_project.Chap20.Example_20_50_2_Core
import StacksProject_2024.stacks_project.Chap20.OpensInstances
import StacksProject_2024.stacks_project.Chap21.Lemma_21_48_3

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.50.3:
- primary domain: duality in the monoidal category of cochain complexes of `𝒪_X`-modules,
  together with the source-facing and canonical local strict-perfectness owners on such complexes;
- sampled owner declarations:
  `CategoryTheory.ExactPairing`,
  `AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyStrictlyPerfect`,
  `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`,
  `SheafOfModules.RingedSite.exactPairing_isLocallyStrictlyPerfect`;
- best owner abstraction: the Chapter 20 source-facing owner is
  `AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyStrictlyPerfect`, while the
  core/canonical owner remains the generic ringed-site theorem
  `SheafOfModules.RingedSite.exactPairing_isLocallyStrictlyPerfect`;
- primitive data: a complex `F`, a chosen left dual `G`, and the canonical left-dual datum
  `ExactPairing G F`;
- derived API: the local strict-perfectness conclusion on `F`, obtained by specializing the
  ringed-site cover at the top open and rewriting it into the Chapter 20 open-cover language.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the left-dual-implies-local-strictly-perfect
  statement, stated in the Chapter 20 owner API;
- `core/canonical`: `SheafOfModules.RingedSite.exactPairing_isLocallyStrictlyPerfect`;
- `bridge/view`: specialization from a general ringed site to the opens site of `X`, then passage
  from a cover of `⊤` to the Chapter 20 open-cover formulation.
-/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (CochainComplex (Modules X) ℤ)]

local notation "CpxX" => CochainComplex (Modules X) ℤ

variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X, ((Opens.grothendieckTopology X).over U).HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]
variable [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
variable [∀ U : Opens X,
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

-- Proof sketch: apply the ringed-site owner theorem on the opens site of `X`, then specialize the
-- resulting local cover to the top open and rewrite that cover into the Chapter 20 open-cover
-- formulation.
/-- Lemma 20.50.3: if a complex of `𝒪_X`-modules on a ringed space has a chosen left
dual in the monoidal category of complexes, then it is locally strictly perfect on `X`. -/
@[stacks 0FPA]
theorem exactPairing_isLocallyStrictlyPerfect
    {F G : CpxX} (hpair : ExactPairing G F) :
    CochainComplex.IsLocallyStrictlyPerfect F := by
  exact (cochainComplex_isLocallyStrictlyPerfect_iff_site F).2
    (RingedSite.exactPairing_isLocallyStrictlyPerfect hpair)

end AlgebraicGeometry.RingedSpace
