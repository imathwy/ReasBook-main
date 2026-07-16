import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_11
import StacksProject_2024.stacks_project.Chap20.Lemma_20_29_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})
variable [LocallySmall (RingedSpace.Modules X)] [WellPowered (RingedSpace.Modules X)]
  [HasWidePullbacks (RingedSpace.Modules X)] [HasCoproducts (RingedSpace.Modules X)]
  [InitialMonoClass (RingedSpace.Modules X)]
  [IsGrothendieckAbelian (RingedSpace.Modules X)]
  [LocallySmall (ModuleCat (globalSectionsRing X))]
  [WellPowered (ModuleCat (globalSectionsRing X))]
  [HasWidePullbacks (ModuleCat (globalSectionsRing X))]
  [HasCoproducts (ModuleCat (globalSectionsRing X))]
  [InitialMonoClass (ModuleCat (globalSectionsRing X))]

local notation "ModX" => RingedSpace.Modules X
private abbrev ModΓXCat (X : RingedSpace.{u}) := ModuleCat.{u} (globalSectionsRing X)
local notation "ModΓX" => ModΓXCat X
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DerivedCategory ModX)
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "HΓ" n => DerivedCategory.homologyFunctor ModΓX n

-- Proof sketch: this remark is the bounded-below finite-filtration specialization of
-- Lemma `20.29.1`. The same filtered hypercohomology spectral sequence exists for any filtered
-- complex; in the bounded-below finite-filtration case, the stage-control hypothesis needed there
-- is supplied by the direct-construction input recorded in this file, so the chosen spectral
-- sequence is bounded and converges.
/- Domain-style sampling for Remark `20.29.2`.
- primary domain: filtered complexes of `𝒪_X`-modules and their associated
  hypercohomology spectral sequences;
- sampled owner declarations:
  `FilteredComplex.HasFiniteFiltrations`,
  `exists_filteredHypercohomologySpectralSequence`,
  `EventualStageHypercohomologyControl`;
- best owner abstraction: the source-facing remark is the bounded-below plus finite-filtration
  bridge from the bounded-below and finite-filtration hypotheses to the Chapter `20.29.1`
  control owner `EventualStageHypercohomologyControl X K`, with the spectral-sequence existence
  theorem retained only as a thin specialization corollary;
- primitive data: the filtered complex `K`, its lower bound, and the canonical finiteness owner
  `K.HasFiniteFiltrations`;
- derived API: the control owner `EventualStageHypercohomologyControl X K`, its two source-facing
  component consequences, and the resulting bounded/convergent hypercohomology spectral-sequence
  specialization obtained by applying Lemma `20.29.1`;
Source/core/bridge triage:
- `source-facing`: the bounded-below finite-filtration control theorem below;
- `core/canonical`: `FilteredComplex`, `HasFiniteFiltrations`,
  `CohomologicalSpectralSequence`, and `FilteredComplex.convergesToCohomology`;
- `bridge/view`: the internal passage through `EventualStageHypercohomologyControl` in
  Lemma `20.29.1`, and then from that control theorem to the bounded/convergent existence
  specialization.

The local ad hoc finiteness binder
`∀ n, ∃ a b, (K.X n).filtration.obj a = ⊤ ∧ (K.X n).filtration.obj b = ⊥`
duplicates the canonical Chapter `12` owner `K.HasFiniteFiltrations`, and the convergence
conclusion should likewise use the Chapter `12` owner `filteredComplex.convergesToCohomology
spectralSequence` rather than a weaker abutment-only repackaging. The source-facing public API of
this file is therefore the control bridge to `EventualStageHypercohomologyControl X K`, with the
existence theorem demoted to a specialization corollary. -/

/-- Remark 20.29.2: if `𝒜^•` is a bounded-below filtered complex of `𝒪_X`-modules whose
individual terms have finite filtrations, then the stagewise hypotheses required in
Lemma `20.29.1` hold: in every total degree, the hypercohomology of the filtration stages
vanishes for `p ≫ 0`, and the canonical stage maps to the abutment hypercohomology are
isomorphisms for `p ≪ 0`. -/
@[stacks 0BKL]
theorem eventualStageHypercohomologyControl_of_boundedBelow_of_hasFiniteFiltrations
    (K : FilteredComplex ModX)
    (hKboundedBelow : ∃ a : ℤ, K.underlying.IsStrictlyGE a)
    (hKfin : K.HasFiniteFiltrations) :
    EventualStageHypercohomologyControl X K := by
  sorry

/-- Under the bounded-below finite-filtration hypotheses of Remark `20.29.2`, the filtration-stage
hypercohomology groups vanish in each total degree for all sufficiently large filtration indices.
-/
theorem eventualStageHypercohomologyVanishesAbove_of_boundedBelow_of_hasFiniteFiltrations
    (K : FilteredComplex ModX)
    (hKboundedBelow : ∃ a : ℤ, K.underlying.IsStrictlyGE a)
    (hKfin : K.HasFiniteFiltrations) :
    EventualStageHypercohomologyVanishesAbove X K :=
  (eventualStageHypercohomologyControl_of_boundedBelow_of_hasFiniteFiltrations
    X K hKboundedBelow hKfin).vanishesAbove

/-- Under the bounded-below finite-filtration hypotheses of Remark `20.29.2`, the canonical maps
from stage hypercohomology to the abutment hypercohomology are isomorphisms in each total degree
for all sufficiently small filtration indices. -/
theorem eventualStageHypercohomologyStabilizesBelow_of_boundedBelow_of_hasFiniteFiltrations
    (K : FilteredComplex ModX)
    (hKboundedBelow : ∃ a : ℤ, K.underlying.IsStrictlyGE a)
    (hKfin : K.HasFiniteFiltrations) :
    EventualStageHypercohomologyStabilizesBelow X K :=
  (eventualStageHypercohomologyControl_of_boundedBelow_of_hasFiniteFiltrations
    X K hKboundedBelow hKfin).stabilizesBelow

end AlgebraicGeometry.RingedSpace
