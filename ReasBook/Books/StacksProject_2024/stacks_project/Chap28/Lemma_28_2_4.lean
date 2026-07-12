import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Source/core/bridge triage for Lemma 28.2.4:
- `source-facing`: the underlying topological space of a quasi-compact and quasi-separated scheme
  is spectral;
- `core/canonical`: the topological owner `SpectralSpace`;
- `bridge/view`: for schemes, the source item is the specialization
  `inferInstance : SpectralSpace X` under the canonical qcqs assumptions.
-/

section

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/- Lemma 28.2.4: if `X` is a quasi-compact and quasi-separated scheme, then the underlying
topological space of `X` is spectral. The canonical owner is `SpectralSpace`, and this file adds
the scheme-specific qcqs instance bridge using the ambient quasi-compactness and
quasi-separatedness hypotheses. -/
instance instSpectralSpace (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    SpectralSpace X :=
  SpectralSpace.mk

/-- Lemma 28.2.4: if `X` is a quasi-compact and quasi-separated scheme, then the underlying
topological space of `X` is spectral. -/
@[stacks 094L]
theorem spectralSpace : SpectralSpace X :=
  inferInstance

end

end AlgebraicGeometry.Scheme
