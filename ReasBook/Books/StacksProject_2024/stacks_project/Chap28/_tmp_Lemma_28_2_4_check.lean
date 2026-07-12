import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

instance instSpectralSpaceTmp (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    SpectralSpace X :=
  SpectralSpace.mk

end AlgebraicGeometry.Scheme
