import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_1_3

open scoped DirectSum

noncomputable section

universe u w

/-- The total source-facing mod-`2` homology object `H_*(T)` attached to a chosen connective
prespectrum reduced-homology presentation of `T` and a chosen based CW model of `S⁰`. -/
abbrev prespectrumModTwoHomologyStar
    (T : Prespectrum.{u, w})
    (presentation : ConnectivePrespectrumReducedHomologyPresentation T)
    (sphereZero : BasedCWComplex) : Type _ :=
  ⨁ n : ℕ,
    ((connectivePrespectrumReducedHomology T presentation) (n : ℤ)).obj sphereZero

/-- `prespectrumModTwoHomologyStar` is definitionally the direct sum of the degreewise reduced
homology groups of the chosen based `S⁰` model. -/
theorem prespectrumModTwoHomologyStar_def
    (T : Prespectrum.{u, w})
    (presentation : ConnectivePrespectrumReducedHomologyPresentation T)
    (sphereZero : BasedCWComplex) :
    prespectrumModTwoHomologyStar T presentation sphereZero =
      ⨁ n : ℕ,
        ((connectivePrespectrumReducedHomology T presentation) (n : ℤ)).obj sphereZero :=
  rfl

/-- A chosen source-facing presentation of the total mod-`2` homology object `H_*(T)` of
prespectra, built from a connective reduced-homology presentation for each `T` and a chosen based
CW model of `S⁰`. -/
structure PrespectrumModTwoHomologyPresentation where
  /-- The chosen connective reduced-homology presentation used to define `H_*(T)` for each
  prespectrum `T`. -/
  homologyPresentation :
    ∀ T : Prespectrum.{u, w}, ConnectivePrespectrumReducedHomologyPresentation T
  /-- The chosen based CW model of `S⁰` used to evaluate the reduced homology theory. -/
  sphereZero : BasedCWComplex
  /-- The underlying space of the chosen based CW model of `S⁰` is identified with the standard
  topological `0`-sphere `TopCat.sphere 0`. -/
  sphereZeroSpaceIso : sphereZero.1.right ≅ TopCat.sphere 0
  /-- The total homology object `H_*(T)` carries a chosen `ZMod 2`-module structure. -/
  hStarModule :
    ∀ T : Prespectrum.{u, w},
      Module (ZMod 2) (prespectrumModTwoHomologyStar T (homologyPresentation T) sphereZero)

namespace PrespectrumModTwoHomologyPresentation

/-- The source-facing total mod-`2` homology object `H_*(T)` attached to a chosen presentation of
prespectrum homology. -/
abbrev HStar
    (presentation : PrespectrumModTwoHomologyPresentation)
    (T : Prespectrum.{u, w}) : Type _ :=
  prespectrumModTwoHomologyStar T (presentation.homologyPresentation T) presentation.sphereZero

/-- `presentation.HStar T` is definitionally the direct sum of the graded reduced homology groups
of the chosen based `S⁰` model. -/
theorem hStar_def
    (presentation : PrespectrumModTwoHomologyPresentation)
    (T : Prespectrum.{u, w}) :
    presentation.HStar T =
      prespectrumModTwoHomologyStar
        T (presentation.homologyPresentation T) presentation.sphereZero :=
  rfl

/-- The chosen presentation of `H_*(T)` supplies its `ZMod 2`-module structure. -/
instance hStarModuleInst
    (presentation : PrespectrumModTwoHomologyPresentation)
    (T : Prespectrum.{u, w}) :
    Module (ZMod 2) (presentation.HStar T) :=
  presentation.hStarModule T

end PrespectrumModTwoHomologyPresentation
