import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Problem_22_6_1

open CategoryTheory
open CategoryTheory.Limits
open scoped Topology Topology.Homotopy

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced the sequential-colimit API but no more canonical
-- ordinary-space reduced-homology owner than the existing Chapter 14 based-space construction.
-- The source-facing theorem therefore keeps `X : TopCat` on the public surface, handles the
-- based model internally via `adjoinBasepoint X`, and records the stable `K(π, n + 1)` colimit
-- by a named source-facing construction rather than a bare existential package.

/-- The additive group in stage `n` of the stable `K(π, n + 2)` representation sequence attached
to `X`. -/
abbrev stableKPiRepresentationStage
    (q : ℕ) (X : BasedSpace) (stageSpace : ℕ → BasedSpace)
    (n : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of
    (Additive
      (π_ ((q + n) + 2)
        (smashProduct X (stageSpace n)).right
        (underTopBasepoint (smashProduct X (stageSpace n)))))

/-- A source-facing stable `K(π, n + 1)` representation system for an ordinary CW complex `X`.
The Chapter 13 pair-homology theory with coefficients in `π`, the stage spaces, their
`K(π, n + 1)` identifications, the stabilization maps, and the representing comparison
isomorphism are recorded explicitly in one named construction so the source-facing existence
theorem can quantify over a single owner. -/
structure StableKPiReducedHomologySystem
    (π : Type) [AddCommGroup π] (q : ℕ) (X : TopCat) where
  /-- The Chapter 13 pair-homology theory whose reduced homology on `adjoinBasepoint X` is
  represented by this stable system. -/
  homologyTheory : PairHomologyTheory π
  /-- The `n`th based `K(π, n + 1)` stage in the stable diagram. -/
  stageSpace : ℕ → BasedSpace
  /-- Each stage realizes the expected additive Eilenberg-MacLane space `K(π, n + 1)`. -/
  stageIsKPi : ∀ n : ℕ, IsAdditiveEilenbergMacLaneSpace π (n + 1) (stageSpace n)
  /-- The chosen stabilization map between successive stable stages. -/
  stabilizationStep :
    ∀ n : ℕ,
      stableKPiRepresentationStage q (adjoinBasepoint X) stageSpace n ⟶
        stableKPiRepresentationStage q (adjoinBasepoint X) stageSpace (n + 1)
  /-- The explicit comparison isomorphism from `H̃_q(X; π)` to the stable colimit built from the
  canonical `K(π, n + 1)` stages and the chosen stabilization maps. -/
  comparison :
    AddCommGrpCat.of (basedReducedHomology homologyTheory (q : ℤ) (adjoinBasepoint X)) ≅
      AddCommGrpCat.FilteredColimits.colimit (Functor.ofSequence stabilizationStep)

namespace StableKPiReducedHomologySystem

/-- The reduced homology group on `X`, computed from the system's explicit Chapter 13
pair-homology theory after adjoining a basepoint. -/
abbrev reducedHomology
    {π : Type} [AddCommGroup π] {q : ℕ} {X : TopCat}
    (system : StableKPiReducedHomologySystem π q X) : Type :=
  basedReducedHomology system.homologyTheory (q : ℤ) (adjoinBasepoint X)

/-- The sequential additive-group diagram attached to a stable `K(π, n + 1)` representation
system. -/
abbrev diagram
    {π : Type} [AddCommGroup π] {q : ℕ} {X : TopCat}
    (system : StableKPiReducedHomologySystem π q X) :
    ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence system.stabilizationStep

/-- The filtered colimit of the stable `K(π, n + 1)` representation system attached to `X`. -/
abbrev colimit
    {π : Type} [AddCommGroup π] {q : ℕ} {X : TopCat}
    (system : StableKPiReducedHomologySystem π q X) :
    AddCommGrpCat :=
  AddCommGrpCat.FilteredColimits.colimit system.diagram

/-- The comparison field of a stable `K(π, n + 1)` representation system, restated with codomain
written as the named filtered colimit `system.colimit`. -/
abbrev comparisonColimit
    {π : Type} [AddCommGroup π] {q : ℕ} {X : TopCat}
    (system : StableKPiReducedHomologySystem π q X) :
    AddCommGrpCat.of system.reducedHomology ≅ system.colimit :=
  system.comparison

end StableKPiReducedHomologySystem

/-- Theorem 22.1.1: for a CW complex `X`, an abelian group `π`, and a nonnegative degree `q`,
the reduced homology group attached to some Chapter 13 pair-homology theory with coefficients in
`π` is represented by a stable colimit of homotopy classes built from an explicit family of
`K(π, n + 1)` stages and their stabilization maps. On the Lean surface, the ordinary space `X` is
handled internally by the based-space model `adjoinBasepoint X`, and the theorem asserts that
some named source-facing stable representation system exists; its comparison isomorphism is one of
the fields of that system. -/
theorem reducedHomology_isStableColimitOf_kPi
    (π : Type) [AddCommGroup π]
    (q : ℕ) (X : TopCat) (cwX : TopCat.CWComplex X) :
    Nonempty (StableKPiReducedHomologySystem π q X) :=
  sorry
