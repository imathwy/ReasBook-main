import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Problem_22_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_6.DualAlgebra
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_6.SphereZero

open scoped DirectSum

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced only general sphere and `AlgEquiv` APIs, not a
-- ready-made owner for `H_*(HZ_2)` in the current repo. The reusable fixed dual Steenrod algebra
-- owner lives in `Lemma_25_4_6.DualAlgebra`, while this file keeps the `HZ_2`-specific homology
-- presentation concrete.

/-- A chosen source-facing presentation of `H_*(HZ_2)` by an `HZ_2` ring-prespectrum model, a
reduced homology presentation of its underlying prespectrum, and a chosen based CW model of `S⁰`.
-/
structure ModTwoEilenbergMacLaneSpectrumHomologyPresentation where
  /-- The chosen ring prespectrum modeling `HZ_2`. -/
  toRingPrespectrum : RingPrespectrum.{0, 0}
  /-- The `n`th stage of the chosen model realizes `K(ZMod 2, n)`. -/
  stageIsKZ2 :
    ∀ n : ℕ,
      IsAdditiveEilenbergMacLaneSpace (ZMod 2) n (toRingPrespectrum.toPrespectrum.basedSpace n)
  /-- The chosen reduced-homology presentation carried by the underlying prespectrum of the chosen
  `HZ_2` ring model. -/
  homologyPresentation :
    ConnectivePrespectrumReducedHomologyPresentation toRingPrespectrum.toPrespectrum
  /-- The chosen based CW model of `S⁰` used to extract the coefficient object `H_*(HZ_2)`. -/
  sphereZero : SphereZeroModel

/-- The underlying prespectrum of a chosen `HZ_2` ring-prespectrum model. -/
abbrev ModTwoEilenbergMacLaneSpectrumHomologyPresentation.toPrespectrum
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    Prespectrum.{0, 0} :=
  presentation.toRingPrespectrum.toPrespectrum

/-- The chosen based CW model of `S⁰` underlying a homology presentation of `HZ_2`. -/
abbrev ModTwoEilenbergMacLaneSpectrumHomologyPresentation.sphereZeroBasedCWComplex
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) : BasedCWComplex :=
  presentation.sphereZero.toBasedCWComplex

/-- The underlying based space of the chosen `S⁰` model in a homology presentation of `HZ_2`. -/
abbrev ModTwoEilenbergMacLaneSpectrumHomologyPresentation.sphereZeroBasedSpace
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) : BasedSpace :=
  presentation.sphereZero.basedSpace

/-- The chosen `S⁰` model in a homology presentation of `HZ_2` comes with a named based-space
comparison to the Chapter 11 smash-product unit `sphereZero`. -/
abbrev ModTwoEilenbergMacLaneSpectrumHomologyPresentation.sphereZeroIso
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    presentation.sphereZeroBasedSpace ≅ _root_.sphereZero :=
  presentation.sphereZero.basedSpaceIso

/-- The source unit map attached to a chosen `HZ_2` ring-prespectrum model. -/
abbrev ModTwoEilenbergMacLaneSpectrumHomologyPresentation.sourceUnit
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    _root_.sphereZero ⟶ presentation.toPrespectrum.basedSpace 0 :=
  presentation.toRingPrespectrum.unit

/-- The source multiplication maps attached to a chosen `HZ_2` ring-prespectrum model. -/
abbrev ModTwoEilenbergMacLaneSpectrumHomologyPresentation.sourceMul
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    ∀ m n : ℕ,
      smashProduct (presentation.toPrespectrum.basedSpace m)
          (presentation.toPrespectrum.basedSpace n) ⟶
        presentation.toPrespectrum.basedSpace (m + n) :=
  presentation.toRingPrespectrum.mul

/-- A `ModTwoEilenbergMacLaneSpectrumHomologyPresentation` records the `K(ZMod 2, n)` stages of
the chosen `HZ_2` ring model; the chosen based CW model of `S⁰` is exposed separately by
`presentation.sphereZero` and `presentation.sphereZeroIso`. -/
theorem modTwoEilenbergMacLaneSpectrumHomologyPresentation_spec
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    ∀ n : ℕ,
      IsAdditiveEilenbergMacLaneSpace
        (ZMod 2) n (presentation.toPrespectrum.basedSpace n) :=
  presentation.stageIsKZ2

/-- The chosen based CW model of `S⁰` carried by a homology presentation of `HZ_2` is identified
with the Chapter 11 `S⁰` owner `sphereZero`. -/
abbrev modTwoEilenbergMacLaneSpectrumHomologyPresentation_sphereZero_spec
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    presentation.sphereZeroBasedSpace ≅ _root_.sphereZero :=
  presentation.sphereZeroIso

/-- The source unit map of a homology presentation of `HZ_2` is the unit of its chosen ring
prespectrum model. -/
@[simp] theorem modTwoEilenbergMacLaneSpectrumHomologyPresentation_sourceUnit_spec
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    presentation.sourceUnit = presentation.toRingPrespectrum.unit :=
  rfl

/-- The source multiplication maps of a homology presentation of `HZ_2` are the multiplications
of its chosen ring-prespectrum model. -/
@[simp] theorem modTwoEilenbergMacLaneSpectrumHomologyPresentation_sourceMul_spec
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    ∀ m n : ℕ, presentation.sourceMul m n = presentation.toRingPrespectrum.mul m n :=
  fun _ _ ↦ rfl

/-- The total source-facing homology object `H_*(HZ_2)` attached to a chosen `HZ_2` homology
presentation, formed as the direct sum of the degreewise reduced homology groups of the chosen
based `S⁰` model. -/
abbrev modTwoEilenbergMacLaneSpectrumHomology
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) : Type :=
  ⨁ n : ℕ,
    ((connectivePrespectrumReducedHomology
      presentation.toPrespectrum presentation.homologyPresentation) (n : ℤ)).obj
        presentation.sphereZeroBasedCWComplex

/-- `modTwoEilenbergMacLaneSpectrumHomology` is definitionally the direct sum of the degreewise
reduced homology groups of the chosen based `S⁰` model under the chosen `HZ_2` homology
presentation. -/
theorem modTwoEilenbergMacLaneSpectrumHomology_def
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    modTwoEilenbergMacLaneSpectrumHomology presentation =
      ⨁ n : ℕ,
        ((connectivePrespectrumReducedHomology
          presentation.toPrespectrum presentation.homologyPresentation) (n : ℤ)).obj
            presentation.sphereZeroBasedCWComplex :=
  rfl

/-- The preexisting additive commutative group structure on the total homology object
`H_*(HZ_2)`. -/
private noncomputable abbrev modTwoEilenbergMacLaneSpectrumHomologyAddCommGroup
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) :
    AddCommGroup (modTwoEilenbergMacLaneSpectrumHomology presentation) :=
  inferInstance

/-- The `ZMod 2`-algebra structures on the fixed homology object `H_*(HZ_2)` whose semiring
structure comes from a chosen ring structure. -/
abbrev modTwoEilenbergMacLaneSpectrumHomologyAlgebraStructure
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation)
    (toRing : Ring (modTwoEilenbergMacLaneSpectrumHomology presentation)) : Type :=
  let _ : Ring (modTwoEilenbergMacLaneSpectrumHomology presentation) := toRing
  Algebra (ZMod 2) (modTwoEilenbergMacLaneSpectrumHomology presentation)

/-- A chosen source-facing algebra structure on the fixed total homology object `H_*(HZ_2)`
attached to a chosen `HZ_2` homology presentation. -/
structure ModTwoEilenbergMacLaneSpectrumHomologyAlgebra
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation) where
  /-- The ring structure on the fixed total homology object `H_*(HZ_2)`. -/
  toRing : Ring (modTwoEilenbergMacLaneSpectrumHomology presentation)
  /-- The additive commutative group underlying the ring structure on `H_*(HZ_2)` agrees with the
  preexisting direct-sum additive structure. -/
  addCommGroup_eq :
    toRing.toAddCommGroup = modTwoEilenbergMacLaneSpectrumHomologyAddCommGroup presentation
  /-- The `ZMod 2`-algebra structure on the fixed total homology object `H_*(HZ_2)`. -/
  toAlgebra : modTwoEilenbergMacLaneSpectrumHomologyAlgebraStructure presentation toRing

/-- The data carried by `ModTwoEilenbergMacLaneSpectrumHomologyAlgebra` is a ring and `ZMod 2`
algebra structure on the fixed total homology object `H_*(HZ_2)`, compatible with the preexisting
direct-sum additive structure. The source unit and source multiplication maps remain the canonical
ones on `presentation.toRingPrespectrum`, exposed by
`presentation.sourceUnit` and `presentation.sourceMul`. -/
theorem modTwoEilenbergMacLaneSpectrumHomologyAlgebra_spec
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation)
    (HStar : ModTwoEilenbergMacLaneSpectrumHomologyAlgebra presentation) :
    HStar.toRing.toAddCommGroup =
      modTwoEilenbergMacLaneSpectrumHomologyAddCommGroup presentation :=
  HStar.addCommGroup_eq

namespace ModTwoSteenrodAlgebraDual

/-- The `ZMod 2`-algebra equivalences between a chosen dual Steenrod algebra owner `A_*` and a
chosen homology algebra owner on `H_*(HZ_2)`. This bridge hides the ambient ring and algebra
instances determined by the two owners. -/
abbrev hz2HomologyAlgEquiv
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation)
    (HStar : ModTwoEilenbergMacLaneSpectrumHomologyAlgebra presentation) : Type :=
  let _ : Ring modTwoSteenrodAlgebraGradedDual := AStar.toRing
  let _ : Algebra (ZMod 2) modTwoSteenrodAlgebraGradedDual := AStar.toAlgebra
  let _ : Ring (modTwoEilenbergMacLaneSpectrumHomology presentation) := HStar.toRing
  let _ : Algebra (ZMod 2) (modTwoEilenbergMacLaneSpectrumHomology presentation) := HStar.toAlgebra
  modTwoSteenrodAlgebraGradedDual ≃ₐ[ZMod 2]
    modTwoEilenbergMacLaneSpectrumHomology presentation

/-- Lemma 25.4.6. The dual Steenrod algebra `A_*` is isomorphic as a `ZMod 2`-algebra to
`H_*(HZ_2)`. Concretely, there exist a chosen source-semantic algebra owner on the fixed linear
graded dual `A_*`, a chosen source-facing presentation of `H_*(HZ_2)`, a chosen source-semantic algebra
owner on that homology object, and an actual `ZMod 2`-algebra equivalence between those specific
textbook algebras. The auxiliary presentation and structure owners remain support API rather than
the main public statement. -/
theorem exists_hz2HomologyAlgEquiv :
    ∃ (AStar : ModTwoSteenrodAlgebraDualAlgebra)
      (presentation : ModTwoEilenbergMacLaneSpectrumHomologyPresentation)
      (HStar : ModTwoEilenbergMacLaneSpectrumHomologyAlgebra presentation),
      Nonempty (hz2HomologyAlgEquiv AStar presentation HStar) := sorry

end ModTwoSteenrodAlgebraDual
