import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWType
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_2

open CategoryTheory Limits
open HomotopicalAlgebra
open scoped Topology Topology.Homotopy

noncomputable section

universe u w

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall: `lean_leansearch` did not surface a ready-made prespectrum-homology owner in
-- the current environment. Local Chapter 14/22 precedent instead packages the source formula by
-- explicit sequential colimit data on based CW complexes, with the stabilization maps recorded as
-- a named system and the theorem stated relative to the Chapter 14 owner
-- `BasedCWReducedSuspensionCofiberSetup`.

/-- The source `(n - 1)`-connectedness hypothesis for the `n`th prespectrum space: stage `0`
imposes no condition, while stage `m + 1` requires `m`-connectedness. -/
abbrev prespectrumConnectivityHypothesis
    (n : ℕ) (X : PointedCompactlyGenerated.{u, w}) : Prop :=
  match n with
  | 0 => True
  | m + 1 => NConnectedSpace m X.toCompactlyGenerated

/-- The stagewise CW-type hypothesis for a prespectrum `T`: each underlying space `T n` has CW
type in the repository sense `TopCat.HasCWType`, rather than being required to carry an actual
CW-complex structure. -/
abbrev prespectrumCWHypothesis (T : Prespectrum.{u, w}) : Prop :=
  ∀ n : ℕ, TopCat.HasCWType (T n).toCompactlyGenerated.toTop

/-- The cofinal tail index used to present the source formula `colim_n π_(q + n)(X ∧ T_n)` with
all displayed homotopy groups in degree at least `2`. -/
abbrev connectivePrespectrumTailIndex (q : ℤ) (n : ℕ) : ℕ :=
  n + Int.natAbs q + 2

/-- The corresponding displayed homotopy degree in the cofinal tail computing
`colim_n π_(q + n)(X ∧ T_n)`. -/
abbrev connectivePrespectrumDisplayedDegree (q : ℤ) (n : ℕ) : ℕ :=
  Int.toNat (q + (n + Int.natAbs q : ℤ)) + 2

/-- The based-space stage `X ∧ T_(n + |q| + 2)` appearing in the source formula. -/
abbrev prespectrumReducedHomologyStageSpace
    (T : Prespectrum.{u, w}) (q : ℤ) (X : BasedCWComplex) (n : ℕ) : BasedSpace :=
  smashProduct X.1
    (PointedCompactlyGenerated.toBasedSpace (T (connectivePrespectrumTailIndex q n)))

/-- The suspended based-space stage `X ∧ Σ(T_(n + |q| + 2))` appearing in the canonical
stabilization diagram for the source formula. -/
abbrev prespectrumReducedHomologySuspensionStageSpace
    (T : Prespectrum.{u, w}) (q : ℤ) (X : BasedCWComplex) (n : ℕ) : BasedSpace :=
  smashProduct X.1
    (PointedCompactlyGenerated.toBasedSpace
      ((reducedSuspension (T (connectivePrespectrumTailIndex q n))) :
        PointedCompactlyGenerated.{u, w}))

/-- The `n`th additive stage in the cofinal tail of the prespectrum-homology formula attached to
`T`, degree `q`, and based CW complex `X`. This is the higher homotopy group of
`X ∧ T_(n + |q| + 2)`, written in additive form so that the sequential colimit lands in
`AddCommGrpCat`. -/
abbrev prespectrumReducedHomologyStage
    (T : Prespectrum.{u, w}) (q : ℤ) (X : BasedCWComplex) (n : ℕ) : AddCommGrpCat.{w} :=
  AddCommGrpCat.of
    (Additive
      (π_ (connectivePrespectrumDisplayedDegree q n)
        (prespectrumReducedHomologyStageSpace T q X n).right
        (underTopBasepoint (prespectrumReducedHomologyStageSpace T q X n))))

/-- The suspended `n`th additive stage in the canonical stabilization diagram for the source
formula `colim_n π_(q + n)(X ∧ T_n)`. -/
abbrev prespectrumReducedHomologySuspensionStage
    (T : Prespectrum.{u, w}) (q : ℤ) (X : BasedCWComplex) (n : ℕ) : AddCommGrpCat.{w} :=
  AddCommGrpCat.of
    (Additive
      (π_ (connectivePrespectrumDisplayedDegree q n + 1)
        (prespectrumReducedHomologySuspensionStageSpace T q X n).right
        (underTopBasepoint (prespectrumReducedHomologySuspensionStageSpace T q X n))))

/-- The source-facing stabilization data for the prespectrum formula on a fixed degree `q` and
based CW complex `X`, split into the suspension part and the structure-map part so that the
system records the canonical source diagram rather than only a single arbitrary successor map. -/
structure PrespectrumReducedHomologySystem
    (T : Prespectrum.{u, w}) (q : ℤ) (X : BasedCWComplex) where
  /-- The suspension comparison `π_k(X ∧ T_j) ⟶ π_(k + 1)(X ∧ ΣT_j)` in the canonical source
  diagram. -/
  suspensionStep (n : ℕ) :
    prespectrumReducedHomologyStage T q X n ⟶
      prespectrumReducedHomologySuspensionStage T q X n
  /-- The map induced by the prespectrum structure map `ΣT_j ⟶ T_(j + 1)` on the canonical source
  diagram. -/
  structureStep (n : ℕ) :
    prespectrumReducedHomologySuspensionStage T q X n ⟶
      prespectrumReducedHomologyStage T q X (n + 1)

namespace PrespectrumReducedHomologySystem

/-- The composite stabilization map `π_k(X ∧ T_j) ⟶ π_(k + 1)(X ∧ T_(j + 1))` recorded by a
source-faithful prespectrum-homology system. -/
abbrev step
    {T : Prespectrum.{u, w}} {q : ℤ} {X : BasedCWComplex}
    (system : PrespectrumReducedHomologySystem T q X) (n : ℕ) :
    prespectrumReducedHomologyStage T q X n ⟶
      prespectrumReducedHomologyStage T q X (n + 1) :=
  system.suspensionStep n ≫ system.structureStep n

/-- The sequential `AddCommGrpCat`-diagram attached to a source-faithful prespectrum-homology
system. -/
abbrev diagram
    {T : Prespectrum.{u, w}} {q : ℤ} {X : BasedCWComplex}
    (system : PrespectrumReducedHomologySystem T q X) :
    ℕ ⥤ AddCommGrpCat.{w} :=
  Functor.ofSequence system.step

/-- The filtered colimit attached to a source-faithful prespectrum-homology system. -/
abbrev colimit
    {T : Prespectrum.{u, w}} {q : ℤ} {X : BasedCWComplex}
    (system : PrespectrumReducedHomologySystem T q X) :
    AddCommGrpCat.{w} :=
  AddCommGrpCat.FilteredColimits.colimit system.diagram

end PrespectrumReducedHomologySystem

/-- A source-faithful presentation of the connective prespectrum homology formula attached to `T`.
It packages a concrete `ℤ`-graded functor family on based CW complexes together with the canonical
stabilization systems whose filtered colimits compute its values pointwise, together with explicit
named suspension and structure comparison families for the source diagram
`colim_n π_(q + n)(X ∧ T_n)`. -/
structure ConnectivePrespectrumReducedHomologyPresentation
    (T : Prespectrum.{u, w}) where
  /-- The `ℤ`-graded functor family realizing the source formula on based CW complexes. -/
  E : ℤ → BasedCWComplex ⥤ AddCommGrpCat.{w}
  /-- The named suspension comparison
  `π_k(X ∧ T_j) ⟶ π_(k + 1)(X ∧ Σ(T_j))` used in the source stabilization system. -/
  suspensionComparison (q : ℤ) (X : BasedCWComplex) (n : ℕ) :
    prespectrumReducedHomologyStage T q X n ⟶
      prespectrumReducedHomologySuspensionStage T q X n
  /-- The named structure-map comparison
  `π_(k + 1)(X ∧ Σ(T_j)) ⟶ π_(k + 1)(X ∧ T_(j + 1))` induced by the prespectrum structure map
  `Σ(T_j) ⟶ T_(j + 1)`. -/
  structureComparison (q : ℤ) (X : BasedCWComplex) (n : ℕ) :
    prespectrumReducedHomologySuspensionStage T q X n ⟶
      prespectrumReducedHomologyStage T q X (n + 1)
  /-- The canonical stabilization system presenting `Ẽ_q(X) = colim_n π_(q + n)(X ∧ T_n)` in
  degree `q` at a based CW complex `X`, using the named suspension and structure comparisons. -/
  canonicalSystem (q : ℤ) (X : BasedCWComplex) : PrespectrumReducedHomologySystem T q X
  /-- The suspension part of the recorded system is exactly the named source suspension
  comparison. -/
  suspensionComparison_spec (q : ℤ) (X : BasedCWComplex) (n : ℕ) :
    (canonicalSystem q X).suspensionStep n = suspensionComparison q X n
  /-- The structure-map part of the recorded system is exactly the named map induced by the
  prespectrum structure map. -/
  structureComparison_spec (q : ℤ) (X : BasedCWComplex) (n : ℕ) :
    (canonicalSystem q X).structureStep n = structureComparison q X n
  /-- Pointwise, `E q` is identified with the filtered colimit of the canonical stabilization
  system in degree `q`. -/
  comparison (q : ℤ) (X : BasedCWComplex) :
    (E q).obj X ≅ (canonicalSystem q X).colimit

/-- The canonically named `ℤ`-graded functor family attached to a connective prespectrum `T`,
realizing the source formula `Ẽ_q(X) = colim_n π_(q + n)(X ∧ T_n)` through explicit
presentation data and named source stabilization maps for `T`. -/
abbrev connectivePrespectrumReducedHomology
    (T : Prespectrum.{u, w}) (presentation : ConnectivePrespectrumReducedHomologyPresentation T) :
    ℤ → BasedCWComplex ⥤ AddCommGrpCat.{w} :=
  presentation.E

/-- A source-faithful presentation of the connective prespectrum homology formula yields the
corresponding reduced homology theory structure on based CW complexes, assuming the stagewise
well-pointedness input used by Theorem 11.2.2. This is a theorem rather than an `instance`
because the suspension/cofiber infrastructure is explicit source data and is not determined by the
graded functor alone. -/
theorem connectivePrespectrumReducedHomologyTheoryOfPresentation
    [CategoryWithCofibrations BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (T : Prespectrum.{u, 0})
    (presentation : ConnectivePrespectrumReducedHomologyPresentation T)
    (h_connected : ∀ n : ℕ, prespectrumConnectivityHypothesis n (T n))
    (h_cw : prespectrumCWHypothesis T)
    (h_wellPointed : ∀ n : ℕ, WellPointedSpace (T n)) :
    ReducedHomologyTheoryOnBasedCWComplexes
      setup.suspension setup.cofiber setup.cofiberMap
      (connectivePrespectrumReducedHomology T presentation) := sorry

/-- Theorem 22.1.3: if each prespectrum space `T n` satisfies the source `(n - 1)`-connectedness
hypothesis and has CW type, then the source formula
`Ẽ_q(X) = colim_n π_(q + n)(X ∧ T_n)` admits some explicit homology-theory infrastructure and
presentation whose associated graded functor is a reduced homology theory on based CW complexes.
The stagewise well-pointedness input needed for Theorem 11.2.2 is made explicit. -/
theorem connectivePrespectrumDefinesReducedHomologyTheory
    [CategoryWithCofibrations BasedCWComplex]
    (T : Prespectrum.{u, 0})
    (h_connected : ∀ n : ℕ, prespectrumConnectivityHypothesis n (T n))
    (h_cw : prespectrumCWHypothesis T)
    (h_wellPointed : ∀ n : ℕ, WellPointedSpace (T n)) :
    ∃ presentation : ConnectivePrespectrumReducedHomologyPresentation T,
      ∃ setup : BasedCWReducedSuspensionCofiberSetup,
        ReducedHomologyTheoryOnBasedCWComplexes
          setup.suspension setup.cofiber setup.cofiberMap
          (connectivePrespectrumReducedHomology T presentation) := sorry
