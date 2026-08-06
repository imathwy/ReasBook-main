import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Theorem_11_2_2

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for `π_ q`,
-- while the local Chapter 11 API already packages the stable-homotopy colimit presentation and
-- its suspension-stage maps via `stableHomotopyGroup`, `stableHomotopyGroupStage`, and
-- `stableHomotopyGroupStepMap`.

/- Remark 11.2.6. This remark is interpretive rather than a new standalone theorem. In the
current Chapter 11 API, `stableHomotopyGroup X q` is the filtered colimit of the suspension-stage
diagram `n ↦ stableHomotopyGroupStage X q n`, with structure maps
`stableHomotopyGroupStepMap X q n`; by Definition 11.2.5 this uses the shifted presentation
`π_ (q + n + 1) (Σ^(n + 1) X)`, so the source stage `π_ (q + n) (Σ^n X)` is recovered by
reindexing. Under the well-pointedness and connectivity hypotheses from Theorem 11.2.2,
`freudenthalSuspension_bijective` is the mechanism expressing that in the Freudenthal range the
stable group has already stabilized at a finite suspension stage. The final sentence about stable
homotopy groups of spheres controlling deep geometric-topology problems is motivational, so this
item is recorded by direct reference to the existing canonical APIs. -/
#check stableHomotopyGroup

/- The suspension stages in that filtered colimit are the groups
`π_ (q + n + 1) (Σ^(n + 1) X)`, i.e. a reindexed form of the source stages `π_ (q + n) (Σ^n X)`.
-/
#check stableHomotopyGroupStage

/- `stableHomotopyGroup_def` unfolds the stable group as the filtered colimit of its suspension
diagram. -/
#check stableHomotopyGroup_def

/- `stableHomotopyGroupStage_def` identifies each stage with the shifted iterated-suspension
homotopy group used to keep the whole diagram group-valued. -/
#check stableHomotopyGroupStage_def

/- `stableHomotopyGroupStepMap` is the structure morphism induced by suspension between successive
stages. -/
#check stableHomotopyGroupStepMap

/- `freudenthalSuspension_bijective` is the finite-stage stabilization mechanism in the
Freudenthal range. -/
#check freudenthalSuspension_bijective
