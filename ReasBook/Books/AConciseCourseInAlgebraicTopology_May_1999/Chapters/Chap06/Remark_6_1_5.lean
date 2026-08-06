import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4

-- Semantic recall: `lean_leansearch` only found the model-category result
-- `HomotopicalAlgebra.PathObject.RightHomotopy.homotopy_extension`, not a topological
-- `ContinuousMap` cofibration API. For this section, `IsCofibration` is the source-faithful owner.
/- Remark 6.1.5: in the HEP diagram, a cofibration only asks for an extending homotopy to exist.
The local owner `IsCofibration i` and its companion `IsCofibration.exists_homotopy_extension`
therefore encode
cofibrations as homotopical extension objects, not as uniqueness objects: the payload is an
existence statement `∃ G, ∃ F, ...`, with no uniqueness field. -/
recall IsCofibration
recall IsCofibration.exists_homotopy_extension
