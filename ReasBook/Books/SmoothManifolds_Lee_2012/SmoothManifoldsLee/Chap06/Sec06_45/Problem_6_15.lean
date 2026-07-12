import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Theorem_6_32

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` surfaced the graph/diffeomorphism/transversality API,
-- and local Chapter 6 inspection verified that this problem is a direct recall of Theorem 6.32.
/-
Problem 6-15 is recall-only in this item-per-file formalization.
Source-facing content: the global characterization of graphs in the three clauses proved in
Theorem 6.32.
Canonical Lean surface: reuse the three existing theorem owners directly instead of duplicating the
same graph / restricted-projection / vertical-slice statement layer in a second file.
-/
recall graphCondition_iff_restrictedFirstProjection_diffeomorph
recall restrictedFirstProjection_diffeomorph_iff_uniqueTransverseVerticalSlices
recall graphingMap_eq_secondProjection_comp_restrictedFirstProjectionInverse
